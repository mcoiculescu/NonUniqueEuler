#!/usr/bin/env python3
"""Check that two copies of the Lean sources contain the same code, ignoring comments.

Usage:
    python3 tools/check_identical_code.py ORIGINAL_ROOT [RELEASE_ROOT] [--verbose]

ORIGINAL_ROOT and RELEASE_ROOT are Lake project roots (the directories that contain
`lakefile.toml`). RELEASE_ROOT defaults to the parent directory of this script.

For every `.lean` file under `NonUniqueEuler/`, and for the root file `NonUniqueEuler.lean`, the
script removes all Lean comments and compares the remaining code. The comments removed are
`-- ...` line comments and nested `/- ... -/` block comments, including doc comments `/-- ... -/`
and module docs `/-! ... -/`. String literals (also interpolated strings `s!"..{..}.."`) and
character literals are lexed so that comment markers inside them are not treated as comments.

Two comparisons are made:
  * strict:  comments are replaced by a single space, then every run of whitespace outside
             string literals is collapsed to one space;
  * loose:   comments are removed, then all whitespace outside string literals is removed.
Both must agree for every file. In addition the set of `.lean` files must be the same in both
trees; `lake-manifest.json` and `lean-toolchain` must be byte-identical, and `lakefile.toml` identical
up to `#` comment lines.

Exit code 0 iff every check passes. Standard library only.
"""
import os
import re
import sys

IDENT_EXTRA = set("_'!?.")


def _is_ident_char(ch):
    return ch.isalnum() or ch in IDENT_EXTRA or ("₀" <= ch <= "ₜ") or ch == "ᵢ"


def lex(src):
    """Split Lean source into segments (kind, text), kind in {'code', 'string', 'comment'}.

    The concatenation of all segment texts is `src`. Raises ValueError on an unterminated
    block comment or string literal.
    """
    segs = []
    n = len(src)
    i = 0
    code_start = 0

    def flush(upto):
        if upto > code_start:
            segs.append(("code", src[code_start:upto]))

    def scan_string(j):
        """`src[j]` is the opening quote; return the index just past the closing quote."""
        interp = j > 0 and src[j - 1] == "!" and j > 1 and src[j - 2].isalpha()
        k = j + 1
        while k < n:
            c = src[k]
            if c == "\\":
                k += 2
                continue
            if c == '"':
                return k + 1
            if interp and c == "{":
                k = scan_interp(k + 1)
                continue
            k += 1
        raise ValueError(f"unterminated string literal at offset {j}")

    def scan_interp(k):
        """Inside `{ ... }` of an interpolated string; return index just past the `}`."""
        depth = 1
        while k < n:
            c = src[k]
            if c == '"':
                k = scan_string(k)
                continue
            if src.startswith("/-", k):
                k = scan_block(k)
                continue
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
                if depth == 0:
                    return k + 1
            k += 1
        raise ValueError("unterminated interpolation")

    def scan_block(j):
        """`src[j:j+2] == '/-'`; return the index just past the matching `-/`."""
        depth = 0
        k = j
        while k < n:
            if src.startswith("/-", k):
                depth += 1
                k += 2
                continue
            if src.startswith("-/", k):
                depth -= 1
                k += 2
                if depth == 0:
                    return k
                continue
            k += 1
        raise ValueError(f"unterminated block comment at offset {j}")

    while i < n:
        c = src[i]
        if src.startswith("/-", i):
            flush(i)
            j = scan_block(i)
            segs.append(("comment", src[i:j]))
            i = code_start = j
            continue
        if src.startswith("--", i):
            flush(i)
            j = src.find("\n", i)
            j = n if j < 0 else j
            segs.append(("comment", src[i:j]))
            i = code_start = j
            continue
        if c == '"':
            flush(i)
            j = scan_string(i)
            segs.append(("string", src[i:j]))
            i = code_start = j
            continue
        if c == "'" and (i == 0 or not _is_ident_char(src[i - 1])):
            # character literal 'x', '\n', '\'', '\x41', '\u{3bb}'
            j = None
            if i + 2 < n and src[i + 1] != "\\" and src[i + 2] == "'":
                j = i + 3
            elif i + 1 < n and src[i + 1] == "\\":
                k = src.find("'", i + 3)
                if 0 < k <= i + 12:
                    j = k + 1
            if j is not None:
                i = j  # stays inside the current code segment
                continue
        i += 1
    flush(n)
    return segs


def normalize(src, mode):
    """The code of `src` without comments, as a list of code chunks and string literals.

    strict: each comment becomes one space and whitespace runs outside strings become one space;
    loose:  comments and all whitespace outside strings are removed.
    """
    pieces = []  # alternating: code text (str), then ('S', literal)
    buf = []
    for kind, text in lex(src):
        if kind == "string":
            pieces.append("".join(buf))
            pieces.append(("S", text))
            buf = []
        elif kind == "comment":
            buf.append(" " if mode == "strict" else "")
        else:
            buf.append(text)
    pieces.append("".join(buf))
    out = []
    for p in pieces:
        if isinstance(p, tuple):
            out.append(p)
        elif mode == "strict":
            out.append(re.sub(r"\s+", " ", p))
        else:
            out.append(re.sub(r"\s+", "", p))
    if mode == "strict" and out:
        out[0] = out[0].lstrip()
        out[-1] = out[-1].rstrip()
    return out


def lean_files(root):
    out = set()
    base = os.path.join(root, "NonUniqueEuler")
    for d, _, fs in os.walk(base):
        for f in fs:
            if f.endswith(".lean"):
                out.add(os.path.relpath(os.path.join(d, f), root))
    if os.path.exists(os.path.join(root, "NonUniqueEuler.lean")):
        out.add("NonUniqueEuler.lean")
    return out


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def main(argv):
    verbose = "--verbose" in argv
    args = [a for a in argv if not a.startswith("--")]
    if not args:
        print(__doc__)
        return 2
    orig = os.path.abspath(args[0])
    rel = os.path.abspath(args[1]) if len(args) > 1 else os.path.dirname(
        os.path.dirname(os.path.abspath(__file__)))
    ok = True

    for f in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        a, b = os.path.join(orig, f), os.path.join(rel, f)
        if not (os.path.exists(a) and os.path.exists(b)):
            print(f"MISSING  {f}")
            ok = False
            continue
        with open(a, "rb") as fa, open(b, "rb") as fb:
            da, db = fa.read(), fb.read()
        if f == "lakefile.toml":
            # TOML: compare with `#` comment lines removed (the release rewords one comment).
            strip_toml = lambda t: b"\n".join(l for l in t.splitlines() if not l.lstrip().startswith(b"#"))
            same = strip_toml(da) == strip_toml(db)
            mode = "comparison without # comment lines"
        else:
            same = da == db
            mode = "byte comparison"
        print(f"{'IDENTICAL' if same else 'DIFFERS  '}  {f} ({mode})")
        ok &= same

    fa, fb = lean_files(orig), lean_files(rel)
    only_a, only_b = sorted(fa - fb), sorted(fb - fa)
    for f in only_a:
        print(f"ONLY IN ORIGINAL  {f}")
    for f in only_b:
        print(f"ONLY IN RELEASE   {f}")
    ok &= not only_a and not only_b

    n_same = n_diff = n_comment_changed = 0
    for f in sorted(fa & fb):
        sa, sb = read(os.path.join(orig, f)), read(os.path.join(rel, f))
        try:
            same = all(normalize(sa, m) == normalize(sb, m) for m in ("strict", "loose"))
        except ValueError as e:
            print(f"LEX ERROR  {f}: {e}")
            ok = False
            n_diff += 1
            continue
        if same:
            n_same += 1
            if sa != sb:
                n_comment_changed += 1
                if verbose:
                    print(f"same code, comments differ  {f}")
        else:
            n_diff += 1
            ok = False
            print(f"CODE DIFFERS  {f}")
    print(f"{len(fa & fb)} Lean files compared: {n_same} identical after stripping comments "
          f"({n_comment_changed} with edited comments, {n_same - n_comment_changed} byte-identical),"
          f" {n_diff} differ")
    print("RESULT: PASS" if ok else "RESULT: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
