#!/usr/bin/env python3
"""Generate the Lean certificate data of part (2) from the package's certificate files.

Usage (from the root of this repository):
    python3 -I -B tools/gen_cert_data.py PACKAGE_DIR [--manuscript A_verification.tex]          # write
    python3 -I -B tools/gen_cert_data.py PACKAGE_DIR [--manuscript A_verification.tex] --check  # compare

PACKAGE_DIR is the root of the Python/Arb reproduction package `euler-ring-certificate`.

Reads (never writes)
    PACKAGE_DIR/certificates/sector3_count_cells.json   ((N1') run, 25 cells)
    PACKAGE_DIR/certificates/sector3_gap_cells.json     ((N2') run, 236 cells)
and writes (relative to the root of this repository)
    NonUniqueEuler/Verify/Data/CellLits.lean   (core only: `certLits : CertSpec`, exact literals)
    NonUniqueEuler/Verify/Data/Cells.lean      (`cert : CertificateData`, and `check_cert`)
With --check it writes nothing and reports whether the two files are up to date.

Checks before writing (it refuses on any failure):
  * the SHA-256 of each file equals the digest quoted in the manuscript (A_verification.tex,
    Section "Reproduction"); the digests are pinned below and, when the manuscript source is
    given with --manuscript, also looked up in it;
  * format "ringcert-certificate-1", the item ("N1'" / "N2'"), sector 3;
  * the "data" block equals the pinned data (data.data_strings() of the package);
  * the "parameters" equal COUNT_PARAMS / GAP_PARAMS of sector3.py;
  * every cell has "G": [lo, hi] and "rect": [x0, x1, y0, y1] as exact rational strings.

Standard library only; no floating-point number is created.
"""
import hashlib
import json
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)  # root of this repository (the Lake project)
PKG = None          # set from the command line
MANUSCRIPT = None   # optional, set from the command line

FILES = {
    "count": ("sector3_count_cells.json", "N1'",
              "518a0ca4f05fd24bae273aebea20862fad1c1beb46dbdee9f8b5fb76c8729dc1",
              {"npu": "20", "max_iter": 16, "max_seg": 6000, "depth": 4}),
    "gap": ("sector3_gap_cells.json", "N2'",
            "fb95a3f72eee1f017ddc5c26e7dfca52841759603e34b0131a440c8992086c91",
            {"npu_numerator": "3", "max_iter": 10, "max_seg": 800, "depth": 5}),
}

DATA = {
    "a0": "-7304210039150669/18014398509481984",
    "d": "5764607523034235/288230376151711744",
    "sL": "-4528212286209965/4503599627370496",
    "sa": "-4077852323472915/4503599627370496",
    "sb": "1/2",
    "sR": "5404319552844595/9007199254740992",
    "Gmax": "5764607523034235/288230376151711744",
}

OUT_LITS = os.path.join(ROOT, "NonUniqueEuler", "Verify", "Data", "CellLits.lean")
OUT_CELLS = os.path.join(ROOT, "NonUniqueEuler", "Verify", "Data", "Cells.lean")


def fail(msg):
    print("gen_cert_data: REFUSED: " + msg, file=sys.stderr)
    sys.exit(1)


def sha256(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def manuscript_digests():
    """The 64-hex-digit strings quoted in the manuscript (None if no source was given)."""
    if MANUSCRIPT is None:
        return None
    if not os.path.exists(MANUSCRIPT):
        fail(f"manuscript source {MANUSCRIPT} not found")
    out = set()
    with open(MANUSCRIPT) as f:
        for line in f:
            for tok in line.replace("{", " ").replace("}", " ").split():
                if len(tok) == 64 and all(c in "0123456789abcdef" for c in tok):
                    out.add(tok)
    return out


def frac(s):
    if not isinstance(s, str):
        fail(f"not an exact rational string: {s!r}")
    q = Fraction(s)
    if str(q) != s:
        fail(f"rational string not in lowest terms / canonical form: {s!r}")
    return q


def lit(q):
    """The Lean literal `q n d` of the rational q."""
    n, d = q.numerator, q.denominator
    return f"q {n} {d}" if n >= 0 else f"q ({n}) {d}"


def load(which):
    fn, item, digest, params = FILES[which]
    path = os.path.join(PKG, "certificates", fn)
    got = sha256(path)
    if got != digest:
        fail(f"{fn}: sha256 {got} differs from the manuscript's {digest}")
    with open(path) as f:
        C = json.load(f)
    if C.get("format") != "ringcert-certificate-1":
        fail(f"{fn}: format {C.get('format')!r}")
    if C.get("item") != item:
        fail(f"{fn}: item {C.get('item')!r}, expected {item!r}")
    if C.get("sector") != 3 or type(C.get("sector")) is not int:
        fail(f"{fn}: sector {C.get('sector')!r}")
    if C.get("data") != DATA:
        fail(f"{fn}: data block differs from the pinned data")
    if C.get("parameters") != params:
        fail(f"{fn}: parameters {C.get('parameters')!r} differ from {params!r}")
    cells = []
    for c in C["cells"]:
        if set(c) != {"G", "rect"} or len(c["G"]) != 2 or len(c["rect"]) != 4:
            fail(f"{fn}: malformed cell {c!r}")
        cells.append(([frac(v) for v in c["G"]], [frac(v) for v in c["rect"]]))
    return fn, digest, params, cells


def cell_line(c):
    (lo, hi), (x0, x1, y0, y1) = c
    return f"  ⟨{lit(lo)}, {lit(hi)}, ⟨{lit(x0)}, {lit(x1)}, {lit(y0)}, {lit(y1)}⟩⟩"


def gen():
    cnt = load("count")
    gap = load("gap")
    header = (
        "-- GENERATED by tools/gen_cert_data.py; do not edit.\n"
        f"-- Source: euler-ring-certificate/certificates/{cnt[0]}\n"
        f"--   sha256 {cnt[1]} (as quoted in A_verification.tex)\n"
        f"-- Source: euler-ring-certificate/certificates/{gap[0]}\n"
        f"--   sha256 {gap[1]} (as quoted in A_verification.tex)\n")
    lits = [header,
            "import NonUniqueEuler.Verify.Comp.RunCore\n\n",
            "/-!\n# Part 2 data: the certificate cells (core form)\n\n"
            "The cells and parameters of the two certificate files, with every number an exact\n"
            "rational literal `q n d = n/d` (`mkRat`), in the order of the files. Core only, so that\n"
            "the executable `Verify/Main.lean` needs no Mathlib. The statement-layer form is\n"
            "`Verify.cert` (`Data/Cells.lean`). `certLits` is `@[irreducible]`: no proof or tactic\n"
            "may evaluate it (checker design decision D14).\n-/\n\n",
            "namespace NonUniqueEuler.Verify\n\nnamespace CellLits\n\n",
            "/-- The rational `n / d`. -/\n@[inline] def q (n : Int) (d : Nat) : Rat := mkRat n d\n\n",
            f"/-- The {len(cnt[3])} cells of the (N1′) run (`{cnt[0]}`). -/\n",
            "def countCells : List CellSpec := [\n",
            ",\n".join(cell_line(c) for c in cnt[3]), "]\n\n",
            f"/-- The {len(gap[3])} cells and rectangles of the (N2′) run (`{gap[0]}`). -/\n",
            "def gapCells : List CellSpec := [\n",
            ",\n".join(cell_line(c) for c in gap[3]), "]\n\n",
            "end CellLits\n\n",
            "open CellLits in\n",
            "/-- The certificate data (core form): the cells of the two files and their parameters\n"
            "(`npu = 20`, 16 rounds, 6000 segments, 4 halvings; `npu_numerator = 3`, 10 rounds,\n"
            "800 segments, 5 halvings). -/\n",
            "@[irreducible] def certLits : CertSpec where\n",
            "  countCells := countCells\n",
            f"  countParams := ⟨{lit(Fraction(cnt[2]['npu']))}, {cnt[2]['max_iter']}, "
            f"{cnt[2]['max_seg']}, {cnt[2]['depth']}⟩\n",
            "  gapCells := gapCells\n",
            f"  gapParams := ⟨{lit(Fraction(gap[2]['npu_numerator']))}, {gap[2]['max_iter']}, "
            f"{gap[2]['max_seg']}, {gap[2]['depth']}⟩\n\n",
            "end NonUniqueEuler.Verify\n"]
    cells = [header,
             "import NonUniqueEuler.Verify.Comp.Runs\n",
             "import NonUniqueEuler.Verify.Data.CellLits\n\n",
             "/-!\n# Part 2 data: the certificate `Verify.cert`\n\n"
             "`cert : CertificateData` is the statement-layer form of `certLits`\n"
             "(`Data/CellLits.lean`, generated from the two certificate files). `check_cert` says that\n"
             "`check cert` is the value `checkCore defaultPrec certLits` that the executable\n"
             "`Verify/Main.lean` computes; its proof evaluates nothing.\n-/\n\n",
             "namespace NonUniqueEuler.Verify\n\n",
             "/-- **The certificate**: the cells, rectangles and parameters of the two runs of\n"
             "§A.6, transcribed from `sector3_count_cells.json` and `sector3_gap_cells.json`. -/\n",
             "def cert : CertificateData := certLits.toCertificateData\n\n",
             "/-- The checker on the certificate is the core computation of the executable. -/\n",
             "theorem check_cert : check cert = checkCore defaultPrec certLits := by\n",
             "  unfold check cert\n",
             "  rw [CertSpec.ofCertificateData_toCertificateData]\n\n",
             "end NonUniqueEuler.Verify\n"]
    return "".join(lits), "".join(cells), (cnt, gap)


def main(argv):
    global PKG, MANUSCRIPT
    args = list(argv)
    check = "--check" in args
    if check:
        args.remove("--check")
    if "--manuscript" in args:
        i = args.index("--manuscript")
        if i + 1 >= len(args):
            fail("--manuscript needs a path")
        MANUSCRIPT = os.path.abspath(args[i + 1])
        del args[i:i + 2]
    if len(args) != 1 or args[0].startswith("-"):
        print(__doc__, file=sys.stderr)
        return 2
    PKG = os.path.abspath(args[0])
    if not os.path.isdir(os.path.join(PKG, "certificates")):
        fail(f"{PKG} has no certificates/ directory (expected the euler-ring-certificate package)")
    md = manuscript_digests()
    for which in ("count", "gap"):
        fn, _, digest, _ = FILES[which]
        if md is not None and digest not in md:
            fail(f"the pinned digest of {fn} does not occur in {MANUSCRIPT}")
    lits, cells, (cnt, gap) = gen()
    print(f"{cnt[0]}: sha256 OK, {len(cnt[3])} cells; {gap[0]}: sha256 OK, {len(gap[3])} cells"
          + ("" if md is None else "; digests found in the manuscript"))
    if check:
        bad = 0
        for path, text in ((OUT_LITS, lits), (OUT_CELLS, cells)):
            cur = open(path).read() if os.path.exists(path) else None
            same = cur == text
            print(f"{os.path.relpath(path, ROOT)}: {'up to date' if same else 'DIFFERS'}")
            bad += not same
        return 1 if bad else 0
    os.makedirs(os.path.dirname(OUT_LITS), exist_ok=True)
    for path, text in ((OUT_LITS, lits), (OUT_CELLS, cells)):
        with open(path, "w", newline="\n") as f:
            f.write(text)
        print(f"wrote {os.path.relpath(path, ROOT)} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
