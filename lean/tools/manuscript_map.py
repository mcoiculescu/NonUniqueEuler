#!/usr/bin/env python3
"""Generate/check the current manuscript-to-Lean navigation table (stdlib only).

The JSON registry owns semantic correspondences; TeX owns labels and numbering.
This is a deliberately limited parser for the repository's shared theorem counter,
not a TeX engine. It rejects unsupported counter changes. --check-aux independently
compares its result with both manuscripts' locally built main.aux files.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean"
REGISTRY = LEAN / "manuscript_map.json"
OUTPUT = LEAN / "MANUSCRIPT_MAP.md"
KINDS = {"theorem", "definition", "proposition", "lemma", "corollary", "hypothesis", "remark"}
RESULT_PREFIXES = ("thm:", "def:", "prop:", "lem:", "cor:", "hyp:")
TOKEN = re.compile(
    r"\\(?P<input>input)\{(?P<file>[^}]+)\}"
    r"|\\(?P<appendix>appendix)\b"
    r"|\\(?P<section>section)(?P<star>\*)?\s*\{"
    r"|\\(?P<begin>begin)\{(?P<env>[^}]+)\}"
    r"|\\(?P<end>end)\{(?P<endenv>[^}]+)\}"
    r"|\\(?P<label>label)\{(?P<key>[^}]+)\}"
)


def uncomment(text: str) -> str:
    # A percent starts a comment precisely when preceded by an even number of slashes.
    return "\n".join(_uncomment_line(line) for line in text.splitlines())


def _uncomment_line(line: str) -> str:
    for index, char in enumerate(line):
        if char == "%":
            slash = index - 1
            while slash >= 0 and line[slash] == "\\":
                slash -= 1
            if (index - slash - 1) % 2 == 0:
                return line[:index]
    return line


def source_labels(part: str) -> dict[str, dict]:
    base = ROOT / "manuscript" / part
    main = uncomment((base / "main.tex").read_text())
    expected = r"\newtheorem{theorem}{Theorem}[section]"
    if expected not in main:
        raise ValueError(f"{part}: unsupported theorem-counter configuration")
    for env in KINDS - {"theorem"}:
        if re.search(r"\\newtheorem\{" + env + r"\}", main):
            if rf"\newtheorem{{{env}}}[theorem]" not in main:
                raise ValueError(f"{part}: {env} no longer shares the theorem counter")
    labels, stack, active = {}, [], []
    section, counter, appendix = 0, 0, False

    def visit(path: Path) -> None:
        nonlocal section, counter, appendix
        path = path.resolve()
        if not path.is_relative_to(base.resolve()) or path in active:
            raise ValueError(f"Unsupported or circular input: {path}")
        active.append(path)
        text = uncomment(path.read_text())
        if re.search(r"\\(?:setcounter|addtocounter|counterwithin|numberwithin|include)\b", text):
            raise ValueError(f"Unsupported counter/input command in {path}")
        for match in TOKEN.finditer(text):
            if match["input"]:
                child = base / match["file"]
                visit(child if child.suffix else child.with_suffix(".tex"))
            elif match["appendix"]:
                section, counter, appendix = 0, 0, True
            elif match["section"] and not match["star"]:
                section += 1
                counter = 0
            elif match["begin"]:
                env = match["env"]
                if env in KINDS:
                    counter += 1
                prefix = chr(64 + section) if appendix else str(section)
                stack.append((env, f"{prefix}.{counter}"))
            elif match["end"]:
                if not stack or stack[-1][0] != match["endenv"]:
                    raise ValueError(f"Unbalanced environment in {path}: {match.group()}")
                stack.pop()
            elif match["label"]:
                key = match["key"]
                if key in labels:
                    raise ValueError(f"Duplicate {part} label: {key}")
                env = next((item for item in reversed(stack) if item[0] in KINDS), None)
                labels[key] = {
                    "part": part, "label": key,
                    "kind": env[0] if env and key.startswith(RESULT_PREFIXES) else None,
                    "number": env[1] if env and key.startswith(RESULT_PREFIXES) else None,
                    "source": path.relative_to(ROOT).as_posix(),
                    "line": text.count("\n", 0, match.start()) + 1,
                }
        active.pop()

    visit(base / "main.tex")
    if stack:
        raise ValueError(f"Unclosed environments in {part}")
    return labels


def read_registry(all_labels: dict) -> dict:
    registry = json.loads(REGISTRY.read_text())
    if registry["schema_version"] != 1:
        raise ValueError("Unsupported manuscript_map.json schema")
    current = {(p, k) for p, labels in all_labels.items() for k, v in labels.items()
               if v["kind"] and v["kind"] != "remark"}
    seen = set()
    for entry in registry["current"]:
        key = (entry["part"], entry["label"])
        if key in seen:
            raise ValueError(f"Duplicate registry entry: {key}")
        seen.add(key)
        if entry["relation"] not in {"entry point", "variant", "components", "definition"}:
            raise ValueError(f"Unknown relation: {entry['relation']}")
        if not entry.get("modules") or not entry.get("note"):
            raise ValueError(f"Missing modules or correspondence note: {key}")
    if current != seen:
        raise ValueError(f"Registry differs from source statements; missing={sorted(current-seen)}, "
                         f"obsolete={sorted(seen-current)}")
    legacy_seen = set()
    for entry in registry["legacy"]:
        if entry["label"] in legacy_seen:
            raise ValueError(f"Duplicate legacy entry: {entry['label']}")
        legacy_seen.add(entry["label"])
        if any(entry["label"] in labels for labels in all_labels.values()):
            raise ValueError(f"Legacy label exists in current source: {entry['label']}")
        if not entry.get("destinations") or not entry.get("note"):
            raise ValueError(f"Missing legacy destination/note: {entry['label']}")
        for dest in entry["destinations"]:
            if dest["label"] not in all_labels.get(dest["part"], {}):
                raise ValueError(f"Unknown legacy destination: {dest}")
    for entry in registry["current"] + registry["legacy"]:
        for module in entry["modules"]:
            path = LEAN / module
            if not path.resolve().is_relative_to((LEAN / "NonUniqueEuler").resolve()):
                raise ValueError(f"Module outside library: {module}")
            if path.suffix != ".lean" or not path.is_file():
                raise ValueError(f"Missing Lean module: {module}")
        for declaration in entry.get("declarations", []):
            # Declarations are unqualified source names; this guards navigation, not types.
            pattern = r"\b(?:def|abbrev|theorem|lemma|structure|inductive)\s+" + re.escape(declaration) + r"\b"
            if not any(re.search(pattern, (LEAN / module).read_text()) for module in entry["modules"]):
                raise ValueError(f"Missing declaration {declaration} in {entry['label']} modules")
    known = set().union(*(set(labels) for labels in all_labels.values()), legacy_seen)
    citation = re.compile(r"\b(?:thm|def|prop|lem|cor|hyp|eq|sec|app):[A-Za-z0-9_-]+")
    for path in (LEAN / "NonUniqueEuler").rglob("*.lean"):
        unknown = set(citation.findall(path.read_text())) - known
        if unknown:
            raise ValueError(f"Unmapped manuscript labels in {path.relative_to(LEAN)}: {sorted(unknown)}")
    return registry


def source_link(obj: dict) -> str:
    part = "I" if obj["part"] == "part1" else "II"
    name = f"{obj['kind'].title()} {obj['number']}" if obj["kind"] else "source location"
    return f"[Part {part}, {name}](../{obj['source']}#L{obj['line']}) (`{obj['label']}`)"


def module_links(entry: dict) -> str:
    return "<br>".join(f"[{m.removeprefix('NonUniqueEuler/')}]({m})"
                       for m in entry["modules"])


def render(registry: dict, all_labels: dict) -> str:
    lines = [
        "# Current manuscript and Lean correspondence", "",
        "This index uses the current two-part manuscript. Stable TeX labels are canonical;",
        "numbers and source links are generated from the included TeX sources. The `Sec2`–`Sec11`",
        "Lean paths retain their original names so imports remain stable. A row gives a useful",
        "entry point, not an assertion that the paper and Lean declarations are identical.", "",
        "**Relations.** `entry point` identifies the main proof module; `definition` identifies",
        "the formal representation; `variant` records a change of hypotheses, conclusion or",
        "representation; `components` means several formal results supply the current argument,",
        "with no single declaration asserted to match the complete statement. Consult",
        "[FORMALIZATION_NOTES.md](FORMALIZATION_NOTES.md) for the precise formalization boundaries",
        "and [README.md](README.md#trust-model) for the certificate hypothesis and trusted base.", "",
        "Regenerate with `python3 lean/tools/manuscript_map.py`; check without writing with",
        "`python3 lean/tools/manuscript_map.py --check`. After building both manuscripts, add",
        "`--check-aux` to compare every statement number with LaTeX's output. The default check",
        "needs no `.aux` files. It also rejects unknown manuscript labels cited in Lean.",
        "Correspondences are maintained in",
        "[manuscript_map.json](manuscript_map.json); this Markdown file is generated.", "",
    ]
    by_key = {(e["part"], e["label"]): e for e in registry["current"]}
    for part, labels in all_labels.items():
        lines += [f"## Part {'I' if part == 'part1' else 'II'}", "",
                  "| Current statement | Lean modules | Relation and scope |", "|---|---|---|"]
        for key, obj in labels.items():
            if (part, key) not in by_key:
                continue
            entry = by_key[part, key]
            decl = " " + ", ".join(f"`{d}`" for d in entry.get("declarations", [])) if entry.get("declarations") else ""
            lines.append(f"| {source_link(obj)} | {module_links(entry)}{decl} | **{entry['relation']}**: {entry['note']} |")
        lines.append("")
    lines += ["## Legacy labels retained in Lean", "",
              "These labels no longer name objects in the current manuscript. The destinations",
              "below identify the proof or definition containing the corresponding argument;",
              "they do not resurrect removed numbered statements. Additional formal auxiliaries",
              "may have no separately stated current counterpart.", "",
              "| Legacy label | Current destination | Lean modules and scope |", "|---|---|---|"]
    for entry in registry["legacy"]:
        dest = "<br>".join(source_link(all_labels[d["part"]][d["label"]]) for d in entry["destinations"])
        lines.append(f"| `{entry['label']}` | {dest} | {module_links(entry)}<br>{entry['note']} |")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the generated map is stale")
    parser.add_argument("--check-aux", action="store_true", help="also compare local LaTeX .aux numbers")
    args = parser.parse_args()
    try:
        labels = {part: source_labels(part) for part in ("part1", "part2")}
        registry = read_registry(labels)
        if args.check_aux:
            for part, objects in labels.items():
                aux = ROOT / "manuscript" / part / "main.aux"
                if not aux.is_file():
                    raise ValueError(f"Build {part} first: missing {aux}")
                numbers = dict(re.findall(r"\\newlabel\{([^}]+)\}\{\{([^}]+)\}", aux.read_text()))
                for key, obj in objects.items():
                    if obj["kind"] and numbers.get(key) != obj["number"]:
                        raise ValueError(f"{part}:{key}: source {obj['number']} != .aux {numbers.get(key)}")
        output = render(registry, labels)
        if args.check:
            if not OUTPUT.is_file() or OUTPUT.read_text() != output:
                raise ValueError("MANUSCRIPT_MAP.md is stale; run python3 lean/tools/manuscript_map.py")
        else:
            OUTPUT.write_text(output)
        print(f"Manuscript map {'checked' if args.check else 'generated'}: "
              f"{len(registry['current'])} current statements, {len(registry['legacy'])} legacy labels"
              + ("; .aux numbers agree" if args.check_aux else ""))
        return 0
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as exc:
        print(f"manuscript_map: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
