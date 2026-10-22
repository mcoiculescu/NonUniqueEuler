#!/usr/bin/env python3
"""Count `sorry`s and forbidden tokens in NonUniqueEuler/ (comments and strings stripped).

Usage (from the root of this repository): python3 tools/status.py [--list] [--json] [subdir]

Forbidden tokens: `axiom`, `admit`, `native_decide`, `decide +native`, `implemented_by`,
`@[extern]`, `unsafe`, `skipKernelTC`, `ofReduceBool`, `@[csimp]`.
"""
import json, os, re, sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'NonUniqueEuler')
FORBIDDEN = [r'\baxiom\b', r'\badmit\b', r'native_decide', r'decide\s*\+native', r'implemented_by',
             r'@\[\s*extern', r'\bunsafe\b', r'skipKernelTC', r'ofReduceBool', r'@\[\s*csimp']

def strip(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if src.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and src.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth:
            out.append('\n' if src[i] == '\n' else ' '); i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append(' ' * (j + 1 - i)); i = j + 1; continue
        out.append(src[i]); i += 1
    return ''.join(out)

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    base = os.path.join(ROOT, args[0]) if args else ROOT
    rows, total, bad = [], 0, []
    for d, _, fs in os.walk(base):
        for f in sorted(fs):
            if not f.endswith('.lean'): continue
            p = os.path.join(d, f); rel = os.path.relpath(p, os.path.join(ROOT, '..'))
            s = strip(open(p, encoding='utf-8').read())
            lines = s.split('\n')
            hits = [k + 1 for k, l in enumerate(lines) if re.search(r'\bsorry\b', l)]
            for pat in FORBIDDEN:
                for k, l in enumerate(lines):
                    if re.search(pat, l): bad.append((rel, k + 1, pat))
            total += len(hits)
            rows.append((rel, len(hits), hits, len(lines)))
    if '--json' in sys.argv:
        print(json.dumps({'total_sorry': total, 'files': [{'file': r, 'sorry': c, 'lines': h, 'loc': L} for r, c, h, L in rows],
                          'forbidden': bad})); return
    by_dir = {}
    for r, c, _, L in rows:
        k = '/'.join(r.split('/')[:3]); by_dir.setdefault(k, [0, 0, 0]); by_dir[k][0] += 1; by_dir[k][1] += c; by_dir[k][2] += L
    print(f"{'directory':45s} {'files':>6s} {'sorry':>6s} {'lines':>7s}")
    for k in sorted(by_dir): print(f"{k:45s} {by_dir[k][0]:6d} {by_dir[k][1]:6d} {by_dir[k][2]:7d}")
    print(f"TOTAL sorry = {total}, files = {len(rows)}, lines = {sum(r[3] for r in rows)}")
    if bad:
        print('FORBIDDEN TOKENS:'); [print(f'  {r}:{k}  {p}') for r, k, p in bad]
    if '--list' in sys.argv:
        for r, c, h, _ in rows:
            if c: print(f'{r}: {c} sorry at lines {h}')

if __name__ == '__main__':
    main()
