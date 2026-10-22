# Output files

All rationals are exact strings `"p/q"` (or integers). No output file of the certified computation
contains a floating-point number, except as an explicitly rounded decimal string labelled as such.

## `constants.json`

`{"format": "ringcert-constants-1", "data": {...}, "checks": [...], "summary": {...}}`. Each check has
`id`, `group`, `method` (`"exact"`: exact rationals; `"arb"`: Arb cross-check), `statement`, `passed` and
`value` (outward-rounded decimals for display; the exact comparison is the one stated). This file is
deterministic.

## `sector3_count.json` and `sector3_gap.json`

Deterministic (no timings, no environment; byte-identical across runs in the reference environment):

| key | meaning |
|---|---|
| `item` | `"N1'"` (count) or `"N2'"` (gap) |
| `statement` | the certified statement |
| `mode` | `"certificate"` (the shipped cell list was certified) or `"search"` |
| `partial` | `true` if only some cells were run (`ringcert cell`, `--quick`) |
| `data` | $a_0,d,\xi_L,\xi_a,\xi_b,\xi_R,G_{\max}$ (keys `a0,d,sL,sa,sb,sR,Gmax`) |
| `parameters` | contour density, bisection limits, maximal number of $G$-halvings |
| `ok`, `gapfree` | every certified cell has winding 1, nothing failed, and every rectangle has the required shape ($R_A$ for N1′; left edge $\frac{211}{2500}$, $x_0<x_1$, $y_0<y_1$, inside $R_A$ for N2′); the cells partition $[0,G_{\max}]$ |
| `failed` | sub-cells not certified (must be empty) |
| `ncells`, `nseg`, `nevals`, `ambiguous` | totals |
| `cells` | sorted by $G$; each has `G` = [a, b], `rect` = [x0, x1, y0, y1], `winding`, `nseg` (segments of the final contour), `nN` (type-N segments), `nind` (indicator points), `ambiguous`, `nevals` (Evans evaluations in the successful attempt), `level` (number of halvings of the input cell) |

`ringcert check` recomputes `ok` and `gapfree` from the cell records with Fraction arithmetic. Integer
fields must be JSON integers: a winding recorded as `true`, `1.0` or `"1"` is rejected.

All JSON files are written under a temporary name and then renamed, so an interrupted write leaves
no truncated file.

## `summary.json`

Written only by `ringcert all`. Not deterministic (timings, environment). Keys: `package_version`,
`quick`, `reference_environment`, `environment` (Python, platform string, python-flint and FLINT
versions, precision, SHA-256 of every module), `data`, `complete`, `all_pass`, `steps` (each with
`passed`, `seconds`, `output`; a skipped self-test is recorded as `{"step": "selftest", "passed": null,
"skipped": true}`), `items` (N1, N2, N3: `statement`, `status` = `PASS` / `FAIL` / `NOT_CERTIFIED`,
`evidence`), `outputs_sha256` (SHA-256 of `constants.json`, `sector3_count.json` and
`sector3_gap.json`), `reference_verification` (`all_pass` and `reference_environment`), `seconds`.

`ringcert all` first deletes the outputs of any earlier run from its output directory and writes a
provisional `summary.json` with `"complete": false` and `"all_pass": false`; the final summary
replaces it only when the run finishes. An interrupted run therefore never leaves a PASS summary.
`ringcert all --quick` writes to `out_quick` unless `--out` is given, and refuses (exit 2) a
directory that holds the outputs of a full run, so it never deletes a completed verification.
`ringcert check` requires, when `summary.json` is present, that the recorded module and output
SHA-256 equal those of the modules running and of the files checked, and that the summary records a
completed run that passed; without `summary.json` it prints a NOTE that provenance was not checked.

## Certificate files (`certificates/`)

`{"format": "ringcert-certificate-1", "item", "sector", "data", "parameters", "cells": [{"G", "rect"}]}`.
They are inputs: `sector3-count` and `sector3-gap` certify these cells and rectangles (a cell that
fails is halved at its midpoint, up to the recorded depth, and the halves are certified; the output
then lists the halves). Both commands, and `ringcert cell`, report success only if the rectangles
have the required shape.
`--search` regenerates them by the rules described in `src/ringcert/sector3.py`, and
`ringcert export-certificate RESULT.json FILE` writes a certificate file from a result file.
