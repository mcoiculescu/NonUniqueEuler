# euler-ring-certificate

Reproduction package for Appendix A of Part II of the paper

> Matei P. Coiculescu, *Non-Uniqueness of Weak Solutions to the Unforced Two-Dimensional Euler
> Equations with Vorticity in $L^1\cap L^p$*, I: A Compactness Criterion and the Linear Analysis;
> II: The Nonlinear Construction (2026).

Lemma and proposition numbers below (Lemma A.1, Proposition A.3, ...) are those of Appendix A of
Part II; section numbers refer to this file.

The main text of the paper proves the main theorem under a numerical hypothesis (N), consisting of
three statements (N1)–(N3) about explicit quantities. This package verifies (N1) and (N2) with
rigorous interval (ball) arithmetic in FLINT/Arb, and re-evaluates in exact rational arithmetic the
quantities of (N3), which the paper proves without machine computation. From the root of this
directory, one command reproduces everything (after a one-time setup):

```sh
python3 -m venv ringcert-env && . ringcert-env/bin/activate   # Python >= 3.10
pip install -r requirements.txt                               # python-flint==0.9.0
./reproduce.sh 8            # 8 worker processes; about 10 minutes on 8 cores
```

**Provenance.** The code, tests and documentation of this package were developed with extensive use
of AI systems (Claude, by Anthropic), under the direction of the author, and were checked in
repeated AI review passes, run independently of one another. These checks are not a substitute for
independent verification by human experts.

---

## 1. What is verified

### 1.1 Data and definitions

All data are dyadic rationals, defined by these literals (`src/ringcert/data.py`):

$$a_0=-7304210039150669\cdot2^{-54},\qquad d=5764607523034235\cdot2^{-58},$$
$$\xi_L=-4528212286209965\cdot2^{-52},\quad \xi_a=-4077852323472915\cdot2^{-52},\quad \xi_b=\tfrac12,\quad \xi_R=5404319552844595\cdot2^{-53}.$$

(For orientation: $a_0\approx\log\frac23$, and $d$, $\xi_L$, $\xi_a$, $\xi_R$ are the binary64 numbers
nearest to $\frac1{50}$, $a_0-\frac35$, $a_0-\frac12$, $\frac35$; these remarks are checked but not used.)
Write $\xi=\log r$, $H(x)=(1+e^{-2x})^{-1}$, and fix a cutoff $\chi\in C_c^\infty(\mathbb R)$ with
values in $[0,1]$, nondecreasing on $(-\infty,\xi_a]$, equal to $1$ on $[\xi_a,\xi_b]$, nonincreasing
on $[\xi_b,\infty)$ and supported in $[\xi_L,\xi_R]$. Put
$$\bar\omega(\xi)=\chi(\xi)\,H\Big(\frac{\xi-a_0}d\Big)H\Big(-\frac\xi d\Big),\quad
\bar\omega_\xi=\frac{d\bar\omega}{d\xi},\quad
g(\xi)=\int_{-\infty}^{\xi}\bar\omega(\xi')e^{2\xi'}d\xi',\quad
\Omega_G(\xi)=(g(\xi)+G)e^{-2\xi}.$$
For an integer $m\ge1$, $G\ge0$ and $\Re\lambda>0$ let $\psi$ solve
$$\psi''=\Big(m^2+\frac{im\,\bar\omega_\xi(\xi)}{\lambda+im\Omega_G(\xi)}\Big)\psi\ \text{ on }[\xi_L,\xi_R],\qquad
\psi(\xi_L)=1,\quad\psi'(\xi_L)=m,$$
and let $\mathcal E_m(\lambda;G)=e^{-m(\xi_R-\xi_L)}\big(\psi'(\xi_R)+m\psi(\xi_R)\big)$ (holomorphic in
$\{\Re\lambda>0\}$). Put $X_m=\pi md/\sin(\pi md)$ and $\epsilon_*=\max\{H((\xi_a-a_0)/d),\,H(-\xi_b/d)\}$.

### 1.2 The statements

> **(N1)** For every $G\in[0,\frac1{50}]$, $\mathcal E_3(\cdot;G)$ has exactly one zero in the closed
> half-plane $\{\Re\lambda\ge\frac9{200}\}$, counted with multiplicity.
>
> **(N2)** For every $G\in[0,\frac1{50}]$, the function $\mathcal E_3(\cdot;G)$ has no zero in the closed
> strip $\{\frac9{200}\le\Re\lambda\le\frac{211}{2500}\}$.
>
> By (N1) and (N2), the zero of (N1) has real part greater than $\frac{211}{2500}$.
>
> **(N3)** For $m\in\{6,9\}$: $\ e^{ma_0}X_m+\epsilon_*<\frac9{100}$.

Everything below holds for every admissible $\chi$ simultaneously, and on the larger range
$G\in[0,G_{\max}]$, $G_{\max}=d=\frac1{50}+\frac{3}{7205759403792793600}$ ($d-\frac1{50}\approx4.16\cdot10^{-19}$).

### 1.3 What the computer checks, and how it relates to (N1)–(N3)

| id | statement checked | method |
|---|---|---|
| **N1′** | for every $G\in[0,G_{\max}]$: $\mathcal E_3(\cdot;G)\ne0$ on $\partial R_A$, $R_A=[\frac9{200},3]\times[-5,3]$, and ${\rm wind}(\mathcal E_3(\cdot;G)\circ\partial R_A,0)=1$ | Arb; 25 $G$-cells |
| **N2′** | for each of 236 $G$-cells $\mathcal C_i$ partitioning $[0,G_{\max}]$, an explicit rectangle $R_i=[\frac{211}{2500},x_i]\times[y_i,y_i']$ with $\mathcal E_3(\cdot;G)\ne0$ on $\partial R_i$ and winding 1, for all $G\in\mathcal C_i$ | Arb |
| **N3** | $\frac12(e^{6a_0}X_6+\epsilon_*)\le0.0449530111<\frac9{200}$ and $\frac12(e^{9a_0}X_9+\epsilon_*)\le0.0137260837<\frac9{200}$, which is (N3) | exact rationals, Arb cross-check |
| LA | $\frac94e^{2\max(x_a,y_b)}\le3e^{-50}$, $x_a=\frac{\xi_a-a_0}d$, $y_b=-\frac{\xi_b}d$ (constant of Lemma A.1, used by the enclosure) | exact rationals |
| LB | $TV/\ln2<2.886<3$ and $-3\Omega_{\max}-TV/\ln2>-5$, $\Omega_{\max}=\frac12+G_{\max}e^{-2\xi_L}$, for $TV=2+2\cdot\frac94e^{2\max(x_a,y_b)}$ and for $TV=2+6e^{-50}$ (constants of Lemma A.2) | exact rationals |
| D | $\xi_L<\xi_a\le a_0/2\le\xi_b<\xi_R$; $d>\frac1{50}$; $x_a,y_b<-24$; $\pi<\frac{355}{113}$; $0<\frac{355}{113}md\le1$ ($m=6,9$) | exact rationals |

Deductions (Lemma A.6 of the paper): Lemma A.2 places every zero of $\mathcal E_3(\cdot;G)$ with
$\Re\lambda\ge\frac9{200}$ in $[\frac9{200},2.9)\times(-4.85,2.9)\subset R_A$, so
**N1′ ⇒ (N1)** by the argument principle (and $[0,\frac1{50}]\subset[0,G_{\max}]$ by D). Each $R_i$
lies in $\{\Re\lambda\ge\frac{211}{2500}\}\subset\{\Re\lambda>\frac9{200}\}$ and contains a zero in its
interior, so **(N1) + N2′ ⇒ (N2)**. The rectangles and cell endpoints are exact rationals in
`certificates/`. The check of $2.886$, and the printed bounds $\Omega_{\max}\le0.6494052616$
and $-3\Omega_{\max}-TV/\ln2\ge-4.833606$, confirm the numbers $2.9$, $0.6495$ and $-4.85$ of the
written proof of Lemma A.2; they are not part of the proof.

## 2. How the package maps to the paper

The main theorem is proved in the main text under (N1)–(N3); this package verifies (N1) and (N2), and
checks the numbers in the written proof of (N3).

| item | used in the paper for | method in Appendix A | command | output | time (8 proc.) |
|---|---|---|---|---|---|
| N1 | sector 3, zero count above $\Re\lambda=\frac9{200}$ | enclosure of $\mathcal E_3$ (Proposition A.3: Lemma A.1, Taylor method, a priori bound); certified winding count (Proposition A.4); Lemma A.2 | `ringcert sector3-count` (+ `constants`) | `sector3_count.json` | ≈ 4 min |
| N2 | sector 3, spectral gap $\Re\lambda_*>0.0844$ | as N1, rectangles with left edge $\frac{211}{2500}$ (Lemma A.6) | `ringcert sector3-gap` | `sector3_gap.json` | ≈ 5 min |
| N3 | sectors $\pm6$ and $\lvert m\rvert\ge9$ below $\frac9{200}$ | closed-form bound (Proposition A.8), exact rational arithmetic | `ringcert constants` | `constants.json` | < 1 s |

## 3. Installation

Requirements: Python ≥ 3.10 (the reference runs used CPython 3.13.5) and `python-flint==0.9.0`,
which bundles FLINT 3.6.0. Nothing else is needed for the verification.

```sh
python3 -m venv ringcert-env && . ringcert-env/bin/activate
pip install -r requirements.txt          # python-flint==0.9.0
```

Run all commands from the root of this directory. The package runs from the source tree
(`./reproduce.sh`, or `PYTHONPATH=src python -m ringcert ...`); below, `ringcert X` is short for
`PYTHONPATH=src python -m ringcert X`. Alternatively an editable install, `pip install -e .`, provides
the `ringcert` command. A non-editable `pip install .` is not supported: the commands read
`certificates/`, `tests/` and `expected/` from the source tree.

## 4. Commands

Single entry point (environment check, exact checks, unit tests, both sector-3 runs, exact re-check
of the outputs, comparison with the reference outputs):

```sh
./reproduce.sh [JOBS] [OUTDIR]                    # or:
PYTHONPATH=src python -m ringcert all --jobs 8 --out out
```

`reproduce.sh` runs `python3` from the `PATH` (the activated environment); set `PYTHON=/path/to/python`
to use another interpreter. `OUTDIR` (default `out`) is relative to the current directory.

Per item (`--out DIR`, for `all`, `constants`, `sector3-*`, `selftest` and `validate`: the output
directory, default `./out`, or `./out_quick` for `all --quick`; `--jobs N`, for `all`, `sector3-*` and
`validate`: the number of processes):

| command | what it does |
|---|---|
| `ringcert env` | prints Python, platform, python-flint and FLINT versions and module SHA-256; refuses a non-reference FLINT (exit 2) unless `--allow-other-flint` (every command refuses `python -O`) |
| `ringcert constants` | N3, LA, LB, D in exact rationals, with Arb cross-checks → `constants.json` |
| `ringcert sector3-count [--jobs N]` | N1′ on the 25 shipped cells → `sector3_count.json`; exit 0 only if every cell is certified with winding 1 and the result passes the exact checks of `check` (coverage, windings, rectangles equal to $R_A$, data) |
| `ringcert sector3-gap [--jobs N]` | N2′ on the 236 shipped cells and rectangles → `sector3_gap.json`; exit 0 only as for `sector3-count`, with every rectangle of left edge $\frac{211}{2500}$, positively oriented and inside $R_A$ |
| `ringcert sector3-count --search` / `sector3-gap --search` | regenerate the cell lists (20 equal cells with adaptive halving; graded cells with rectangles placed around Newton approximations of the eigenvalue) and certify them |
| `ringcert cell count I` / `ringcert cell gap I` | re-certify cell number `I` (0-based) of a certificate file (spot check, about 1–2 min / 5–20 s); prints `CERTIFIED, winding 1` only if the winding is 1, no sub-cell failed and the rectangle has the required shape; its progress line reports `without gaps=False`, as expected for a single cell |
| `ringcert check [DIR]` | exact re-check of the outputs with `Fraction` arithmetic only (coverage, windings, rectangles, data, flags recomputed) and re-run of the exact constants; if `DIR/summary.json` exists (written by `all`), also checks the recorded SHA-256 of the modules and of the three output files, and that the recorded run completed and passed |
| `ringcert compare [DIR] [REF]` | cell-by-cell comparison with the reference outputs in `expected/` |
| `ringcert selftest` | unit, known-answer and failure-path tests (about 40 s) |
| `ringcert validate [--full]` | slower independent checks (section 9) |
| `ringcert all --quick` | smoke test on 2 + 10 cells; **not a verification**. It writes to `./out_quick` by default and clears that directory first, like `all`; it refuses (exit 2) a directory that holds the outputs of a full run, so it never deletes a completed verification |

## 5. Runtimes

Measured on an Apple arm64 machine (macOS 26.6, 11 cores), CPython 3.13.5, python-flint 0.9.0,
8 processes unless stated. Other hardware has not been measured; use the CPU-time column (sum of the
per-cell times) to scale. The wall time of sector3-count is bounded below by its longest cell.

| step | wall time | CPU time | longest single cell |
|---|---|---|---|
| constants | < 1 s | < 1 s | — |
| selftest | ≈ 38 s | ≈ 38 s | — |
| sector3-count (shipped cells) | 234 s | 1636 s | 126 s |
| sector3-gap (shipped cells) | 315 s | 2473 s | 16 s |
| check | ≈ 1 s | | |
| **all** (`./reproduce.sh 8`) | **588 s** | 4119 s (all processes) | |
| sector3-count `--search` (7 processes) | 700 s (five of the 20 cells fail at full width before being halved) | 3808 s | 561 s |
| sector3-gap `--search` (7 processes) | 358 s (Newton placement 17 s) | 2358 s | 16 s |

Memory: about 40 MB per worker process (measured peak resident set 37 MB on a sector3-count cell).

## 6. Interpreting the outputs

A run is **the reference verification of (N1) and (N2)** when all of the following hold:

1. `ringcert all` exits with status 0 and prints `ALL PASS: True`; `summary.json` has
   `"complete": true`, `"all_pass": true` and `"quick": false`, and items N1, N2, N3 have status
   `PASS`.
2. `ringcert check out` exits with status 0 (`CHECK: ALL TRUE`). This recomputes, from the JSON
   literals alone, that the cells partition $[0,G_{\max}]$ exactly, every winding is the integer 1, no
   indicator is ambiguous, no sub-cell failed, the rectangles are $R_A$ (N1′) or have left edge
   exactly $\frac{211}{2500}$, satisfy $x_0<x_1$ and $y_0<y_1$, and lie inside $R_A$ (N2′), and the
   data are the pinned ones. It also checks that the SHA-256 recorded in `summary.json` match the
   modules and the output files, so the files checked are those of the run that wrote the summary.
3. The run used the reference environment: `summary.json` has `"reference_environment": true`
   (equivalently `"reference_verification": true`).

With `--allow-other-flint`, `ringcert all` can exit 0 and print
`ALL PASS: True [NON-REFERENCE ENVIRONMENT]`. **That is not the reference verification.** Its results
hold relative to the python-flint and FLINT versions recorded in `summary.json`, which is a different
trusted base from the one in section 8 (FLINT 3.6.0).

`ringcert all` first deletes the outputs of any earlier run from its output directory and writes a
provisional `summary.json` with `"all_pass": false`, which it replaces only when the run finishes. An
interrupted or crashed run therefore leaves no PASS summary, and `ringcert check` on its directory
fails. A run of `ringcert all --quick` writes to `./out_quick` unless `--out` is given, and refuses to
run in a directory that holds the outputs of a full run (`sector3_count.json`, `sector3_gap.json`,
`selftest.log`, `check.log`, or a `summary.json` without `"quick": true`); it therefore cannot
delete a completed verification.

Expected exact summaries (`expected/summary.json`, `expected/*.json`):

| item | expected |
|---|---|
| N1′ | 25 cells, union exactly $[0,\,5764607523034235/288230376151711744]$, every rectangle $[\frac9{200},3]\times[-5,3]$, every winding 1, 0 ambiguous, 0 failed |
| N2′ | 236 cells, union exactly $[0,\,5764607523034235/288230376151711744]$, every left edge $\frac{211}{2500}$, every winding 1, 0 ambiguous, 0 failed |
| N3 | $\frac12(e^{6a_0}X_6+\epsilon_*)\le0.0449530111<0.045$; $\frac12(e^{9a_0}X_9+\epsilon_*)\le0.0137260837<0.045$ |
| LA, LB | ratio $\le0.750000000000005$; $TV/\ln2\le2.8853900818$; $\Omega_{\max}\le0.6494052616$; $-3\Omega_{\max}-TV/\ln2\ge-4.833606$ |

**Reference hashes.** `constants.json`, `sector3_count.json` and `sector3_gap.json` contain no timings
and no environment data, and Arb is deterministic for a fixed FLINT version. In the reference
environment they are byte-identical to the files in `expected/`, whose SHA-256 are listed in
`expected/SHA256SUMS`:

```sh
cd out && shasum -a 256 -c ../expected/SHA256SUMS      # or: sha256sum -c ../expected/SHA256SUMS
```

`ringcert compare out expected` reports the same comparison cell by cell. A difference here is
**not** by itself a failure: with another FLINT version or platform the segment counts may differ.
What matters is items 1–3 above.

**Uncertified is not false.** A *dead* cell (the subdivision did not converge) or an *ambiguous*
indicator means that the method could not decide; the driver then halves the cell. It is never
evidence against (N1) or (N2). Every reported winding number is a proof, relative to the trusted base
(section 8); the certifier errs only by refusing (the failure-path tests and `validation/` show this).

**Exit codes.** 0: all requested items passed; 1: some item failed or was not certified; 2: refused:
the environment (`python -O`, python-flint missing or not 0.9.0/FLINT 3.6.0), a command-line usage
error, or `all --quick` into a directory that holds a full run; 3: internal error or interruption.

## 7. Method in brief

(Details: `docs/method.md`; proofs: Appendix A of the paper.)

- **Enclosure of $\mathcal E_m$** (`src/ringcert/evans.py`). On the end regions
  $[\xi_L,\xi_a]$, $[\xi_b,\xi_R]$ the profile is below $e^{-50}$; Lemma A.1 bounds the deviation from
  $\psi''=m^2\psi$ by a Gronwall estimate, using LA. On $[\xi_a,\xi_b]$ (where $\chi=1$): 360 exact
  dyadic steps of length $\approx2^{-8}$, Taylor method of order 16 in 128-bit ball arithmetic, Taylor
  coefficients of all coefficient functions from exact ODE recurrences, an a priori enclosure over
  each step from a Gronwall bound, and the integral-form remainder added as a convex box. The
  enclosure is valid for a whole box of $\lambda$ and a whole interval of $G$ at once.
- **Winding numbers** (`src/ringcert/winding.py`). The rectangle boundary is cut into segments with
  exact rational endpoints; each image box must avoid $(-\infty,0]$ or $[0,\infty)$; the winding
  number is a signed count of sign changes of $\Im\mathcal E$ at junctions, read from certified point
  enclosures. Unclassified segments are bisected.
- **Uniformity in $G$.** Each computation is done on a whole $G$-cell (an Arb ball), so finitely many
  cells cover the continuum $[0,G_{\max}]$.
- **Exact checks** (`src/ringcert/constants.py`). Taylor bounds with Lagrange remainders for $\exp$,
  Machin's formula for $\pi$, the alternating series for $\sin$, the series
  $\ln2=\sum1/(k2^k)$; all in Python `Fraction`.

## 8. Trusted base

The verification is a proof relative to:

1. **FLINT 3.6.0 ball arithmetic** (`arb`, `acb`), as bundled in python-flint 0.9.0: every operation
   used (`+ − × ÷`, `exp`, `sqrt`, `sin`, `log`, `pi`, `union`, `lower`, `upper`, `max`,
   `nonnegative_part`, `abs_upper`, certain comparisons, constructors from integers) returns a ball
   containing the exact result for all inputs in the input balls. FLINT's internal error bounds were
   not inspected; any internal use of hardware floating point by FLINT is part of this assumption.
   python-flint is trusted to pass values through unchanged (`validation/arb_semantics.py` probes the
   semantics relied upon).
2. **CPython integers and `fractions.Fraction`**, which hold the data, contour points, cell endpoints,
   and carry out the exact checks and the coverage check.
3. **Execution as written**: assertions are active (every command of the package refuses to run under
   `python -O`).

Not trusted: Python floats (none enters a certified quantity; floats occur only in tests and logs);
numpy and scipy (not used, except by the optional uncertified reference script).

## 9. Tests and validation

`ringcert selftest` (`tests/`, about 40 s, 36365 checks):

- exact data (literals, binary64 provenance, exactness in Arb, the grid);
- conversions and Arb `exp`, $H$, $1-H$ against 60-digit decimal arithmetic;
- **known answers**: no ring ($\mathcal E_m=2m$ exactly); a constant-coefficient problem with a
  closed-form solution (and a wrong constant excluded); containment of an independent 192-bit RK4
  reference with Richardson extrapolation on the production grid and five coarse grids; agreement with
  an independent double-precision solver; known windings 1 and 0 on small rectangles;
- **failure paths**: refusal for $\Re\lambda\le0$, for a box straddling $\Re\lambda=0$, for $\varepsilon>1$,
  for an oversized step; a deliberately broken enclosure routine (remainder dropped) is detected; a perturbed
  $a_0$ gives a disjoint enclosure; the output checker rejects tampered outputs (gaps, overlaps,
  reversed $G$-cells, winding 0 or 2, a winding recorded as `true`, `1.0` or `"1"`, ambiguity, wrong
  left edge, degenerate, reversed or misplaced rectangles, wrong data, missing cells, short coverage,
  partial runs, failed sub-cells); the exact inequalities fail when thresholds are moved past the
  computed bounds; `python -O` and a non-reference FLINT are refused;
- **PASS logic**: with the two sector-3 computations replaced by the reference results and by
  tampered copies of them, `ringcert all` exits 0 with `all_pass` true only on the reference results,
  and `ringcert check` agrees; a run that crashes in a directory holding the outputs of an earlier
  passing run leaves no PASS summary there and fails `check`; a changed output file fails `check`;
  `all --quick` writes to `out_quick` by default, refuses a directory holding a full run and leaves
  that run intact; a non-reference run is marked as such; `sector3-count` and `sector3-gap` fail on
  rectangles of the wrong shape;
- **float-freeness**: a static scan of the certified modules (float literals, `float()`, float
  libraries, true division of integer literals, negative literal exponents), a dynamic guard on the
  Arb constructors, and a run of an instrumented copy of the package in which the value of every
  operation and call of the certified modules is checked for floats, over the exact checks, the
  certificate loading, the output checker and a complete small certification (a planted `arb(1) + n/10`
  is detected).

`ringcert validate` (`validation/`, a few minutes; `--full` adds about 8 minutes):

- `arb_semantics.py`: 40 probes of the python-flint behaviour the code relies on;
- `independent_winding.py`: an independently written winding counter (different contour,
  Fraction-based acceptance, a different winding formula without indicators) on a seeded random sample
  of certificate cells;
- `sharpness.py`: the certifier separates $\Re\lambda_*$ from $0.0844$ on both sides of the end of the
  $G$-range, and refuses when the eigenvalue crosses the rectangle edge;
- `known_windings.py`: windings 0 and 1 on large and small rectangles; with `--full`, a rectangle whose
  edge passes through the eigenvalue is not certified;
- `reference_dop853.py` (optional, needs `requirements-reference.txt`): regenerates the floating-point
  fixture; not certified.

## 10. Limitations

- The verification relies on the trusted base of section 8. The code has not been formally verified.
- The mathematical reduction (Lemmas A.1, A.2 and A.6, Propositions A.3 and A.4, the correspondence
  between zeros of $\mathcal E_m$ and eigenvalues, and the deduction of the main theorem from
  (N1)–(N3)) is proved in the paper, not in this code.
- The a priori enclosure step of the enclosure routine is checked by reading the code against
  `docs/method.md`, §3; omitting it would not be detected by the black-box tests.
- The reference outputs were produced on one platform (macOS arm64). Other platforms have not yet been
  run; the deterministic outputs are expected to agree for the same FLINT version, but this is not
  established.
- `requirements.txt` pins the version but not the wheel hashes.

## 11. Repository layout

```
README.md  LICENSE  NOTICE  CITATION.cff  pyproject.toml  requirements.txt  requirements-reference.txt  reproduce.sh
src/ringcert/   data.py (exact data)  balls.py (Arb helpers)  evans.py (enclosure of E_m)
                winding.py (winding count)  sector3.py (runs N1', N2')  constants.py (exact checks)
                results.py (exact output checker)  environment.py  cli.py
certificates/   sector3_count_cells.json (25 cells)  sector3_gap_cells.json (236 cells and rectangles)
expected/       reference outputs, SHA256SUMS
tests/          unit, known-answer and failure-path tests (plain Python; pytest also works)
validation/     slower independent checks
docs/           method.md  output_format.md
```

## 12. Citation and license

Cite the paper above (see `CITATION.cff`). The code is released under the Apache License 2.0
(`LICENSE`, `NOTICE`). python-flint is MIT-licensed; the FLINT, GMP and MPFR libraries bundled in its wheels
are LGPL-3.0-or-later.
