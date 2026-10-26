# Non-uniqueness of weak solutions to the unforced 2D Euler equations with vorticity in L¹ ∩ Lᵖ

This repository contains the manuscript

> Matei P. Coiculescu, *Non-Uniqueness of Weak Solutions to the Unforced Two-Dimensional Euler
> Equations with Vorticity in L¹ ∩ Lᵖ*,
> I: A Compactness Criterion and the Linear Analysis;
> II: The Nonlinear Construction,

together with a Lean 4 formalization of its proof and the code of its computer-assisted part.

> **Status.** The Lean-verified run of the certificate checker (`ncert par`) completed on
> 2026-10-22 and printed `check cert = true`: all 261 cells were certified (output and log in
> [`lean/certificate_run/`](lean/certificate_run/)). (N1)–(N2) are thus established both by the
> Python/Arb certificate in [`euler-ring-certificate/`](euler-ring-certificate/) and by the
> Lean-verified checker. See "How (N1)–(N2) are established" below.

The main theorem (Theorem 1.1 of both parts) says that the incompressible Euler equations in the
plane, without external force, have two distinct renormalized weak solutions with the same initial
vorticity `f`. The datum `f` is radial and nonnegative, lies in L¹ ∩ L^q for every q < ∞, and is
not bounded. One solution is the stationary solution `f`. The other is 3-fold rotationally
symmetric, is equimeasurable with `f` at every time, and departs from `f` in finite time.

| Folder | What it is | Status |
|---|---|---|
| [`manuscript/part1/`](manuscript/part1/) | LaTeX source of Part I: the compactness criterion and the linear instability of the ring. | Complete; the version submitted to arXiv. |
| [`manuscript/part2/`](manuscript/part2/) | LaTeX source of Part II: the nonlinear construction, the verification of Hypothesis (N) and the proof of the main theorem. | Not on arXiv. |
| [`lean/`](lean/) | A Lean 4 + Mathlib formalization of the whole proof, including the algorithms of the computer-assisted part. See `lean/README.md`. | No `sorry`, only the standard axioms. The compiled run of the verified checker printed `true` on all 261 cells (see below). |
| [`euler-ring-certificate/`](euler-ring-certificate/) | The computer-assisted proof of (N1)–(N2) in Python with FLINT/Arb, with the certificate (`certificates/*.json`) and the recorded outputs of its run (`expected/`, with SHA-256 checksums). See `euler-ring-certificate/README.md`. | Complete; every cell passes. |

## Structure of the proof

Theorem 1.1 is proved in two steps (Part II, Section 1).

- **Part II, Proposition 1.2.** Hypothesis (N), that is, the three statements (N1)–(N3) of
  Part I, Hypothesis 4.17, implies Theorem 1.1. The proof uses the compactness criterion and the
  linear analysis of Part I, and the nonlinear construction of Part II.
- **Part II, Theorem 1.3 and Appendix A.** Hypothesis (N) holds. (N1) and (N2) are established by
  a computer-assisted proof in rigorous ball arithmetic. (N3) has a short written proof.

## What is formally proved (`lean/`)

- **`NonUniqueEuler.main_theorem_of_N : ConditionalTheorem`.** For every admissible cutoff `χ`,
  Hypothesis (N1)–(N3) implies Theorem 1.1. This is Proposition 1.2 of Part II, the whole analytic
  part of the proof (Part I, Sections 2–4; Part II, Sections 1–8 and Appendix B), formalized.
- **`NonUniqueEuler.n3_holds : N3`.** (N3), proved in Lean.
- **`NonUniqueEuler.Verify.check_sound : CheckerSound Verify.check`.** Lean implements the
  algorithms of Appendix A of Part II: ball arithmetic, the Taylor enclosure of the Evans function,
  the winding-number certification and the coverage checks. If this checker returns `true` on any
  certificate, then (N1) and (N2) hold for every admissible cutoff.
- **`NonUniqueEuler.main_theorem_of_certificate`.** If `Verify.check Verify.cert = true`, then
  Theorem 1.1 holds. Here `Verify.cert` is the certificate of `euler-ring-certificate`,
  transcribed with SHA-256 checks.

`#print axioms` on these theorems gives:

```
'NonUniqueEuler.main_theorem_of_N' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonUniqueEuler.main_theorem_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonUniqueEuler.main_theorem_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonUniqueEuler.Verify.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonUniqueEuler.Verify.check_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonUniqueEuler.Verify.check_eq_checkCorePar' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## How (N1)–(N2) are established

1. **The Arb certificate** (`euler-ring-certificate/`). This is the computer-assisted proof
   described in Appendix A of Part II. Its recorded run (`expected/summary.json`) certifies every
   cell of both runs: `"complete": true`, `"all_pass": true`. It used FLINT 3.6.0 /
   python-flint 0.9.0 at 128-bit precision. `./reproduce.sh` re-runs it.
2. **The Lean-verified checker** (`lean/`). The same certificate is checked a second time by the
   compiled Lean program `ncert`, whose algorithm is proved sound in Lean (`Verify.check_sound`).
   The executable evaluates exactly the hypothesis `Verify.check Verify.cert = true` of
   `main_theorem_of_certificate` (theorem `Verify.check_eq_checkCorePar`). Its trusted base is the
   Lean compiler and runtime and GMP.

   **Status of the Lean-verified re-run: complete.** On 2026-10-22 the full run of `ncert par`
   (6 threads, Apple M3 Pro, 8.75 hours, 106,680 Evans enclosures) printed
   `checkCorePar defaultPrec certLits = check cert = true` and exited with code 0. All 261 cells
   were certified with winding number 1 (output and log: `lean/certificate_run/`). So (N1)–(N2)
   are established twice: by the Arb certificate, and by the Lean-verified checker, whose result
   is the hypothesis of the kernel-checked `main_theorem_of_certificate`.

## How the code refers to the manuscript

The Lean formalization and the code were written against an earlier, single-volume version of the
manuscript (Sections 1–11 and Appendices A–C), which was later divided into Parts I and II. That
version is not included here. In `lean/` and `euler-ring-certificate/`, "the manuscript" means
that version.

The formal result does not depend on this correspondence. The Lean statement is self-contained
(`lean/NonUniqueEuler/Statement/`), and the proofs are checked by the Lean kernel. The references
only help a reader find the matching argument on paper.

- **Numbers.** Theorem 1.1, Proposition 1.2, Theorem 1.3 and the numbered statements of
  Appendix A (Lemma A.1 to Proposition A.8) have the same numbers in Part II. Most other statement
  and equation numbers have changed.
- **Labels.** The Lean sources cite statements mainly by their LaTeX labels, such as `lem:clock`.
  Of the 213 labels cited in `lean/`, 174 are also labels in `manuscript/part1` or
  `manuscript/part2`; for example, `grep -rn 'label{lem:clock}' manuscript/` finds the statement.
  The other 39 have no counterpart label in Parts I and II.
- **Source files.** References of the form `B_global_smooth.tex:30-35` in Lean comments are to the
  source files of the single-volume version.

The sections correspond as follows.

| Single-volume version | Parts I and II | Lean folders (`Defs/`, `P/`, `H/`) |
|---|---|---|
| Section 1, Introduction | Part I, Section 1, and Part II, Section 1 | |
| Section 2, Preliminaries | Part I, Section 2; several results are in Part II, Section 1.4 instead (for example `lem:Hk-calculus`, Part II, Lemma 1.9) | `Sec2` |
| Section 3, Compactness | Part I, Section 3 | `Sec3` |
| Section 4, The ring | Part I, Section 4 (Hypothesis (N) is Part I, Hypothesis 4.17) | `Sec4` |
| Sections 5–11 | Part II, Sections 2–8 (subtract 3) | `Sec5` … `Sec11` |
| Appendix A | Part II, Appendix A | `Verify` |
| Appendix B | Part II, Appendix B | `SmoothB` |

## Building

- Manuscript: see `manuscript/part1/README.md` and `manuscript/part2/README.md` (build Part I
  first; Part II reads Part I's statement numbers from it).
- Lean: see `lean/README.md` (`lake exe cache get`, then `lake build`; then
  `lake env lean tools/PrintAxioms.lean`).
- Arb certificate: see `euler-ring-certificate/README.md` (`./reproduce.sh`).

## Authorship and AI assistance

The main idea of a linear instability in physical coordinates driving the non-uniqueness
mechanism, the use of non-monotone unstable radial vortices and of a multiscale datum, and the
overall strategy of the proof are due to the author. Within this strategy, the detailed proofs and
estimates, the code for the computer-assisted verification and the text of the manuscript were
largely produced with Claude Opus 5.5 (Anthropic), under the direction of the author. The Lean
formalization was likewise produced with Claude (Anthropic), under the direction of the author.
The author has checked all proofs of the manuscript by hand and takes full responsibility for it.
The formal guarantee of `lean/` rests on the Lean kernel check described above, together with the
stated trusted base for the compiled run.

## License

Apache License 2.0 (`LICENSE`), copyright 2026 Matei P. Coiculescu, for everything in this
repository. `lean/` and `euler-ring-certificate/` also carry their own `LICENSE` and `NOTICE`.
`lean/NonUniqueEuler/Vendor/` contains files adapted from OpenAI's NavierStokesAndEuler, also under
the Apache License 2.0.
