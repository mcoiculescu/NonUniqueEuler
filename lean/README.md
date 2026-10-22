# Non-uniqueness for the 2D Euler equations: a Lean 4 formalization

This folder contains a Lean 4 / Mathlib formalization of the main theorem of

> Matei P. Coiculescu, *Non-Uniqueness of Weak Solutions to the Unforced Two-Dimensional Euler
> Equations with Vorticity in L¹ ∩ Lᵖ*, I: A Compactness Criterion and the Linear Analysis;
> II: The Nonlinear Construction (LaTeX sources in [`../manuscript/`](../manuscript/)).

**Manuscript references.** The formalization was written against an earlier, single-volume version
of the manuscript, which was later divided into Parts I and II. Below and in the Lean sources,
"the manuscript", its section and statement numbers, its LaTeX labels and its source files refer to
that version. Theorem 1.1, Proposition 1.2, Theorem 1.3 and Appendix A (Lemma A.1 to
Proposition A.8) have the same numbers in Part II. For everything else, see "How the code refers to
the manuscript" in the [top-level README](../README.md).

The formalization has two parts.

1. **The conditional theorem.** A proof that the numerical hypothesis (N1)–(N3) of the
   manuscript implies Theorem 1.1 (the manuscript's Proposition 1.2, `prop:reduction`).
2. **The verification algorithms of Appendix A.** These are a computable certificate checker,
   written in Lean, and a proof that it is sound. The checker consists of rigorous ball
   arithmetic, a Taylor enclosure of the Evans function and a certified winding count.

The two parts are combined into one theorem. Its only hypothesis is that the checker accepts
the certificate of Appendix A.

Lean `v4.34.0-rc2`; Mathlib `v4.34.0-rc2` (revision `85e3a25e006c35636f0e53b0e9296caca2685bc0`,
pinned in `lake-manifest.json`). About 1,280 Lean files and 170,000 lines.

## What is proved (from the hypothesis `Verify.check Verify.cert = true`)

**Theorem 1.1 of the manuscript (informal statement).** Let `Φ` be the ring of `def:ring` and
let `a ∈ (0, 1)` be the inner radius defined there. Then there are numbers `μ ∈ (1, 17/16]` and
`s̄ ∈ (0, a/16]` such that the following holds for every `A₁ > 0`. Consider the datum

    f = Σ_{k≥1} A_k Φ(·/r_k),   A_k = A₁ μ^{k-1},   r₁ = 1,   r_{k+1} = s_k r_k,   s_k = s̄ (2μ)^{-k}.

1. `f` is radial and nonnegative. It lies in `L^q(ℝ²)` for every `q ∈ [1, ∞)`, but not in
   `L^∞`.
2. There is a time `T* ∈ (0, ∞)` with the following property. For every `T > T*` and every
   `q ∈ (4/3, ∞)`, the unforced Euler equations in vorticity form,

       ∂_t ω + v·∇ω = 0,   v = K_BS ∗ ω,   ω(0) = f,

   have two distinct renormalized weak solutions in `X_q(T) = L^∞(0, T; L¹ ∩ L^q)`:
   - the stationary solution `ω(t) = f`;
   - a solution `ω_∞`. This solution lies in `C([0, ∞); L^p)` for every `p ∈ [1, ∞)`. For every
     `t ≥ 0`, `ω_∞(t)` is equimeasurable with `f` and invariant under the rotation by `2π/3`.
3. More precisely, there is `t₀ ∈ [0, T*)` such that `ω_∞` and `f` are distinct elements of
   `X_q(T')` for every `T' > t₀`.

**The Lean statement.** `NonUniqueEuler.MainTheorem χ` (`NonUniqueEuler/Statement/MainTheorem.lean`)
is this statement for the ring built from a cutoff `χ`, with the manuscript's order of
quantifiers. It also includes the explicit form `thm:main-explicit`:
- `ω_∞` is a renormalized weak solution on `[0, ∞)` with `q = 2`;
- both solutions are renormalized weak solutions in `X_q(T)` for every `T > t₀`.

The objects it uses are defined in `NonUniqueEuler/Statement/`. That directory contains only
definitions and statements: weak and renormalized weak solutions, `X_q(T)`, the ring, the datum,
the Evans function and Hypothesis (N).

**The final theorems** are in `NonUniqueEuler/Final.lean`:

```lean
theorem main_theorem_of_certificate : MainTheoremOfCertificate Verify.check Verify.cert
```

```lean
theorem main_theorem_full :
    IsAdmissibleCutoff chiStd ∧ CheckerSound Verify.check ∧
      (Verify.check Verify.cert = true →
        ∀ χ : ℝ → ℝ, IsAdmissibleCutoff χ → NumericalHypothesis χ ∧ MainTheorem χ)
```

They use two definitions from `NonUniqueEuler/Statement/Certificate.lean`:

```lean
def CheckerSound (check : CertificateData → Bool) : Prop :=
  ∀ cert : CertificateData, check cert = true →
    ∀ χ : ℝ → ℝ, IsAdmissibleCutoff χ → N1 χ ∧ N2 χ

def MainTheoremOfCertificate (check : CertificateData → Bool) (cert : CertificateData) : Prop :=
  check cert = true → IsAdmissibleCutoff chiStd ∧ ∀ χ : ℝ → ℝ, IsAdmissibleCutoff χ → MainTheorem χ
```

Notes on these statements:
- `IsAdmissibleCutoff χ` lists the properties that `def:ring` requires of the cutoff.
- The theorem is proved for **every** admissible cutoff. This is slightly stronger than the
  manuscript, which fixes one cutoff.
- `chiStd` is the explicit cutoff from the proof of `lem:ring-facts`. That it is admissible
  (`chiStd_admissible`) shows that the class is not empty.
- `NumericalHypothesis χ` is Hypothesis (N), that is (N1), (N2) and (N3)
  (`NonUniqueEuler/Statement/Evans.lean`).

The proof combines four results:

| Result | Lean theorem | File |
|---|---|---|
| Part 1, the conditional theorem | `main_theorem_of_N : ConditionalTheorem` | `P/Main/Reduction.lean` |
| Part 2, soundness of the checker | `Verify.check_sound : CheckerSound Verify.check` | `P/Verify/Final.lean` |
| (N3), proved without machine computation (Proposition A.8) | `n3_holds : N3` | `P/Verify/N3.lean` |
| the explicit cutoff is admissible | `chiStd_admissible` | `P/Ring/ChiStd.lean` |

## Trust model

**What the kernel checks.** The proof of `main_theorem_of_certificate` is checked by the Lean
kernel. Its only hypothesis is the closed Boolean equation `Verify.check Verify.cert = true`.
The development contains no `sorry`, no `axiom` declaration and no `native_decide`. Running
`#print axioms NonUniqueEuler.main_theorem_of_certificate` gives:

```
'NonUniqueEuler.main_theorem_of_N' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonUniqueEuler.main_theorem_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonUniqueEuler.main_theorem_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonUniqueEuler.Verify.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonUniqueEuler.Verify.check_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonUniqueEuler.Verify.check_eq_checkCorePar' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Why the hypothesis is not evaluated by the kernel.** Reducing `Verify.check Verify.cert` in
the kernel is infeasible. The computation consists of tens of thousands of Evans enclosures,
each made of hundreds of Taylor steps in multi-precision ball arithmetic. The formalization does
not use `native_decide`, which would add the axiom `Lean.ofReduceBool`. Instead the hypothesis
stays explicit, and it is established in three steps.

1. **The checker is an honest program.**
   - `Verify.check c` is `checkCore defaultPrec (CertSpec.ofCertificateData c)`: a structural
     conversion of the data, followed by the core algorithm `checkCore`.
   - `checkCore`, its parallel form `checkCorePar`, and everything they use
     (`NonUniqueEuler/Verify/Comp/*`, apart from the conversion in `Runs.lean`) import only Lean
     core.
   - Nothing that `Verify.check` reaches is `noncomputable`. It uses no `Classical`
     decidability, and no `partial`, `implemented_by`, `extern`, `unsafe` or `Float`.

   The soundness theorem `Verify.check_sound` says the following: if `Verify.check` returns
   `true` on any data, then (N1) and (N2) hold for every admissible cutoff. This is what makes
   `true` meaningful. (A checker that always returned `false` would make the final theorem
   vacuous. A run that prints `true` excludes this.)

2. **The run evaluates exactly the hypothesis.**
   - The hypothesis is established by running the compiled executable `ncert`
     (`NonUniqueEuler/Verify/Main.lean`).
   - `ncert par` evaluates `checkCorePar defaultPrec certLits`, the version that evaluates the
     cells in parallel.
   - The kernel-checked theorem `check_eq_checkCorePar : check cert = checkCorePar defaultPrec certLits`
     (`Verify/Data/CellsPar.lean`) identifies this value with the hypothesis.
   - Likewise, `check_cert : check cert = checkCore defaultPrec certLits`
     (`Verify/Data/Cells.lean`) covers the single-threaded `ncert all`.

   The step "the executable printed `true`, hence `check cert = true`" is not checked by the
   kernel. Its trusted base is the same one that `native_decide` would use:
   - the Lean compiler (to C) and the C compiler;
   - the Lean runtime, including its thread pool for `ncert par`;
   - GMP, which implements the arbitrary-precision integers.

3. **The data are those of the manuscript.**
   - `Verify.cert` is generated by `tools/gen_cert_data.py` from the two JSON certificates of the
     Python/Arb reproduction package `euler-ring-certificate` (version 1.0.0, distributed with
     the manuscript).
   - The generator checks the SHA-256 digests of both files against the digests printed in
     Appendix A of the manuscript, and refuses on any mismatch.
   - Note that the conclusion of the final theorem does not mention `cert`. The data decide
     only whether the hypothesis can be met, not the soundness of the argument.

**Status of the run.** The full run completed on 2026-10-22. `ncert par` (6 threads, Apple M3 Pro, 8.75 hours wall time, 106,680 Evans enclosures) printed

```
checkCorePar defaultPrec certLits = check cert = true  (31481.868 s)
```

and exited with code 0. All 261 cells (25 for (N1′), 236 for (N2′)) were certified with winding number 1. The output and the per-cell log, with the JSON record of every certified sub-cell, are in `certificate_run/`. The hypothesis `Verify.check Verify.cert = true` is therefore established by this program, and Theorem 1.1 follows by `main_theorem_of_certificate`. The same certificate is also certified independently by the Python/Arb package `euler-ring-certificate` (the computer-assisted proof of Appendix A of the manuscript).

## Layout

| Directory | Contents |
|---|---|
| `NonUniqueEuler/Statement/` | The statements: the plane and the Biot–Savart law, weak and renormalized weak solutions, the ring, the datum, the Evans function and (N1)–(N3), the main theorem, and the certificate types. Definitions only, no proofs. |
| `NonUniqueEuler/Defs/` | Definitions used by the proofs, grouped by manuscript section (`Sec2` … `Sec11`, `SmoothB` for Appendix B, `Verify` for Appendix A), plus manuscript-independent infrastructure (`Infra`). |
| `NonUniqueEuler/I/` | Interface modules. `I/X.lean` is the single line `import NonUniqueEuler.P.X`, so it re-exports the proof module `P/X`. Other proofs import the statements they need through `I/…`. |
| `NonUniqueEuler/P/` | Proofs. `P/X.lean` proves one manuscript statement, or a small group of statements. |
| `NonUniqueEuler/H/` | Helper lemmas. `H/X/*` is used only by `P/X` and by its sibling helpers. |
| `NonUniqueEuler/Verify/` | The certificate checker. `Comp/` holds the algorithms in core Lean: dyadic ball arithmetic, the Evans enclosure, the contour, the winding certification, the runs, and the parallel evaluation. The exception is `Runs.lean`, which defines `Verify.check` on the statement-layer data types. `Data/` holds the certificate. `Main.lean` is the executable `ncert`. |
| `NonUniqueEuler/Vendor/` | Code adapted from the OpenAI `NavierStokesAndEuler` repository (Apache-2.0): global Picard existence and the flow of a bounded Lipschitz vector field. |
| `NonUniqueEuler/Final.lean` | The final theorems. |
| `tools/` | The scripts described below. |

**Import rules.** Several comments in `H/` and `P/` refer to these rules.
- A proof module `P/X` imports Mathlib, `Statement/`, `Defs/`, `Vendor/`, `Verify/`, its own
  helpers `H/X/*`, and the interface modules `I/Y` of the statements it uses.
- It never imports another `P` file, and never another proof's helper files.

The import graph therefore follows the dependency order of the manuscript's statements, and it
is acyclic. When two proofs need the same auxiliary lemma, the lemma is duplicated under
separate namespaces. Proof and helper files declare no global instances; the shared instances
are in `Defs/Infra/Instances.lean`.

## Building

1. Install [elan](https://github.com/leanprover/elan). The toolchain in `lean-toolchain` is
   selected automatically.
2. Run:

   ```
   lake exe cache get     # download the Mathlib build cache for the pinned revision
   lake build             # build the whole library
   ```

With the Mathlib cache, the build takes about one to two hours on an 11-core Apple-silicon
machine. Mathlib itself is not rebuilt.

**Checking for `sorry` and forbidden tokens.** `python3 tools/status.py` counts the `sorry`s
and forbidden tokens (`axiom`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`,
…), ignoring comments. It should report `TOTAL sorry = 0` and list no forbidden tokens.

**Checking the axioms.** After `lake build`, run:

```
lake env lean tools/PrintAxioms.lean
```

This prints the axioms of `main_theorem_of_certificate`, `main_theorem_full`,
`Verify.check_sound`, `check_cert` and `check_eq_checkCorePar`.

## Running the certificate checker

The executable imports only Lean core, so it compiles and links only about 15 modules and none
of Mathlib.

```
tools/ncert_build.sh OUTDIR          # lake build NonUniqueEuler.Verify.Main, then compile and link OUTDIR/ncert
tools/ncert_par_run.sh OUTDIR 6      # start `ncert par` in the background with 6 worker threads
```

**Output.** `ncert_par_run.sh` writes two files:
- `OUTDIR/par_all.log` shows the progress, one line per certified cell of the 261 cells.
- `OUTDIR/par_all.out` receives the result,
  `checkCorePar defaultPrec certLits = check cert = true|false`, followed by the exit code
  (`0` iff `true`).

**Threads and other variants.**
- The number of worker threads is the size of the Lean runtime's thread pool. It is
  `LEAN_NUM_THREADS` if set, and otherwise the number of hardware threads.
- On macOS, set `MallocNanoZone=1`, as the script does. Without it, the GMP allocations of
  different threads contend in `malloc`.
- `OUTDIR/ncert all` runs the same check single-threaded.
- `ncert count I J` and `ncert gap I J` certify individual cells. A partial run is evidence,
  not a verification. Only `ncert`, `ncert all` and `ncert par` evaluate the hypothesis of the
  final theorem.

**Cost.** The run is long. Each Evans enclosure takes about two CPU-seconds (Apple arm64). The
ball arithmetic is looser than Arb's, so the 25 (N1′) cells often need adaptive halving and many
more enclosures than the Python/Arb reference. The recorded full run used 106,680 enclosures:
8.75 hours wall time on 6 threads of an Apple M3 Pro, about 52 CPU-hours.

**Regenerating the certificate data.** The following command reproduces
`NonUniqueEuler/Verify/Data/CellLits.lean` and `Cells.lean` byte for byte. With `--check` it
writes nothing:

```
python3 -I -B tools/gen_cert_data.py PATH/TO/euler-ring-certificate --manuscript PATH/TO/A_verification.tex --check
```

`tools/check_identical_code.py ORIGINAL RELEASE` compares two copies of the Lean sources after
removing all comments and collapsing whitespace. It checks that two trees have the same code up to
comments and whitespace.

## Relation to the manuscript

**What is formalized.**
- `NumericalHypothesis` is the manuscript's Hypothesis (N), `hyp:N`. Its parts are the Evans
  function condition (N1) (stated as "exactly one zero in `{Re λ ≥ 9/200}`, and it is
  simple"), the zero-free strip (N2), and the inequality (N3).
- Part 2 formalizes Appendix A:
  - the reduction of (N1), (N2) to the finite statements (N1′), (N2′) (Lemma A.6);
  - the enclosure of the Evans function (Proposition A.3);
  - the winding formula (Proposition A.4);
  - the two runs (Proposition A.7).
- The written proof of (N3) (Proposition A.8) is also formalized.

**How it follows the manuscript.** The formalization follows the manuscript's argument, with
restructured proofs in places. The statements are unchanged, or replaced by equivalent or
sufficient forms. The design decisions and the list of restructurings are in
`FORMALIZATION_NOTES.md`. More local deviations of proofs are described in the docstrings of
the modules concerned.

**Inaccuracies found in the manuscript.** The formalization found three minor inaccuracies.
None affects the results.

1. **Rotations on `H^s`.** The paragraph after `def:sector-setting` (`04_ring.tex:181-185`)
   claims that rotations are isometries of `H^s(ℝ²)`, and that `P_ℓ` has norm at most 1 on
   every `Y^s`. With the manuscript's norm `‖g‖²_{H^s} = Σ_{|γ|≤s} ‖∂^γ g‖²`, this is false for
   `s ≥ 2`. The correct statements are `‖g ∘ O_θ‖_{H^s} ≤ 2^{s/2} ‖g‖_{H^s}` and
   `‖P_ℓ‖ ≤ 2^{s/2}`. The formalization proves the bound `2^s`, which suffices, because every
   later use needs only boundedness.
2. **The dependency table (Appendix C)** omits some inputs:
   - the row of `lem:iter-cauchy` omits `lem:iter-lip`;
   - the row of `lem:clock` omits `lem:inner-circ` and the uniqueness of trajectories
     (`thm:smooth`/`lem:flow`).
3. **Some hypotheses are stronger than needed.**
   - The conditions `μ⁴ s̄² ≤ 1/8` in `prop:confine`(iii), `s̄^{m-2} ≤ 1/2` in `lem:nesting`,
     and the `+1` in `lem:window-length` are not used.
   - `prop:kick` states the lower constant `1/10`, but its proof gives `1/5`.

   The Lean statements keep the manuscript's forms.

## Credits

- [Lean 4](https://lean-lang.org) and [Mathlib](https://github.com/leanprover-community/mathlib4).
- The files in `NonUniqueEuler/Vendor/` are adapted from the OpenAI repository
  [`NavierStokesAndEuler`](https://github.com/openai/NavierStokesAndEuler) (Apache License 2.0):
  global Picard existence for globally Lipschitz fields, and the flow of a bounded, uniformly
  Lipschitz vector field. The header of each file states its origin and what was changed. See
  `NOTICE`.
- The certificate data come from the Python/Arb reproduction package `euler-ring-certificate`
  that accompanies the manuscript. Its algorithms are the reference for `Verify/Comp`.

## License

Apache License 2.0 (`LICENSE`), copyright 2026 Matei P. Coiculescu. The files in
`NonUniqueEuler/Vendor/` are adapted from OpenAI's NavierStokesAndEuler, also under the Apache
License 2.0; see `NOTICE`.
