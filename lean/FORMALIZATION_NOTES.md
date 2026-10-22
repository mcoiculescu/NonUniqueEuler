# Formalization notes

This file records the representation choices and the restructured arguments of the
formalization. Comments in the Lean files refer to the labels used here:
- decision `D1`–`D15` (Part 1);
- restructuring `R1`–`R16`;
- library `I-…`;
- checker design decision `D1`–`D14`, and the checker deviations `A…`, `G1`, `T…`, `W…`.

Manuscript locators such as `04_ring.tex:181` refer to the TeX sources of the manuscript.

## 1. Representation of the objects (Part 1)

| | Decision |
|---|---|
| D1 | **The plane is `ℂ`**, with its Lebesgue measure `volume`. Real vector fields are `ℂ`-valued (`u₁ + i u₂`), and the rotation `O_θ` is multiplication by `e^{iθ}`. The manuscript itself identifies ℝ² with ℂ. |
| D2 | **Derivatives.** Directional derivatives are written `v·∇φ(x) = fderiv ℝ φ x v` with `v : ℂ`. The partial derivatives are `∂₁ = fderiv ℝ · x 1` and `∂₂ = fderiv ℝ · x I`; multi-index derivatives are obtained by iteration. |
| D3 | **Space–time functions are curried**: `ω : ℝ → ℂ → ℝ`, with `ω t x = ω(t, x)`. The test functions of `𝒟_T` are real-valued maps `φ : ℝ × ℂ → ℝ` of class `C^∞` with compact support in `(-∞, T) × ℝ²`. Since `ω` and `v` are real, complex test functions give the same class of solutions. |
| D4 | **Membership in `X_q(T) = L^∞(0,T; L¹ ∩ L^q)`** is a predicate with two parts: joint a.e.-strong measurability of `(t, x) ↦ ω t x` on `(0,T) × ℝ²`, and an essential bound on `‖ω(t)‖_{L¹} + ‖ω(t)‖_{L^q}`. This is the manuscript's own convention (`02_prelim.tex:101-120`). "Distinct elements of `X_q(T)`" means "not a.e. equal on `(0,T) × ℝ²`". |
| D5 | **The weak formulation includes its integrability conditions.** The absolute integrability of `ω(∂_tφ + v·∇φ)` on `(0,T) × ℝ²` and of `ω_in φ(0, ·)` are explicit conjuncts. So is the a.e. absolute convergence of the Biot–Savart integral. In Lean, the integral of a non-integrable function is `0`; the conjuncts keep this junk value out of the definition. The manuscript derives these conditions from `ω ∈ X_q(T)` with `q > 4/3`, so the definition is equivalent to the manuscript's. |
| D6 | **The velocity** is the Bochner integral `v(x) = ∫ K_BS(x − y) ω(y) dy`, with value `0` where the integrand is not integrable. It equals the manuscript's velocity a.e., and only its a.e. values enter. |
| D7 | **Sobolev spaces `H^k`** (integer `k` only, as in the manuscript) are defined by weak derivatives in `L²`. Fourier `H^s` is not used. |
| D8 | **The linear evolution is defined sector by sector**: `S(t)w = Σ_{ℓ ∈ 3ℤ} (exp(t L_ℓ(G)) g_ℓ) e^{iℓθ}`. Here `exp` is the Banach-algebra exponential of the bounded sector operator `L_ℓ(G)`. This is the manuscript's semigroup (`lem:semigroup-construct`(3)). See R1. |
| D9 | **Exponent 2 in Section 3.** The compactness section (Section 3) is formalized with the exponent `b = 2` only. The manuscript says that only this exponent is needed. Membership in `X_q` for other `q` follows from equimeasurability. See R5 and R7. |
| D10 | **The Riesz projection is explicit.** On the full space it is the rank-two operator `R(G)w = 2 Re(ℓ_*(G)(w) φ_*(G))`; on sector 3 it is `P g = ℓ_*(g) g_*`. Contour integrals appear only in one lemma, an exponential bound for a bounded operator, and only on circles. See R2. |
| D11 | **Constants are existential.** Every constant "depending only on …" is either existentially quantified or defined by `Classical.choose` from an existence theorem. The parameter lists (P0)–(P6) become structures. Uniformity is then a matter of quantifier order, which Lean checks. |
| D12 | **The cutoff `χ` of `def:ring` is a parameter**, constrained by the predicate `IsAdmissibleCutoff χ`. The main theorem is proved for every admissible `χ`, which is slightly stronger than the statement for one fixed `χ`. The explicit cutoff `chiStd` of `lem:ring-facts` is proved admissible, so the class is not empty. |
| D13 | **(N1)** is stated as "`E_3(·; G)` has exactly one zero in `{Re λ ≥ 9/200}`, and this zero is simple (`∂_λ E_3 ≠ 0`)". Since `E_3(·; G)` is holomorphic on `{Re λ > 0}`, this is equivalent to "exactly one zero, counted with multiplicity". |
| D14 | **One ambient space with predicates.** Function spaces are handled as one ambient space with predicates (`MemH k f`, …) and norms, not as a tower of subtypes. Sector spaces `Y^s_ℓ` are subtypes only where Banach-algebra exponentials need a complete type. |
| D15 | **Smoothness** is `ContDiff ℝ ∞` (`C^∞`), never `ContDiff ℝ ⊤`. In this version of Mathlib, `⊤` means analytic. |

Further statement-level conventions:
- **Radiality of `f`** is asserted pointwise, which is stronger than the a.e. notion.
- **`MainTheorem`** also contains the explicit form `thm:main-explicit` (see `README.md`).
- **The Evans function.** `E_ℓ(λ; G)` is defined from a solution pair of the first-order system,
  with one-sided derivatives at the endpoints, chosen by `Classical.epsilon`. Its existence and
  uniqueness for `Re λ > 0` are proved. The rings are indexed by `k = j + 1` with `j : ℕ`.

## 2. Restructured arguments (Part 1)

Each restructuring keeps the manuscript's statement, or replaces it by an equivalent form, or by
a weaker form that suffices for every use in the manuscript.

| | Restructuring |
|---|---|
| R1 | **No theory of C₀-semigroups.** The evolution is the sector-wise exponential of D8.<br>- Bounds for `\|ℓ\| ≥ M_γ` come from `prop:large-sectors`, by Duhamel's formula for bounded operators. The finitely many small `\|ℓ\|` are treated individually.<br>- `lem:duhamel` is proved sector by sector.<br>- `lem:semigroup-construct`(2) is stated as follows: the semigroup law, strong continuity, both Duhamel formulas, and `d/dt S(t)w = L S(t)w` for `w ∈ X^{s+1}`. This is all that later sections use. |
| R2 | **No Riesz projections of unbounded operators, and no contour deformation.**<br>- The spectral projection is the explicit rank-one operator of D10.<br>- `thm:evans-simple`(2) is stated as follows: `(λ − L₃)⁻¹ − (λ − λ_*)⁻¹ P` extends continuously to `λ_*`.<br>- The gap bound `‖exp(t L_ℓ)(1 − P_ℓ)‖ ≤ C e^{σ' t}` for the finitely many small sectors comes from a deflation `L₃ − (λ_* − μ₀) P` and a Dunford integral on one circle, uniformly in `G` (library I-DUNF).<br>- The second paragraph of `prop:SU` (the spectrum and Riesz projection of the full operator) is not needed downstream. |
| R3 | **No Fourier transform on ℝ².**<br>- The embedding (E2) holds with a constant that depends on the support.<br>- (E3) is proved by integration by parts.<br>- `lem:Hk-calculus`(2) is stated for products in which one factor is supported in a fixed ball, which covers all its uses. |
| R4 | **No Fourier transform on ℝ.** `lem:elliptic` is proved by the energy identity for `ψ'' − ℓ²ψ = f` in the logarithmic variable, using exponential decay at `±∞`. |
| R5 | **No Bochner spaces with values in `L¹ ∩ L^q`, no Pettis theorem, no `L^p` duality for `p ≠ 2`.**<br>- Section 3 works with weakly continuous `L²`-valued paths and Riesz representation in `L²`.<br>- The jointly measurable representative of `ω_∞` is constructed once (library I-JOINT).<br>- Membership in `X_q(T')` for `q ≠ 2` comes from equimeasurability.<br>- `lem:weak-cont` and `prop:compact` are stated for `b = 2`. |
| R6 | **No Green's identity on `{\|y\| > ε}`.** It is replaced by polar coordinates: an angular average followed by one-dimensional integration by parts. Where possible, it is replaced by whole-plane integration by parts, using the decay of the stream function. |
| R7 | **The DiPerna–Lions argument only for `a = b = 2`.** The field `w = K_BS ∗ ω` is an `L²_loc` limit of smooth divergence-free fields whose gradients converge in `L²`. This covers every use: the manuscript also uses `(a, b) = (1, ∞)`, but only for functions in `L^∞(L¹ ∩ L^∞) ⊂ L^∞(L²)`. |
| R8 | **Radon–Riesz only for `p = 2`.** `thm:criterion`(iii) for `q > 2` is proved by interpolation between continuity in `L²` and a uniform bound in `L^r`, `r > q`. Its hypothesis becomes `f ∈ L^r` for some `r > q`, which covers its only use (`f ∈ ⋂ L^q`). |
| R9 | **Continuity of `λ_*(G)` instead of real-analytic dependence.** Continuity on `[0, G₁]` is obtained from (N1), by boundedness and a limit-point argument. Only continuity, the attained minimum and continuity at `0` are used. |
| R10 | **`prop:bootstrap` by induction** over the phase intervals, in the chronological order that the manuscript's proof fixes. Each interval is closed by a generic continuity lemma. The proof is split into one statement per step of the manuscript's proof. |
| R11 | **No winding numbers in `lem:reduction`(1).** They are replaced by the circulation of `K_BS(· − y)` around circles, computed from the Laurent expansion of `(z − w)⁻¹` (library I-MULT). |
| R12 | **Explicit constants.** Constants that are used only existentially are existential (D11). The explicit numbers that matter stay explicit: `9/200`, `211/2500`, `1/50`, `17/16`, `a/16`, and the `μ`-dependent margins. |
| R13 | **Statements off the path to Theorem 1.1.** These are `lem:Lq-growth`, the unused implications of `prop:equiv`, the converse directions of `thm:evans-simple`(3), and `lem:nesting`. The main theorem does not depend on them. `lem:Lq-growth` and `lem:nesting` are formalized nevertheless. |
| R14 | **Independence of `q`.** The weak and renormalized identities are the same for every `q`. Once the integrability conditions hold, a solution is a solution in every `X_q(T)`. This is the manuscript's own argument in `thm:main-explicit`(ii). |
| R15 | **`lem:ode`** is proved from Mathlib's Picard–Lindelöf theorem, together with the vendored global existence and flow results (library I-FLOW). |
| R16 | **Symmetry of smooth solutions.** `thm:smooth`(6) follows from the uniqueness statement (5), applied to `ω(t) ∘ O_θ`. Time-translation and scaling covariance also follow from (5). Uniqueness itself is an `L²` energy estimate. |

## 3. Infrastructure libraries

These are manuscript-independent libraries, under `Defs/Infra`, `P/Infra` and `H/Infra`.

| Label | Content |
|---|---|
| I-POLAR | polar coordinates and radial calculus on `ℂ` |
| I-LPINT | interpolation in `L¹ ∩ L^q` |
| I-LPDUAL | weak convergence in `L^p`: boundedness, and `L¹` bounds of weak limits |
| I-EQM | equimeasurability and rearrangement facts |
| I-CONV | Minkowski's integral inequality, `L¹ ∗ L^p` |
| I-WEAKL2 | weak convergence in `L²` |
| I-JOINT | jointly measurable representatives of paths |
| I-CONT | continuity (bootstrap) arguments |
| I-CK | `C^k` norms on closed sets |
| I-HK | Sobolev spaces `H^k` by weak derivatives |
| I-SOB1 | weighted one-dimensional Sobolev norms (logarithmic variable) |
| I-MULT | the complex-variable form of the Biot–Savart law, multipoles |
| I-ANG | angular Fourier decomposition |
| I-SECT | sector spaces and sector-wise operators |
| I-ODE | linear second-order ODEs with parameters (shared with Part 2) |
| I-DUNF | exponential bounds from the spectrum, by Dunford integrals on circles |
| I-FLOW | flows of smooth bounded vector fields on `ℂ` (partly vendored) |
| I-FAA | derivatives of `e^{iφ} g` |

## 4. The certificate checker (Part 2)

### Checker design decisions

| | Decision |
|---|---|
| D1 | **The final theorem is conditional** on `Verify.check Verify.cert = true`. No kernel evaluation, `decide`, `rfl` or `native_decide` is applied to the certificate. A compiled run discharges the hypothesis outside the logic. |
| D2 | **Numbers.** The number type is `Dy`: mantissa and exponent in `Int`, with value `man · 2^exp`. It is not normalized. Rounding to `p` significant bits uses an explicit floor or ceiling. |
| D3 | **Balls.** A ball is `{mid, rad, fin}`, with membership `fin = false ∨ (0 ≤ rad ∧ \|x − mid\| ≤ rad)`. Every operation is total; division by a ball that contains `0` returns the infinite ball. |
| D4 | **Boxes.** A complex box is a pair of balls, `z ∈ B ↔ Re z ∈ B.re ∧ Im z ∈ B.im`. There is no disk arithmetic. |
| D5 | **Upper bounds.** These are held in `UB = Option Dy`, where `none` means `+∞`. They are monotone bounds, not enclosures. |
| D6 | **The computation modules** (`Verify/Comp/*`, `Verify/Data/*`) import only Lean core. The proofs import Mathlib. |
| D7 | **Proof-carrying search.** Every accepted segment, indicator and certified cell carries the evidence that the enclosure was computed and classified. The bisection, the counters and the adaptive halving therefore need no invariant proofs. |
| D8 | **The contour.** The rectangle contour is one closed curve, parametrized on `[0, 4]` by a closed form. Its segment endpoints are rational parameters, and its points are computed exactly in `ℚ`. |
| D9 | **Taylor remainders** use Lagrange's form for `Re ∘ f` and `Im ∘ f` separately. This is equivalent to the manuscript's integral form with convexity, because a box is a product of intervals. |
| D10 | **Smoothness** is `ContDiff ℝ ∞`. |
| D11 | **Every cutoff.** All soundness theorems hold for every admissible cutoff `χ`. |
| D12 | **Coefficient vectors** are lists of length at most `N + 2 = 18`, built by structural recursion with fuel. |
| D13 | **Exact rationals** are used only for the contour, the cells, the rectangles and the construction of the grid. They enter the ball arithmetic as in §A.1 of the manuscript. |
| D14 | **No unfolding of the data.** The certificate and the top-level runs are `@[irreducible]`, or are reached only through generic theorems, so that no proof evaluates them. |

### Deviations from the reference package (Python/Arb)

The soundness theorems hold for every precision, grid and run parameters. A difference from the
reference package can therefore only make the check fail. It can never make an unsound check
pass.

| | Deviation |
|---|---|
| A1 | **Own ball arithmetic** instead of FLINT/Arb, with the containment property proved, not trusted. Radii, and hence segment counts, may differ slightly. The manuscript (§A.7) allows this. |
| A2 | **`exp`** by argument reduction, Taylor series and squaring; `H` through `exp`. |
| A3 | **`κ_*`** is a checked dyadic candidate with `κ² ≥ max(q_*, ℓ²)`, which is all that the proof of Proposition A.3 uses. |
| A4 | **Ball division** is multiplication by a ball reciprocal. |
| A5 | **Midpoints** are truncated toward zero; the error goes into the radius. |
| A6 | **Addition of upper bounds** floors the smaller operand at `2⁻³⁰` relative to the larger. |
| A7 | **A tight complex inverse** (`CBox.invTight`) is used for `1/D_0`, similar to Arb's `acb_inv`. |
| G1 | **The grid** is checked at run time (the check fails closed). The Python code asserts these conditions instead. |
| T1 | **The Taylor remainder** uses Lagrange's form per component (D9). |
| T2 | **Lemma A.1(2)** is proved by scalar variation of constants for `ψ' ± ℓψ`, instead of a matrix exponential. |
| T3 | **Lemma A.1(1).** The proof uses `B(1 − B) ≤ 1/4`, and the exact identity `w' = (2/d) A B (Ā − B̄)` for `w = AB`. |
| W1 | **The indicator sum** is evaluated with junction indicators. It is proved equal to the full indicator sum by cyclic summation by parts. |
| W2 | **No sorting before the coverage check.** The certified sub-cells are not sorted (the check fails closed; the inputs are sorted). |
| W3 | **The contour** is parametrized on `[0, 4]`. It has the same points and segments as the package. |
| S1 | **Proposition A.3 is stronger.** It is proved for every `ℓ ≥ 1`, every precision and every real `G`, which is stronger than the manuscript. |
| C1 | **The package's numerical checks of the written proofs** (Lemma A.1(1), Lemma A.2, (N3)) are not ported. These statements are proved in Lean. |

The argument principle for rectangles, which Lemma A.6 uses, is proved topologically. Linear
factors are divided out (with `dslope`), and no contour integral is involved.
