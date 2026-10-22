import NonUniqueEuler.Defs.Sec3.Criterion

/-!
# Section 3: the conclusions of `thm:criterion` and the conditions of `prop:equiv`

Manuscript sources: `thm:criterion` (`03_compactness.tex:933-968`), `prop:equiv`
(`03_compactness.tex:1079-1097`).

* `IsCriterionLimit T₀ T f ωs φ ωinf`: the conclusions (i)–(vi) of `thm:criterion` for the
  subsequence `φ` (`n ↦ ωs (φ n)`) and the limit `ωinf` (the manuscript's `ω_∞`). The criterion
  reads `∃ φ ωinf, IsCriterionLimit T₀ T f ωs φ ωinf` (`I/Sec3/Criterion.lean`). Conventions:
  - `ωinf` is identified with its weakly continuous representative on `[0, T₀)`
    (`weakCont`; the manuscript's `ω_∞ : [0, T₀) → L¹ ∩ L²`, `03_compactness.tex:943-944`,
    and the convention `03_compactness.tex:238-247`);
  - (iii) for `q > 2` is in the form of restructuring **R8**:
    continuity into `L^q` for `q ∈ (2, r)` when `f ∈ L^r`, instead of "for `q` with `f ∈ L^q`";
  - (v): `𝒪 = departureSet T₀ ωinf f`, `t₀ = departureTime T₀ ωinf f`; "distinct elements of
    `X_q(T')`" is `DistinctInX T' …` (it does not depend on `q`), and "both are renormalized
    weak solutions with datum `f`" is stated for every `q ∈ (4/3, ∞)` with `f ∈ L^q`;
  - (vi): orthogonal maps of `ℝ²` are linear isometries `ℂ ≃ₗᵢ[ℝ] ℂ`.
* The conditions (c), (d), (e) of `prop:equiv` (`03_compactness.tex:1086-1096`):
  `NotDistribTendsto T ωs f` ((c): for some `t ∈ (0, T]`, `ω⁽ⁿ⁾(t) ↛ f` in `𝒟'(ℝ²)`, i.e. for
  some `ψ ∈ C_c^∞(ℝ²)` the pairings `∫ ω⁽ⁿ⁾(t) ψ` do not converge to `∫ f ψ`),
  `HasPairingDefect T ωs f` ((d)), `HasNonstationaryLimit T₀ T ωs f` ((e); the limit is
  identified with its weakly continuous representative, so that `ω_∞(t)` is a function class for
  every `t`). Conditions (a) and (b) are `0 < defectLp p T ωs f` with `p = 1`, resp.
  `p = ofReal q`, `q ∈ (1, 2]`.

This file contains definitions only.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact

open Weak

/-- The conclusions (i)–(vi) of `thm:criterion` (`03_compactness.tex:942-967`) for the
subsequence `φ` of the `2`-admissible sequence `ωs` and the limit `ωinf` (`ω_∞`), with
`T ∈ (0, T₀)` the time of eq:defect. -/
structure IsCriterionLimit (T₀ : ℝ≥0∞) (T : ℝ) (f : ℂ → ℝ) (ωs : ℕ → ℝ → ℂ → ℝ) (φ : ℕ → ℕ)
    (ωinf : ℝ → ℂ → ℝ) : Prop where
  /-- `(n_k)` is a subsequence. -/
  strictMono : StrictMono φ
  /-- (i) `ω_∞` is a renormalized weak solution on `[0, T₀)` with datum `f`, exponent `2`. -/
  renormalized : IsRenormalizedWeakSolutionUpTo 2 T₀ f ωinf
  /-- `ω_∞ : [0, T₀) → L¹ ∩ L²` is weakly continuous into `L²` (its own representative). -/
  weakCont : IsWeakContL2On (timeInterval T₀) ωinf
  /-- (ii) `ω_∞(t)` is equimeasurable with `f` for every `t ∈ [0, T₀)`. -/
  equimeasurable : ∀ t ∈ timeInterval T₀, Equimeasurable (ωinf t) f
  /-- (ii) `‖ω_∞(t)‖_{L^p} = ‖f‖_{L^p}` for every `p ∈ [1, ∞]`. -/
  eLpNorm_eq : ∀ t ∈ timeInterval T₀, ∀ p : ℝ≥0∞, 1 ≤ p →
    eLpNorm (ωinf t) p volume = eLpNorm f p volume
  /-- (ii) `ω_∞ ≥ 0` if `f ≥ 0`. -/
  nonneg : 0 ≤ᵐ[volume] f → ∀ t ∈ timeInterval T₀, 0 ≤ᵐ[volume] ωinf t
  /-- (ii) `ω_∞` is a renormalized weak solution in `X_q(T')` for every `T' < T₀` and every
  `q ∈ (4/3, ∞)` with `f ∈ L^q`. -/
  renormalized_q : ∀ T' : ℝ, 0 < T' → ENNReal.ofReal T' < T₀ → ∀ q : ℝ, 4 / 3 < q →
    MemLp f (ENNReal.ofReal q) volume → IsRenormalizedWeakSolution q T' f ωinf
  /-- (iii) `ω_∞ ∈ C([0, T₀); L^q)` for `q ∈ [1, 2]`. -/
  continuousIntoLp_le_two : ∀ q : ℝ, 1 ≤ q → q ≤ 2 →
    ContinuousIntoLpOn (ENNReal.ofReal q) (timeInterval T₀) ωinf
  /-- (iii) for `q > 2`, in the form R8: `ω_∞ ∈ C([0, T₀); L^q)` if `f ∈ L^r` for some
  `r > q`. -/
  continuousIntoLp_gt_two : ∀ q r : ℝ, 2 < q → q < r → MemLp f (ENNReal.ofReal r) volume →
    ContinuousIntoLpOn (ENNReal.ofReal q) (timeInterval T₀) ωinf
  /-- (iv) `sup_{0 ≤ t ≤ T'} ‖ω^{(n_k)}(t) - ω_∞(t)‖_{L^q} → 0` for `T' < T₀`, `q ∈ [1, 2]`. -/
  tendstoUnif : TendstoUnifLqUpTo T₀ (fun n => ωs (φ n)) ωinf
  /-- (v) `sup_{0 ≤ t ≤ T} ‖ω_∞(t) - f‖_{L¹} = c` (eq:defect). -/
  supDist_eq : supDist 1 (Icc 0 T) ωinf (stationary f) = defectLp 1 T ωs f
  /-- (v) `𝒪` is open. -/
  isOpen_departureSet : IsOpen (departureSet T₀ ωinf f)
  /-- (v) `0 ∉ 𝒪`. -/
  zero_not_mem_departureSet : (0 : ℝ) ∉ departureSet T₀ ωinf f
  /-- (v) `𝒪 ∩ (0, T] ≠ ∅`. -/
  departureSet_inter_nonempty : (departureSet T₀ ωinf f ∩ Ioc 0 T).Nonempty
  /-- (v) `t₀ = inf 𝒪 < T` (and `0 ≤ t₀`: `departureTime_nonneg`). -/
  departureTime_lt : departureTime T₀ ωinf f < T
  /-- (v) `ω_∞` and the stationary solution `f` are distinct elements of `X_q(T')` for every
  `T' ∈ (t₀, T₀)`. -/
  distinct : ∀ T' : ℝ, departureTime T₀ ωinf f < T' → ENNReal.ofReal T' < T₀ →
    DistinctInX T' ωinf (stationary f)
  /-- (v) both are renormalized weak solutions in `X_q(T')` with datum `f`, for every
  `T' ∈ (t₀, T₀)` and every `q ∈ (4/3, ∞)` with `f ∈ L^q`. -/
  both_renormalized : ∀ T' : ℝ, departureTime T₀ ωinf f < T' → ENNReal.ofReal T' < T₀ →
    ∀ q : ℝ, 4 / 3 < q → MemLp f (ENNReal.ofReal q) volume →
      IsRenormalizedWeakSolution q T' f (stationary f) ∧ IsRenormalizedWeakSolution q T' f ωinf
  /-- (vi) symmetries `ω⁽ⁿ⁾(t, Qx) = ι ω⁽ⁿ⁾(t, x)` of all `ω⁽ⁿ⁾` pass to `ω_∞`. -/
  symmetric : ∀ (Q : ℂ ≃ₗᵢ[ℝ] ℂ) (ι : ℝ), (ι = 1 ∨ ι = -1) →
    (∀ n, ∀ t ∈ timeInterval T₀, IsSymmetricUnder Q ι (ωs n t)) →
    ∀ t ∈ timeInterval T₀, IsSymmetricUnder Q ι (ωinf t)

/-- `prop:equiv`(c) (`03_compactness.tex:1088-1089`): there is `t ∈ (0, T]` such that `ω⁽ⁿ⁾(t)`
does not converge to `f` in `𝒟'(ℝ²)`, i.e. for some real `ψ ∈ C_c^∞(ℝ²)` the pairings
`∫ ω⁽ⁿ⁾(t) ψ` do not converge to `∫ f ψ`. -/
def NotDistribTendsto (T : ℝ) (ωs : ℕ → ℝ → ℂ → ℝ) (f : ℂ → ℝ) : Prop :=
  ∃ t ∈ Ioc 0 T, ∃ ψ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ HasCompactSupport ψ ∧
    ¬ Tendsto (fun n => ∫ x, ωs n t x * ψ x) atTop (𝓝 (∫ x, f x * ψ x))

/-- `prop:equiv`(d) (`03_compactness.tex:1090-1091`): there is a real `ψ ∈ C_c^∞(ℝ²)` with
`limsup_n sup_{t ≤ T} |∫ (ω⁽ⁿ⁾(t) - f) ψ| > 0`. -/
def HasPairingDefect (T : ℝ) (ωs : ℕ → ℝ → ℂ → ℝ) (f : ℂ → ℝ) : Prop :=
  ∃ ψ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ HasCompactSupport ψ ∧
    0 < defectPairing T ωs f ψ

/-- `prop:equiv`(e) (`03_compactness.tex:1092-1096`): some subsequence converges, in the sense of
`thm:criterion`(iv), to a renormalized weak solution `ω_∞` on `[0, T₀)` with datum `f`
(exponent `2`, identified with its weakly continuous representative) such that `ω_∞(t) ≠ f` for
some `t ∈ (0, T]`. -/
def HasNonstationaryLimit (T₀ : ℝ≥0∞) (T : ℝ) (ωs : ℕ → ℝ → ℂ → ℝ) (f : ℂ → ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ωinf : ℝ → ℂ → ℝ,
    IsRenormalizedWeakSolutionUpTo 2 T₀ f ωinf ∧ IsWeakContL2On (timeInterval T₀) ωinf ∧
    TendstoUnifLqUpTo T₀ (fun n => ωs (φ n)) ωinf ∧
    ∃ t ∈ Ioc 0 T, ¬ (ωinf t =ᵐ[volume] f)

end NonUniqueEuler.Compact
