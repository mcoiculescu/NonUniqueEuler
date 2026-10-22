import NonUniqueEuler.Defs.Infra.Dunford
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Proof of `I/Infra/Dunford/Integral.lean` (I-DUNF (D1), (D2))

Let `X` be a complex Banach space and `A : X →L[ℂ] X` with `spectrum ℂ A ⊆ ball c ρ`. Write
`R(z) = (z - A)⁻¹` (Mathlib's `resolvent A z`). The proof of the Dunford formula
`exp(tA) = (2πi)⁻¹ ∮_{|z-c|=ρ} e^{tz} R(z) dz` is organised as follows (no Neumann series
and no Cauchy formula for derivatives are needed).

1. `circleIntegral_resolvent`: `∮_{C(c,ρ)} R(z) dz = 2πi`. The integral does not depend on the
   radius `r ≥ ρ` (Cauchy on the annulus, which lies in the resolvent set), and
   `R(z) - (z - c)⁻¹ = (z - c)⁻¹ R(z) (A - c)` is `O(r⁻¹ ‖R(z)‖)` on `C(c, r)`, while
   `R(z) → 0` at infinity (`spectrum.resolvent_tendsto_cobounded`); so the difference with
   `∮_{C(c,r)} (z - c)⁻¹ dz = 2πi` is arbitrarily small.
2. `circleIntegral_pow_smul_resolvent`: `∮ z^n R(z) dz = A^n ∮ R(z) dz`, by induction from
   `z R(z) = 1 + A R(z)` and `∮ z^n dz = 0`.
3. `circleIntegral_exp_smul_resolvent`: expanding `e^{tz} = ∑ (tz)^n / n!` (uniformly on the
   circle) and integrating termwise (`hasSum_circleIntegral_of_norm_le`, dominated convergence)
   gives `∮ e^{tz} R(z) dz = 2πi ∑ t^n A^n / n! = 2πi exp(tA)`.

The circle bound is `circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const` with
`‖e^{tz}‖ = e^{t Re z} ≤ e^{t (Re c + ρ)}` on the circle for `t ≥ 0`.

All helper lemmas (steps 1–3 and the resolvent identities) are in the namespace
`NonUniqueEuler.Dunford.IntegralAux`.
-/

noncomputable section

open Filter Topology Metric
open scoped Real Nat

namespace NonUniqueEuler.Dunford

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-! Helper lemmas live in the sub-namespace `IntegralAux` to avoid clashes with other files of
the `NonUniqueEuler.Dunford` namespace in the full library. -/
namespace IntegralAux

section Helpers

/-- Termwise integration on a circle of a series dominated by a summable sequence of constants. -/
theorem hasSum_circleIntegral_of_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {F : ℕ → ℂ → E} {f : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hF : ∀ n, ContinuousOn (F n) (sphere c R)) (b : ℕ → ℝ) (hb : Summable b)
    (hFb : ∀ n, ∀ z ∈ sphere c R, ‖F n z‖ ≤ b n)
    (hlim : ∀ z ∈ sphere c R, HasSum (fun n => F n z) (f z)) :
    HasSum (fun n => ∮ z in C(c, R), F n z) (∮ z in C(c, R), f z) := by
  simp only [circleIntegral]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => R * b n)
    (fun n => ((hF n).circleIntegrable hR).out.def'.aestronglyMeasurable) ?_ ?_
    intervalIntegrable_const ?_
  · intro n
    refine Eventually.of_forall (fun θ _ => ?_)
    rw [norm_smul, deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one,
      abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_left (hFb n _ (circleMap_mem_sphere _ hR _)) hR
  · exact Eventually.of_forall (fun θ _ => hb.mul_left R)
  · exact Eventually.of_forall (fun θ _ => (hlim _ (circleMap_mem_sphere _ hR _)).const_smul _)

/-- A constant operator can be pulled out of a circle integral (on the left). -/
theorem circleIntegral_mul_left (B : X →L[ℂ] X) {f : ℂ → X →L[ℂ] X} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), B * f z) = B * ∮ z in C(c, R), f z := by
  have h := (ContinuousLinearMap.mul ℂ (X →L[ℂ] X) B).intervalIntegral_comp_comm hf.out
  simp only [ContinuousLinearMap.mul_apply', mul_smul_comm] at h
  simpa only [circleIntegral] using h

omit [CompleteSpace X] in
/-- Points at distance `≥ ρ` from `c` are in the resolvent set when the spectrum lies in
`ball c ρ`. -/
theorem mem_resolventSet_of_le_dist {A : X →L[ℂ] X} {c : ℂ} {ρ : ℝ}
    (hA : spectrum ℂ A ⊆ ball c ρ) {z : ℂ} (hz : ρ ≤ dist z c) : z ∈ resolventSet ℂ A := by
  by_contra h
  have h' : z ∈ spectrum ℂ A := h
  have := hA h'
  rw [mem_ball] at this
  linarith

omit [CompleteSpace X] in
/-- `z R(z) = 1 + A R(z)` on the resolvent set. -/
theorem smul_resolvent_eq {A : X →L[ℂ] X} {z : ℂ} (hz : z ∈ resolventSet ℂ A) :
    z • resolvent A z = 1 + A * resolvent A z := by
  have h : (algebraMap ℂ (X →L[ℂ] X) z - A) * resolvent A z = 1 :=
    Ring.mul_inverse_cancel _ hz
  rw [Algebra.algebraMap_eq_smul_one, sub_mul, smul_mul_assoc, one_mul] at h
  rw [← h]
  abel

omit [CompleteSpace X] in
/-- `R(z) (A - c) = (z - c) R(z) - 1` on the resolvent set. -/
theorem resolvent_mul_sub_eq {A : X →L[ℂ] X} {z : ℂ} (hz : z ∈ resolventSet ℂ A) (c : ℂ) :
    resolvent A z * (A - c • (1 : X →L[ℂ] X)) = (z - c) • resolvent A z - 1 := by
  have h : resolvent A z * (algebraMap ℂ (X →L[ℂ] X) z - A) = 1 :=
    Ring.inverse_mul_cancel _ hz
  have hsplit : A - c • (1 : X →L[ℂ] X) =
      (z - c) • (1 : X →L[ℂ] X) - (algebraMap ℂ (X →L[ℂ] X) z - A) := by
    rw [Algebra.algebraMap_eq_smul_one, sub_smul]
    abel
  rw [hsplit, mul_sub, h, mul_smul_comm, mul_one]

/-- The resolvent is continuous at points of the resolvent set. -/
theorem continuousAt_resolvent {A : X →L[ℂ] X} {z : ℂ} (hz : z ∈ resolventSet ℂ A) :
    ContinuousAt (resolvent A) z :=
  (spectrum.hasDerivAt_resolvent_const_left hz).continuousAt

/-- The resolvent is continuous on `{ρ ≤ |z - c|}` when the spectrum lies in `ball c ρ`. -/
theorem continuousOn_resolvent_of_subset {A : X →L[ℂ] X} {c : ℂ} {ρ : ℝ}
    (hA : spectrum ℂ A ⊆ ball c ρ) {s : Set ℂ} (hs : ∀ z ∈ s, ρ ≤ dist z c) :
    ContinuousOn (resolvent A) s :=
  fun z hz => (continuousAt_resolvent (mem_resolventSet_of_le_dist hA (hs z hz))).continuousWithinAt

theorem continuousOn_resolvent_sphere {A : X →L[ℂ] X} {c : ℂ} {ρ r : ℝ}
    (hA : spectrum ℂ A ⊆ ball c ρ) (hr : ρ ≤ r) : ContinuousOn (resolvent A) (sphere c r) :=
  continuousOn_resolvent_of_subset hA (fun z hz => by rw [mem_sphere.1 hz]; exact hr)

end Helpers

section Moments

variable {A : X →L[ℂ] X} {c : ℂ} {ρ : ℝ}

/-- Step 1: `∮_{C(c,ρ)} (z - A)⁻¹ dz = 2πi`. -/
theorem circleIntegral_resolvent (hρ : 0 < ρ) (hA : spectrum ℂ A ⊆ ball c ρ) :
    (∮ z in C(c, ρ), resolvent A z) = (2 * π * Complex.I) • (1 : X →L[ℂ] X) := by
  -- independence of the radius
  have hrad : ∀ r, ρ ≤ r → (∮ z in C(c, r), resolvent A z) = ∮ z in C(c, ρ), resolvent A z := by
    intro r hr
    refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hρ hr
      Set.countable_empty ?_ ?_
    · refine continuousOn_resolvent_of_subset hA (fun z hz => ?_)
      have := hz.2
      rw [mem_ball, not_lt] at this
      exact this
    · intro z hz
      have h1 := hz.1.2
      rw [mem_closedBall, not_le] at h1
      exact (spectrum.hasDerivAt_resolvent_const_left
        (mem_resolventSet_of_le_dist hA h1.le)).differentiableAt
  set K : ℝ := ‖A - c • (1 : X →L[ℂ] X)‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  apply eq_of_forall_dist_le
  intro ε hε
  set δ : ℝ := ε / (2 * π * (K + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hev : ∀ᶠ z in Bornology.cobounded ℂ, dist (resolvent A z) 0 < δ :=
    Metric.tendsto_nhds.1 (spectrum.resolvent_tendsto_cobounded (𝕜 := ℂ) A) δ hδ0
  obtain ⟨r₀, -, hr₀⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.1 hev
  set r : ℝ := max ρ (r₀ + ‖c‖) with hr
  have hρr : ρ ≤ r := le_max_left _ _
  have hr0 : 0 < r := lt_of_lt_of_le hρ hρr
  -- on the big circle
  have hint1 : CircleIntegrable (resolvent A) c r :=
    (continuousOn_resolvent_sphere hA hρr).circleIntegrable hr0.le
  have hcont2 : ContinuousOn (fun z : ℂ => (z - c)⁻¹ • (1 : X →L[ℂ] X)) (sphere c r) := by
    have hinv : ContinuousOn (fun z : ℂ => (z - c)⁻¹) (sphere c r) :=
      (continuousOn_id.sub continuousOn_const).inv₀
        (fun z hz => sub_ne_zero.2 (ne_of_mem_sphere hz hr0.ne'))
    exact hinv.smul continuousOn_const
  have hint2 : CircleIntegrable (fun z : ℂ => (z - c)⁻¹ • (1 : X →L[ℂ] X)) c r :=
    hcont2.circleIntegrable hr0.le
  have h2pi : (∮ z in C(c, r), (z - c)⁻¹ • (1 : X →L[ℂ] X)) =
      (2 * π * Complex.I) • (1 : X →L[ℂ] X) := by
    rw [circleIntegral.integral_smul_const, circleIntegral.integral_sub_inv_of_mem_ball
      (mem_ball_self hr0)]
  rw [← hrad r hρr, ← h2pi, dist_eq_norm, ← circleIntegral.integral_sub hint1 hint2]
  -- pointwise bound
  have hbound : ∀ z ∈ sphere c r,
      ‖resolvent A z - (z - c)⁻¹ • (1 : X →L[ℂ] X)‖ ≤ r⁻¹ * (δ * K) := by
    intro z hz
    have hzc : dist z c = r := mem_sphere.1 hz
    have hz' : z ∈ resolventSet ℂ A := mem_resolventSet_of_le_dist hA (hzc ▸ hρr)
    have hne : z - c ≠ 0 := sub_ne_zero.2 (ne_of_mem_sphere hz hr0.ne')
    have hid : resolvent A z - (z - c)⁻¹ • (1 : X →L[ℂ] X) =
        (z - c)⁻¹ • (resolvent A z * (A - c • (1 : X →L[ℂ] X))) := by
      rw [resolvent_mul_sub_eq hz' c, smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have hnorm_z : r₀ ≤ ‖z‖ := by
      have h1 : ‖z - c‖ ≤ ‖z‖ + ‖c‖ := norm_sub_le _ _
      rw [← dist_eq_norm, hzc] at h1
      have h2 : r₀ + ‖c‖ ≤ r := le_max_right _ _
      linarith
    have hRz : ‖resolvent A z‖ ≤ δ := by
      have := hr₀ (show z ∈ {x : ℂ | r₀ ≤ ‖x‖} from hnorm_z)
      rw [dist_zero_right] at this
      exact this.le
    rw [hid, norm_smul, norm_inv, ← dist_eq_norm, hzc]
    gcongr
    calc ‖resolvent A z * (A - c • (1 : X →L[ℂ] X))‖
        ≤ ‖resolvent A z‖ * K := norm_mul_le _ _
      _ ≤ δ * K := by gcongr
  refine (circleIntegral.norm_integral_le_of_norm_le_const hr0.le hbound).trans ?_
  have : 2 * π * r * (r⁻¹ * (δ * K)) = 2 * π * δ * K := by
    field_simp
  rw [this, hδ]
  have hpi : 0 < 2 * π := Real.two_pi_pos
  rw [div_eq_mul_inv, mul_inv]
  calc 2 * π * (ε * ((2 * π)⁻¹ * (K + 1)⁻¹)) * K = ε * (K / (K + 1)) := by
        field_simp
    _ ≤ ε * 1 := by
        gcongr
        rw [div_le_one (by linarith)]
        linarith
    _ = ε := mul_one ε

/-- Step 2: `∮_{C(c,ρ)} z^n (z - A)⁻¹ dz = A^n ∮_{C(c,ρ)} (z - A)⁻¹ dz`. -/
theorem circleIntegral_pow_smul_resolvent (hρ : 0 < ρ) (hA : spectrum ℂ A ⊆ ball c ρ) (n : ℕ) :
    (∮ z in C(c, ρ), z ^ n • resolvent A z) = A ^ n * ∮ z in C(c, ρ), resolvent A z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hres := continuousOn_resolvent_sphere hA (le_refl ρ)
    have hcongr : Set.EqOn (fun z : ℂ => z ^ (n + 1) • resolvent A z)
        (fun z : ℂ => z ^ n • (1 : X →L[ℂ] X) + A * (z ^ n • resolvent A z)) (sphere c ρ) := by
      intro z hz
      have hz' : z ∈ resolventSet ℂ A :=
        mem_resolventSet_of_le_dist hA (le_of_eq (mem_sphere.1 hz).symm)
      simp only
      rw [pow_succ, mul_smul, smul_resolvent_eq hz', smul_add, mul_smul_comm]
    have hint1 : CircleIntegrable (fun z : ℂ => z ^ n • (1 : X →L[ℂ] X)) c ρ :=
      ((continuous_pow n).smul continuous_const).continuousOn.circleIntegrable hρ.le
    have hint2 : CircleIntegrable (fun z : ℂ => z ^ n • resolvent A z) c ρ :=
      (((continuous_pow n).continuousOn).smul hres).circleIntegrable hρ.le
    have hint3 : CircleIntegrable (fun z : ℂ => A * (z ^ n • resolvent A z)) c ρ :=
      ((continuousOn_const.mul (((continuous_pow n).continuousOn).smul hres))).circleIntegrable
        hρ.le
    have hzero : (∮ z in C(c, ρ), z ^ n • (1 : X →L[ℂ] X)) = 0 := by
      refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.le Set.countable_empty
        ((continuous_pow n).smul continuous_const).continuousOn (fun z _ => ?_)
      exact ((differentiable_pow n) z).smul_const _
    rw [circleIntegral.integral_congr hρ.le hcongr, circleIntegral.integral_add hint1 hint3,
      hzero, zero_add, circleIntegral_mul_left A hint2, ih, ← mul_assoc, ← pow_succ']

/-- Step 3: `∮_{C(c,ρ)} e^{tz} (z - A)⁻¹ dz = 2πi exp(tA)`. -/
theorem circleIntegral_exp_smul_resolvent (hρ : 0 < ρ) (hA : spectrum ℂ A ⊆ ball c ρ) (t : ℂ) :
    (∮ z in C(c, ρ), Complex.exp (t * z) • resolvent A z) =
      (2 * π * Complex.I) • NormedSpace.exp (t • A) := by
  have hres := continuousOn_resolvent_sphere hA (le_refl ρ)
  obtain ⟨M, hM⟩ := (isCompact_sphere c ρ).exists_bound_of_continuousOn hres
  set F : ℕ → ℂ → X →L[ℂ] X := fun n z => ((n ! : ℂ)⁻¹ • (t * z) ^ n) • resolvent A z with hF
  have hsum : HasSum (fun n => ∮ z in C(c, ρ), F n z)
      (∮ z in C(c, ρ), Complex.exp (t * z) • resolvent A z) := by
    refine hasSum_circleIntegral_of_norm_le hρ.le (fun n => ?_)
      (fun n => (‖t‖ * (‖c‖ + ρ)) ^ n / n ! * M)
      ((Real.summable_pow_div_factorial _).mul_right M) (fun n z hz => ?_) (fun z hz => ?_)
    · exact ((((continuous_const.mul continuous_id).pow n).const_smul ((n ! : ℂ)⁻¹)).continuousOn).smul hres
    · have hzn : ‖z‖ ≤ ‖c‖ + ρ := by
        have h1 : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := norm_le_norm_sub_add z c
        rw [← dist_eq_norm, mem_sphere.1 hz] at h1
        linarith
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hz)
      simp only [hF]
      rw [norm_smul, norm_smul, norm_pow, norm_mul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
      gcongr
      · exact hM z hz
    · have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (t * z)).smul_const (resolvent A z)
      rw [← Complex.exp_eq_exp_ℂ] at h
      exact h
  have hterm : ∀ n : ℕ, (∮ z in C(c, ρ), F n z) =
      (2 * π * Complex.I) • ((n ! : ℂ)⁻¹ • (t • A) ^ n) := by
    intro n
    have hpt : (fun z => F n z) = fun z => ((n ! : ℂ)⁻¹ * t ^ n) • (z ^ n • resolvent A z) := by
      funext z
      simp only [hF, smul_eq_mul, mul_pow, smul_smul, mul_assoc]
    rw [hpt, circleIntegral.integral_smul, circleIntegral_pow_smul_resolvent hρ hA n,
      circleIntegral_resolvent hρ hA, mul_smul_comm, mul_one, smul_pow, smul_smul, smul_smul,
      smul_smul]
    congr 1
    ring
  have h2 : HasSum (fun n : ℕ => (2 * π * Complex.I) • ((n ! : ℂ)⁻¹ • (t • A) ^ n))
      ((2 * π * Complex.I) • NormedSpace.exp (t • A)) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (t • A)).const_smul _
  have hsum' : HasSum (fun n : ℕ => (2 * π * Complex.I) • ((n ! : ℂ)⁻¹ • (t • A) ^ n))
      (∮ z in C(c, ρ), Complex.exp (t * z) • resolvent A z) := by
    simpa only [hterm] using hsum
  exact hsum'.unique h2

end Moments

end IntegralAux

open IntegralAux

/-- **(D1) The Dunford formula** on a circle enclosing the spectrum. -/
theorem exp_eq_expDunford (A : X →L[ℂ] X) {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hA : spectrum ℂ A ⊆ ball c ρ) (t : ℂ) :
    NormedSpace.exp (t • A) = expDunford A c ρ t := by
  rw [expDunford, circleIntegral_exp_smul_resolvent hρ hA t,
    inv_smul_smul₀ Complex.two_pi_I_ne_zero]

set_option linter.unusedSectionVars false in
/-- The norm of the Dunford integral, from a bound on the resolvent on the circle. -/
theorem norm_expDunford_le (A : X →L[ℂ] X) {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {M : ℝ}
    (hM : ∀ z ∈ sphere c ρ, ‖resolvent A z‖ ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    ‖expDunford A c ρ t‖ ≤ ρ * M * Real.exp ((c.re + ρ) * t) := by
  rw [expDunford]
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (C := M * Real.exp ((c.re + ρ) * t)) hρ.le (fun z hz => ?_)).trans
    (le_of_eq (mul_assoc _ _ _).symm)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hz)
  have hre : z.re ≤ c.re + ρ := by
    have h1 : (z - c).re ≤ ‖z - c‖ := Complex.re_le_norm _
    rw [← dist_eq_norm, mem_sphere.1 hz, Complex.sub_re] at h1
    linarith
  rw [norm_smul, Complex.norm_exp, Complex.re_ofReal_mul, mul_comm M]
  have he : Real.exp (t * z.re) ≤ Real.exp ((c.re + ρ) * t) :=
    Real.exp_le_exp.2 (by nlinarith)
  exact mul_le_mul he (hM z hz) (norm_nonneg _) (Real.exp_pos _).le

/-- **(D2) The circle bound**: `‖exp(tA)‖ ≤ ρ M e^{(Re c + ρ) t}` for `t ≥ 0`, if the spectrum
lies in `ball c ρ` and `‖(z - A)⁻¹‖ ≤ M` on its boundary circle. -/
theorem norm_exp_le_of_spectrum_subset_ball (A : X →L[ℂ] X) {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hA : spectrum ℂ A ⊆ ball c ρ) {M : ℝ} (hM : ∀ z ∈ sphere c ρ, ‖resolvent A z‖ ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp ((t : ℂ) • A)‖ ≤ ρ * M * Real.exp ((c.re + ρ) * t) := by
  rw [exp_eq_expDunford A hρ hA (t : ℂ)]
  exact norm_expDunford_le A hρ hM ht

end NonUniqueEuler.Dunford
