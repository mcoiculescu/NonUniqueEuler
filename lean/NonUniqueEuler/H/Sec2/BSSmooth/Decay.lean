import NonUniqueEuler.H.Sec2.BSSmooth.Differentiate
import NonUniqueEuler.I.Infra.Multipole.CauchySmooth
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Helper for `lem:BS-basic`(d): decay of the velocity and its derivatives

Helper of `P/Sec2/BSSmooth.lean` (`02_prelim.tex:241-250`). For real `h ∈ C_c^∞` with support in
`B_ρ` and `|x| ≥ 2ρ`, `|D^q (K ∗ h)(x)| ≤ (2π)⁻¹ q! ‖h‖₁ (|x|/2)^{-(q+1)}`
(`Multipole.norm_iteratedFDeriv_velocity_le`, with `δ = |x|/2`). Consequences: `∂_v u` is
`O(|x|^{-2})`, hence in `L² ∩ L^∞`; `u = O(|x|^{-1})`, `∂_v∂_w u = O(|x|^{-3})`.

`DecaysLike F n`: `|F(x)| ≤ C |x|^{-n}` for `|x| ≥ R` (some `R > 0`, `C`).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ContDiff ENNReal

namespace NonUniqueEuler.BSSmoothH

/-- `|F(x)| ≤ C |x|^{-n}` for `|x| ≥ R`. -/
def DecaysLike {E : Type*} [NormedAddCommGroup E] (F : ℂ → E) (n : ℕ) : Prop :=
  ∃ R C : ℝ, 0 < R ∧ ∀ x : ℂ, R ≤ ‖x‖ → ‖F x‖ ≤ C * (‖x‖ ^ n)⁻¹

section Generic

variable {E : Type*} [NormedAddCommGroup E]

theorem DecaysLike.mono_norm {E' : Type*} [NormedAddCommGroup E'] {F : ℂ → E} {G : ℂ → E'}
    {n : ℕ} (hF : DecaysLike F n) (h : ∀ x, ‖G x‖ ≤ ‖F x‖) : DecaysLike G n := by
  obtain ⟨R, C, hR, hb⟩ := hF
  exact ⟨R, C, hR, fun x hx => (h x).trans (hb x hx)⟩

theorem DecaysLike.const_mul_norm {E' : Type*} [NormedAddCommGroup E'] {F : ℂ → E} {G : ℂ → E'}
    {n : ℕ} (hF : DecaysLike F n) (c : ℝ) (h : ∀ x, ‖G x‖ ≤ c * ‖F x‖) : DecaysLike G n := by
  obtain ⟨R, C, hR, hb⟩ := hF
  refine ⟨R, |c| * C, hR, fun x hx => ?_⟩
  calc ‖G x‖ ≤ c * ‖F x‖ := h x
    _ ≤ |c| * ‖F x‖ := mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg _)
    _ ≤ |c| * (C * (‖x‖ ^ n)⁻¹) := mul_le_mul_of_nonneg_left (hb x hx) (abs_nonneg c)
    _ = |c| * C * (‖x‖ ^ n)⁻¹ := by ring

theorem DecaysLike.mul {F G : ℂ → ℂ} {m n : ℕ} (hF : DecaysLike F m) (hG : DecaysLike G n) :
    DecaysLike (fun x => F x * G x) (m + n) := by
  obtain ⟨R₁, C₁, hR₁, hb₁⟩ := hF
  obtain ⟨R₂, C₂, hR₂, hb₂⟩ := hG
  refine ⟨max R₁ R₂, C₁ * C₂, lt_max_of_lt_left hR₁, fun x hx => ?_⟩
  have h1 := hb₁ x ((le_max_left _ _).trans hx)
  have h2 := hb₂ x ((le_max_right _ _).trans hx)
  have hC₁ : 0 ≤ C₁ * (‖x‖ ^ m)⁻¹ := (norm_nonneg _).trans h1
  rw [norm_mul, pow_add, mul_inv]
  calc ‖F x‖ * ‖G x‖ ≤ (C₁ * (‖x‖ ^ m)⁻¹) * (C₂ * (‖x‖ ^ n)⁻¹) :=
        mul_le_mul h1 h2 (norm_nonneg _) hC₁
    _ = C₁ * C₂ * ((‖x‖ ^ m)⁻¹ * (‖x‖ ^ n)⁻¹) := by ring

/-- A continuous function decaying like `|x|^{-n}`, `n ≥ 3`, is integrable. -/
theorem DecaysLike.integrable {F : ℂ → E} {n : ℕ} (hF : Continuous F) (hd : DecaysLike F n)
    (hn : 3 ≤ n) : Integrable F volume := by
  obtain ⟨R, C, hR, hb⟩ := hd
  have h1 : IntegrableOn F (closedBall (0 : ℂ) R) volume :=
    hF.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)
  have hmeas : MeasurableSet {x : ℂ | R < ‖x‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have h2 : IntegrableOn F {x : ℂ | R < ‖x‖} volume := by
    have hs : (-(n : ℝ)) < -2 := by
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hi := (Polar.integrableOn_compl_ball_norm_rpow hs hR).const_mul C
    refine hi.mono' hF.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' hmeas).mpr (Eventually.of_forall fun x hx => ?_)
    have hx' : R ≤ ‖x‖ := le_of_lt hx
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
    exact hb x hx'
  have hU : closedBall (0 : ℂ) R ∪ {x : ℂ | R < ‖x‖} = univ := by
    ext x
    simp only [mem_union, mem_closedBall, dist_zero_right, mem_ofPred_eq, mem_univ, iff_true]
    exact le_or_gt _ _
  rw [← integrableOn_univ, ← hU]
  exact h1.union h2

/-- A continuous function decaying like `|x|^{-n}`, `n ≥ 2`, is in `L²`. -/
theorem DecaysLike.memLp_two {F : ℂ → E} {n : ℕ} (hF : Continuous F) (hd : DecaysLike F n)
    (hn : 2 ≤ n) : MemLp F 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable]
  have hcont : Continuous fun x => ‖F x‖ ^ 2 := hF.norm.pow 2
  refine DecaysLike.integrable hcont ?_ (by omega : 3 ≤ n + n)
  obtain ⟨R₁, C₁, hR₁, hb₁⟩ := hd
  refine ⟨R₁, C₁ * C₁, hR₁, fun x hx => ?_⟩
  have h1 := hb₁ x hx
  have hC : 0 ≤ C₁ * (‖x‖ ^ n)⁻¹ := (norm_nonneg _).trans h1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_add, mul_inv]
  show ‖F x‖ ^ 2 ≤ _
  rw [sq]
  calc ‖F x‖ * ‖F x‖ ≤ (C₁ * (‖x‖ ^ n)⁻¹) * (C₁ * (‖x‖ ^ n)⁻¹) :=
        mul_le_mul h1 h1 (norm_nonneg _) hC
    _ = C₁ * C₁ * ((‖x‖ ^ n)⁻¹ * (‖x‖ ^ n)⁻¹) := by ring

/-- A continuous function with a decay bound is bounded, hence in `L^∞`. -/
theorem DecaysLike.memLp_top {F : ℂ → E} {n : ℕ} (hF : Continuous F) (hd : DecaysLike F n) :
    MemLp F ⊤ volume := by
  obtain ⟨R, C, hR, hb⟩ := hd
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hF.continuousOn
  refine memLp_top_of_bound hF.aestronglyMeasurable (max M (|C| * (R ^ n)⁻¹))
    (Eventually.of_forall fun x => ?_)
  rcases le_or_gt ‖x‖ R with hx | hx
  · exact (hM x (by simpa using hx)).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    refine (hb x hx.le).trans ?_
    have hxn : (‖x‖ ^ n)⁻¹ ≤ (R ^ n)⁻¹ :=
      inv_anti₀ (pow_pos hR n) (pow_le_pow_left₀ hR.le hx.le n)
    calc C * (‖x‖ ^ n)⁻¹ ≤ |C| * (‖x‖ ^ n)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (R ^ n)⁻¹ := mul_le_mul_of_nonneg_left hxn (abs_nonneg C)

end Generic

/-- A compactly supported function vanishes outside some ball `B_ρ`, `ρ > 0`. -/
theorem exists_radius_of_hasCompactSupport {h : ℂ → ℝ} (hc : HasCompactSupport h) :
    ∃ ρ > 0, ∀ y : ℂ, ρ ≤ ‖y‖ → h y = 0 := by
  obtain ⟨ρ, hρ, hsub⟩ := hc.isCompact.isBounded.subset_ball_lt 0 0
  refine ⟨ρ, hρ, fun y hy => image_eq_zero_of_notMem_tsupport fun hy' => ?_⟩
  have := hsub hy'
  rw [mem_ball_zero_iff] at this
  linarith

/-- `|D^q (K ∗ h)(x)| = O(|x|^{-(q+1)})`. -/
theorem decaysLike_iteratedFDeriv_velocity {h : ℂ → ℝ} (hh : Continuous h)
    (hc : HasCompactSupport h) (q : ℕ) :
    DecaysLike (fun x => iteratedFDeriv ℝ q (velocity h) x) (q + 1) := by
  obtain ⟨ρ, hρ, hvan⟩ := exists_radius_of_hasCompactSupport hc
  have hint : Integrable h volume := hh.integrable_of_hasCompactSupport hc
  refine ⟨2 * ρ, (2 * Real.pi)⁻¹ * q.factorial * (∫ w, |h w|) * 2 ^ (q + 1), by positivity,
    fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := by linarith
  have hδ : 0 < ‖x‖ / 2 := by linarith
  have hsupp : ∀ᵐ w, w ∈ ball x (‖x‖ / 2) → h w = 0 := by
    refine Eventually.of_forall fun w hw => hvan w ?_
    rw [mem_ball, dist_comm, dist_eq_norm] at hw
    have := norm_sub_norm_le x w
    have : ‖x‖ - ‖w‖ ≤ ‖x - w‖ := norm_sub_norm_le x w
    linarith
  have := Multipole.norm_iteratedFDeriv_velocity_le hint hδ hsupp q
  refine this.trans (le_of_eq ?_)
  rw [div_pow, inv_div]
  field_simp

/-- `u = K ∗ h = O(|x|^{-1})`. -/
theorem decaysLike_velocity {h : ℂ → ℝ} (hh : Continuous h) (hc : HasCompactSupport h) :
    DecaysLike (velocity h) 1 :=
  (decaysLike_iteratedFDeriv_velocity hh hc 0).mono_norm fun x => by
    rw [norm_iteratedFDeriv_zero]

/-- `∂_v u = O(|x|^{-2})`. -/
theorem decaysLike_fderiv_velocity {h : ℂ → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (v : ℂ) : DecaysLike (fun x => fderiv ℝ (velocity h) x v) 2 :=
  (decaysLike_iteratedFDeriv_velocity hh hc 1).const_mul_norm ‖v‖ fun x => by
    rw [norm_iteratedFDeriv_one, mul_comm]
    exact (fderiv ℝ (velocity h) x).le_opNorm v

/-- `∂_v∂_w u = O(|x|^{-3})`. -/
theorem decaysLike_fderiv_fderiv_velocity {h : ℂ → ℝ} (hh : Continuous h)
    (hc : HasCompactSupport h) (v w : ℂ) :
    DecaysLike (fun x => fderiv ℝ (fderiv ℝ (velocity h)) x v w) 3 :=
  (decaysLike_iteratedFDeriv_velocity hh hc 2).const_mul_norm (‖v‖ * ‖w‖) fun x => by
    have e := iteratedFDeriv_two_apply (𝕜 := ℝ) (velocity h) x ![v, w]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    rw [← e]
    refine ((iteratedFDeriv ℝ 2 (velocity h) x).le_opNorm _).trans (le_of_eq ?_)
    simp [Fin.prod_univ_two]
    ring

/-- `lem:BS-basic`(d): `∂_v (K ∗ h) ∈ L² ∩ L^∞`. -/
theorem memLp_fderiv_velocity {h : ℂ → ℝ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (v : ℂ) :
    MemLp (fun x => fderiv ℝ (velocity h) x v) 2 volume ∧
      MemLp (fun x => fderiv ℝ (velocity h) x v) ⊤ volume := by
  have hcont : Continuous fun x => fderiv ℝ (velocity h) x v :=
    ((contDiff_velocity hh hc).continuous_fderiv (by simp)).clm_apply continuous_const
  exact ⟨(decaysLike_fderiv_velocity hh.continuous hc v).memLp_two hcont le_rfl,
    (decaysLike_fderiv_velocity hh.continuous hc v).memLp_top hcont⟩

end NonUniqueEuler.BSSmoothH
