import NonUniqueEuler.Defs.Sec6.All
import NonUniqueEuler.Defs.Sec7.Transfer
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Helpers for `lem:regions-basic`: generic facts

Helper of `P/Sec6/RegionsBasic.lean` (`06_datum.tex:244-292`). Nothing here depends on the
approximation `P`.

* `RegionsBasicAux.eq_zero_of_rot_eq`: `O_{2π/3}` fixes only `0` (`06_datum.tex:262-263`);
* `RegionsBasicAux.IsGood θ G` (`G ∈ C_c^∞`, `G ≥ 0`, `G ∘ O_θ = G` pointwise) and its closure
  under dilations `c G(·/r)`, finite sums and composition with a smooth homeomorphism commuting
  with `O_θ` (`06_datum.tex:275-279`);
* `RegionsBasicAux.image_rot_tsupport`: the support of an `O_θ`-invariant function is
  `O_θ`-invariant;
* `RegionsBasicAux.tsupport_scale_subset`, `integral_scale`, `integral_scale_mul`: supports and
  integrals of `c G(·/r)` and `c G(r ·)`;
* `RegionsBasicAux.eLpNorm_one_of_nonneg`, `eLpNorm_one_le_CL1`: `‖g‖_{L¹} = ∫ g` for `g ≥ 0`,
  and Cauchy–Schwarz on `N` (`06_datum.tex:291-292`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.Datum.Approx.RegionsBasicAux

open RingData

/-! ### Rotations -/

theorem rot_zero (θ : ℝ) : rot θ 0 = 0 := by
  simp [rot]

theorem rot_ofReal_mul (θ r : ℝ) (y : ℂ) : rot θ ((r : ℂ) * y) = (r : ℂ) * rot θ y := by
  simp only [rot]
  ring

theorem rot_div_ofReal (θ r : ℝ) (y : ℂ) : rot θ y / (r : ℂ) = rot θ (y / (r : ℂ)) := by
  simp only [rot, mul_div_assoc]

theorem norm_rot (θ : ℝ) (y : ℂ) : ‖rot θ y‖ = ‖y‖ := by
  simp only [rot, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `e^{2πi/3} ≠ 1`. -/
theorem exp_two_pi_three_ne_one :
    Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) ≠ 1 := by
  intro h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2 : ((2 * Real.pi / 3 : ℝ) : ℂ) = ((n * (2 * Real.pi) : ℝ) : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    rw [hn]
    push_cast
    ring
  have h3 : (2 * Real.pi / 3 : ℝ) = n * (2 * Real.pi) := Complex.ofReal_injective h2
  have h5 : (n : ℝ) = 1 / 3 := by
    have h6 : (n : ℝ) * (2 * Real.pi) = (1 / 3) * (2 * Real.pi) := by rw [← h3]; ring
    exact mul_right_cancel₀ (by positivity) h6
  have h7 : ((3 * n : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by
    push_cast
    rw [h5]
    norm_num
  have h8 : 3 * n = 1 := Int.cast_injective h7
  omega

/-- `O_{2π/3}` fixes only `0` (`06_datum.tex:262-263`). -/
theorem eq_zero_of_rot_eq {z : ℂ} (h : rot (2 * Real.pi / 3) z = z) : z = 0 := by
  have h' : (Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) - 1) * z = 0 := by
    have : rot (2 * Real.pi / 3) z = Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) * z :=
      rfl
    rw [sub_mul, one_mul, ← this, h, sub_self]
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact absurd (sub_eq_zero.1 h1) exp_two_pi_three_ne_one
  · exact h1

/-- The rotation `O_θ` as a homeomorphism. -/
theorem exists_rot_homeomorph (θ : ℝ) : ∃ e : ℂ ≃ₜ ℂ, ⇑e = rot θ :=
  ⟨Homeomorph.mulLeft₀ _ (Complex.exp_ne_zero ((θ : ℂ) * Complex.I)), by
    rw [Homeomorph.coe_mulLeft₀]
    rfl⟩

/-- The support of an `O_θ`-invariant function is `O_θ`-invariant. -/
theorem image_rot_tsupport {θ : ℝ} {g : ℂ → ℝ} (hg : ∀ y, g (rot θ y) = g y) :
    rot θ '' tsupport g = tsupport g := by
  obtain ⟨e, he⟩ := exists_rot_homeomorph θ
  have h1 : g ∘ ⇑e = g := by
    funext y
    simp only [Function.comp, he, hg]
  have h2 : tsupport g = ⇑e ⁻¹' tsupport g := by
    conv_lhs => rw [← h1]
    exact tsupport_comp_eq_preimage g e
  rw [← he]
  conv_lhs => rw [h2]
  exact image_preimage_eq _ e.surjective

/-- A rotation-invariant set mapped by an injective rotation-equivariant map. -/
theorem image_rot_image {θ : ℝ} {F : ℂ → ℂ} (hF : ∀ y, F (rot θ y) = rot θ (F y)) {S : Set ℂ}
    (hS : rot θ '' S = S) : rot θ '' (F '' S) = F '' S := by
  rw [image_image]
  conv_rhs => rw [← hS, image_image]
  simp only [hF]

/-! ### Good profiles -/

/-- `G ∈ C_c^∞(ℝ²)`, `G ≥ 0` and `G ∘ O_θ = G` pointwise. -/
def IsGood (θ : ℝ) (G : ℂ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧ HasCompactSupport G ∧ (∀ y, 0 ≤ G y) ∧
    ∀ y, G (rot θ y) = G y

theorem isGood_scale {θ : ℝ} {G : ℂ → ℝ} (hG : IsGood θ G) {c : ℝ} (hc : 0 ≤ c)
    {r : ℝ} (hr : r ≠ 0) : IsGood θ (fun x => c * G (x / (r : ℂ))) := by
  obtain ⟨h1, h2, h3, h4⟩ := hG
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  refine ⟨contDiff_const.mul (h1.comp (contDiff_id.div_const _)), ?_,
    fun x => mul_nonneg hc (h3 _), fun x => ?_⟩
  · have e : (fun x : ℂ => c * G (x / (r : ℂ))) =
        (fun _ => c) * (G ∘ (Homeomorph.mulRight₀ ((r : ℂ)⁻¹) (inv_ne_zero hr'))) := by
      funext x
      simp [div_eq_mul_inv]
    rw [e]
    exact (h2.comp_homeomorph _).mul_left
  · show c * G (rot θ x / (r : ℂ)) = c * G (x / (r : ℂ))
    rw [rot_div_ofReal, h4]

theorem isGood_zero (θ : ℝ) : IsGood θ (fun _ => 0) :=
  ⟨contDiff_const, HasCompactSupport.zero, fun _ => le_rfl, fun _ => rfl⟩

theorem isGood_add {θ : ℝ} {G H : ℂ → ℝ} (hG : IsGood θ G) (hH : IsGood θ H) :
    IsGood θ (fun x => G x + H x) :=
  ⟨hG.1.add hH.1, hG.2.1.add hH.2.1, fun y => add_nonneg (hG.2.2.1 y) (hH.2.2.1 y),
    fun y => by simp only [hG.2.2.2 y, hH.2.2.2 y]⟩

theorem isGood_sum {θ : ℝ} {ι : Type*} (s : Finset ι) {F : ι → ℂ → ℝ}
    (hF : ∀ i ∈ s, IsGood θ (F i)) : IsGood θ (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isGood_zero θ
  | insert i s hi ih =>
    have e : (fun x => ∑ j ∈ insert i s, F j x) = fun x => F i x + ∑ j ∈ s, F j x := by
      funext x
      rw [Finset.sum_insert hi]
    rw [e]
    exact isGood_add (hF i (Finset.mem_insert_self i s))
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

/-- Composition with a smooth homeomorphism commuting with `O_θ`. -/
theorem isGood_comp {θ : ℝ} {G : ℂ → ℝ} (hG : IsGood θ G) (e : ℂ ≃ₜ ℂ)
    (he : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ⇑e) (hrot : ∀ x, e (rot θ x) = rot θ (e x)) :
    IsGood θ (fun x => G (e x)) :=
  ⟨hG.1.comp he, hG.2.1.comp_homeomorph e, fun x => hG.2.2.1 _,
    fun x => by simp only [hrot, hG.2.2.2]⟩

/-! ### Supports and integrals of dilations -/

theorem tsupport_scale_subset (c : ℝ) (G : ℂ → ℝ) (r : ℝ) :
    tsupport (fun x => c * G (x / (r : ℂ))) ⊆ (fun x => x / (r : ℂ)) ⁻¹' tsupport G :=
  (tsupport_mul_subset_right (f := fun _ => c) (g := fun x => G (x / (r : ℂ)))).trans
    (tsupport_comp_subset_preimage G (continuous_id.div_const _))

theorem tsupport_scale_mul_subset (c : ℝ) (G : ℂ → ℝ) (r : ℝ) :
    tsupport (fun x => c * G ((r : ℂ) * x)) ⊆ (fun x => (r : ℂ) * x) ⁻¹' tsupport G :=
  (tsupport_mul_subset_right (f := fun _ => c) (g := fun x => G ((r : ℂ) * x))).trans
    (tsupport_comp_subset_preimage G (continuous_const.mul continuous_id))

theorem hasCompactSupport_scale_mul {G : ℂ → ℝ} (hG : HasCompactSupport G) (c : ℝ) {r : ℝ}
    (hr : r ≠ 0) : HasCompactSupport (fun x => c * G ((r : ℂ) * x)) := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have e : (fun x : ℂ => c * G ((r : ℂ) * x)) =
      (fun _ => c) * (G ∘ (Homeomorph.mulLeft₀ (r : ℂ) hr')) := by
    funext x
    simp
  rw [e]
  exact (hG.comp_homeomorph _).mul_left

/-- `∫ c G(x/r) dx = c r² ∫ G` (`r > 0`). -/
theorem integral_scale (c : ℝ) (G : ℂ → ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ x, c * G (x / (r : ℂ)) = c * r ^ 2 * ∫ x, G x := by
  have h1 : (fun x : ℂ => G (x / (r : ℂ))) = fun x => G ((r⁻¹ : ℝ) • x) := by
    funext x
    congr 1
    rw [Complex.real_smul, div_eq_inv_mul]
    push_cast
    rfl
  rw [integral_const_mul, h1, Measure.integral_comp_smul, Complex.finrank_real_complex,
    smul_eq_mul, inv_pow, inv_inv, abs_of_pos (by positivity)]
  ring

/-- `∫ c G(r x) dx = c r⁻² ∫ G` (`r > 0`). -/
theorem integral_scale_mul (c : ℝ) (G : ℂ → ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ x, c * G ((r : ℂ) * x) = c * (r ^ 2)⁻¹ * ∫ x, G x := by
  have h1 : (fun x : ℂ => G ((r : ℂ) * x)) = fun x => G (r • x) := by
    funext x
    rw [Complex.real_smul]
  rw [integral_const_mul, h1, Measure.integral_comp_smul, Complex.finrank_real_complex,
    smul_eq_mul, abs_of_pos (by positivity)]
  ring

/-! ### `L¹` norms -/

/-- `‖g‖_{L¹} = ∫ g` for an integrable `g ≥ 0`. -/
theorem eLpNorm_one_of_nonneg {g : ℂ → ℝ} (hg : Integrable g) (h0 : ∀ y, 0 ≤ g y) :
    eLpNorm g 1 volume = ENNReal.ofReal (∫ y, g y) := by
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hg]
  congr 2
  funext y
  exact Real.norm_of_nonneg (h0 y)

/-- `N` has finite measure. -/
theorem volume_annN_lt_top : volume annN < ⊤ := by
  have h : annN ⊆ closedBall (0 : ℂ) 2 := fun y hy => by
    rw [mem_closedBall, dist_zero_right]
    exact hy.2
  exact (measure_mono h).trans_lt measure_closedBall_lt_top

/-- Cauchy–Schwarz on `N`: `‖g‖_{L¹} ≤ |N|^{1/2} ‖g‖_{L²}` for `g` vanishing outside `N`
(`06_datum.tex:291-292`). -/
theorem eLpNorm_one_le_CL1 {g : ℂ → ℝ} (hg : AEStronglyMeasurable g volume)
    (hs : ∀ y, y ∉ annN → g y = 0) :
    eLpNorm g 1 volume ≤ ENNReal.ofReal Rings.CL1 * eLpNorm g 2 volume := by
  have hsupp : Function.support g ⊆ annN := fun y hy => by
    by_contra h
    exact hy (hs y h)
  rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict annN) (p := 1)
    (q := 2) (by norm_num) hg.restrict
  rw [Measure.restrict_apply_univ] at h1
  have e1 : (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) = 1 / 2 := by norm_num
  rw [e1] at h1
  have hfin := volume_annN_lt_top
  have e2 : volume annN ^ (1 / 2 : ℝ) = ENNReal.ofReal Rings.CL1 := by
    rw [Rings.CL1, Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
      (by norm_num), ENNReal.ofReal_toReal hfin.ne]
  rw [e2] at h1
  calc eLpNorm g 1 (volume.restrict annN)
      ≤ eLpNorm g 2 (volume.restrict annN) * ENNReal.ofReal Rings.CL1 := h1
    _ ≤ eLpNorm g 2 volume * ENNReal.ofReal Rings.CL1 := by
        gcongr
        exact Measure.restrict_le_self
    _ = ENNReal.ofReal Rings.CL1 * eLpNorm g 2 volume := mul_comm _ _

end NonUniqueEuler.Datum.Approx.RegionsBasicAux
