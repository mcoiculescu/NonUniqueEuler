import NonUniqueEuler.Defs.Sec6.All
import NonUniqueEuler.I.Infra.CkNorm.Continuity
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Helpers for `P/Sec6/FieldContinuity`: generic lemmas

Proved helper lemmas (no manuscript content of their own) for the proof of
`I/Sec6/FieldContinuity.lean` (`06_datum.tex:294-321`):

* `ckPathOn_of_ext`, `continuousOn_normCk_of_ext`: if a time-dependent field `h` agrees, at every
  time `τ ≥ 0`, with a field `H` that is jointly `C^∞` in `(τ, y)` on `ℝ × (ℂ ∖ {0})`, then
  `τ ↦ h τ` is continuous into `C^M(N')` on every `J ⊆ [0, ∞)`, and so is its `C^M(N')` norm
  (from `I/Infra/CkNorm/Continuity.lean`, with `W = {p | p.2 ≠ 0} ⊇ J × N'`);
* `contDiffOn_monopole`: `(τ, y) ↦ G y^⊥/|y|²` is `C^∞` on `ℝ × (ℂ ∖ {0})`;
* `maj_continuousOn`: the Duhamel majorant of a function continuous on `[0, B]` is continuous on
  `[0, B]` (`06_datum.tex:319-321`);
* `continuous_integral_of_slab`: `t ↦ ∫ F(t, x) dx` is continuous if `F` is jointly continuous and
  its supports are bounded locally uniformly in time (dominated convergence, here through
  `continuous_parametric_integral_of_continuous` on a ball).
-/

noncomputable section

open scoped ContDiff Topology
open MeasureTheory Set Metric Filter

namespace NonUniqueEuler

namespace Datum

namespace FieldContinuityAux

open RingData

/-- `0 ∉ N'`. -/
theorem zero_not_mem_annN' : (0 : ℂ) ∉ annN' := by
  intro h
  have ha : 0 < a := Real.exp_pos _
  have h1 : a / 4 ≤ ‖(0 : ℂ)‖ := h.1
  rw [norm_zero] at h1
  linarith

/-- `J × N' ⊆ ℝ × (ℂ ∖ {0})`. -/
theorem prod_annN'_subset (J : Set ℝ) : J ×ˢ annN' ⊆ {p : ℝ × ℂ | p.2 ≠ 0} := by
  intro p hp
  have h2 : p.2 ∈ annN' := hp.2
  intro h0
  rw [h0] at h2
  exact zero_not_mem_annN' h2

theorem isOpen_snd_ne : IsOpen {p : ℝ × ℂ | p.2 ≠ 0} :=
  isOpen_ne.preimage continuous_snd

/-- A field that agrees for `τ ≥ 0` with a field jointly `C^∞` on `ℝ × (ℂ ∖ {0})` is continuous
into `C^M(N')` on every set of times `J ⊆ [0, ∞)`. -/
theorem ckPathOn_of_ext {M : ℕ} {J : Set ℝ} (hJ : J ⊆ Ici 0) {h : ℝ → ℂ → ℂ}
    (hext : ∃ H : ℝ → ℂ → ℂ, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => H p.1 p.2) {p | p.2 ≠ 0} ∧
      ∀ τ, 0 ≤ τ → h τ = H τ) :
    OneRing.CkPathOn M annN' J h := by
  obtain ⟨H, hH, heq⟩ := hext
  have hHM : ContDiffOn ℝ M (fun p : ℝ × ℂ => H p.1 p.2) {p | p.2 ≠ 0} :=
    hH.of_le (by exact_mod_cast le_top)
  have heqJ : ∀ τ ∈ J, h τ = H τ := fun τ hτ => heq τ (hJ hτ)
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [heqJ t ht]
    exact memCk_slice_of_contDiffOn isCompact_annN' isOpen_snd_ne (prod_annN'_subset J) hHM ht
  · have h1 := tendsto_normCk_sub_of_contDiffOn isCompact_annN' isOpen_snd_ne
      (prod_annN'_subset J) hHM ht
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t' ht'
    rw [heqJ t' ht', heqJ t ht]

/-- The `C^M(N')` norm of such a field is continuous on every `J ⊆ [0, ∞)`. -/
theorem continuousOn_normCk_of_ext {M : ℕ} {J : Set ℝ} (hJ : J ⊆ Ici 0) {h : ℝ → ℂ → ℂ}
    (hext : ∃ H : ℝ → ℂ → ℂ, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => H p.1 p.2) {p | p.2 ≠ 0} ∧
      ∀ τ, 0 ≤ τ → h τ = H τ) :
    ContinuousOn (fun τ => normCk M annN' (h τ)) J := by
  obtain ⟨H, hH, heq⟩ := hext
  have hHM : ContDiffOn ℝ M (fun p : ℝ × ℂ => H p.1 p.2) {p | p.2 ≠ 0} :=
    hH.of_le (by exact_mod_cast le_top)
  refine (continuousOn_normCk_of_contDiffOn isCompact_annN' isOpen_snd_ne
    (prod_annN'_subset J) hHM).congr fun τ hτ => ?_
  simp only [heq τ (hJ hτ)]

/-- The sum of two fields with smooth extensions has a smooth extension. -/
theorem ext_add {h₁ h₂ : ℝ → ℂ → ℂ}
    (h1 : ∃ H : ℝ → ℂ → ℂ, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => H p.1 p.2) {p | p.2 ≠ 0} ∧
      ∀ τ, 0 ≤ τ → h₁ τ = H τ)
    (h2 : ∃ H : ℝ → ℂ → ℂ, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => H p.1 p.2) {p | p.2 ≠ 0} ∧
      ∀ τ, 0 ≤ τ → h₂ τ = H τ) :
    ∃ H : ℝ → ℂ → ℂ, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => H p.1 p.2) {p | p.2 ≠ 0} ∧
      ∀ τ, 0 ≤ τ → (fun y => h₁ τ y + h₂ τ y) = H τ := by
  obtain ⟨H₁, hH₁, he₁⟩ := h1
  obtain ⟨H₂, hH₂, he₂⟩ := h2
  refine ⟨fun τ y => H₁ τ y + H₂ τ y, hH₁.add hH₂, fun τ hτ => ?_⟩
  rw [he₁ τ hτ, he₂ τ hτ]

/-- The monopole term `(τ, y) ↦ G y^⊥/|y|²` (`y^⊥ = i y`) is `C^∞` on `ℝ × (ℂ ∖ {0})`. -/
theorem contDiffOn_monopole (G : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => (G : ℂ) * (Complex.I * p.2) / ((‖p.2‖ ^ 2 : ℝ) : ℂ))
      {p | p.2 ≠ 0} := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℂ => (G : ℂ) * (Complex.I * p.2)) :=
    contDiff_const.mul (contDiff_const.mul contDiff_snd)
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ((‖p.2‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_norm_sq ℝ).comp contDiff_snd)
  have h3 : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => (((‖p.2‖ ^ 2 : ℝ) : ℂ))⁻¹) {p | p.2 ≠ 0} :=
    h2.contDiffOn.fun_inv fun p hp => by
      have hp' : p.2 ≠ 0 := hp
      have : ‖p.2‖ ≠ 0 := norm_ne_zero_iff.2 hp'
      exact_mod_cast pow_ne_zero 2 this
  have h4 := h1.contDiffOn.mul h3
  refine h4.congr fun p _ => ?_
  simp only [div_eq_mul_inv]

/-- **Continuity of a Duhamel majorant** (`06_datum.tex:202-209`, `:319-321`): if `η` is
continuous on `[0, B]`, then `maj σ η` is continuous on `[0, B]`. -/
theorem maj_continuousOn {σ : ℝ} {η : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hη : ContinuousOn η (Icc 0 B)) : ContinuousOn (OneRing.maj σ η) (Icc 0 B) := by
  have hc : Continuous fun v : ℝ => Real.exp (-(σ * v)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id).neg
  have hint : IntegrableOn (fun v => Real.exp (-(σ * v)) * η v) (uIcc 0 B) := by
    rw [uIcc_of_le hB]
    exact (hc.continuousOn.mul hη).integrableOn_Icc
  have hprim := intervalIntegral.continuousOn_primitive_interval hint
  rw [uIcc_of_le hB] at hprim
  have heq : ∀ τ, OneRing.maj σ η τ =
      Real.exp (σ * τ) * ∫ v in (0 : ℝ)..τ, Real.exp (-(σ * v)) * η v := by
    intro τ
    simp only [OneRing.maj]
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext v
    rw [show σ * (τ - v) = σ * τ + -(σ * v) by ring, Real.exp_add, mul_assoc]
  have hcont : ContinuousOn
      (fun τ => Real.exp (σ * τ) * ∫ v in (0 : ℝ)..τ, Real.exp (-(σ * v)) * η v) (Icc 0 B) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hprim
  exact hcont.congr fun τ _ => heq τ

/-- `t ↦ ∫ F(t, x) dx` is continuous if `F` is jointly continuous and, for every `T`, the
functions `F(t, ·)`, `|t| ≤ T`, vanish outside a common ball. -/
theorem continuous_integral_of_slab {F : ℝ → ℂ → ℂ} (hF : Continuous (Function.uncurry F))
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → F t x = 0) :
    Continuous fun t => ∫ x, F t x := by
  rw [continuous_iff_continuousAt]
  intro t₀
  obtain ⟨ρ, hρ⟩ := hsupp (|t₀| + 1)
  have hc : Continuous fun t => ∫ x in closedBall (0 : ℂ) ρ, F t x :=
    continuous_parametric_integral_of_continuous hF (isCompact_closedBall 0 ρ)
  have hmem : Ioo (-(|t₀| + 1)) (|t₀| + 1) ∈ 𝓝 t₀ :=
    Ioo_mem_nhds (by linarith [neg_abs_le t₀]) (by linarith [le_abs_self t₀])
  have hev : (fun t => ∫ x in closedBall (0 : ℂ) ρ, F t x) =ᶠ[𝓝 t₀] fun t => ∫ x, F t x := by
    filter_upwards [hmem] with t ht
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply hρ t (Ioo_subset_Icc_self ht) x
    simpa [mem_closedBall, dist_zero_right, not_le] using hx
  exact hc.continuousAt.congr hev

end FieldContinuityAux

end Datum

end NonUniqueEuler
