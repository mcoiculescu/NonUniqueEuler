import NonUniqueEuler.H.Infra.Sobolev.DiffQuot.Basic
import NonUniqueEuler.I.Infra.ConvMinkowski.Minkowski
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-!
# Helper for `P/Infra/Sobolev/DiffQuot`: the difference-quotient identity and bound

Setting: `f, g₁, g₂ : ℂ → ℂ` integrable on the plane (`g₁, g₂` strongly measurable), with
`g₁ = ∂₁ f`, `g₂ = ∂₂ f` weakly on `B_r`, and `R + |h| ≤ r`. Put
`G = h.re g₁ + h.im g₂` (the weak derivative `∂_h f`) and `w(x) = ∫_0^1 G(x - s h) ds`.

* `DiffQuotAux.integral_smul_sub_eq_zero`: for every real test function `ψ` supported in `B_R`,
  `∫ ψ (f - f(· - h) - w) = 0`. Proof: `∫ ψ (f - f(·-h)) = -∫ f (ψ(·+h) - ψ)`
  (translation), `ψ(y+h) - ψ(y) = ∫_0^1 Dψ(y + s h) h ds` (FTC), Fubini, the weak derivative
  tested against `y ↦ ψ(y + s h)` (supported in `B_{R + s|h|} ⊆ B_r`), translation back and
  Fubini again.
* `DiffQuotAux.ae_eq_integral`: hence `f(x) - f(x - h) = w(x)` for a.e. `x ∈ B_R` (fundamental
  lemma of the calculus of variations,
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`).
* `DiffQuotAux.eLpNorm_integral_comp_sub_le`: `‖w‖_{L²(B_R)} ≤ ‖G‖_{L²(B_r)}` (Minkowski's
  integral inequality `Conv.eLpNorm_integral_le` and translation invariance).
* `DiffQuotAux.eLpNorm_sub_comp_sub_le_of_integrable`: `‖f - f(·-h)‖_{L²(B_R)} ≤ ‖G‖_{L²(B_r)}`.

This is the manuscript's `w(x) - w(x - εz) = ε ∫_0^1 ∇w(x - sεz) z ds`
(`03_compactness.tex:388-397`), proved directly for weak derivatives (in the weak form, by
duality against test functions) instead of by mollification.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob.DiffQuotAux

/-- The weak derivative tested against a translate: for `ψ` a real test function supported in
`B_R` and `R + |c| ≤ r`, `∫ f Dψ(· + c)h = -∫ (h.re g₁ + h.im g₂) ψ(· + c)`. -/
theorem integral_mul_fderiv_translate {r R : ℝ} {f g₁ g₂ : ℂ → ℂ}
    (hf : Integrable f) (hg₁ : Integrable g₁) (hg₂ : Integrable g₂)
    (h₁ : HasWeakDerivOn (ball (0 : ℂ) r) [1] f g₁)
    (h₂ : HasWeakDerivOn (ball (0 : ℂ) r) [Complex.I] f g₂)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψR : tsupport ψ ⊆ ball 0 R) {c : ℂ} (hc : R + ‖c‖ ≤ r) (h : ℂ) :
    ∫ y, f y * (fderiv ℝ ψ (y + c) h : ℂ) =
      -∫ y, ((h.re : ℂ) * g₁ y + (h.im : ℂ) * g₂ y) * (ψ (y + c) : ℂ) := by
  have hT := isTestFn_translate hψ hψc hψR hc
  have hd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have e1 := h₁ _ hT
  have e2 := h₂ _ hT
  simp only [iterDirDeriv_cons, iterDirDeriv_nil, dirDeriv, List.length_cons, List.length_nil,
    zero_add, pow_one, fderiv_translate_apply hd] at e1 e2
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hcf : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv hn
  obtain ⟨C, hC⟩ := hcf.bounded_above_of_compact_support (hψc.fderiv (𝕜 := ℝ))
  obtain ⟨C0, hC0⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hcont : ∀ v : ℂ, Continuous (fun y => (fderiv ℝ ψ (y + c) v : ℂ)) := fun v =>
    Complex.continuous_ofReal.comp
      ((hcf.comp (continuous_id.add continuous_const)).clm_apply continuous_const)
  have hbd : ∀ v : ℂ, ∀ y, ‖(fderiv ℝ ψ (y + c) v : ℂ)‖ ≤ C * ‖v‖ := fun v y => by
    rw [Complex.norm_real]
    exact ((fderiv ℝ ψ (y + c)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg v))
  have i1 : ∀ v, Integrable (fun y => f y * (fderiv ℝ ψ (y + c) v : ℂ)) := fun v =>
    hf.mul_bdd (hcont v).aestronglyMeasurable (Filter.Eventually.of_forall (hbd v))
  have hcont0 : Continuous (fun y => (ψ (y + c) : ℂ)) :=
    Complex.continuous_ofReal.comp (hψ.continuous.comp (continuous_id.add continuous_const))
  have hbd0 : ∀ y, ‖(ψ (y + c) : ℂ)‖ ≤ C0 := fun y => by
    rw [Complex.norm_real]
    exact hC0 _
  have j1 : Integrable (fun y => g₁ y * (ψ (y + c) : ℂ)) :=
    hg₁.mul_bdd hcont0.aestronglyMeasurable (Filter.Eventually.of_forall hbd0)
  have j2 : Integrable (fun y => g₂ y * (ψ (y + c) : ℂ)) :=
    hg₂.mul_bdd hcont0.aestronglyMeasurable (Filter.Eventually.of_forall hbd0)
  have key : ∀ y, f y * (fderiv ℝ ψ (y + c) h : ℂ) =
      (h.re : ℂ) * (f y * (fderiv ℝ ψ (y + c) 1 : ℂ)) +
        (h.im : ℂ) * (f y * (fderiv ℝ ψ (y + c) Complex.I : ℂ)) := by
    intro y
    rw [clm_apply_eq]
    push_cast
    ring
  have key2 : ∀ y, ((h.re : ℂ) * g₁ y + (h.im : ℂ) * g₂ y) * (ψ (y + c) : ℂ) =
      (h.re : ℂ) * (g₁ y * (ψ (y + c) : ℂ)) + (h.im : ℂ) * (g₂ y * (ψ (y + c) : ℂ)) := by
    intro y
    ring
  simp_rw [key, key2]
  rw [integral_add ((i1 1).const_mul _) ((i1 Complex.I).const_mul _),
    integral_add (j1.const_mul _) (j2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, e1, e2]
  ring

/-- First Fubini step: `∫ f (ψ(· + h) - ψ) = ∫_0^1 ∫ f Dψ(· + s h)h`. -/
theorem integral_mul_sub_translate {f : ℂ → ℂ} (hf : Integrable f)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (h : ℂ) :
    ∫ y, f y * ((ψ (y + h) - ψ y : ℝ) : ℂ) =
      ∫ s in Ioc (0 : ℝ) 1, ∫ y, f y * (fderiv ℝ ψ (y + s • h) h : ℂ) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hcf : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv hn
  obtain ⟨C, hC⟩ := hcf.bounded_above_of_compact_support (hψc.fderiv (𝕜 := ℝ))
  have hcont : Continuous (fun p : ℂ × ℝ => (fderiv ℝ ψ (p.1 + p.2 • h) h : ℂ)) :=
    Complex.continuous_ofReal.comp ((hcf.comp
      (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const)
  have hF : Integrable (Function.uncurry fun (y : ℂ) (s : ℝ) =>
      f y * (fderiv ℝ ψ (y + s • h) h : ℂ)) (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    have h1 : Integrable (fun p : ℂ × ℝ => f p.1)
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := hf.comp_fst _
    refine h1.mul_bdd (c := C * ‖h‖) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Complex.norm_real]
    exact ((fderiv ℝ ψ _).le_opNorm h).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg h))
  rw [← integral_integral_swap hF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [sub_eq_integral_fderiv (hψ.of_le (by simp)) y h, ← integral_complex_ofReal, ← integral_const_mul]

/-- Integrability of `(x, s) ↦ G(x - s h)` on `ℂ × (0, 1]`. -/
theorem integrable_comp_sub_smul {G : ℂ → ℂ} (hGm : StronglyMeasurable G) (hG : Integrable G)
    (h : ℂ) :
    Integrable (fun p : ℂ × ℝ => G (p.1 - p.2 • h))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  have hm : StronglyMeasurable (fun p : ℂ × ℝ => G (p.1 - p.2 • h)) :=
    hGm.comp_measurable ((continuous_fst.sub (continuous_snd.smul continuous_const)).measurable)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod_symm _ hm.measurable.enorm.aemeasurable]
  have : ∀ s : ℝ, ∫⁻ x, ‖G (x - s • h)‖ₑ = ∫⁻ x, ‖G x‖ₑ := fun s =>
    lintegral_sub_right_eq_self (fun x => ‖G x‖ₑ) (s • h)
  simp only [this, lintegral_const]
  exact ENNReal.mul_lt_top hG.2 (by simp)

/-- Second Fubini step: `∫ ψ w = ∫_0^1 ∫ ψ G(· - s h)`. -/
theorem integral_mul_w {G : ℂ → ℂ} (hGm : StronglyMeasurable G) (hG : Integrable G) (h : ℂ)
    {ψ : ℂ → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) :
    ∫ x, (ψ x : ℂ) * ∫ s in Ioc (0 : ℝ) 1, G (x - s • h) =
      ∫ s in Ioc (0 : ℝ) 1, ∫ x, (ψ x : ℂ) * G (x - s • h) := by
  obtain ⟨C0, hC0⟩ := hψc.bounded_above_of_compact_support hψs
  have hF : Integrable (Function.uncurry fun (x : ℂ) (s : ℝ) => (ψ x : ℂ) * G (x - s • h))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    refine (integrable_comp_sub_smul hGm hG h).bdd_mul (c := C0)
      ((Complex.continuous_ofReal.comp (hψc.comp continuous_fst)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    simpa [Complex.norm_real] using hC0 p.1
  rw [← integral_integral_swap hF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [integral_const_mul]

/-- Translation: `∫ G ψ(· + c) = ∫ ψ G(· - c)`. -/
theorem integral_translate (G : ℂ → ℂ) (ψ : ℂ → ℝ) (c : ℂ) :
    ∫ y, G y * (ψ (y + c) : ℂ) = ∫ x, (ψ x : ℂ) * G (x - c) := by
  rw [← integral_sub_right_eq_self (fun y => G y * (ψ (y + c) : ℂ)) c]
  congr 1
  funext x
  simp only [sub_add_cancel]
  ring

/-- The weak form of `f(x) - f(x - h) = ∫_0^1 ∂_h f(x - s h) ds` on `B_R`. -/
theorem integral_smul_sub_eq_zero {r R : ℝ} {h : ℂ} (hRr : R + ‖h‖ ≤ r) {f g₁ g₂ : ℂ → ℂ}
    (hf : Integrable f) (hg₁m : StronglyMeasurable g₁) (hg₁ : Integrable g₁)
    (hg₂m : StronglyMeasurable g₂) (hg₂ : Integrable g₂)
    (h₁ : HasWeakDerivOn (ball (0 : ℂ) r) [1] f g₁)
    (h₂ : HasWeakDerivOn (ball (0 : ℂ) r) [Complex.I] f g₂)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψR : tsupport ψ ⊆ ball 0 R) :
    ∫ x, ψ x • (f x - f (x - h) - ∫ s in Ioc (0 : ℝ) 1,
      ((h.re : ℂ) * g₁ (x - s • h) + (h.im : ℂ) * g₂ (x - s • h))) = 0 := by
  set G : ℂ → ℂ := fun y => (h.re : ℂ) * g₁ y + (h.im : ℂ) * g₂ y with hGdef
  have hGm : StronglyMeasurable G := (hg₁m.const_mul _).add (hg₂m.const_mul _)
  have hG : Integrable G := (hg₁.const_mul _).add (hg₂.const_mul _)
  obtain ⟨C0, hC0⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hψm : AEStronglyMeasurable (fun x => (ψ x : ℂ)) :=
    (Complex.continuous_ofReal.comp hψ.continuous).aestronglyMeasurable
  have hbd : ∀ᵐ x ∂(volume : Measure ℂ), ‖(ψ x : ℂ)‖ ≤ C0 :=
    Filter.Eventually.of_forall fun x => by simpa [Complex.norm_real] using hC0 x
  have hψhm : AEStronglyMeasurable (fun x => (ψ (x + h) : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (hψ.continuous.comp (continuous_id.add continuous_const))).aestronglyMeasurable
  have hbdh : ∀ᵐ x ∂(volume : Measure ℂ), ‖(ψ (x + h) : ℂ)‖ ≤ C0 :=
    Filter.Eventually.of_forall fun x => by simpa [Complex.norm_real] using hC0 (x + h)
  have hw : Integrable (fun x => ∫ s in Ioc (0 : ℝ) 1, G (x - s • h)) :=
    (integrable_comp_sub_smul hGm hG h).integral_prod_left
  have i_f : Integrable (fun x => (ψ x : ℂ) * f x) := hf.bdd_mul hψm hbd
  have i_fh : Integrable (fun x => (ψ x : ℂ) * f (x - h)) :=
    (hf.comp_sub_right h).bdd_mul hψm hbd
  have i_fh' : Integrable (fun y => (ψ (y + h) : ℂ) * f y) := hf.bdd_mul hψhm hbdh
  have i_w : Integrable (fun x => (ψ x : ℂ) * ∫ s in Ioc (0 : ℝ) 1, G (x - s • h)) :=
    hw.bdd_mul hψm hbd
  have i_fsub : Integrable (fun x => (ψ x : ℂ) * f x - (ψ x : ℂ) * f (x - h)) := i_f.sub i_fh
  have hsm : (fun x => ψ x • (f x - f (x - h) - ∫ s in Ioc (0 : ℝ) 1, G (x - s • h))) =
      fun x => (ψ x : ℂ) * f x - (ψ x : ℂ) * f (x - h) -
        (ψ x : ℂ) * ∫ s in Ioc (0 : ℝ) 1, G (x - s • h) := by
    funext x
    rw [Complex.real_smul, mul_sub, mul_sub]
  show ∫ x, ψ x • (f x - f (x - h) - ∫ s in Ioc (0 : ℝ) 1, G (x - s • h)) = 0
  rw [hsm, integral_sub i_fsub i_w, integral_sub i_f i_fh]
  have e1 : ∫ x, (ψ x : ℂ) * f (x - h) = ∫ y, (ψ (y + h) : ℂ) * f y := by
    rw [← integral_sub_right_eq_self (fun y => (ψ (y + h) : ℂ) * f y) h]
    simp only [sub_add_cancel]
  have e2 : (∫ y, (ψ y : ℂ) * f y) - ∫ y, (ψ (y + h) : ℂ) * f y =
      -∫ y, f y * ((ψ (y + h) - ψ y : ℝ) : ℂ) := by
    rw [← integral_sub i_f i_fh', ← integral_neg]
    congr 1
    funext y
    push_cast
    ring
  rw [e1, e2, integral_mul_sub_translate hf hψ hψc h, integral_mul_w hGm hG h hψ.continuous hψc]
  have e3 : ∫ s in Ioc (0 : ℝ) 1, ∫ y, f y * (fderiv ℝ ψ (y + s • h) h : ℂ) =
      -∫ s in Ioc (0 : ℝ) 1, ∫ x, (ψ x : ℂ) * G (x - s • h) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    have hc : R + ‖s • h‖ ≤ r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs.1]
      nlinarith [norm_nonneg h, hs.2]
    show _ = -_
    rw [integral_mul_fderiv_translate hf hg₁ hg₂ h₁ h₂ hψ hψc hψR hc h, integral_translate]
  rw [e3]
  ring

/-- `f(x) - f(x - h) = ∫_0^1 ∂_h f(x - s h) ds` for a.e. `x ∈ B_R`. -/
theorem ae_eq_integral {r R : ℝ} {h : ℂ} (hRr : R + ‖h‖ ≤ r) {f g₁ g₂ : ℂ → ℂ}
    (hf : Integrable f) (hg₁m : StronglyMeasurable g₁) (hg₁ : Integrable g₁)
    (hg₂m : StronglyMeasurable g₂) (hg₂ : Integrable g₂)
    (h₁ : HasWeakDerivOn (ball (0 : ℂ) r) [1] f g₁)
    (h₂ : HasWeakDerivOn (ball (0 : ℂ) r) [Complex.I] f g₂) :
    ∀ᵐ x, x ∈ ball (0 : ℂ) R → f x - f (x - h) = ∫ s in Ioc (0 : ℝ) 1,
      ((h.re : ℂ) * g₁ (x - s • h) + (h.im : ℂ) * g₂ (x - s • h)) := by
  have hGm : StronglyMeasurable (fun y => (h.re : ℂ) * g₁ y + (h.im : ℂ) * g₂ y) :=
    (hg₁m.const_mul _).add (hg₂m.const_mul _)
  have hG : Integrable (fun y => (h.re : ℂ) * g₁ y + (h.im : ℂ) * g₂ y) :=
    (hg₁.const_mul _).add (hg₂.const_mul _)
  have hw := (integrable_comp_sub_smul hGm hG h).integral_prod_left
  have hloc : LocallyIntegrableOn (fun x => f x - f (x - h) - ∫ s in Ioc (0 : ℝ) 1,
      ((h.re : ℂ) * g₁ (x - s • h) + (h.im : ℂ) * g₂ (x - s • h))) (ball (0 : ℂ) R) :=
    ((hf.sub (hf.comp_sub_right h)).sub hw).locallyIntegrable.locallyIntegrableOn _
  have := isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun ψ hψ hψc hψR => integral_smul_sub_eq_zero hRr hf hg₁m hg₁ hg₂m hg₂ h₁ h₂ hψ hψc hψR)
  filter_upwards [this] with x hx hxR
  exact sub_eq_zero.1 (hx hxR)

/-- Translation into a larger ball: `‖G(· - c)‖_{L²(B_R)} ≤ ‖G‖_{L²(B_r)}` for `R + |c| ≤ r`. -/
theorem eLpNorm_comp_sub_le {G : ℂ → ℂ} (hGm : StronglyMeasurable G) {R r : ℝ} {c : ℂ}
    (hc : R + ‖c‖ ≤ r) :
    eLpNorm (fun x => G (x - c)) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
      eLpNorm G 2 (volume.restrict (ball (0 : ℂ) r)) := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball,
    ← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]
  calc eLpNorm ((ball (0 : ℂ) R).indicator fun x => G (x - c)) 2 volume
      ≤ eLpNorm ((ball (0 : ℂ) r).indicator G ∘ fun x => x - c) 2 volume := by
        refine eLpNorm_mono fun x => ?_
        by_cases hx : x ∈ ball (0 : ℂ) R
        · have hx' : x - c ∈ ball (0 : ℂ) r := by
            rw [mem_ball_zero_iff] at hx ⊢
            calc ‖x - c‖ ≤ ‖x‖ + ‖c‖ := norm_sub_le _ _
              _ < R + ‖c‖ := by linarith
              _ ≤ r := hc
          simp [indicator_of_mem hx, Function.comp, indicator_of_mem hx']
        · simp [indicator_of_notMem hx]
    _ = eLpNorm ((ball (0 : ℂ) r).indicator G) 2 volume :=
        eLpNorm_comp_measurePreserving ((hGm.indicator measurableSet_ball).aestronglyMeasurable)
          (measurePreserving_sub_right volume c)

/-- `‖∫_0^1 G(· - s h) ds‖_{L²(B_R)} ≤ ‖G‖_{L²(B_r)}` for `R + |h| ≤ r` (Minkowski). -/
theorem eLpNorm_integral_comp_sub_le {G : ℂ → ℂ} (hGm : StronglyMeasurable G) {R r : ℝ}
    {h : ℂ} (hRr : R + ‖h‖ ≤ r) :
    eLpNorm (fun x => ∫ s in Ioc (0 : ℝ) 1, G (x - s • h)) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
      eLpNorm G 2 (volume.restrict (ball (0 : ℂ) r)) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (x : ℂ) (s : ℝ) => G (x - s • h))
      ((volume.restrict (ball (0 : ℂ) R)).prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
    (hGm.comp_measurable
      ((continuous_fst.sub (continuous_snd.smul continuous_const)).measurable)).aestronglyMeasurable
  refine (Conv.eLpNorm_integral_le hmeas (by norm_num) (by norm_num)).trans ?_
  calc ∫⁻ s in Ioc (0 : ℝ) 1, eLpNorm (fun x => G (x - s • h)) 2 (volume.restrict (ball (0 : ℂ) R))
      ≤ ∫⁻ s in Ioc (0 : ℝ) 1, eLpNorm G 2 (volume.restrict (ball (0 : ℂ) r)) := by
        refine setLIntegral_mono' measurableSet_Ioc fun s hs => eLpNorm_comp_sub_le hGm ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs.1]
        nlinarith [norm_nonneg h, hs.2]
    _ = eLpNorm G 2 (volume.restrict (ball (0 : ℂ) r)) := by simp [lintegral_const]

/-- The difference-quotient bound for integrable `f` with integrable, strongly measurable weak
derivatives `g₁ = ∂₁ f`, `g₂ = ∂₂ f` on `B_r`: `‖f - f(·-h)‖_{L²(B_R)} ≤ ‖∂_h f‖_{L²(B_r)}`. -/
theorem eLpNorm_sub_comp_sub_le_of_integrable {r R : ℝ} {h : ℂ} (hRr : R + ‖h‖ ≤ r)
    {f g₁ g₂ : ℂ → ℂ} (hf : Integrable f) (hg₁m : StronglyMeasurable g₁) (hg₁ : Integrable g₁)
    (hg₂m : StronglyMeasurable g₂) (hg₂ : Integrable g₂)
    (h₁ : HasWeakDerivOn (ball (0 : ℂ) r) [1] f g₁)
    (h₂ : HasWeakDerivOn (ball (0 : ℂ) r) [Complex.I] f g₂) :
    eLpNorm (fun x => f x - f (x - h)) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
      eLpNorm (fun y => (h.re : ℂ) * g₁ y + (h.im : ℂ) * g₂ y) 2
        (volume.restrict (ball (0 : ℂ) r)) := by
  have hGm : StronglyMeasurable (fun y => (h.re : ℂ) * g₁ y + (h.im : ℂ) * g₂ y) :=
    (hg₁m.const_mul _).add (hg₂m.const_mul _)
  have hae := ae_eq_integral hRr hf hg₁m hg₁ hg₂m hg₂ h₁ h₂
  rw [eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_ball).2 hae)]
  exact eLpNorm_integral_comp_sub_le hGm hRr

end NonUniqueEuler.Sob.DiffQuotAux
