import NonUniqueEuler.Defs.Infra.ConvMinkowski
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Proof: measurability of convolutions and of the Biot–Savart velocity (I-CONV)

Proof of `NonUniqueEuler/I/Infra/ConvMinkowski/Measurable.lean` (same declarations, same
statements). Self-contained: it uses only Mathlib and `Defs/Infra/ConvMinkowski`.

Strategy (as in the interface docstring).
* Representatives: the majorant `convAbs K g` and the velocity `velocity g` only see `K` and `g`
  up to null sets (`convAbs_congr_ae`, `velocity_congr_ae`), because `y ↦ x - y` is
  quasi-measure-preserving on `ℂ`.
* For strongly measurable representatives the measurability is `Measurable.lintegral_prod_right'`
  and `StronglyMeasurable.integral_prod_right` (Tonelli/Fubini measurability).
* Split kernels: `‖K₂‖_∞ ‖g‖₁` bounds the far part everywhere; the near part has
  `∫ |K₁| ⋆ |g| = ‖K₁‖₁ ‖g‖₁ < ∞` (Tonelli), hence is finite a.e.
* Space–time: a strongly measurable modification `ω'` of `uncurry ω`; for `μ`-a.e. `t`,
  `ω t =ᵐ ω'(t, ·)` (`Measure.ae_ae_eq_curry_of_prod`), and `quasiMeasurePreserving_fst` lifts
  this to `μ.prod volume`-a.e. `(t, x)`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Conv

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-! ### Helpers -/

/-- `y ↦ x - y` is quasi-measure-preserving on `ℂ`. -/
private lemma qmp_sub_left (x : ℂ) :
    Measure.QuasiMeasurePreserving (fun y : ℂ => x - y) volume volume :=
  quasiMeasurePreserving_sub_left_of_right_invariant volume x

/-- The majorant does not see null modifications of `K` and `g`. -/
private lemma convAbs_congr_ae {E' F' : Type*} [NormedAddCommGroup E'] [NormedAddCommGroup F']
    {K : ℂ → E} {K' : ℂ → E'} {g : ℂ → F} {g' : ℂ → F'}
    (hK : ∀ᵐ z, ‖K z‖ₑ = ‖K' z‖ₑ) (hg : ∀ᵐ y, ‖g y‖ₑ = ‖g' y‖ₑ) (x : ℂ) :
    convAbs K g x = convAbs K' g' x := by
  unfold convAbs
  apply lintegral_congr_ae
  filter_upwards [(qmp_sub_left x).ae hK, hg] with y h1 h2
  rw [h1, h2]

private lemma convAbs_congr_ae' {K K' : ℂ → E} {g g' : ℂ → F}
    (hK : K =ᵐ[volume] K') (hg : g =ᵐ[volume] g') (x : ℂ) :
    convAbs K g x = convAbs K' g' x :=
  convAbs_congr_ae (hK.mono fun _ h => by rw [h]) (hg.mono fun _ h => by rw [h]) x

/-- Measurability of the majorant for strongly measurable `K`, `g`. -/
private lemma measurable_convAbs_of_stronglyMeasurable {K : ℂ → E} {g : ℂ → F}
    (hK : StronglyMeasurable K) (hg : StronglyMeasurable g) : Measurable (convAbs K g) := by
  have h : Measurable fun p : ℂ × ℂ => ‖K (p.1 - p.2)‖ₑ * ‖g p.2‖ₑ :=
    (hK.enorm.comp (measurable_fst.sub measurable_snd)).mul (hg.enorm.comp measurable_snd)
  exact h.lintegral_prod_right'

/-- `‖K(x - y) g(y)‖ₑ = ‖K(x - y)‖ₑ ‖g(y)‖ₑ`, so the `L¹` norm of the integrand is the
majorant. -/
private lemma lintegral_enorm_conv_eq (K : ℂ → ℂ) (g : ℂ → ℝ) (x : ℂ) :
    ∫⁻ y, ‖K (x - y) * (g y : ℂ)‖ₑ = convAbs K g x := by
  unfold convAbs
  refine lintegral_congr fun y => ?_
  rw [enorm_mul]
  congr 1
  simp only [enorm, Complex.nnnorm_real]

/-- `|K| ⋆ |g| ≤ |K₁| ⋆ |g| + |K₂| ⋆ |g|` under `|K| ≤ |K₁| + |K₂|`. -/
private lemma convAbs_le_add_of_split {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] {K : ℂ → E} {K₁ : ℂ → E₁} {K₂ : ℂ → E₂}
    (hK₁ : AEStronglyMeasurable K₁ volume)
    (hsplit : ∀ z, ‖K z‖ ≤ ‖K₁ z‖ + ‖K₂ z‖) {g : ℂ → F} (hg : AEStronglyMeasurable g volume)
    (x : ℂ) : convAbs K g x ≤ convAbs K₁ g x + convAbs K₂ g x := by
  have hz : ∀ z, ‖K z‖ₑ ≤ ‖K₁ z‖ₑ + ‖K₂ z‖ₑ := fun z => by
    simp only [← ofReal_norm]
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hsplit z)
  have hmeas : AEMeasurable (fun y => ‖K₁ (x - y)‖ₑ * ‖g y‖ₑ) volume :=
    ((hK₁.comp_quasiMeasurePreserving (qmp_sub_left x)).enorm).mul hg.enorm
  unfold convAbs
  calc ∫⁻ y, ‖K (x - y)‖ₑ * ‖g y‖ₑ
      ≤ ∫⁻ y, (‖K₁ (x - y)‖ₑ * ‖g y‖ₑ + ‖K₂ (x - y)‖ₑ * ‖g y‖ₑ) := by
        refine lintegral_mono fun y => ?_
        rw [← add_mul]
        exact mul_le_mul_left (hz (x - y)) _
    _ = _ := lintegral_add_left' hmeas _

/-- `(|K| ⋆ |g|)(x) ≤ ‖K‖_∞ ‖g‖₁` for every `x`. -/
private lemma convAbs_le_eLpNormEssSup_mul (K : ℂ → E) {g : ℂ → F}
    (hg : AEStronglyMeasurable g volume) (x : ℂ) :
    convAbs K g x ≤ eLpNormEssSup K volume * ∫⁻ y, ‖g y‖ₑ := by
  unfold convAbs
  rw [← lintegral_const_mul'' _ hg.enorm]
  refine lintegral_mono_ae ?_
  filter_upwards [(qmp_sub_left x).ae (ae_le_eLpNormEssSup (f := K) (μ := volume))] with y hy
  exact mul_le_mul_left hy _

/-- Tonelli for strongly measurable representatives: `∫ |K| ⋆ |g| = ‖K‖₁ ‖g‖₁`. -/
private lemma lintegral_convAbs_of_stronglyMeasurable {K : ℂ → E} {g : ℂ → F}
    (hK : StronglyMeasurable K) (hg : StronglyMeasurable g) :
    ∫⁻ x, convAbs K g x = (∫⁻ z, ‖K z‖ₑ) * ∫⁻ y, ‖g y‖ₑ := by
  have h : Measurable (Function.uncurry fun x y : ℂ => ‖K (x - y)‖ₑ * ‖g y‖ₑ) :=
    (hK.enorm.comp (measurable_fst.sub measurable_snd)).mul (hg.enorm.comp measurable_snd)
  unfold convAbs
  rw [lintegral_lintegral_swap h.aemeasurable, ← lintegral_const_mul _ hg.enorm]
  refine lintegral_congr fun y => ?_
  have hm : Measurable fun x : ℂ => ‖K (x - y)‖ₑ := hK.enorm.comp (measurable_id.sub_const y)
  rw [lintegral_mul_const _ hm,
    lintegral_sub_right_eq_self (fun z => ‖K z‖ₑ) y, mul_comm]

/-- `K, g ∈ L¹` gives `∫ |K| ⋆ |g| < ∞`, hence `|K| ⋆ |g| < ∞` a.e. -/
private lemma ae_convAbs_lt_top_of_memLp_one {K : ℂ → E} {g : ℂ → F} (hK : MemLp K 1 volume)
    (hg : MemLp g 1 volume) : ∀ᵐ x, convAbs K g x < ∞ := by
  have hK' := hK.1.stronglyMeasurable_mk
  have hg' := hg.1.stronglyMeasurable_mk
  have heq : convAbs K g = convAbs (hK.1.mk K) (hg.1.mk g) :=
    funext (convAbs_congr_ae' hK.1.ae_eq_mk hg.1.ae_eq_mk)
  have hKi : ∫⁻ z, ‖hK.1.mk K z‖ₑ ≠ ∞ := by
    rw [← eLpNorm_one_eq_lintegral_enorm, ← eLpNorm_congr_ae hK.1.ae_eq_mk]
    exact hK.2.ne
  have hgi : ∫⁻ y, ‖hg.1.mk g y‖ₑ ≠ ∞ := by
    rw [← eLpNorm_one_eq_lintegral_enorm, ← eLpNorm_congr_ae hg.1.ae_eq_mk]
    exact hg.2.ne
  rw [heq]
  refine ae_lt_top (measurable_convAbs_of_stronglyMeasurable hK' hg') ?_
  rw [lintegral_convAbs_of_stronglyMeasurable hK' hg']
  exact ENNReal.mul_ne_top hKi hgi

/-- The velocity does not see null modifications of `g`. -/
private lemma velocity_congr_ae {g g' : ℂ → ℝ} (hg : g =ᵐ[volume] g') (x : ℂ) :
    velocity g x = velocity g' x := by
  unfold velocity
  refine integral_congr_ae ?_
  filter_upwards [hg] with y hy
  rw [hy]

private lemma measurable_biotSavartKernel : Measurable biotSavartKernel := by
  unfold biotSavartKernel
  fun_prop

/-- `(p, y) ↦ K(x(p) - y) * g(p, y)` is strongly measurable for strongly measurable data. -/
private lemma stronglyMeasurable_conv_integrand {α : Type*} [MeasurableSpace α] {x : α → ℂ}
    (hx : Measurable x) {G : α × ℂ → ℝ} (hG : StronglyMeasurable G) :
    StronglyMeasurable (Function.uncurry fun (p : α) (y : ℂ) =>
      biotSavartKernel (x p - y) * (G (p, y) : ℂ)) := by
  have h1 : StronglyMeasurable fun q : α × ℂ => biotSavartKernel (x q.1 - q.2) :=
    (measurable_biotSavartKernel.comp
      ((hx.comp measurable_fst).sub measurable_snd)).stronglyMeasurable
  have h2 : StronglyMeasurable fun q : α × ℂ => (G q : ℂ) :=
    Complex.continuous_ofReal.comp_stronglyMeasurable hG
  exact h1.mul h2

/-! ### The interface statements -/

theorem measurable_convAbs {K : ℂ → E} {g : ℂ → F} (hK : AEStronglyMeasurable K volume)
    (hg : AEStronglyMeasurable g volume) : Measurable (convAbs K g) := by
  have heq : convAbs K g = convAbs (hK.mk K) (hg.mk g) :=
    funext (convAbs_congr_ae' hK.ae_eq_mk hg.ae_eq_mk)
  rw [heq]
  exact measurable_convAbs_of_stronglyMeasurable hK.stronglyMeasurable_mk hg.stronglyMeasurable_mk

/-- Finite majorant ⇒ absolutely convergent convolution integral. -/
theorem integrable_conv_of_convAbs_ne_top {K : ℂ → ℂ} {g : ℂ → ℝ}
    (hK : AEStronglyMeasurable K volume) (hg : AEStronglyMeasurable g volume) {x : ℂ}
    (hx : convAbs K g x ≠ ∞) : Integrable (fun y => K (x - y) * (g y : ℂ)) := by
  refine ⟨?_, ?_⟩
  · have h1 : AEStronglyMeasurable (fun y => K (x - y)) volume :=
      hK.comp_quasiMeasurePreserving (qmp_sub_left x)
    have h2 : AEStronglyMeasurable (fun y => (g y : ℂ)) volume :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hg
    exact h1.mul h2
  · rw [hasFiniteIntegral_iff_enorm, lintegral_enorm_conv_eq]
    exact hx.lt_top

/-- Split kernel and `g ∈ L¹`: the convolution integral converges absolutely for a.e. `x`. -/
theorem ae_integrable_conv_of_split {K K₁ K₂ : ℂ → ℂ} (hK : AEStronglyMeasurable K volume)
    (hK₁ : MemLp K₁ 1 volume) (hK₂ : MemLp K₂ ⊤ volume) (hsplit : ∀ z, ‖K z‖ ≤ ‖K₁ z‖ + ‖K₂ z‖)
    {g : ℂ → ℝ} (hg : MemLp g 1 volume) :
    ∀ᵐ x, Integrable (fun y => K (x - y) * (g y : ℂ)) := by
  have hfar : ∀ x, convAbs K₂ g x < ∞ := fun x => by
    refine (convAbs_le_eLpNormEssSup_mul K₂ hg.1 x).trans_lt (ENNReal.mul_lt_top ?_ ?_)
    · rw [← eLpNorm_exponent_top]; exact hK₂.2
    · rw [← eLpNorm_one_eq_lintegral_enorm]; exact hg.2
  filter_upwards [ae_convAbs_lt_top_of_memLp_one hK₁ hg] with x hx
  refine integrable_conv_of_convAbs_ne_top hK hg.1 ?_
  exact ((convAbs_le_add_of_split hK₁.1 hsplit hg.1 x).trans_lt
    (ENNReal.add_lt_top.2 ⟨hx, hfar x⟩)).ne

/-- The Biot–Savart velocity of an a.e.-strongly measurable vorticity is strongly measurable. -/
theorem stronglyMeasurable_velocity {g : ℂ → ℝ} (hg : AEStronglyMeasurable g volume) :
    StronglyMeasurable (velocity g) := by
  have heq : velocity g = fun x => ∫ y, biotSavartKernel (x - y) * ((hg.mk g y : ℝ) : ℂ) :=
    funext (velocity_congr_ae hg.ae_eq_mk)
  rw [heq]
  refine StronglyMeasurable.integral_prod_right ?_
  exact stronglyMeasurable_conv_integrand measurable_id
    (hg.stronglyMeasurable_mk.comp_measurable measurable_snd)

/-- Space–time measurability of the majorant. -/
theorem aemeasurable_convAbs_prod {μ : Measure ℝ} [SFinite μ] {K : ℂ → E}
    (hK : AEStronglyMeasurable K volume) {ω : ℝ → ℂ → ℝ}
    (hω : AEStronglyMeasurable (Function.uncurry ω) (μ.prod volume)) :
    AEMeasurable (fun p : ℝ × ℂ => convAbs K (ω p.1) p.2) (μ.prod volume) := by
  set ω' := hω.mk (Function.uncurry ω)
  have hω' : StronglyMeasurable ω' := hω.stronglyMeasurable_mk
  have hK' : StronglyMeasurable (hK.mk K) := hK.stronglyMeasurable_mk
  have hae : ∀ᵐ t ∂μ, ω t =ᵐ[volume] fun y => ω' (t, y) :=
    Measure.ae_ae_eq_curry_of_prod hω.ae_eq_mk
  have hmeas : Measurable fun p : ℝ × ℂ => convAbs (hK.mk K) (fun y => ω' (p.1, y)) p.2 := by
    have h : Measurable fun q : (ℝ × ℂ) × ℂ =>
        ‖hK.mk K (q.1.2 - q.2)‖ₑ * ‖ω' (q.1.1, q.2)‖ₑ :=
      (hK'.enorm.comp ((measurable_snd.comp measurable_fst).sub measurable_snd)).mul
        (hω'.enorm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    exact h.lintegral_prod_right'
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hae] with p hp
  exact (convAbs_congr_ae' hK.ae_eq_mk hp p.2).symm

/-- Space–time measurability of the velocity `v(t, x) = (K ⋆ ω(t))(x)`. -/
theorem aestronglyMeasurable_velocityField_prod {μ : Measure ℝ} [SFinite μ] {ω : ℝ → ℂ → ℝ}
    (hω : AEStronglyMeasurable (Function.uncurry ω) (μ.prod volume)) :
    AEStronglyMeasurable (fun p : ℝ × ℂ => velocityField ω p.1 p.2) (μ.prod volume) := by
  set ω' := hω.mk (Function.uncurry ω)
  have hω' : StronglyMeasurable ω' := hω.stronglyMeasurable_mk
  have hae : ∀ᵐ t ∂μ, ω t =ᵐ[volume] fun y => ω' (t, y) :=
    Measure.ae_ae_eq_curry_of_prod hω.ae_eq_mk
  have hsm : StronglyMeasurable fun p : ℝ × ℂ =>
      ∫ y, biotSavartKernel (p.2 - y) * (ω' (p.1, y) : ℂ) := by
    refine StronglyMeasurable.integral_prod_right ?_
    exact stronglyMeasurable_conv_integrand measurable_snd
      (hω'.comp_measurable ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  refine hsm.aestronglyMeasurable.congr ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hae] with p hp
  exact (velocity_congr_ae hp p.2).symm

/-- Space–time measurability of the velocity on the slab `(0, T) × ℂ` (statement layer). -/
theorem aestronglyMeasurable_velocityField_slab {T : ℝ} {ω : ℝ → ℂ → ℝ}
    (hω : AEStronglyMeasurable (Function.uncurry ω) (volume.restrict (slab T))) :
    AEStronglyMeasurable (fun p : ℝ × ℂ => velocityField ω p.1 p.2)
      (volume.restrict (slab T)) := by
  have hrestr : (volume : Measure (ℝ × ℂ)).restrict (slab T) =
      (volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure ℂ) := by
    rw [slab, Measure.volume_eq_prod ℝ ℂ, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hrestr] at hω ⊢
  exact aestronglyMeasurable_velocityField_prod hω

end NonUniqueEuler.Conv
