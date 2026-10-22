import NonUniqueEuler.Defs.Infra.ConvMinkowski
import NonUniqueEuler.I.Infra.ConvMinkowski.Minkowski
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Data.ENNReal.Holder

/-!
# Proof of `I/Infra/ConvMinkowski/Young.lean`: convolution majorants on `ℂ` (I-CONV)

For `convAbs K g x = ∫⁻ ‖K(x-y)‖ ‖g(y)‖ dy`:
* substitution `y = x - z` (`MeasurePreserving.lintegral_comp_emb` for `z ↦ x - z`);
* `L¹ ⋆ L^p`: Minkowski's integral inequality (`I/Infra/ConvMinkowski/Minkowski.lean`,
  `eLpNorm_lintegral_le`) applied to `F x z = ‖K z‖ ‖g(x - z)‖`, and translation invariance of
  `eLpNorm`; `p = ∞` from the pointwise bound `‖g(x - z)‖ ≤ ‖g‖_∞` for a.e. `z`;
* the ball form: on `B_R`, `|K| ⋆ |g| = |K 1_{B_{R+ρ}}| ⋆ |g|` when `g = 0` a.e. off `B_ρ`;
* pointwise `L^∞ ⋆ L¹` and Hölder bounds (`eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm` with `r = 1`);
* Tonelli (`lintegral_lintegral_swap`) and translation invariance of the Lebesgue integral;
* split kernels: `|K| ⋆ |g| ≤ |K₁| ⋆ |g| + |K₂| ⋆ |g|` pointwise.

The joint measurability of the integrands comes from the quasi-measure-preservation of
`(x, y) ↦ x - y` (`quasiMeasurePreserving_sub`) and of `Prod.snd`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace NonUniqueEuler.Conv

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-! ### Helpers -/

/-- Joint measurability of `(x, z) ↦ ‖K z‖ ‖g (x - z)‖`. -/
private theorem aemeasurable_prod_sub {K : ℂ → E} {g : ℂ → F}
    (hK : AEStronglyMeasurable K volume) (hg : AEStronglyMeasurable g volume) :
    AEMeasurable (fun p : ℂ × ℂ => ‖K p.2‖ₑ * ‖g (p.1 - p.2)‖ₑ)
      ((volume : Measure ℂ).prod volume) :=
  hK.enorm.comp_snd.mul
    (hg.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume))

/-- Joint measurability of `(x, y) ↦ ‖K (x - y)‖ ‖g y‖`. -/
private theorem aemeasurable_prod_conv {K : ℂ → E} {g : ℂ → F}
    (hK : AEStronglyMeasurable K volume) (hg : AEStronglyMeasurable g volume) :
    AEMeasurable (fun p : ℂ × ℂ => ‖K (p.1 - p.2)‖ₑ * ‖g p.2‖ₑ)
      ((volume : Measure ℂ).prod volume) :=
  (hK.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)).mul
    hg.enorm.comp_snd

/-- `|K| ⋆ |g|` is a.e.-measurable. -/
private theorem aemeasurable_convAbs {K : ℂ → E} {g : ℂ → F}
    (hK : AEStronglyMeasurable K volume) (hg : AEStronglyMeasurable g volume) :
    AEMeasurable (convAbs K g) volume :=
  (aemeasurable_prod_conv hK hg).lintegral_prod_right'

/-- For fixed `x`, `y ↦ ‖K (x - y)‖ ‖g y‖` is a.e.-measurable. -/
private theorem aemeasurable_conv_integrand {K : ℂ → E} {g : ℂ → F}
    (hK : AEStronglyMeasurable K volume) (hg : AEStronglyMeasurable g volume) (x : ℂ) :
    AEMeasurable (fun y => ‖K (x - y)‖ₑ * ‖g y‖ₑ) volume :=
  (hK.enorm.comp_quasiMeasurePreserving
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving).mul hg.enorm

/-- `‖K z‖ ≤ ‖K₁ z‖ + ‖K₂ z‖` in `ℝ≥0∞`. -/
private theorem enorm_le_add_of_split {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] {K : ℂ → E} {K₁ : ℂ → E₁} {K₂ : ℂ → E₂}
    (hsplit : ∀ z, ‖K z‖ ≤ ‖K₁ z‖ + ‖K₂ z‖) (z : ℂ) :
    ‖K z‖ₑ ≤ ‖K₁ z‖ₑ + ‖K₂ z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hsplit z)

/-- Split kernel: `|K| ⋆ |g| ≤ |K₁| ⋆ |g| + |K₂| ⋆ |g|` pointwise. -/
private theorem convAbs_le_add_of_split {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] {K : ℂ → E} {K₁ : ℂ → E₁} {K₂ : ℂ → E₂}
    (hK₁ : AEStronglyMeasurable K₁ volume) (hsplit : ∀ z, ‖K z‖ ≤ ‖K₁ z‖ + ‖K₂ z‖)
    {g : ℂ → F} (hg : AEStronglyMeasurable g volume) (x : ℂ) :
    convAbs K g x ≤ convAbs K₁ g x + convAbs K₂ g x := by
  calc convAbs K g x
      ≤ ∫⁻ y, ‖K₁ (x - y)‖ₑ * ‖g y‖ₑ + ‖K₂ (x - y)‖ₑ * ‖g y‖ₑ := by
        refine lintegral_mono fun y => ?_
        rw [← add_mul]
        gcongr
        exact enorm_le_add_of_split hsplit _
    _ = convAbs K₁ g x + convAbs K₂ g x :=
        lintegral_add_left' (aemeasurable_conv_integrand hK₁ hg x) _

/-! ### Substitution -/

/-- `(|K| ⋆ |g|)(x) = ∫⁻ ‖K(z)‖ ‖g(x - z)‖ dz`. -/
theorem convAbs_eq_lintegral_sub (K : ℂ → E) (g : ℂ → F) (x : ℂ) :
    convAbs K g x = ∫⁻ z, ‖K z‖ₑ * ‖g (x - z)‖ₑ := by
  have h := (Measure.measurePreserving_sub_left volume x).lintegral_comp_emb
    (MeasurableEquiv.subLeft x).measurableEmbedding (fun y => ‖K (x - y)‖ₑ * ‖g y‖ₑ)
  simp only [sub_sub_cancel] at h
  rw [convAbs, ← h]

/-! ### Pointwise bounds -/

/-- `(|K| ⋆ |g|)(x) ≤ ‖K‖₁ ‖g‖_∞`. -/
private theorem convAbs_le_lintegral_mul_essSup {K : ℂ → E} {g : ℂ → F}
    (hK : AEStronglyMeasurable K volume) (x : ℂ) :
    convAbs K g x ≤ (∫⁻ z, ‖K z‖ₑ) * eLpNormEssSup g volume := by
  rw [convAbs_eq_lintegral_sub, ← lintegral_mul_const'' _ hK.enorm]
  refine lintegral_mono_ae ?_
  filter_upwards [(Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae
    (ae_le_eLpNormEssSup (f := g))] with z hz
  gcongr

set_option linter.unusedVariables false in
/-- `(|K| ⋆ |g|)(x) ≤ ‖K‖_∞ ‖g‖₁` for every `x`. -/
theorem convAbs_le_eLpNorm_top_mul {K : ℂ → E} {g : ℂ → F} (hK : AEStronglyMeasurable K volume)
    (hg : AEStronglyMeasurable g volume) (x : ℂ) :
    convAbs K g x ≤ eLpNorm K ⊤ volume * eLpNorm g 1 volume := by
  rw [convAbs, eLpNorm_exponent_top, eLpNorm_one_eq_lintegral_enorm,
    ← lintegral_const_mul'' _ hg.enorm]
  refine lintegral_mono_ae ?_
  filter_upwards [(Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae
    (ae_le_eLpNormEssSup (f := K))] with y hy
  gcongr

/-- Hölder: `(|K| ⋆ |g|)(x) ≤ ‖K‖_p ‖g‖_q` for every `x`, `1/p + 1/q = 1`. -/
theorem convAbs_le_eLpNorm_mul_eLpNorm {K : ℂ → E} {g : ℂ → F}
    (hK : AEStronglyMeasurable K volume) (hg : AEStronglyMeasurable g volume)
    {p q : ℝ≥0∞} (hpq : p.HolderConjugate q) (x : ℂ) :
    convAbs K g x ≤ eLpNorm K p volume * eLpNorm g q volume := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure ℂ) x
  have hK' : AEStronglyMeasurable (fun y => K (x - y)) volume := hK.comp_measurePreserving hmp
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := volume) (p := p) (q := q) (r := 1)
    hK' hg (fun a b => ‖a‖ * ‖b‖) 1 (Eventually.of_forall fun y => by simp) (hpqr := hpq)
  have hKeq : eLpNorm (fun y => K (x - y)) p volume = eLpNorm K p volume :=
    eLpNorm_comp_measurePreserving (f := fun y => x - y) hK hmp
  rw [hKeq, ENNReal.coe_one, one_mul, eLpNorm_one_eq_lintegral_enorm] at h
  refine le_of_eq_of_le ?_ h
  rw [convAbs]
  refine lintegral_congr fun y => ?_
  rw [enorm_mul, enorm_norm, enorm_norm]

/-! ### `L¹ ⋆ L^p` -/

/-- `‖|K| ⋆ |g|‖_p ≤ ‖K‖₁ ‖g‖_p`, `1 ≤ p ≤ ∞`. -/
theorem eLpNorm_convAbs_le {K : ℂ → E} {g : ℂ → F} (hK : AEStronglyMeasurable K volume)
    (hg : AEStronglyMeasurable g volume) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (convAbs K g) p volume ≤ (∫⁻ z, ‖K z‖ₑ) * eLpNorm g p volume := by
  rcases eq_or_ne p ∞ with rfl | hp'
  · rw [eLpNorm_exponent_top, eLpNorm_exponent_top]
    refine essSup_le_of_ae_le _ (Eventually.of_forall fun x => ?_)
    change ‖convAbs K g x‖ₑ ≤ _
    rw [enorm_eq_self]
    exact convAbs_le_lintegral_mul_essSup hK x
  have hmink := eLpNorm_lintegral_le (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))
    (F := fun x z => ‖K z‖ₑ * ‖g (x - z)‖ₑ) (aemeasurable_prod_sub hK hg) hp hp'
  have hfun : convAbs K g = fun x => ∫⁻ z, ‖K z‖ₑ * ‖g (x - z)‖ₑ :=
    funext (convAbs_eq_lintegral_sub K g)
  rw [hfun]
  refine hmink.trans ?_
  calc ∫⁻ z, eLpNorm (fun x => ‖K z‖ₑ * ‖g (x - z)‖ₑ) p volume
      ≤ ∫⁻ z, ‖K z‖ₑ * eLpNorm g p volume := by
        refine lintegral_mono fun z => ?_
        have h1 : eLpNorm (fun x => ‖K z‖ₑ * ‖g (x - z)‖ₑ) p volume ≤
            ‖K z‖₊ • eLpNorm (fun x => g (x - z)) p volume :=
          eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
            (Eventually.of_forall fun x => by rw [enorm_eq_self]; rfl) p
        have h2 : eLpNorm (fun x => g (x - z)) p volume = eLpNorm g p volume :=
          eLpNorm_comp_measurePreserving (f := fun x => x - z) hg
            (measurePreserving_sub_right volume z)
        rw [h2] at h1
        exact h1
    _ = (∫⁻ z, ‖K z‖ₑ) * eLpNorm g p volume := lintegral_mul_const'' _ hK.enorm

/-- Local form (`lem:BS-basic`(c)): if `g = 0` a.e. outside `B_ρ`, then
`‖|K| ⋆ |g|‖_{L^p(B_R)} ≤ (∫_{B_{R+ρ}} |K|) ‖g‖_p`. -/
theorem eLpNorm_convAbs_ball_le {K : ℂ → E} {g : ℂ → F} (hK : AEStronglyMeasurable K volume)
    (hg : AEStronglyMeasurable g volume) {p : ℝ≥0∞} (hp : 1 ≤ p) {ρ R : ℝ}
    (hsupp : ∀ᵐ y, ρ ≤ ‖y‖ → g y = 0) :
    eLpNorm (convAbs K g) p (volume.restrict (ball 0 R)) ≤
      (∫⁻ z in ball (0 : ℂ) (R + ρ), ‖K z‖ₑ) * eLpNorm g p volume := by
  set K' : ℂ → E := (ball (0 : ℂ) (R + ρ)).indicator K with hK'def
  have hK' : AEStronglyMeasurable K' volume := hK.indicator measurableSet_ball
  have heq : ∀ x ∈ ball (0 : ℂ) R, convAbs K g x = convAbs K' g x := by
    intro x hx
    refine lintegral_congr_ae ?_
    filter_upwards [hsupp] with y hy
    by_cases hyρ : ρ ≤ ‖y‖
    · simp [hy hyρ]
    · push Not at hyρ
      have hmem : x - y ∈ ball (0 : ℂ) (R + ρ) := by
        rw [mem_ball_zero_iff] at hx ⊢
        calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
          _ < R + ρ := add_lt_add hx hyρ
      rw [hK'def, indicator_of_mem hmem]
  calc eLpNorm (convAbs K g) p (volume.restrict (ball 0 R))
      = eLpNorm (convAbs K' g) p (volume.restrict (ball 0 R)) :=
        eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall heq))
    _ ≤ eLpNorm (convAbs K' g) p volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ (∫⁻ z, ‖K' z‖ₑ) * eLpNorm g p volume := eLpNorm_convAbs_le hK' hg hp
    _ = (∫⁻ z in ball (0 : ℂ) (R + ρ), ‖K z‖ₑ) * eLpNorm g p volume := by
        rw [← lintegral_indicator measurableSet_ball]
        congr 1
        refine lintegral_congr fun z => ?_
        rw [hK'def, enorm_indicator_eq_indicator_enorm]

/-! ### Tonelli -/

set_option linter.unusedVariables false in
/-- Tonelli on a set: `∫_A |K| ⋆ |g| = ∫ |g(y)| ∫_A |K(x - y)| dx dy`. -/
theorem setLIntegral_convAbs {K : ℂ → E} {g : ℂ → F} (hK : AEStronglyMeasurable K volume)
    (hg : AEStronglyMeasurable g volume) {A : Set ℂ} (hA : MeasurableSet A) :
    ∫⁻ x in A, convAbs K g x = ∫⁻ y, ‖g y‖ₑ * ∫⁻ x in A, ‖K (x - y)‖ₑ := by
  have hac : (volume.restrict A).prod (volume : Measure ℂ) ≪ (volume : Measure ℂ).prod volume :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod
      Measure.AbsolutelyContinuous.rfl
  have hF : AEMeasurable (Function.uncurry fun x y => ‖K (x - y)‖ₑ * ‖g y‖ₑ)
      ((volume.restrict A).prod volume) :=
    (aemeasurable_prod_conv hK hg).mono_ac hac
  simp only [convAbs]
  rw [lintegral_lintegral_swap hF]
  refine lintegral_congr fun y => ?_
  rw [lintegral_mul_const'' _ ?_, mul_comm]
  exact (hK.enorm.comp_quasiMeasurePreserving
    (measurePreserving_sub_right volume y).quasiMeasurePreserving).restrict

theorem lintegral_convAbs {K : ℂ → E} {g : ℂ → F} (hK : AEStronglyMeasurable K volume)
    (hg : AEStronglyMeasurable g volume) :
    ∫⁻ x, convAbs K g x = (∫⁻ z, ‖K z‖ₑ) * ∫⁻ y, ‖g y‖ₑ := by
  have h := setLIntegral_convAbs hK hg MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  rw [h]
  have h2 : ∀ y, ∫⁻ x, ‖K (x - y)‖ₑ = ∫⁻ z, ‖K z‖ₑ := fun y =>
    lintegral_sub_right_eq_self (fun z => ‖K z‖ₑ) y
  simp_rw [h2]
  rw [lintegral_mul_const'' _ hg.enorm, mul_comm]

/-! ### Split kernels -/

/-- Split kernel `|K| ≤ |K₁| + |K₂|`, `K₁ ∈ L¹`, `K₂ ∈ L^∞`, and `g ∈ L¹`: `|K| ⋆ |g| < ∞` a.e. -/
theorem ae_convAbs_lt_top_of_split {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] {K : ℂ → E} {K₁ : ℂ → E₁} {K₂ : ℂ → E₂}
    (hK₁ : MemLp K₁ 1 volume) (hK₂ : MemLp K₂ ⊤ volume) (hsplit : ∀ z, ‖K z‖ ≤ ‖K₁ z‖ + ‖K₂ z‖)
    {g : ℂ → F} (hg : MemLp g 1 volume) : ∀ᵐ x, convAbs K g x < ∞ := by
  have hfin : ∫⁻ x, convAbs K₁ g x ≠ ∞ := by
    rw [lintegral_convAbs hK₁.1 hg.1, ← eLpNorm_one_eq_lintegral_enorm,
      ← eLpNorm_one_eq_lintegral_enorm]
    exact ENNReal.mul_ne_top hK₁.2.ne hg.2.ne
  have h1 : ∀ᵐ x, convAbs K₁ g x < ∞ := ae_lt_top' (aemeasurable_convAbs hK₁.1 hg.1) hfin
  filter_upwards [h1] with x hx
  calc convAbs K g x ≤ convAbs K₁ g x + convAbs K₂ g x :=
        convAbs_le_add_of_split hK₁.1 hsplit hg.1 x
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hx, (convAbs_le_eLpNorm_top_mul hK₂.1 hg.1 x).trans_lt
        (ENNReal.mul_lt_top hK₂.2 hg.2)⟩

/-- Split kernel, pointwise (`lem:LpLinf`, `lem:BS-basic`(b)): for Hölder conjugates `p, q`,
`(|K| ⋆ |g|)(x) ≤ ‖K₁‖_p ‖g‖_q + ‖K₂‖_∞ ‖g‖₁` for every `x`. -/
theorem convAbs_le_of_split_holder {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] {K : ℂ → E} {K₁ : ℂ → E₁} {K₂ : ℂ → E₂}
    (hK₁ : AEStronglyMeasurable K₁ volume) (hK₂ : AEStronglyMeasurable K₂ volume)
    (hsplit : ∀ z, ‖K z‖ ≤ ‖K₁ z‖ + ‖K₂ z‖) {g : ℂ → F} (hg : AEStronglyMeasurable g volume)
    {p q : ℝ≥0∞} (hpq : p.HolderConjugate q) (x : ℂ) :
    convAbs K g x ≤
      eLpNorm K₁ p volume * eLpNorm g q volume + eLpNorm K₂ ⊤ volume * eLpNorm g 1 volume :=
  (convAbs_le_add_of_split hK₁ hsplit hg x).trans
    (add_le_add (convAbs_le_eLpNorm_mul_eLpNorm hK₁ hg hpq x)
      (convAbs_le_eLpNorm_top_mul hK₂ hg x))

set_option linter.unusedVariables false in
/-- Split kernel, `L^p(A)` bound:`‖|K| ⋆ |g|‖_{L^p(A)} ≤ ‖K₁‖₁ ‖g‖_p + |A|^{1/p} ‖K₂‖_∞ ‖g‖₁`. -/
theorem eLpNorm_convAbs_split_le {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] {K : ℂ → E} {K₁ : ℂ → E₁} {K₂ : ℂ → E₂}
    (hK₁ : MemLp K₁ 1 volume) (hK₂ : MemLp K₂ ⊤ volume) (hsplit : ∀ z, ‖K z‖ ≤ ‖K₁ z‖ + ‖K₂ z‖)
    {g : ℂ → F} (hg : AEStronglyMeasurable g volume) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (A : Set ℂ) :
    eLpNorm (convAbs K g) p (volume.restrict A) ≤
      eLpNorm K₁ 1 volume * eLpNorm g p volume +
        volume A ^ (1 / p.toReal) * (eLpNorm K₂ ⊤ volume * eLpNorm g 1 volume) := by
  have m1 : AEStronglyMeasurable (convAbs K₁ g) (volume.restrict A) :=
    (aemeasurable_convAbs hK₁.1 hg).aestronglyMeasurable.restrict
  have m2 : AEStronglyMeasurable (convAbs K₂ g) (volume.restrict A) :=
    (aemeasurable_convAbs hK₂.1 hg).aestronglyMeasurable.restrict
  calc eLpNorm (convAbs K g) p (volume.restrict A)
      ≤ eLpNorm (convAbs K₁ g + convAbs K₂ g) p (volume.restrict A) := by
        refine eLpNorm_mono_enorm fun x => ?_
        rw [enorm_eq_self, enorm_eq_self]
        exact convAbs_le_add_of_split hK₁.1 hsplit hg x
    _ ≤ eLpNorm (convAbs K₁ g) p (volume.restrict A) +
          eLpNorm (convAbs K₂ g) p (volume.restrict A) := eLpNorm_add_le m1 m2 hp
    _ ≤ _ := by
        gcongr
        · calc eLpNorm (convAbs K₁ g) p (volume.restrict A)
              ≤ eLpNorm (convAbs K₁ g) p volume :=
                eLpNorm_mono_measure _ Measure.restrict_le_self
            _ ≤ (∫⁻ z, ‖K₁ z‖ₑ) * eLpNorm g p volume := eLpNorm_convAbs_le hK₁.1 hg hp
            _ = eLpNorm K₁ 1 volume * eLpNorm g p volume := by
                rw [eLpNorm_one_eq_lintegral_enorm]
        · refine (eLpNorm_le_of_ae_enorm_bound
            (C := eLpNorm K₂ ⊤ volume * eLpNorm g 1 volume)
            (Eventually.of_forall fun x => ?_)).trans_eq ?_
          · rw [enorm_eq_self]
            exact convAbs_le_eLpNorm_top_mul hK₂.1 hg x
          · rw [Measure.restrict_apply_univ, smul_eq_mul, mul_comm, one_div]

end NonUniqueEuler.Conv
