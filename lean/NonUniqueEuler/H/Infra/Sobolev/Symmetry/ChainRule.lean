import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper: weak derivatives under changes of variables (for `P/Infra/Sobolev/Symmetry`)

Generic facts about `HasWeakDerivOn univ` on the plane:
* `iterDirDeriv_comp`: `∂_{vs} (ψ ∘ T) = (∂_{L vs} ψ) ∘ T` when `DT ≡ L`;
* `hasWeakDerivOn_comp`: the chain rule for weak derivatives under a map `T` with constant
  derivative `L`, a smooth inverse, and `T_* vol = ν • vol`;
* `memLp_comp`, `eLpNorm_comp`: the `L²` norm under such a `T`;
* `hasWeakDerivOn_cons_add`: linearity of weak derivatives in the first direction;
* `hasWeakDerivOn_map_smul`: `∂_{r vs} f = r^{|vs|} ∂_{vs} f`;
* `hasWeakDerivOn_conj`: `∂_{vs} (conj f) = conj (∂_{vs} f)`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff ComplexConjugate

namespace NonUniqueEuler.Sob.SymmAux

/-! ### Smoothness of iterated directional derivatives -/

theorem contDiff_dirDeriv {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (v : ℂ) :
    ContDiff ℝ ∞ (dirDeriv v φ) :=
  (ContDiff.fderiv_right (m := ∞) h (by simp)).clm_apply contDiff_const

theorem contDiff_iterDirDeriv {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (vs : List ℂ) :
    ContDiff ℝ ∞ (iterDirDeriv vs φ) := by
  induction vs with
  | nil => simpa using h
  | cons v vs ih => simpa using contDiff_dirDeriv ih v

theorem differentiable_iterDirDeriv {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (vs : List ℂ) :
    Differentiable ℝ (iterDirDeriv vs φ) :=
  (contDiff_iterDirDeriv h vs).differentiable (by simp)

/-! ### Chain rule for classical directional derivatives -/

/-- `∂_{vs} (ψ ∘ T) = (∂_{L vs} ψ) ∘ T` for a map `T` with constant derivative `L`. -/
theorem iterDirDeriv_comp {T : ℂ → ℂ} {L : ℂ →L[ℝ] ℂ} (hT : ∀ x, HasFDerivAt T L x)
    {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (vs : List ℂ) :
    iterDirDeriv vs (fun x => ψ (T x)) = fun x => iterDirDeriv (vs.map L) ψ (T x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    simp only [iterDirDeriv_cons, List.map_cons]
    rw [ih]
    have hG := (differentiable_iterDirDeriv hψ (vs.map L)) (T x)
    have h2 := hG.hasFDerivAt.comp x (hT x)
    show fderiv ℝ ((iterDirDeriv (vs.map L) ψ) ∘ T) x v =
      fderiv ℝ (iterDirDeriv (vs.map L) ψ) (T x) (L v)
    rw [h2.fderiv]
    rfl

/-- Transport of a test function by a smooth map `S` with a continuous left inverse `T`. -/
theorem isTestFn_comp {T S : ℂ → ℂ} (hTc : Continuous T) (hS : ContDiff ℝ ∞ S)
    (hTS : ∀ y, T (S y) = y) {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) :
    IsTestFn univ (fun y => φ (S y)) := by
  refine ⟨hφ.smooth.comp hS, ?_, subset_univ _⟩
  refine HasCompactSupport.intro (hφ.compact.image hTc) (fun y hy => ?_)
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact hy ⟨S y, h, hTS y⟩

/-- Change of variables in a Bochner integral when `T_* vol = ν • vol`. -/
theorem integral_comp_of_map {T : ℂ → ℂ} (hT : MeasurableEmbedding T) {ν : ℝ≥0∞}
    (hmap : Measure.map T volume = ν • volume) (h : ℂ → ℂ) :
    ∫ x, h (T x) = (ν.toReal : ℂ) * ∫ y, h y := by
  rw [← hT.integral_map h, hmap, integral_smul_measure, Complex.real_smul]

/-- The chain rule for weak derivatives under a change of variables `T` with constant
derivative `L`, smooth inverse `S`, and `T_* vol = ν • vol`. -/
theorem hasWeakDerivOn_comp {T S : ℂ → ℂ} {L : ℂ →L[ℝ] ℂ} (hT : ∀ x, HasFDerivAt T L x)
    (hS : ContDiff ℝ ∞ S) (hST : ∀ x, S (T x) = x) (hTS : ∀ y, T (S y) = y)
    (hTm : MeasurableEmbedding T) {ν : ℝ≥0∞} (hmap : Measure.map T volume = ν • volume)
    {vs : List ℂ} {f g : ℂ → ℂ} (h : HasWeakDerivOn univ (vs.map L) f g) :
    HasWeakDerivOn univ vs (fun x => f (T x)) (fun x => g (T x)) := by
  intro φ hφ
  have hTc : Continuous T := continuous_iff_continuousAt.2 fun x => (hT x).continuousAt
  have hψ : IsTestFn univ (fun y => φ (S y)) := isTestFn_comp hTc hS hTS hφ
  have hφψ : φ = fun x => (fun y => φ (S y)) (T x) := by
    funext x
    simp only [hST]
  have key := h _ hψ
  rw [List.length_map] at key
  have e1 := integral_comp_of_map hTm hmap
    (fun y => f y * iterDirDeriv (vs.map L) (fun y => φ (S y)) y)
  have e2 := integral_comp_of_map hTm hmap (fun y => g y * φ (S y))
  have e3 := iterDirDeriv_comp hT hψ.smooth vs
  rw [← hφψ] at e3
  rw [e3]
  have e4 : ∫ x, g (T x) * φ x = ∫ x, g (T x) * φ (S (T x)) := by simp only [hST]
  rw [e4, e1, e2, key]
  ring

/-! ### `L²` norms under a change of variables -/

theorem memLp_comp {T : ℂ → ℂ} (hT : MeasurableEmbedding T) {ν : ℝ≥0∞} (hν : ν ≠ ⊤)
    (hmap : Measure.map T volume = ν • volume) {g : ℂ → ℂ} (hg : MemLp g 2 volume) :
    MemLp (fun x => g (T x)) 2 volume := by
  have h1 : MemLp g 2 (Measure.map T volume) := by
    rw [hmap]
    exact hg.smul_measure hν
  exact hT.memLp_map_measure_iff.1 h1

theorem eLpNorm_comp {T : ℂ → ℂ} (hT : MeasurableEmbedding T) {ν : ℝ≥0∞} (hν : ν ≠ 0)
    (hmap : Measure.map T volume = ν • volume) (g : ℂ → ℂ) :
    eLpNorm (fun x => g (T x)) 2 volume = ν ^ (1 / 2 : ℝ) * eLpNorm g 2 volume := by
  have h1 := hT.eLpNorm_map_measure (g := g) (p := 2) (μ := volume)
  rw [hmap, eLpNorm_smul_measure_of_ne_zero hν] at h1
  rw [← show (g ∘ T) = fun x => g (T x) from rfl, ← h1]
  simp [smul_eq_mul]

/-- `‖g ∘ T‖²_{L²} = ν ‖g‖²_{L²}`. -/
theorem l2_comp_sq {T : ℂ → ℂ} (hT : MeasurableEmbedding T) {ν : ℝ≥0∞} (hν : ν ≠ 0)
    (hmap : Measure.map T volume = ν • volume) (g : ℂ → ℂ) :
    l2 (fun x => g (T x)) ^ 2 = ν.toReal * l2 g ^ 2 := by
  unfold l2
  have e : (ν ^ (1 / 2 : ℝ)) ^ 2 = ν := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [eLpNorm_comp hT hν hmap, ENNReal.toReal_mul, mul_pow, ← ENNReal.toReal_pow, e]

/-! ### Integrability against test functions -/

theorem integrable_mul_testFn {g φ : ℂ → ℂ} (hg : LocallyIntegrableOn g univ)
    (hφ : IsTestFn univ φ) : Integrable (fun x => g x * φ x) := by
  have hK : IsCompact (tsupport φ) := hφ.compact
  have h1 : IntegrableOn g (tsupport φ) := hg.integrableOn_compact_subset hφ.subset hK
  have h2 : IntegrableOn (fun x => g x * φ x) (tsupport φ) :=
    h1.mul_continuousOn hφ.continuous.continuousOn hK
  refine h2.integrable_of_forall_notMem_eq_zero (fun x hx => ?_)
  simp [image_eq_zero_of_notMem_tsupport hx]

/-! ### Linearity in the directions -/

theorem iterDirDeriv_cons_add {φ : ℂ → ℂ} (u w : ℂ) (a b : ℝ) (vs : List ℂ) (x : ℂ) :
    iterDirDeriv ((a • u + b • w) :: vs) φ x =
      (a : ℂ) * iterDirDeriv (u :: vs) φ x + (b : ℂ) * iterDirDeriv (w :: vs) φ x := by
  simp only [iterDirDeriv_cons, dirDeriv, map_add, map_smul]
  simp only [Complex.real_smul]

/-- Linearity of weak derivatives in the first direction. -/
theorem hasWeakDerivOn_cons_add {u w : ℂ} {vs : List ℂ} {f g₁ g₂ : ℂ → ℂ}
    (hf : LocallyIntegrableOn f univ) (hg₁ : LocallyIntegrableOn g₁ univ)
    (hg₂ : LocallyIntegrableOn g₂ univ) (a b : ℝ)
    (h₁ : HasWeakDerivOn univ (u :: vs) f g₁) (h₂ : HasWeakDerivOn univ (w :: vs) f g₂) :
    HasWeakDerivOn univ ((a • u + b • w) :: vs) f
      (fun x => (a : ℂ) * g₁ x + (b : ℂ) * g₂ x) := by
  intro φ hφ
  have i1 := integrable_mul_testFn hf (hφ.iterDirDeriv (u :: vs))
  have i2 := integrable_mul_testFn hf (hφ.iterDirDeriv (w :: vs))
  have j1 := integrable_mul_testFn hg₁ hφ
  have j2 := integrable_mul_testFn hg₂ hφ
  have k1 := h₁ φ hφ
  have k2 := h₂ φ hφ
  simp only [List.length_cons] at k1 k2 ⊢
  have e1 : ∫ x, f x * iterDirDeriv ((a • u + b • w) :: vs) φ x =
      (a : ℂ) * (∫ x, f x * iterDirDeriv (u :: vs) φ x) +
        (b : ℂ) * (∫ x, f x * iterDirDeriv (w :: vs) φ x) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _)
      (i2.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [iterDirDeriv_cons_add]
    ring
  have e2 : ∫ x, ((a : ℂ) * g₁ x + (b : ℂ) * g₂ x) * φ x =
      (a : ℂ) * (∫ x, g₁ x * φ x) + (b : ℂ) * (∫ x, g₂ x * φ x) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (j1.const_mul _)
      (j2.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [e1, e2, k1, k2]
  ring

/-! ### Scaling of the directions -/

theorem iterDirDeriv_map_smul {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) (r : ℝ) (vs : List ℂ) :
    iterDirDeriv (vs.map fun v => r • v) φ =
      fun x => ((r ^ vs.length : ℝ) : ℂ) * iterDirDeriv vs φ x := by
  induction vs with
  | nil => funext x; simp
  | cons v vs ih =>
    funext x
    simp only [List.map_cons, iterDirDeriv_cons, List.length_cons]
    rw [ih]
    have hd := differentiable_iterDirDeriv hφ vs x
    show fderiv ℝ (fun y => ((r ^ vs.length : ℝ) : ℂ) * iterDirDeriv vs φ y) x (r • v) =
      _ * fderiv ℝ (iterDirDeriv vs φ) x v
    have hlin : ∀ w : ℂ, fderiv ℝ (iterDirDeriv vs φ) x ((r : ℂ) * w) =
        (r : ℂ) * fderiv ℝ (iterDirDeriv vs φ) x w := fun w => by
      have := (fderiv ℝ (iterDirDeriv vs φ) x).map_smul r w
      simpa [Complex.real_smul] using this
    rw [fderiv_const_mul hd]
    simp only [smul_apply, smul_eq_mul, Complex.real_smul]
    rw [hlin]
    push_cast
    ring

/-- `∂_{r vs} f = r^{|vs|} ∂_{vs} f` weakly. -/
theorem hasWeakDerivOn_map_smul {vs : List ℂ} {f g : ℂ → ℂ} (h : HasWeakDerivOn univ vs f g)
    (r : ℝ) :
    HasWeakDerivOn univ (vs.map fun v => r • v) f
      (fun x => ((r ^ vs.length : ℝ) : ℂ) * g x) := by
  intro φ hφ
  rw [iterDirDeriv_map_smul hφ.smooth, List.length_map]
  have k := h φ hφ
  simp only [mul_assoc, ← mul_left_comm (((r ^ vs.length : ℝ) : ℂ))]
  rw [integral_const_mul, integral_const_mul, k]
  ring

/-! ### Complex conjugation -/

theorem iterDirDeriv_conj {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) (vs : List ℂ) :
    iterDirDeriv vs (fun x => conj (φ x)) = fun x => conj (iterDirDeriv vs φ x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    simp only [iterDirDeriv_cons]
    rw [ih]
    have hd := differentiable_iterDirDeriv hφ vs x
    have h2 := (Complex.conjCLE.hasFDerivAt (x := iterDirDeriv vs φ x)).comp x hd.hasFDerivAt
    show fderiv ℝ (Complex.conjCLE ∘ iterDirDeriv vs φ) x v = _
    rw [h2.fderiv]
    rfl

theorem isTestFn_conj {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) :
    IsTestFn univ (fun x => conj (φ x)) := by
  refine ⟨Complex.conjCLE.contDiff.comp hφ.smooth, ?_, subset_univ _⟩
  exact hφ.compact.comp_left (g := conj) (map_zero _)

/-- `∂_{vs} (conj f) = conj (∂_{vs} f)` weakly. -/
theorem hasWeakDerivOn_conj {vs : List ℂ} {f g : ℂ → ℂ} (h : HasWeakDerivOn univ vs f g) :
    HasWeakDerivOn univ vs (fun x => conj (f x)) (fun x => conj (g x)) := by
  intro φ hφ
  have hψ := isTestFn_conj hφ
  have k := h _ hψ
  have e1 : iterDirDeriv vs φ = fun x => conj (iterDirDeriv vs (fun x => conj (φ x)) x) := by
    rw [iterDirDeriv_conj hφ.smooth]
    simp
  rw [e1]
  have e2 : ∫ x, conj (f x) * conj (iterDirDeriv vs (fun x => conj (φ x)) x) =
      conj (∫ x, f x * iterDirDeriv vs (fun x => conj (φ x)) x) := by
    rw [← integral_conj]
    simp
  have e3 : ∫ x, conj (g x) * φ x = conj (∫ x, g x * conj (φ x)) := by
    rw [← integral_conj]
    simp
  rw [e2, e3, k]
  simp

end NonUniqueEuler.Sob.SymmAux
