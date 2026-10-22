import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helper for `P/Sec2/HkCalculus`: weak derivatives, complex conjugation and real parts

Generic facts on an arbitrary set `V ⊆ ℂ` (the helper `H/Infra/Sobolev/Symmetry/ChainRule.lean`
has the case `V = univ`; copied and generalized here):
* `hasWeakDerivOn_conj`: `∂_{vs} (conj f) = conj (∂_{vs} f)` weakly on `V`;
* `hasWeakDerivOn_re`: `∂_{vs} (Re f) = Re (∂_{vs} f)` weakly on an open `V`;
* `ae_im_eq_zero_of_hasWeakDerivOn`: weak derivatives of real functions are real a.e.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff ComplexConjugate

namespace NonUniqueEuler.Sob.HkCalcAux

theorem iterDirDeriv_conj {V : Set ℂ} {φ : ℂ → ℂ} (hφ : IsTestFn V φ) (vs : List ℂ) :
    iterDirDeriv vs (fun x => conj (φ x)) = fun x => conj (iterDirDeriv vs φ x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    simp only [iterDirDeriv_cons]
    rw [ih]
    have hd : DifferentiableAt ℝ (iterDirDeriv vs φ) x :=
      ((hφ.iterDirDeriv vs).smooth.differentiable (by simp)) x
    have h2 := (Complex.conjCLE.hasFDerivAt (x := iterDirDeriv vs φ x)).comp x hd.hasFDerivAt
    show fderiv ℝ (Complex.conjCLE ∘ iterDirDeriv vs φ) x v = _
    rw [h2.fderiv]
    rfl

theorem isTestFn_conj {V : Set ℂ} {φ : ℂ → ℂ} (hφ : IsTestFn V φ) :
    IsTestFn V (fun x => conj (φ x)) := by
  refine ⟨Complex.conjCLE.contDiff.comp hφ.smooth,
    hφ.compact.comp_left (g := conj) (map_zero _), ?_⟩
  exact (tsupport_comp_subset (g := conj) (map_zero _) φ).trans hφ.subset

/-- `∂_{vs} (conj f) = conj (∂_{vs} f)` weakly on `V`. -/
theorem hasWeakDerivOn_conj {V : Set ℂ} {vs : List ℂ} {f g : ℂ → ℂ}
    (h : HasWeakDerivOn V vs f g) :
    HasWeakDerivOn V vs (fun x => conj (f x)) (fun x => conj (g x)) := by
  intro φ hφ
  have hψ := isTestFn_conj hφ
  have k := h _ hψ
  have e1 : iterDirDeriv vs φ = fun x => conj (iterDirDeriv vs (fun x => conj (φ x)) x) := by
    rw [iterDirDeriv_conj hφ]
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

/-- Local integrability is preserved by a continuous linear map. -/
theorem locInt_clm {V : Set ℂ} {f : ℂ → ℂ} (hf : LocallyIntegrableOn f V)
    (L : ℂ →L[ℝ] ℂ) : LocallyIntegrableOn (fun x => L (f x)) V := by
  intro x hx
  obtain ⟨t, ht, hi⟩ := hf x hx
  exact ⟨t, ht, L.integrable_comp hi⟩

theorem locInt_conj {V : Set ℂ} {f : ℂ → ℂ} (hf : LocallyIntegrableOn f V) :
    LocallyIntegrableOn (fun x => conj (f x)) V :=
  locInt_clm hf Complex.conjCLE.toContinuousLinearMap

theorem locInt_re {V : Set ℂ} {f : ℂ → ℂ} (hf : LocallyIntegrableOn f V) :
    LocallyIntegrableOn (fun x => ((f x).re : ℂ)) V :=
  locInt_clm hf (Complex.ofRealCLM.comp Complex.reCLM)

theorem locInt_im {V : Set ℂ} {f : ℂ → ℂ} (hf : LocallyIntegrableOn f V) :
    LocallyIntegrableOn (fun x => ((f x).im : ℂ)) V :=
  locInt_clm hf (Complex.ofRealCLM.comp Complex.imCLM)

/-- `∂_{vs} (Re f) = Re (∂_{vs} f)` weakly on an open set. -/
theorem hasWeakDerivOn_re {V : Set ℂ} (hV : IsOpen V) {vs : List ℂ} {f g : ℂ → ℂ}
    (hf : LocallyIntegrableOn f V) (hg : LocallyIntegrableOn g V)
    (h : HasWeakDerivOn V vs f g) :
    HasWeakDerivOn V vs (fun x => ((f x).re : ℂ)) (fun x => ((g x).re : ℂ)) := by
  have h1 := HasWeakDerivOn.add hV hf (locInt_conj hf) hg (locInt_conj hg) h (hasWeakDerivOn_conj h)
  have h2 := h1.const_mul (1 / 2 : ℂ)
  have ef : (fun x => (1 / 2 : ℂ) * (f + fun x => conj (f x)) x) =
      fun x => ((f x).re : ℂ) := by
    funext x; simp only [Pi.add_apply]; rw [Complex.re_eq_add_conj]; ring
  have eg : (fun x => (1 / 2 : ℂ) * (g + fun x => conj (g x)) x) =
      fun x => ((g x).re : ℂ) := by
    funext x; simp only [Pi.add_apply]; rw [Complex.re_eq_add_conj]; ring
  rw [ef, eg] at h2
  exact h2

/-- Weak derivatives of real functions are real a.e. on an open set. -/
theorem ae_im_eq_zero_of_hasWeakDerivOn {V : Set ℂ} (hV : IsOpen V) {vs : List ℂ}
    {f g : ℂ → ℂ} (hg : LocallyIntegrableOn g V) (h : HasWeakDerivOn V vs f g)
    (hreal : ∀ᵐ x, x ∈ V → (f x).im = 0) : ∀ᵐ x, x ∈ V → (g x).im = 0 := by
  have h1 := hasWeakDerivOn_conj h
  have h2 : HasWeakDerivOn V vs f (fun x => conj (g x)) := by
    refine h1.congr_ae ?_ (Filter.Eventually.of_forall fun _ _ => rfl)
    filter_upwards [hreal] with x hx hxV
    exact Complex.conj_eq_iff_im.2 (hx hxV)
  have h3 := HasWeakDerivOn.ae_eq hV hg (locInt_conj hg) h h2
  filter_upwards [h3] with x hx hxV
  exact Complex.conj_eq_iff_im.1 (hx hxV).symm

end NonUniqueEuler.Sob.HkCalcAux
