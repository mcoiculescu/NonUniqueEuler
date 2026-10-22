import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import NonUniqueEuler.Defs.Infra.Sobolev
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv

/-!
# Proof: real and imaginary parts in `H^k` (library I-HK)

Proof of `NonUniqueEuler/I/Infra/Sobolev/ReIm.lean` (same declaration, same statement).

Manuscript: `02_prelim.tex:58-64` (the `H^k` norm of a complex function sums over its real
entries).

* `ReImAux.hasWeakDerivOn_conj`: `∂_{vs} (conj f) = conj (∂_{vs} f)` weakly (conjugation commutes
  with directional derivatives of test functions, `integral_conj`); the conjugation lemmas are
  copied from `H/Sec2/HkCalculus/ReIm.lean`, in a separate namespace.
* `ReImAux.hasWeakDerivOn_re_univ`, `ReImAux.hasWeakDerivOn_im_univ`: `Re f = (f + conj f)/2`
  and `Im f = Re (-i f)`, linearity of weak derivatives (`I/Infra/Sobolev/WeakDeriv.lean`).
* `ReImAux.l2_re_sq_add_l2_im_sq`: `‖Re g‖²_{L²} + ‖Im g‖²_{L²} = ‖g‖²_{L²}`.
* The `H^k` identity: `∂^γ Re f = Re ∂^γ f` a.e. (`MemH.weakPartial_ae_eq`,
  `I/Infra/Sobolev/NormDeriv.lean`), then sum over `γ ∈ multiIdx k`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff ComplexConjugate

namespace NonUniqueEuler.Sob

namespace ReImAux

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

/-- `∂_{vs} (Re f) = Re (∂_{vs} f)` weakly on an open set. -/
theorem hasWeakDerivOn_re {V : Set ℂ} (hV : IsOpen V) {vs : List ℂ} {f g : ℂ → ℂ}
    (hf : LocallyIntegrableOn f V) (hg : LocallyIntegrableOn g V)
    (h : HasWeakDerivOn V vs f g) :
    HasWeakDerivOn V vs (fun x => ((f x).re : ℂ)) (fun x => ((g x).re : ℂ)) := by
  have h1 :=
    HasWeakDerivOn.add hV hf (locInt_conj hf) hg (locInt_conj hg) h (hasWeakDerivOn_conj h)
  have h2 := h1.const_mul (1 / 2 : ℂ)
  have ef : (fun x => (1 / 2 : ℂ) * (f + fun x => conj (f x)) x) =
      fun x => ((f x).re : ℂ) := by
    funext x; simp only [Pi.add_apply]; rw [Complex.re_eq_add_conj]; ring
  have eg : (fun x => (1 / 2 : ℂ) * (g + fun x => conj (g x)) x) =
      fun x => ((g x).re : ℂ) := by
    funext x; simp only [Pi.add_apply]; rw [Complex.re_eq_add_conj]; ring
  rw [ef, eg] at h2
  exact h2

theorem locInt_of_memLp {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    LocallyIntegrableOn f univ :=
  (hf.locallyIntegrable (by norm_num)).locallyIntegrableOn univ

/-- `∂_{vs} (Re f) = Re (∂_{vs} f)` weakly on the plane, for `L²` functions. -/
theorem hasWeakDerivOn_re_univ {vs : List ℂ} {f g : ℂ → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (h : HasWeakDerivOn univ vs f g) :
    HasWeakDerivOn univ vs (fun x => ((f x).re : ℂ)) (fun x => ((g x).re : ℂ)) :=
  hasWeakDerivOn_re isOpen_univ (locInt_of_memLp hf) (locInt_of_memLp hg) h

theorem im_eq_re_neg_I_mul (z : ℂ) : ((-Complex.I * z).re : ℂ) = (z.im : ℂ) := by
  simp

/-- `∂_{vs} (Im f) = Im (∂_{vs} f)` weakly on the plane, for `L²` functions. -/
theorem hasWeakDerivOn_im_univ {vs : List ℂ} {f g : ℂ → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (h : HasWeakDerivOn univ vs f g) :
    HasWeakDerivOn univ vs (fun x => ((f x).im : ℂ)) (fun x => ((g x).im : ℂ)) := by
  have h1 := hasWeakDerivOn_re_univ (hf.const_mul (-Complex.I)) (hg.const_mul (-Complex.I))
    (h.const_mul (-Complex.I))
  simpa only [im_eq_re_neg_I_mul] using h1

theorem memLp_re {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (fun x => ((f x).re : ℂ)) 2 volume := by
  have h := hf.re.ofReal (K := ℂ)
  simpa using h

theorem memLp_im {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (fun x => ((f x).im : ℂ)) 2 volume := by
  have h := hf.im.ofReal (K := ℂ)
  simpa using h

/-- `‖g‖²_{L²} = ∫ |g|²`. -/
theorem l2_sq_eq {g : ℂ → ℂ} (hg : MemLp g 2 volume) : l2 g ^ 2 = ∫ x, ‖g x‖ ^ 2 := by
  have h := hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have hnn : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ≥0∞).toReal := integral_nonneg (fun x => by positivity)
  unfold l2
  rw [h, ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat] at hnn ⊢
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num

/-- `‖Re g‖²_{L²} + ‖Im g‖²_{L²} = ‖g‖²_{L²}`. -/
theorem l2_re_sq_add_l2_im_sq {g : ℂ → ℂ} (hg : MemLp g 2 volume) :
    l2 (fun x => ((g x).re : ℂ)) ^ 2 + l2 (fun x => ((g x).im : ℂ)) ^ 2 = l2 g ^ 2 := by
  rw [l2_sq_eq (memLp_re hg), l2_sq_eq (memLp_im hg), l2_sq_eq hg]
  have i1 : Integrable (fun x => (g x).re ^ 2) volume := by
    simpa using hg.re.integrable_sq
  have i2 : Integrable (fun x => (g x).im ^ 2) volume := by
    simpa using hg.im.integrable_sq
  have e1 : (fun x => ‖((g x).re : ℂ)‖ ^ 2) = fun x => (g x).re ^ 2 := by
    funext x; simp [Complex.norm_real]
  have e2 : (fun x => ‖((g x).im : ℂ)‖ ^ 2) = fun x => (g x).im ^ 2 := by
    funext x; simp [Complex.norm_real]
  have e3 : (fun x => ‖g x‖ ^ 2) = fun x => (g x).re ^ 2 + (g x).im ^ 2 := by
    funext x; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [e1, e2, e3, integral_add i1 i2]

theorem l2_congr_ae {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) : l2 f = l2 g := by
  unfold l2
  rw [eLpNorm_congr_ae h]

theorem normH_sq_eq (k : ℕ) (f : ℂ → ℂ) :
    normH k f ^ 2 = ∑ γ ∈ multiIdx k, l2 (weakPartial γ f) ^ 2 := by
  rw [normH_eq, Real.sq_sqrt (Finset.sum_nonneg fun γ _ => sq_nonneg _)]

end ReImAux

open ReImAux in
/-- The real and imaginary parts of an `H^k` function lie in `H^k`, and
`‖Re f‖²_{H^k} + ‖Im f‖²_{H^k} = ‖f‖²_{H^k}`. -/
theorem MemH.re_im {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) :
    MemH k (fun x => ((f x).re : ℂ)) ∧ MemH k (fun x => ((f x).im : ℂ)) ∧
      normH k (fun x => ((f x).re : ℂ)) ^ 2 + normH k (fun x => ((f x).im : ℂ)) ^ 2 =
        normH k f ^ 2 := by
  have hfL : MemLp f 2 volume := (memH_iff.1 hf).1
  have hre : MemH k (fun x => ((f x).re : ℂ)) := by
    refine memH_iff.2 ⟨memLp_re hfL, fun γ hγ => ?_⟩
    obtain ⟨hgL, hgD⟩ := hf.memLp_weakPartial hγ
    exact ⟨_, memLp_re hgL, hasWeakDerivOn_re_univ hfL hgL hgD⟩
  have him : MemH k (fun x => ((f x).im : ℂ)) := by
    refine memH_iff.2 ⟨memLp_im hfL, fun γ hγ => ?_⟩
    obtain ⟨hgL, hgD⟩ := hf.memLp_weakPartial hγ
    exact ⟨_, memLp_im hgL, hasWeakDerivOn_im_univ hfL hgL hgD⟩
  refine ⟨hre, him, ?_⟩
  rw [normH_sq_eq, normH_sq_eq, normH_sq_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  obtain ⟨hgL, hgD⟩ := hf.memLp_weakPartial hγ
  have a1 := hre.weakPartial_ae_eq hγ (memLp_re hgL) (hasWeakDerivOn_re_univ hfL hgL hgD)
  have a2 := him.weakPartial_ae_eq hγ (memLp_im hgL) (hasWeakDerivOn_im_univ hfL hgL hgD)
  rw [l2_congr_ae a1, l2_congr_ae a2]
  exact l2_re_sq_add_l2_im_sq hgL

end NonUniqueEuler.Sob
