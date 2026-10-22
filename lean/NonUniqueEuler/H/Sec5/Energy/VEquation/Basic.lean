import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Helpers for `energy_vEquation` (the equation of `v = w - w_app`)

Helpers of `P/Sec5/Energy/VEquation.lean` (step 1 of the proof of `lem:energy`,
`05_single_ring.tex:318-331`). All fully proved.

* `VEqH.weakPartial_add_ae`, `VEqH.weakPartial_sub_ae`: the weak derivatives of `H^k` functions
  are additive a.e. (uniqueness of weak derivatives, `MemH.weakPartial_ae_eq`);
* `VEqH.memLp_one_re_im`: a function of `X^k` has real and imaginary parts in `L¹` (it is in
  `L²` and vanishes a.e. outside the compact annulus `N`);
* `VEqH.velocityRe_sub_apply`, `VEqH.velocityIm_sub_apply`: the Biot–Savart law is additive at
  every point where the integrals converge;
* `VEqH.integral_coupling_eq`: `∫ DΦ(x)(K_BS(x-y)) f(y) dy = DΦ(x)((K_BS * Re f)(x)) +
  i DΦ(x)((K_BS * Im f)(x))` where the integrals converge (`ContinuousLinearMap.integral_comp_comm`);
* `VEqH.dotGradPhi_eq`: the classical derivatives of `Φ` in `U·∇Φ`, `U₁∂₁Φ + U₂∂₂Φ = DΦ(x)U`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff

namespace NonUniqueEuler

namespace OneRing

namespace VEqH

open RingData

/-! ### Additivity of weak derivatives -/

theorem memLp_two_of_memH {k : ℕ} {f : ℂ → ℂ} (hf : Sob.MemH k f) : MemLp f 2 volume := by
  have h := (show Sob.MemHOn k univ f from hf).memLp
  rwa [Measure.restrict_univ] at h

theorem locIntOn_of_memLp_two {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    LocallyIntegrableOn f univ volume :=
  (hf.locallyIntegrable (by norm_num)).locallyIntegrableOn univ

theorem weakPartial_add_ae {k : ℕ} {f g : ℂ → ℂ} (hf : Sob.MemH k f) (hg : Sob.MemH k g)
    {γ : ℕ × ℕ} (hγ : γ ∈ Sob.multiIdx k) :
    Sob.weakPartial γ (f + g) =ᵐ[volume] Sob.weakPartial γ f + Sob.weakPartial γ g := by
  obtain ⟨hf2, hfd⟩ := hf.memLp_weakPartial hγ
  obtain ⟨hg2, hgd⟩ := hg.memLp_weakPartial hγ
  exact (hf.add hg).1.weakPartial_ae_eq hγ (hf2.add hg2)
    (Sob.HasWeakDerivOn.add isOpen_univ (locIntOn_of_memLp_two (memLp_two_of_memH hf))
      (locIntOn_of_memLp_two (memLp_two_of_memH hg)) (locIntOn_of_memLp_two hf2)
      (locIntOn_of_memLp_two hg2) hfd hgd)

theorem weakPartial_sub_ae {k : ℕ} {f g : ℂ → ℂ} (hf : Sob.MemH k f) (hg : Sob.MemH k g)
    {γ : ℕ × ℕ} (hγ : γ ∈ Sob.multiIdx k) :
    Sob.weakPartial γ (f - g) =ᵐ[volume] Sob.weakPartial γ f - Sob.weakPartial γ g := by
  obtain ⟨hf2, hfd⟩ := hf.memLp_weakPartial hγ
  obtain ⟨hg2, hgd⟩ := hg.memLp_weakPartial hγ
  have hng := hgd.const_mul (-1)
  have hng2 : MemLp (fun x => (-1 : ℂ) * Sob.weakPartial γ g x) 2 volume := hg2.const_mul _
  have hngL : MemLp (fun x => (-1 : ℂ) * g x) 2 volume := (memLp_two_of_memH hg).const_mul _
  have hadd := Sob.HasWeakDerivOn.add isOpen_univ (locIntOn_of_memLp_two (memLp_two_of_memH hf))
    (locIntOn_of_memLp_two hngL) (locIntOn_of_memLp_two hf2) (locIntOn_of_memLp_two hng2) hfd hng
  have e1 : (f + fun x => (-1 : ℂ) * g x) = f - g := by
    funext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
  have e2 : (Sob.weakPartial γ f + fun x => (-1 : ℂ) * Sob.weakPartial γ g x) =
      Sob.weakPartial γ f - Sob.weakPartial γ g := by
    funext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [e1, e2] at hadd
  exact (hf.sub hg).1.weakPartial_ae_eq hγ (hf2.sub hg2) hadd

/-! ### `X^k` functions are in `L¹` -/

theorem memLp_one_of_memXFn {k : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn k f) : MemLp f 1 volume := by
  have h2 : MemLp f 2 volume := memLp_two_of_memH hf.1
  have hfg : annN.indicator f =ᵐ[volume] f := by
    filter_upwards [hf.2.1] with x hx
    by_cases hxN : x ∈ annN
    · exact indicator_of_mem hxN f
    · rw [indicator_of_notMem hxN, hx hxN]
  have hg2 : MemLp (annN.indicator f) 2 volume := h2.ae_eq hfg.symm
  have hg1 : MemLp (annN.indicator f) 1 volume :=
    hg2.mono_exponent_of_measure_support_ne_top (s := annN)
      (fun x hx => indicator_of_notMem hx f)
      (Sect.isCompact_closedAnnulus _ _).measure_lt_top.ne (by norm_num)
  exact hg1.ae_eq hfg

theorem memLp_one_re_im {k : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn k f) :
    MemLp (fun y => (f y).re) 1 volume ∧ MemLp (fun y => (f y).im) 1 volume :=
  ⟨(memLp_one_of_memXFn hf).re, (memLp_one_of_memXFn hf).im⟩

/-! ### The Biot–Savart law at a point -/

theorem velocityRe_sub_apply {f g : ℂ → ℂ} {x : ℂ}
    (hf : Integrable (fun y => biotSavartKernel (x - y) * (((f y).re : ℝ) : ℂ)) volume)
    (hg : Integrable (fun y => biotSavartKernel (x - y) * (((g y).re : ℝ) : ℂ)) volume) :
    BS.velocityRe (f - g) x = BS.velocityRe f x - BS.velocityRe g x := by
  simp only [BS.velocityRe, velocity, Pi.sub_apply, Complex.sub_re, Complex.ofReal_sub, mul_sub]
  exact integral_sub hf hg

theorem velocityIm_sub_apply {f g : ℂ → ℂ} {x : ℂ}
    (hf : Integrable (fun y => biotSavartKernel (x - y) * (((f y).im : ℝ) : ℂ)) volume)
    (hg : Integrable (fun y => biotSavartKernel (x - y) * (((g y).im : ℝ) : ℂ)) volume) :
    BS.velocityIm (f - g) x = BS.velocityIm f x - BS.velocityIm g x := by
  simp only [BS.velocityIm, velocity, Pi.sub_apply, Complex.sub_im, Complex.ofReal_sub, mul_sub]
  exact integral_sub hf hg

/-- The coupling integral in terms of the Biot–Savart velocities of `Re f` and `Im f`, where the
integrals converge. -/
theorem integral_coupling_eq (D : ℂ →L[ℝ] ℝ) {f : ℂ → ℂ} {x : ℂ}
    (hre : Integrable (fun y => biotSavartKernel (x - y) * (((f y).re : ℝ) : ℂ)) volume)
    (him : Integrable (fun y => biotSavartKernel (x - y) * (((f y).im : ℝ) : ℂ)) volume) :
    ∫ y, ((D (biotSavartKernel (x - y)) : ℝ) : ℂ) * f y =
      ((D (BS.velocityRe f x) : ℝ) : ℂ) + Complex.I * ((D (BS.velocityIm f x) : ℝ) : ℂ) := by
  have e : ∀ (r : ℝ) (u : ℂ), D (u * (r : ℂ)) = r * D u := fun r u => by
    rw [mul_comm, ← Complex.real_smul, D.map_smul, smul_eq_mul]
  have h1 : Integrable (fun y => ((D (biotSavartKernel (x - y) * (((f y).re : ℝ) : ℂ)) : ℝ) : ℂ))
      volume := (D.integrable_comp hre).ofReal
  have h2 : Integrable (fun y => Complex.I *
      ((D (biotSavartKernel (x - y) * (((f y).im : ℝ) : ℂ)) : ℝ) : ℂ)) volume :=
    ((D.integrable_comp him).ofReal).const_mul Complex.I
  have hpt : (fun y => ((D (biotSavartKernel (x - y)) : ℝ) : ℂ) * f y) = fun y =>
      ((D (biotSavartKernel (x - y) * (((f y).re : ℝ) : ℂ)) : ℝ) : ℂ) +
        Complex.I * ((D (biotSavartKernel (x - y) * (((f y).im : ℝ) : ℂ)) : ℝ) : ℂ) := by
    funext y
    rw [e, e]
    push_cast
    conv_lhs => rw [← Complex.re_add_im (f y)]
    ring
  rw [hpt, integral_add h1 h2, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
    D.integral_comp_comm hre, D.integral_comp_comm him]
  rfl

/-! ### The classical derivatives of `Φ` -/

theorem partialD_one_zero (f : ℂ → ℂ) (x : ℂ) : Sob.partialD (1, 0) f x = fderiv ℝ f x 1 := by
  simp [Sob.partialD, Sob.pdList, Sob.iterDirDeriv, Sob.dirDeriv]

theorem partialD_zero_one (f : ℂ → ℂ) (x : ℂ) :
    Sob.partialD (0, 1) f x = fderiv ℝ f x Complex.I := by
  simp [Sob.partialD, Sob.pdList, Sob.iterDirDeriv, Sob.dirDeriv]

theorem PhiC_eq_comp (χ : ℝ → ℝ) : PhiC χ = Complex.ofRealCLM ∘ ringPhi χ := by
  funext y
  simp [PhiC]

/-- `U₁ ∂₁Φ(x) + U₂ ∂₂Φ(x) = DΦ(x) U` with the classical derivatives of the complexified `Φ`. -/
theorem dotGradPhi_eq {χ : ℝ → ℝ} (hd : Differentiable ℝ (ringPhi χ)) (x U : ℂ) :
    ((U.re : ℝ) : ℂ) * Sob.partialD (1, 0) (PhiC χ) x +
        ((U.im : ℝ) : ℂ) * Sob.partialD (0, 1) (PhiC χ) x =
      ((fderiv ℝ (ringPhi χ) x U : ℝ) : ℂ) := by
  have hF : HasFDerivAt (PhiC χ) (Complex.ofRealCLM.comp (fderiv ℝ (ringPhi χ) x)) x := by
    rw [PhiC_eq_comp]
    exact Complex.ofRealCLM.hasFDerivAt.comp x (hd x).hasFDerivAt
  rw [partialD_one_zero, partialD_zero_one, hF.fderiv]
  have hU : U = U.re • (1 : ℂ) + U.im • Complex.I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
  conv_rhs => rw [hU]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, map_add, map_smul,
    smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]

/-- `Φ ∈ H^k` and its weak derivatives are the classical ones a.e. -/
theorem memH_PhiC {χ : ℝ → ℝ} (hs : ContDiff ℝ ∞ (ringPhi χ)) (hc : HasCompactSupport (ringPhi χ))
    (k : ℕ) :
    Sob.MemH k (PhiC χ) ∧
      ∀ γ ∈ Sob.multiIdx k, Sob.weakPartial γ (PhiC χ) =ᵐ[volume] Sob.partialD γ (PhiC χ) := by
  have hs' : ContDiff ℝ ∞ (PhiC χ) := by
    rw [PhiC_eq_comp]
    exact Complex.ofRealCLM.contDiff.comp hs
  have hc' : HasCompactSupport (PhiC χ) := by
    rw [PhiC_eq_comp]
    exact hc.comp_left (by simp)
  obtain ⟨h1, h2, -⟩ := Sob.memH_of_contDiff_hasCompactSupport hs' hc' k
  exact ⟨h1, h2⟩

end VEqH

end OneRing

end NonUniqueEuler
