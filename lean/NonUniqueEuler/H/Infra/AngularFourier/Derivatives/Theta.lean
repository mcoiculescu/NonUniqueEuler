import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import NonUniqueEuler.H.Infra.AngularFourier.Derivatives.Basic
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives.SmoothSector

/-!
# Helpers for `P/Infra/AngularFourier/Derivatives`: `P_ℓ (∂_θ g) = iℓ P_ℓ g`

Duality argument (instead of integrating by parts in `φ` and using density). For a real test
function `ψ`:
1. `χ = conj (P_ℓ ψ)` is a test function (`contDiff_sectorProj`,
   `I/Infra/AngularFourier/Derivatives/SmoothSector.lean`; supports are rotation invariant), and
   classically `x₁ ∂₂χ - x₂ ∂₁χ = -iℓ χ` (differentiate `P_ℓ ψ (O_φ x) = e^{iℓφ} P_ℓ ψ (x)` at
   `φ = 0`, `sectorProj_rot`).
2. Weak derivatives: `∫ χ ∂_θ g = -∫ g (x₁ ∂₂χ - x₂ ∂₁χ)` (`integral_mul_thetaDeriv`).
3. Self-adjointness of `P_ℓ` (`DerivAux.integral_conj_mul_sectorProj`), applied with the weight
   `w = 1 + |x|` (`w⁻¹ ∂_θ g ∈ L²`, `P_ℓ` commutes with `w`), gives
   `∫ ψ P_ℓ(∂_θ g) = ∫ χ ∂_θ g = iℓ ∫ χ g = iℓ ∫ ψ P_ℓ g`.
4. The fundamental lemma (`DerivAux.ae_eq_zero_of_integral_real_testFn`).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal ComplexConjugate ContDiff

namespace NonUniqueEuler.Ang

namespace DerivAux

/-! ### `P_ℓ ψ` for test functions `ψ` -/

theorem hasCompactSupport_sectorProj {ψ : ℂ → ℂ} (hψ : HasCompactSupport ψ) (m : ℤ) :
    HasCompactSupport (sectorProj m ψ) := by
  obtain ⟨R, hR⟩ := hψ.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx => ?_
  have h0 : ∀ φ : ℝ, ψ (rot φ x) = 0 := by
    intro φ
    refine image_eq_zero_of_notMem_tsupport fun hmem => hx ?_
    have := hR hmem
    rwa [Metric.mem_closedBall, dist_zero_right, Polar.norm_rot,
      ← dist_zero_right] at this
  simp [sectorProj, h0]

theorem isTestFn_conj_sectorProj {ψ : ℂ → ℂ} (hψ : Sob.IsTestFn univ ψ) (m : ℤ) :
    Sob.IsTestFn univ (fun x => conj (sectorProj m ψ x)) := by
  refine ⟨?_, ?_, subset_univ _⟩
  · have := (Complex.conjCLE.contDiff (n := ∞)).comp (contDiff_sectorProj hψ.smooth m)
    simpa [Function.comp_def] using this
  · exact (hasCompactSupport_sectorProj hψ.compact m).comp_left (by simp)

theorem hasDerivAt_rot (x : ℂ) :
    HasDerivAt (fun φ : ℝ => rot φ x) (Complex.I * x) 0 := by
  have h1 : HasDerivAt (fun φ : ℝ => (φ : ℂ) * Complex.I) (1 * Complex.I) 0 :=
    ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I
  have h2 := (h1.cexp).mul_const x
  simpa [rot] using h2

/-- `D(P_m ψ)(x)(i x) = i m P_m ψ (x)`. -/
theorem fderiv_sectorProj_I_mul {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (m : ℤ) (x : ℂ) :
    fderiv ℝ (sectorProj m ψ) x (Complex.I * x) = ((m : ℂ) * Complex.I) * sectorProj m ψ x := by
  set P := sectorProj m ψ
  have hP : Differentiable ℝ P := (contDiff_sectorProj hψ m).differentiable (by simp)
  have hl : HasFDerivAt P (fderiv ℝ P (rot 0 x)) (rot 0 x) := (hP _).hasFDerivAt
  have h1 := hl.comp_hasDerivAt (0 : ℝ) (hasDerivAt_rot x)
  rw [Polar.rot_zero] at h1
  have h2 : HasDerivAt (fun φ : ℝ => Complex.exp ((m : ℂ) * φ * Complex.I) * P x)
      (((m : ℂ) * Complex.I) * P x) 0 := by
    have h3 : HasDerivAt (fun φ : ℝ => (m : ℂ) * φ * Complex.I) ((m : ℂ) * 1 * Complex.I) 0 :=
      (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (m : ℂ)).mul_const Complex.I
    have h4 := (h3.cexp).mul_const (P x)
    simpa using h4
  have heq : (P ∘ fun φ : ℝ => rot φ x) =
      fun φ : ℝ => Complex.exp ((m : ℂ) * φ * Complex.I) * P x := by
    funext φ; exact sectorProj_rot m ψ φ x
  rw [heq] at h1
  exact h1.unique h2

theorem I_mul_eq (x : ℂ) : Complex.I * x = x.re • Complex.I - x.im • (1 : ℂ) := by
  apply Complex.ext <;> simp

/-- The classical angular derivative of `P_m ψ`. -/
theorem theta_sectorProj {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (m : ℤ) (x : ℂ) :
    (x.re : ℂ) * Sob.dirDeriv Complex.I (sectorProj m ψ) x -
        (x.im : ℂ) * Sob.dirDeriv 1 (sectorProj m ψ) x =
      ((m : ℂ) * Complex.I) * sectorProj m ψ x := by
  rw [← fderiv_sectorProj_I_mul hψ m x, I_mul_eq, map_sub, map_smul, map_smul,
    Complex.real_smul, Complex.real_smul]
  rfl

/-- The classical angular derivative of `conj (P_m ψ)`. -/
theorem theta_conj_sectorProj {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (m : ℤ) (x : ℂ) :
    (x.re : ℂ) * Sob.dirDeriv Complex.I (fun y => conj (sectorProj m ψ y)) x -
        (x.im : ℂ) * Sob.dirDeriv 1 (fun y => conj (sectorProj m ψ y)) x =
      -((m : ℂ) * Complex.I) * conj (sectorProj m ψ x) := by
  have hd : ∀ v : ℂ, Sob.dirDeriv v (fun y => conj (sectorProj m ψ y)) x =
      conj (Sob.dirDeriv v (sectorProj m ψ) x) := by
    intro v
    have e : (fun y => conj (sectorProj m ψ y)) = Complex.conjCLE ∘ sectorProj m ψ := by
      funext y; simp
    simp only [Sob.dirDeriv]
    rw [e, ContinuousLinearEquiv.comp_fderiv]
    simp
  rw [hd, hd]
  have h := congrArg conj (theta_sectorProj hψ m x)
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast] at h
  rw [h]
  ring

/-! ### Integration by parts against `∂_θ g` -/

theorem dirDeriv_re_mul {χ : ℂ → ℂ} (hχ : Differentiable ℝ χ) (x : ℂ) :
    Sob.dirDeriv Complex.I (fun y => (y.re : ℂ) * χ y) x =
      (x.re : ℂ) * Sob.dirDeriv Complex.I χ x := by
  have h1 : HasFDerivAt (fun y : ℂ => (y.re : ℂ)) (Complex.ofRealCLM.comp Complex.reCLM) x :=
    (Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt
  have h2 : HasFDerivAt χ (fderiv ℝ χ x) x := (hχ x).hasFDerivAt
  have h3 : HasFDerivAt (fun y => (y.re : ℂ) * χ y) _ x := h1.mul h2
  simp only [Sob.dirDeriv]
  rw [h3.fderiv]
  simp

theorem dirDeriv_im_mul {χ : ℂ → ℂ} (hχ : Differentiable ℝ χ) (x : ℂ) :
    Sob.dirDeriv 1 (fun y => (y.im : ℂ) * χ y) x = (x.im : ℂ) * Sob.dirDeriv 1 χ x := by
  have h1 : HasFDerivAt (fun y : ℂ => (y.im : ℂ)) (Complex.ofRealCLM.comp Complex.imCLM) x :=
    (Complex.ofRealCLM.comp Complex.imCLM).hasFDerivAt
  have h2 : HasFDerivAt χ (fderiv ℝ χ x) x := (hχ x).hasFDerivAt
  have h3 : HasFDerivAt (fun y => (y.im : ℂ) * χ y) _ x := h1.mul h2
  simp only [Sob.dirDeriv]
  rw [h3.fderiv]
  simp

theorem isTestFn_re_mul {χ : ℂ → ℂ} (hχ : Sob.IsTestFn univ χ) :
    Sob.IsTestFn univ (fun y => (y.re : ℂ) * χ y) :=
  ⟨((Complex.ofRealCLM.comp Complex.reCLM).contDiff).mul hχ.smooth, hχ.compact.mul_left,
    subset_univ _⟩

theorem isTestFn_im_mul {χ : ℂ → ℂ} (hχ : Sob.IsTestFn univ χ) :
    Sob.IsTestFn univ (fun y => (y.im : ℂ) * χ y) :=
  ⟨((Complex.ofRealCLM.comp Complex.imCLM).contDiff).mul hχ.smooth, hχ.compact.mul_left,
    subset_univ _⟩

/-- `∫ χ ∂_θ g = -∫ g (x₁ ∂₂χ - x₂ ∂₁χ)` for `g ∈ H^1` and a test function `χ`. -/
theorem integral_mul_thetaDeriv {g χ : ℂ → ℂ} (hg : Sob.MemH 1 g) (hχ : Sob.IsTestFn univ χ) :
    ∫ x, χ x * thetaDeriv g x =
      -∫ x, g x * ((x.re : ℂ) * Sob.dirDeriv Complex.I χ x -
        (x.im : ℂ) * Sob.dirDeriv 1 χ x) := by
  have hχd : Differentiable ℝ χ := hχ.smooth.differentiable (by simp)
  obtain ⟨h01, h10⟩ := memLp_weakPartial_one hg
  have hgL : MemLp g 2 volume := (Sob.memH_iff.1 hg).1
  have hw01 := (hg.memLp_weakPartial (γ := (0, 1)) (Sob.mem_multiIdx.2 (by norm_num))).2
  have hw10 := (hg.memLp_weakPartial (γ := (1, 0)) (Sob.mem_multiIdx.2 (by norm_num))).2
  have hφ₂ := isTestFn_re_mul hχ
  have hφ₁ := isTestFn_im_mul hχ
  have e₂ := hw01 _ hφ₂
  have e₁ := hw10 _ hφ₁
  simp only [Sob.pdList, List.replicate_zero, List.replicate_one, List.nil_append,
    List.append_nil, Sob.iterDirDeriv_cons, Sob.iterDirDeriv_nil, List.length_singleton,
    pow_one, neg_one_mul] at e₂ e₁
  have hd₂ : (Sob.dirDeriv Complex.I fun y => (y.re : ℂ) * χ y) =
      fun x => (x.re : ℂ) * Sob.dirDeriv Complex.I χ x := funext (dirDeriv_re_mul hχd)
  have hd₁ : (Sob.dirDeriv 1 fun y => (y.im : ℂ) * χ y) =
      fun x => (x.im : ℂ) * Sob.dirDeriv 1 χ x := funext (dirDeriv_im_mul hχd)
  rw [hd₂] at e₂
  rw [hd₁] at e₁
  -- integrability
  have i₂ : Integrable (fun x => Sob.weakPartial (0, 1) g x * ((x.re : ℂ) * χ x)) volume :=
    h01.integrable_mul (hφ₂.memLp 2 volume)
  have i₁ : Integrable (fun x => Sob.weakPartial (1, 0) g x * ((x.im : ℂ) * χ x)) volume :=
    h10.integrable_mul (hφ₁.memLp 2 volume)
  have j₂ : Integrable (fun x => g x * ((x.re : ℂ) * Sob.dirDeriv Complex.I χ x)) volume := by
    have := hgL.integrable_mul ((hφ₂.dirDeriv Complex.I).memLp 2 volume)
    rw [hd₂] at this; exact this
  have j₁ : Integrable (fun x => g x * ((x.im : ℂ) * Sob.dirDeriv 1 χ x)) volume := by
    have := hgL.integrable_mul ((hφ₁.dirDeriv 1).memLp 2 volume)
    rw [hd₁] at this; exact this
  have lhs : (fun x => χ x * thetaDeriv g x) = fun x =>
      Sob.weakPartial (0, 1) g x * ((x.re : ℂ) * χ x) -
        Sob.weakPartial (1, 0) g x * ((x.im : ℂ) * χ x) := by
    funext x; simp only [thetaDeriv]; ring
  have rhs : (fun x => g x * ((x.re : ℂ) * Sob.dirDeriv Complex.I χ x -
      (x.im : ℂ) * Sob.dirDeriv 1 χ x)) = fun x =>
        g x * ((x.re : ℂ) * Sob.dirDeriv Complex.I χ x) -
          g x * ((x.im : ℂ) * Sob.dirDeriv 1 χ x) := by
    funext x; ring
  rw [lhs, rhs, integral_sub i₂ i₁, integral_sub j₂ j₁, e₂, e₁]
  ring

/-! ### `P_ℓ (∂_θ g) = iℓ P_ℓ g` -/

theorem memLp_of_continuous_compact {u : ℂ → ℂ} (hu : Continuous u) (hc : HasCompactSupport u) :
    MemLp u 2 volume :=
  hu.memLp_of_hasCompactSupport hc

/-- The key identity: `∫ ψ P_ℓ(∂_θ g) = iℓ ∫ ψ P_ℓ g` for a real-valued test function `ψ`. -/
theorem integral_testFn_mul_sectorProj_thetaDeriv {g : ℂ → ℂ} (hg : Sob.MemH 1 g) (ℓ : ℤ)
    {ψ : ℂ → ℂ} (hψ : Sob.IsTestFn univ ψ) (hconjψ : ∀ x, conj (ψ x) = ψ x) :
    ∫ x, ψ x * sectorProj ℓ (thetaDeriv g) x =
      ((ℓ : ℂ) * Complex.I) * ∫ x, ψ x * sectorProj ℓ g x := by
  have hgL : MemLp g 2 volume := (Sob.memH_iff.1 hg).1
  have hF : MemLp (thetaWeighted g) 2 volume := memLp_thetaWeighted hg
  have hψL : MemLp ψ 2 volume := hψ.memLp 2 volume
  have hconjw : ∀ x : ℂ, conj (((1 + ‖x‖ : ℝ) : ℂ)) = ((1 + ‖x‖ : ℝ) : ℂ) :=
    fun x => Complex.conj_ofReal _
  have huL : MemLp (fun x => ((1 + ‖x‖ : ℝ) : ℂ) * ψ x) 2 volume :=
    memLp_of_continuous_compact (by have := hψ.continuous; fun_prop) (hψ.compact.mul_left)
  have hPu : sectorProj ℓ (fun x => ((1 + ‖x‖ : ℝ) : ℂ) * ψ x) =
      fun x => ((1 + ‖x‖ : ℝ) : ℂ) * sectorProj ℓ ψ x :=
    sectorProj_radial_mul ℓ (fun r => ((1 + r : ℝ) : ℂ)) ψ
  have hχ : Sob.IsTestFn univ (fun x => conj (sectorProj ℓ ψ x)) := isTestFn_conj_sectorProj hψ ℓ
  have step1 : ∫ x, ψ x * sectorProj ℓ (thetaDeriv g) x =
      ∫ x, conj (((1 + ‖x‖ : ℝ) : ℂ) * ψ x) * sectorProj ℓ (thetaWeighted g) x := by
    rw [sectorProj_thetaDeriv_eq_weight]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, hconjw, hconjψ]
    ring
  have step2 : ∫ x, conj (sectorProj ℓ (fun x => ((1 + ‖x‖ : ℝ) : ℂ) * ψ x) x) *
      thetaWeighted g x = ∫ x, conj (sectorProj ℓ ψ x) * thetaDeriv g x := by
    rw [hPu, thetaDeriv_eq_weight g]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, hconjw]
    ring
  have step3 : ∫ x, g x * ((x.re : ℂ) * Sob.dirDeriv Complex.I
        (fun y => conj (sectorProj ℓ ψ y)) x -
        (x.im : ℂ) * Sob.dirDeriv 1 (fun y => conj (sectorProj ℓ ψ y)) x) =
      -((ℓ : ℂ) * Complex.I) * ∫ x, conj (sectorProj ℓ ψ x) * g x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [theta_conj_sectorProj hψ.smooth ℓ x]
    ring
  rw [step1, integral_conj_mul_sectorProj huL hF ℓ, step2, integral_mul_thetaDeriv hg hχ, step3,
    ← integral_conj_mul_sectorProj hψL hgL ℓ]
  simp_rw [hconjψ]
  ring

theorem isTestFn_ofReal {ψr : ℂ → ℝ} (hψr : ContDiff ℝ ∞ ψr) (hcr : HasCompactSupport ψr) :
    Sob.IsTestFn univ (fun x => (ψr x : ℂ)) := by
  refine ⟨?_, ?_, subset_univ _⟩
  swap
  · have h := HasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) hcr Complex.ofReal_zero
    exact h
  have h := (Complex.ofRealCLM.contDiff (n := ∞)).comp hψr
  simpa [Function.comp_def] using h

theorem sectorProj_thetaDeriv_aux {g : ℂ → ℂ} (hg : Sob.MemH 1 g) (ℓ : ℤ) :
    sectorProj ℓ (thetaDeriv g) =ᵐ[volume]
      fun x => ((ℓ : ℂ) * Complex.I) * sectorProj ℓ g x := by
  have hgL : MemLp g 2 volume := (Sob.memH_iff.1 hg).1
  have hF : MemLp (thetaWeighted g) 2 volume := memLp_thetaWeighted hg
  have hPg : MemLp (sectorProj ℓ g) 2 volume := (memLp_sectorProj hgL ℓ).1
  have hPF : MemLp (sectorProj ℓ (thetaWeighted g)) 2 volume := (memLp_sectorProj hF ℓ).1
  have hHloc : LocallyIntegrable (fun x => sectorProj ℓ (thetaDeriv g) x -
      ((ℓ : ℂ) * Complex.I) * sectorProj ℓ g x) volume :=
    (locallyIntegrable_sectorProj_thetaDeriv hg ℓ).sub
      ((hPg.const_mul _).locallyIntegrable (by norm_num))
  have hH0 := ae_eq_zero_of_integral_real_testFn hHloc fun ψr hψr hcr => by
    have hψ : Sob.IsTestFn univ (fun x => (ψr x : ℂ)) := isTestFn_ofReal hψr hcr
    have hψL : MemLp (fun x => (ψr x : ℂ)) 2 volume := hψ.memLp 2 volume
    have huL : MemLp (fun x => ((1 + ‖x‖ : ℝ) : ℂ) * (ψr x : ℂ)) 2 volume :=
      memLp_of_continuous_compact (by have := hψ.continuous; fun_prop) (hψ.compact.mul_left)
    have i1 : Integrable (fun x => (ψr x : ℂ) * sectorProj ℓ (thetaDeriv g) x) volume := by
      have := huL.integrable_mul hPF
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      rw [sectorProj_thetaDeriv_eq_weight]
      simp only [Pi.mul_apply]
      ring
    have i2 : Integrable (fun x => (ψr x : ℂ) * (((ℓ : ℂ) * Complex.I) * sectorProj ℓ g x))
        volume := hψL.integrable_mul (hPg.const_mul _)
    have e : (fun x => (ψr x : ℂ) * (sectorProj ℓ (thetaDeriv g) x -
        ((ℓ : ℂ) * Complex.I) * sectorProj ℓ g x)) = fun x =>
          (ψr x : ℂ) * sectorProj ℓ (thetaDeriv g) x -
            (ψr x : ℂ) * (((ℓ : ℂ) * Complex.I) * sectorProj ℓ g x) := by
      funext x; ring
    rw [e, integral_sub i1 i2,
      integral_testFn_mul_sectorProj_thetaDeriv hg ℓ hψ (fun x => Complex.conj_ofReal _)]
    have e2 : (fun x => (ψr x : ℂ) * (((ℓ : ℂ) * Complex.I) * sectorProj ℓ g x)) =
        fun x => ((ℓ : ℂ) * Complex.I) * ((ψr x : ℂ) * sectorProj ℓ g x) := by
      funext x; ring
    rw [e2, integral_const_mul, sub_self]
  filter_upwards [hH0] with x hx
  simpa [sub_eq_zero] using hx

end DerivAux

end NonUniqueEuler.Ang
