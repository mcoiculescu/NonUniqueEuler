import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L2Space
import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.I.Infra.AngularFourier.Parseval
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv

/-!
# Helpers for `P/Infra/AngularFourier/Derivatives`: duality, linearity, weights

* `integral_conj_mul_sectorProj`: `∫ conj(u) P_ℓ F = ∫ conj(P_ℓ u) F` for `u, F ∈ L²`
  (self-adjointness `inner_sectorProjL`, `I/Infra/AngularFourier/Parseval.lean`);
* `sectorProj_sub_ae`: a.e. linearity of `P_ℓ` on `L²`;
* `ae_eq_zero_of_integral_real_testFn`: the fundamental lemma of the calculus of variations,
  tested against real smooth compactly supported functions;
* the weight `w(x) = 1 + |x|`: for `g ∈ H^1`, `w⁻¹ ∂_θ g ∈ L²` (`memLp_thetaWeighted`) and
  `P_ℓ (∂_θ g) = w P_ℓ (w⁻¹ ∂_θ g)` (`sectorProj_thetaDeriv_eq_weight`).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal ComplexConjugate ContDiff

namespace NonUniqueEuler.Ang

namespace DerivAux

/-! ### Duality and linearity of `P_ℓ` on `L²` -/

/-- `∫ conj(u) · P_ℓ F = ∫ conj(P_ℓ u) · F` for `u, F ∈ L²`. -/
theorem integral_conj_mul_sectorProj {u F : ℂ → ℂ} (hu : MemLp u 2 volume)
    (hF : MemLp F 2 volume) (ℓ : ℤ) :
    ∫ x, conj (u x) * sectorProj ℓ F x = ∫ x, conj (sectorProj ℓ u x) * F x := by
  have h := inner_sectorProjL ℓ (hu.toLp u) (hF.toLp F)
  rw [L2.inner_def, L2.inner_def] at h
  have hu' : sectorProj ℓ (hu.toLp u : ℂ → ℂ) =ᵐ[volume] sectorProj ℓ u :=
    sectorProj_congr_ae ℓ (MemLp.coeFn_toLp hu)
  have hF' : sectorProj ℓ (hF.toLp F : ℂ → ℂ) =ᵐ[volume] sectorProj ℓ F :=
    sectorProj_congr_ae ℓ (MemLp.coeFn_toLp hF)
  have e1 : ∫ x, inner ℂ ((sectorProjL ℓ (hu.toLp u) : ℂ → ℂ) x) ((hF.toLp F : ℂ → ℂ) x) =
      ∫ x, conj (sectorProj ℓ u x) * F x := by
    refine integral_congr_ae ?_
    filter_upwards [sectorProjL_spec ℓ (hu.toLp u), hu', MemLp.coeFn_toLp hF] with x h1 h2 h3
    rw [h1, h2, h3, RCLike.inner_apply, mul_comm]
  have e2 : ∫ x, inner ℂ ((hu.toLp u : ℂ → ℂ) x) ((sectorProjL ℓ (hF.toLp F) : ℂ → ℂ) x) =
      ∫ x, conj (u x) * sectorProj ℓ F x := by
    refine integral_congr_ae ?_
    filter_upwards [sectorProjL_spec ℓ (hF.toLp F), hF', MemLp.coeFn_toLp hu] with x h1 h2 h3
    rw [h1, h2, h3, RCLike.inner_apply, mul_comm]
  rw [← e1, ← e2, h]

/-- A.e. linearity of `P_ℓ` on `L²`. -/
theorem sectorProj_sub_ae {F K : ℂ → ℂ} (hF : MemLp F 2 volume) (hK : MemLp K 2 volume)
    (ℓ : ℤ) : sectorProj ℓ (F - K) =ᵐ[volume] sectorProj ℓ F - sectorProj ℓ K := by
  have hFK : MemLp (F - K) 2 volume := hF.sub hK
  have hlin := (sectorProjL ℓ).map_sub (hF.toLp F) (hK.toLp K)
  have h1 : ((hF.toLp F - hK.toLp K : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[volume] F - K := by
    filter_upwards [Lp.coeFn_sub (hF.toLp F) (hK.toLp K), MemLp.coeFn_toLp hF,
      MemLp.coeFn_toLp hK] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, Pi.sub_apply]
  have e1 : sectorProj ℓ (F - K) =ᵐ[volume]
      (sectorProjL ℓ (hF.toLp F - hK.toLp K) : ℂ → ℂ) :=
    (sectorProj_congr_ae ℓ h1.symm).trans (sectorProjL_spec ℓ _).symm
  rw [hlin] at e1
  filter_upwards [e1, Lp.coeFn_sub (sectorProjL ℓ (hF.toLp F)) (sectorProjL ℓ (hK.toLp K)),
    sectorProjL_spec ℓ (hF.toLp F), sectorProjL_spec ℓ (hK.toLp K),
    sectorProj_congr_ae ℓ (MemLp.coeFn_toLp hF), sectorProj_congr_ae ℓ (MemLp.coeFn_toLp hK)]
    with x h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.sub_apply, h3, h4, h5, h6, Pi.sub_apply]

/-! ### The fundamental lemma with real test functions -/

/-- A locally integrable `h : ℂ → ℂ` with `∫ ψ h = 0` for every real smooth compactly supported
`ψ` vanishes a.e. -/
theorem ae_eq_zero_of_integral_real_testFn {h : ℂ → ℂ} (hh : LocallyIntegrable h volume)
    (H : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x, (ψ x : ℂ) * h x = 0) : h =ᵐ[volume] 0 := by
  have := ae_eq_zero_of_integral_contDiff_smul_eq_zero hh (fun ψ hψ hc => by
    have e : (fun x => ψ x • h x) = fun x => (ψ x : ℂ) * h x := by
      funext x; rw [Complex.real_smul]
    rw [e]; exact H ψ hψ hc)
  filter_upwards [this] with x hx
  simpa using hx

/-! ### The weight `1 + |x|` -/

/-- `w⁻¹ ∂_θ g` with `w(x) = 1 + |x|`. -/
def thetaWeighted (g : ℂ → ℂ) (x : ℂ) : ℂ :=
  ((1 + ‖x‖ : ℝ) : ℂ)⁻¹ * thetaDeriv g x

theorem one_add_norm_ne_zero (x : ℂ) : ((1 + ‖x‖ : ℝ) : ℂ) ≠ 0 := by
  have : (0 : ℝ) < 1 + ‖x‖ := by positivity
  exact_mod_cast this.ne'

theorem thetaDeriv_eq_weight (g : ℂ → ℂ) :
    thetaDeriv g = fun x => ((1 + ‖x‖ : ℝ) : ℂ) * thetaWeighted g x := by
  funext x
  rw [thetaWeighted, ← mul_assoc, mul_inv_cancel₀ (one_add_norm_ne_zero x), one_mul]

theorem sectorProj_thetaDeriv_eq_weight (g : ℂ → ℂ) (ℓ : ℤ) :
    sectorProj ℓ (thetaDeriv g) =
      fun x => ((1 + ‖x‖ : ℝ) : ℂ) * sectorProj ℓ (thetaWeighted g) x := by
  rw [thetaDeriv_eq_weight g]
  exact sectorProj_radial_mul ℓ (fun r => ((1 + r : ℝ) : ℂ)) (thetaWeighted g)

theorem norm_thetaWeighted_le (g : ℂ → ℂ) (x : ℂ) :
    ‖thetaWeighted g x‖ ≤ ‖Sob.weakPartial (0, 1) g x‖ + ‖Sob.weakPartial (1, 0) g x‖ := by
  have hw : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have hre : |x.re| ≤ 1 + ‖x‖ := (Complex.abs_re_le_norm x).trans (by linarith)
  have him : |x.im| ≤ 1 + ‖x‖ := (Complex.abs_im_le_norm x).trans (by linarith)
  rw [thetaWeighted, thetaDeriv, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hw]
  rw [inv_mul_le_iff₀ hw]
  calc ‖(x.re : ℂ) * Sob.weakPartial (0, 1) g x - (x.im : ℂ) * Sob.weakPartial (1, 0) g x‖
      ≤ ‖(x.re : ℂ) * Sob.weakPartial (0, 1) g x‖ + ‖(x.im : ℂ) * Sob.weakPartial (1, 0) g x‖ :=
        norm_sub_le _ _
    _ = |x.re| * ‖Sob.weakPartial (0, 1) g x‖ + |x.im| * ‖Sob.weakPartial (1, 0) g x‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ (1 + ‖x‖) * ‖Sob.weakPartial (0, 1) g x‖ + (1 + ‖x‖) * ‖Sob.weakPartial (1, 0) g x‖ := by
        gcongr
    _ = (1 + ‖x‖) * (‖Sob.weakPartial (0, 1) g x‖ + ‖Sob.weakPartial (1, 0) g x‖) := by ring

theorem memLp_weakPartial_one {g : ℂ → ℂ} (hg : Sob.MemH 1 g) :
    MemLp (Sob.weakPartial (0, 1) g) 2 volume ∧ MemLp (Sob.weakPartial (1, 0) g) 2 volume :=
  ⟨(hg.memLp_weakPartial (γ := (0, 1)) (Sob.mem_multiIdx.2 (by norm_num))).1,
    (hg.memLp_weakPartial (γ := (1, 0)) (Sob.mem_multiIdx.2 (by norm_num))).1⟩

theorem aestronglyMeasurable_thetaDeriv {g : ℂ → ℂ} (hg : Sob.MemH 1 g) :
    AEStronglyMeasurable (thetaDeriv g) volume := by
  obtain ⟨h1, h2⟩ := memLp_weakPartial_one hg
  have hre : Continuous fun x : ℂ => (x.re : ℂ) := by fun_prop
  have him : Continuous fun x : ℂ => (x.im : ℂ) := by fun_prop
  exact (hre.aestronglyMeasurable.mul h1.1).sub (him.aestronglyMeasurable.mul h2.1)

theorem memLp_thetaWeighted {g : ℂ → ℂ} (hg : Sob.MemH 1 g) :
    MemLp (thetaWeighted g) 2 volume := by
  obtain ⟨h1, h2⟩ := memLp_weakPartial_one hg
  have hm : AEStronglyMeasurable (thetaWeighted g) volume := by
    have hw : Continuous fun x : ℂ => ((1 + ‖x‖ : ℝ) : ℂ)⁻¹ := by
      refine Continuous.inv₀ (by fun_prop) one_add_norm_ne_zero
    exact hw.aestronglyMeasurable.mul (aestronglyMeasurable_thetaDeriv hg)
  refine (h1.norm.add h2.norm).of_le hm (Filter.Eventually.of_forall fun x => ?_)
  refine (norm_thetaWeighted_le g x).trans ?_
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]

/-- `P_ℓ (∂_θ g)` is locally integrable for `g ∈ H^1`. -/
theorem locallyIntegrable_sectorProj_thetaDeriv {g : ℂ → ℂ} (hg : Sob.MemH 1 g) (ℓ : ℤ) :
    LocallyIntegrable (sectorProj ℓ (thetaDeriv g)) volume := by
  rw [sectorProj_thetaDeriv_eq_weight]
  have hP : LocallyIntegrable (sectorProj ℓ (thetaWeighted g)) volume :=
    (memLp_sectorProj (memLp_thetaWeighted hg) ℓ).1.locallyIntegrable (by norm_num)
  have := hP.continuous_smul (g := fun x : ℂ => ((1 + ‖x‖ : ℝ) : ℂ)) (by fun_prop)
  simpa [smul_eq_mul] using this

end DerivAux

end NonUniqueEuler.Ang
