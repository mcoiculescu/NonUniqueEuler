import NonUniqueEuler.H.Infra.AngularFourier.Derivatives.Theta

/-!
# Helpers for `P/Infra/AngularFourier/Derivatives`: `∂_θ (h(r) e^{iℓθ}) = iℓ h(r) e^{iℓθ}`

For `G = h(r)e^{iℓθ} ∈ H^1`, put `w = 1 + |x|`, `F = w⁻¹ ∂_θ G ∈ L²` and `K = w⁻¹ iℓ G ∈ L²`.
For every `m`, `P_m F = w⁻¹ P_m(∂_θ G) = w⁻¹ im P_m G` (`sectorProj_thetaDeriv_aux`) and
`P_m K = w⁻¹ iℓ P_m G`; since `P_m G = δ_{mℓ} G` (`sectorProj_ofProfile`) these agree, so
`F = K` a.e. by uniqueness of the angular Fourier expansion (`ae_eq_zero_of_sectorProj`,
`I/Infra/AngularFourier/Parseval.lean`), i.e. `∂_θ G = iℓ G` a.e.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal ComplexConjugate ContDiff

namespace NonUniqueEuler.Ang

namespace DerivAux

theorem sectorProj_thetaWeighted (g : ℂ → ℂ) (m : ℤ) :
    sectorProj m (thetaWeighted g) =
      fun x => ((1 + ‖x‖ : ℝ) : ℂ)⁻¹ * sectorProj m (thetaDeriv g) x :=
  sectorProj_radial_mul m (fun r => ((1 + r : ℝ) : ℂ)⁻¹) (thetaDeriv g)

theorem thetaDeriv_ofProfile_aux {ℓ : ℤ} {h : ℝ → ℂ} (hh : Sob.MemH 1 (ofProfile ℓ h)) :
    thetaDeriv (ofProfile ℓ h) =ᵐ[volume]
      fun x => ((ℓ : ℂ) * Complex.I) * ofProfile ℓ h x := by
  have hGL : MemLp (ofProfile ℓ h) 2 volume := (Sob.memH_iff.1 hh).1
  have hF : MemLp (thetaWeighted (ofProfile ℓ h)) 2 volume := memLp_thetaWeighted hh
  have hw : Continuous fun x : ℂ => ((1 + ‖x‖ : ℝ) : ℂ)⁻¹ :=
    Continuous.inv₀ (by fun_prop) one_add_norm_ne_zero
  have hK : MemLp (fun x => ((1 + ‖x‖ : ℝ) : ℂ)⁻¹ * (((ℓ : ℂ) * Complex.I) * ofProfile ℓ h x))
      2 volume := by
    refine (hGL.const_mul ((ℓ : ℂ) * Complex.I)).of_le
      (hw.aestronglyMeasurable.mul (hGL.const_mul _).1)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    have h1 : ‖((1 + ‖x‖ : ℝ) : ℂ)⁻¹‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact inv_le_one_of_one_le₀ (by linarith [norm_nonneg x])
    calc ‖((1 + ‖x‖ : ℝ) : ℂ)⁻¹‖ * ‖((ℓ : ℂ) * Complex.I) * ofProfile ℓ h x‖
        ≤ 1 * ‖((ℓ : ℂ) * Complex.I) * ofProfile ℓ h x‖ := by gcongr
      _ = ‖((ℓ : ℂ) * Complex.I) * ofProfile ℓ h x‖ := one_mul _
  have hsec : ∀ m : ℤ, sectorProj m (thetaWeighted (ofProfile ℓ h) -
      fun x => ((1 + ‖x‖ : ℝ) : ℂ)⁻¹ * (((ℓ : ℂ) * Complex.I) * ofProfile ℓ h x)) =ᵐ[volume] 0 := by
    intro m
    have hPK : sectorProj m
        (fun x => ((1 + ‖x‖ : ℝ) : ℂ)⁻¹ * (((ℓ : ℂ) * Complex.I) * ofProfile ℓ h x)) =
          fun x => ((1 + ‖x‖ : ℝ) : ℂ)⁻¹ * (((ℓ : ℂ) * Complex.I) *
            sectorProj m (ofProfile ℓ h) x) := by
      rw [sectorProj_radial_mul m (fun r => ((1 + r : ℝ) : ℂ)⁻¹)
        (fun x => ((ℓ : ℂ) * Complex.I) * ofProfile ℓ h x)]
      rw [sectorProj_radial_mul m (fun _ => ((ℓ : ℂ) * Complex.I)) (ofProfile ℓ h)]
    filter_upwards [sectorProj_sub_ae hF hK m, sectorProj_thetaDeriv_aux hh m] with x h1 h2
    rw [h1, Pi.sub_apply, hPK, sectorProj_thetaWeighted]
    simp only [Pi.zero_apply]
    rw [h2, sectorProj_ofProfile]
    split_ifs with hm
    · subst hm; ring
    · simp
  have hFK := ae_eq_zero_of_sectorProj (hF.sub hK) hsec
  filter_upwards [hFK] with x hx
  have hx' : thetaWeighted (ofProfile ℓ h) x =
      ((1 + ‖x‖ : ℝ) : ℂ)⁻¹ * (((ℓ : ℂ) * Complex.I) * ofProfile ℓ h x) := by
    simpa [sub_eq_zero] using hx
  rw [thetaDeriv_eq_weight]
  beta_reduce
  rw [hx', ← mul_assoc, mul_inv_cancel₀ (one_add_norm_ne_zero x), one_mul]

end DerivAux

end NonUniqueEuler.Ang
