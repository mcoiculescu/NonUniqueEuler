import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.I.Sec4.Sector
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Sec4.Resolvent
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Helpers for `P/Sec4/EvansSimple/GenEigen`: `M_*`, `k_ℓ`, `g_*` and the forcing `F_*`

Elementary facts used in the proof of `thm:evans-simple`(3), first half (`04_ring.tex:536-555`):
* `denom_ne_zero`, `denom_mul_Mres`: `(λ + iℓΩ) M_λ = 1` for `Re λ > 0`;
* `contDiffOn_kcoef`, `contDiffOn_Mres`: `k_ℓ`, `M_λ` are smooth on `(0,∞)`;
* `kcoef_eq_zero`: `k_ℓ = 0` on `(0,∞) \ [r₁,r₂]`;
* `isProfileL2_neg_gStar`: `-g_* ∈ Y^0_ℓ` (as a profile);
* `contDiff_Fstar`, `Fstar_eq_zero`: the forcing
  `F_*(ξ) = e^{2ξ} M_*(e^ξ) (-g_*(e^ξ)) = S.Fres ℓ z G (-g_*)` is smooth on `ℝ` and vanishes when
  `e^ξ ∉ [r₁,r₂]`;
* `J_eq_neg_integral`: `J = -∫_ℝ ψ_* F_*` (the substitution `r = e^ξ`, `04_ring.tex:546-548`).

Several of these are copies of the corresponding lemmas of `H/Sec4/Resolvent/Profile.lean` and
`H/Sec4/EvansSimple/Basic.lean` (helpers of other proofs, which may not be imported here).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.GenEigenAux

open SectorSetting

/-- `λ + iℓΩ ≠ 0` for `Re λ > 0`. -/
theorem denom_ne_zero (S : SectorSetting) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ) (G r : ℝ) :
    z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- `(λ + iℓΩ) M_λ = 1`. -/
theorem denom_mul_Mres (S : SectorSetting) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ) (G r : ℝ) :
    (z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)) * S.Mres ℓ z G r = 1 :=
  mul_inv_cancel₀ (denom_ne_zero S hz ℓ G r)

theorem contDiff_omR (S : SectorSetting) (hS : S.Valid) : ContDiff ℝ ∞ S.omR :=
  hS.contDiff.comp Complex.ofRealCLM.contDiff

theorem contDiff_dom (S : SectorSetting) (hS : S.Valid) : ContDiff ℝ ∞ S.dom :=
  (contDiff_infty_iff_deriv.1 (contDiff_omR S hS)).2

/-- `k_ℓ` is smooth on `(0,∞)`. -/
theorem contDiffOn_kcoef (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) :
    ContDiffOn ℝ ∞ (S.kcoef ℓ) (Ioi 0) := by
  have h1 : ContDiff ℝ ∞ fun r : ℝ => ((S.dom r : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_dom S hS)
  have h2 : ContDiffOn ℝ ∞ (fun r : ℝ => ((r : ℝ) : ℂ)⁻¹) (Ioi 0) :=
    (Complex.ofRealCLM.contDiff.contDiffOn).inv fun r hr => by
      simpa using (ne_of_gt (show (0 : ℝ) < r from hr))
  have h3 : ContDiffOn ℝ ∞ (fun r : ℝ => Complex.I * (ℓ : ℂ) * ((S.dom r : ℝ) : ℂ) *
      ((r : ℝ) : ℂ)⁻¹) (Ioi 0) :=
    ((contDiffOn_const.mul h1.contDiffOn).mul h2)
  refine h3.congr fun r _ => ?_
  simp only [kcoef, div_eq_mul_inv]

/-- `M_λ` is smooth on `(0,∞)`. -/
theorem contDiffOn_Mres (S : SectorSetting) (hS : S.Valid) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ)
    (G : ℝ) : ContDiffOn ℝ ∞ (S.Mres ℓ z G) (Ioi 0) := by
  have h1 : ContDiffOn ℝ ∞ (fun r : ℝ => ((S.Omega G r : ℝ) : ℂ)) (Ioi 0) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_Omega S hS G)
  have h2 : ContDiffOn ℝ ∞ (fun r : ℝ => z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ))
      (Ioi 0) := contDiffOn_const.add (contDiffOn_const.mul h1)
  exact h2.inv fun r _ => denom_ne_zero S hz ℓ G r

/-- `k_ℓ = 0` on `(0,∞) \ [r₁,r₂]`. -/
theorem kcoef_eq_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) {r : ℝ} (hr : 0 < r)
    (hrI : r ∉ Icc S.r₁ S.r₂) : S.kcoef ℓ r = 0 := by
  simp [kcoef, hS.dom_eq_zero r hr hrI]

/-- `g_* = 0` on `(0,∞) \ [r₁,r₂]` (for any `λ`). -/
theorem gStar_eq_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (z : ℂ) (G : ℝ) {r : ℝ}
    (hr : 0 < r) (hrI : r ∉ Icc S.r₁ S.r₂) : S.gStar ℓ z G r = 0 := by
  simp [gStar, kcoef_eq_zero S hS ℓ hr hrI]

/-- `-g_*` lies in `Y^0_ℓ` as a profile. -/
theorem isProfileL2_neg_gStar (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) :
    S.IsProfileL2 (fun r => -S.gStar ℓ z G r) := by
  obtain ⟨hcd, -⟩ := eigen_of_evans_eq_zero S hS ℓ hℓ z hz G hE
  have hIcc : Icc S.ρm S.ρp ⊆ Ioi 0 := fun _ hr => lt_of_lt_of_le hS.ρm_pos hr.1
  have hsub : Icc S.r₁ S.r₂ ⊆ Icc S.ρm S.ρp :=
    Icc_subset_Icc hS.ρm_lt_r₁.le hS.r₂_lt_ρp.le
  have hc : ContinuousOn (fun r => -S.gStar ℓ z G r) (Icc S.ρm S.ρp) :=
    (hcd.continuousOn.mono hIcc).neg
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨MemLp.of_bound (hc.aestronglyMeasurable measurableSet_Icc) C ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hC r hr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr hr'
    rw [gStar_eq_zero S hS ℓ z G hr fun h => hr' (hsub h), neg_zero]

/-- The forcing `F_* = -e^{2ξ} M_* g_*` (`04_ring.tex:537`) is smooth on `ℝ`. -/
theorem contDiff_Fstar (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) :
    ContDiff ℝ ∞ (S.Fres ℓ z G (fun r => -S.gStar ℓ z G r)) := by
  have hg : ContDiffOn ℝ ∞ (S.gStar ℓ z G) (Ioi 0) :=
    (eigen_of_evans_eq_zero S hS ℓ hℓ z hz G hE).1
  have h1 : ContDiffOn ℝ ∞ (fun r => S.Mres ℓ z G r * -S.gStar ℓ z G r) (Ioi 0) :=
    (contDiffOn_Mres S hS hz ℓ G).mul hg.neg
  have h2 : ContDiff ℝ ∞
      (fun ξ => S.Mres ℓ z G (Real.exp ξ) * -S.gStar ℓ z G (Real.exp ξ)) :=
    h1.comp_contDiff Real.contDiff_exp (fun ξ => Real.exp_pos ξ)
  have h3 : ContDiff ℝ ∞ (fun ξ : ℝ => ((Real.exp (2 * ξ) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  exact h3.mul h2

/-- `F_*(ξ) = 0` when `e^ξ ∉ [r₁, r₂]`. -/
theorem Fstar_eq_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (z : ℂ) (G : ℝ) {ξ : ℝ}
    (hξ : Real.exp ξ ∉ Icc S.r₁ S.r₂) :
    S.Fres ℓ z G (fun r => -S.gStar ℓ z G r) ξ = 0 := by
  simp only [Fres, gStar_eq_zero S hS ℓ z G (Real.exp_pos ξ) hξ, neg_zero, mul_zero]

/-- **`J = -∫_ℝ ψ_* F_*`** (`04_ring.tex:546-548`; substitution `r = e^ξ`). -/
theorem J_eq_neg_integral (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) :
    S.J ℓ z G = -∫ ξ : ℝ, S.psi ℓ z G ξ * S.Fres ℓ z G (fun r => -S.gStar ℓ z G r) ξ := by
  have himg : Real.exp '' univ = Ioi (0 : ℝ) := by rw [image_univ, Real.range_exp]
  have hcv := integral_image_eq_integral_abs_deriv_smul (s := univ) (f := Real.exp)
    (f' := Real.exp) MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun r : ℝ => S.gStar ℓ z G r * S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ))
  rw [himg, Measure.restrict_univ] at hcv
  rw [J, hcv, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  have hexp : Real.exp (2 * ξ) = Real.exp ξ * Real.exp ξ := by
    rw [← Real.exp_add]
    ring_nf
  simp only [abs_of_pos (Real.exp_pos ξ), Real.log_exp, Fres, Complex.real_smul, hexp]
  push_cast
  ring

end NonUniqueEuler.GenEigenAux
