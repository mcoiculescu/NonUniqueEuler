import NonUniqueEuler.I.Sec4.SectorSetting
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Helper for `lem:sector`(2),(3): the conjugation symmetry of `L_ℓ` and the Riccati coefficient

Helper file of `P/Sec4/Sector.lean` (fully proved). Manuscript `04_ring.tex:274-277` (the
relation `L_{-ℓ}(G)ḡ = conj(L_ℓ(G)g)`) and `:278-281` (part (3)).
-/

noncomputable section

open MeasureTheory Set Real ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler.SectorH

open SectorSetting

/-! ### `L_{-ℓ}(G) ḡ = conj(L_ℓ(G) g)` -/

theorem green_neg_conj (ℓ : ℤ) (g : ℝ → ℂ) (r : ℝ) :
    green (-ℓ) (fun ρ => conj (g ρ)) r = conj (green ℓ g r) := by
  simp only [green, Int.cast_neg, abs_neg, Int.natAbs_neg, map_mul, map_neg, Complex.conj_ofReal]
  congr 1
  rw [← integral_conj]
  congr 1
  funext ρ
  simp only [map_mul, Complex.conj_ofReal]

theorem kcoef_neg (S : SectorSetting) (ℓ : ℤ) (r : ℝ) :
    S.kcoef (-ℓ) r = conj (S.kcoef ℓ r) := by
  simp only [kcoef, Int.cast_neg, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal,
    map_intCast]
  ring

theorem LsecFn_neg_conj' (S : SectorSetting) (ℓ : ℤ) (G : ℝ) (g : ℝ → ℂ) (r : ℝ) :
    S.LsecFn (-ℓ) G (fun ρ => conj (g ρ)) r = conj (S.LsecFn ℓ G g r) := by
  simp only [LsecFn, KsecFn, green_neg_conj, kcoef_neg, map_add, map_mul, map_neg,
    Complex.conj_I, Complex.conj_ofReal, map_intCast, Int.cast_neg]
  ring

/-! ### The Riccati coefficient -/

theorem contDiff_omR (S : SectorSetting) (hS : S.Valid) : ContDiff ℝ ∞ S.omR :=
  hS.contDiff.comp Complex.ofRealCLM.contDiff

theorem contDiff_dom (S : SectorSetting) (hS : S.Valid) : ContDiff ℝ ∞ S.dom :=
  (contDiff_infty_iff_deriv.1 (contDiff_omR S hS)).2

theorem contDiff_fxi (S : SectorSetting) (hS : S.Valid) : ContDiff ℝ ∞ S.fxi := by
  have h := (contDiff_dom S hS).comp Real.contDiff_exp
  exact Real.contDiff_exp.mul h

theorem contDiff_Omega_exp (S : SectorSetting) (hS : S.Valid) (G : ℝ) :
    ContDiff ℝ ∞ fun ξ => S.Omega G (Real.exp ξ) :=
  (contDiffOn_Omega S hS G).comp_contDiff Real.contDiff_exp fun ξ => Real.exp_pos ξ

theorem re_add_I_mul (z : ℂ) (ℓ : ℝ) (Ω : ℝ) :
    (z + Complex.I * (ℓ : ℂ) * (Ω : ℂ)).re = z.re := by
  simp

theorem den_ne_zero {z : ℂ} (hz : 0 < z.re) (ℓ Ω : ℝ) :
    z + Complex.I * (ℓ : ℂ) * (Ω : ℂ) ≠ 0 := by
  intro h
  have := re_add_I_mul z ℓ Ω
  rw [h, Complex.zero_re] at this
  linarith

theorem sector_riccati' (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (G : ℝ) :
    (∀ z : ℂ, 0 < z.re → ∀ r : ℝ, 0 < r →
        z.re ≤ ‖z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)‖) ∧
      (∀ z : ℂ, 0 < z.re → ContDiff ℝ ∞ (fun ξ => S.Vric ℓ z G ξ)) ∧
      (∀ ξ : ℝ, DifferentiableOn ℂ (fun z => S.Vric ℓ z G ξ) {z : ℂ | 0 < z.re}) ∧
      ContinuousOn (fun p : ℝ × ℂ => S.Vric ℓ p.2 G p.1) (univ ×ˢ {z : ℂ | 0 < z.re}) ∧
      (∀ (z : ℂ) (ξ : ℝ), ξ ∉ Icc S.ξ₁ S.ξ₂ → S.Vric ℓ z G ξ = (ℓ : ℂ) ^ 2) := by
  have hℓ : ((ℓ : ℝ) : ℂ) = (ℓ : ℂ) := by push_cast; rfl
  refine ⟨fun z _ r _ => ?_, fun z hz => ?_, fun ξ => ?_, ?_, fun z ξ hξ => ?_⟩
  · have := re_add_I_mul z ℓ (S.Omega G r)
    rw [hℓ] at this
    rw [← this]
    exact Complex.re_le_norm _
  · have hden : ContDiff ℝ ∞ fun ξ => z + Complex.I * (ℓ : ℂ) *
        ((S.Omega G (Real.exp ξ) : ℝ) : ℂ) :=
      contDiff_const.add (contDiff_const.mul
        (Complex.ofRealCLM.contDiff.comp (contDiff_Omega_exp S hS G)))
    have hne : ∀ ξ, z + Complex.I * (ℓ : ℂ) * ((S.Omega G (Real.exp ξ) : ℝ) : ℂ) ≠ 0 := by
      intro ξ
      have := den_ne_zero hz ℓ (S.Omega G (Real.exp ξ))
      rwa [hℓ] at this
    have hnum : ContDiff ℝ ∞ fun ξ => Complex.I * (ℓ : ℂ) * ((S.fxi ξ : ℝ) : ℂ) :=
      contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_fxi S hS))
    have : (fun ξ => S.Vric ℓ z G ξ) = fun ξ => (ℓ : ℂ) ^ 2 +
        (Complex.I * (ℓ : ℂ) * ((S.fxi ξ : ℝ) : ℂ)) *
          (z + Complex.I * (ℓ : ℂ) * ((S.Omega G (Real.exp ξ) : ℝ) : ℂ))⁻¹ := by
      funext ξ
      simp only [Vric, div_eq_mul_inv]
    rw [this]
    exact contDiff_const.add (hnum.mul (hden.inv hne))
  · simp only [Vric]
    refine (DifferentiableOn.div (differentiableOn_const _) ?_ fun z hz => ?_).const_add _
    · exact DifferentiableOn.add differentiableOn_id (differentiableOn_const _)
    · have := den_ne_zero (show 0 < z.re from hz) ℓ (S.Omega G (Real.exp ξ))
      rwa [hℓ] at this
  · have hfx : Continuous fun p : ℝ × ℂ => Complex.I * (ℓ : ℂ) * ((S.fxi p.1 : ℝ) : ℂ) :=
      continuous_const.mul (Complex.continuous_ofReal.comp
        ((contDiff_fxi S hS).continuous.comp continuous_fst))
    have hd : Continuous fun p : ℝ × ℂ => p.2 + Complex.I * (ℓ : ℂ) *
        ((S.Omega G (Real.exp p.1) : ℝ) : ℂ) :=
      continuous_snd.add (continuous_const.mul (Complex.continuous_ofReal.comp
        ((contDiff_Omega_exp S hS G).continuous.comp continuous_fst)))
    refine (continuous_const.continuousOn).add (hfx.continuousOn.div hd.continuousOn ?_)
    intro p hp
    have := den_ne_zero (show 0 < p.2.re from hp.2) ℓ (S.Omega G (Real.exp p.1))
    rwa [hℓ] at this
  · have hfxi : S.fxi ξ = 0 := by
      have he := Real.exp_pos ξ
      have hnot : Real.exp ξ ∉ Icc S.r₁ S.r₂ := by
        intro h
        apply hξ
        refine ⟨?_, ?_⟩
        · rw [ξ₁, ← Real.exp_le_exp, Real.exp_log hS.r₁_pos]
          exact h.1
        · rw [ξ₂, ← Real.exp_le_exp, Real.exp_log hS.r₂_pos]
          exact h.2
      simp only [fxi, hS.dom_eq_zero _ he hnot, mul_zero]
    simp only [Vric, hfxi, Complex.ofReal_zero, mul_zero, zero_div, add_zero]

end NonUniqueEuler.SectorH
