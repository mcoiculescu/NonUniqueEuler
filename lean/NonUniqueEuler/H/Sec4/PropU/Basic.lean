import NonUniqueEuler.Defs.Sec4.Extra2Eigendata
import NonUniqueEuler.I.Sec4.HypN
import NonUniqueEuler.I.Sec4.EvansUnits
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec4.EvansSimple
import NonUniqueEuler.I.Sec4.Adjoint
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Infra.AngularFourier.Sector

/-!
# Helpers for `P/Sec4/PropU`: the eigendata at one `G ∈ [0, G₁]`

* `Rc_sq_mul_mem`: `R_c² G ∈ [0, 1/50]`;
* `eig_facts`: `λ_*(G)` is a simple zero of `E^Φ_3(·;G)` with `Re λ_*(G) > 211/2500`, and
  `∂_λE^Φ_3(λ_*;G) = ∂_λE_3(λ_*;R_c²G)` (`hypN_lamC`, `eq:evans-units`);
* `angularSector_ofProfile_self`: the sector-`ℓ` profile of `h(r)e^{iℓθ}` is `h` on `(0,∞)`;
* `pout_eq`, `beta_eq`: `pout_* = n_*⁻¹ pout_*^{sector}`, `β = n_* β^{sector}`
  (`def:eigendata`; the sector quantities are those of `lem:adjoint` for `g_*`);
* `norm_beta_mul_norm_pout`: `prop:U`(c).
-/

noncomputable section

open MeasureTheory Set Real ComplexConjugate

namespace NonUniqueEuler

namespace Eig

namespace PropUH

open RingData

theorem Rc_pos : 0 < Rc := Real.exp_pos _

theorem Rc_sq_mul_mem {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) : Rc ^ 2 * G ∈ Icc (0 : ℝ) (1 / 50) := by
  have hR : 0 < Rc ^ 2 := pow_pos Rc_pos 2
  refine ⟨mul_nonneg hR.le hG.1, ?_⟩
  calc Rc ^ 2 * G ≤ Rc ^ 2 * Gbar := mul_le_mul_of_nonneg_left hG.2 hR.le
    _ = 1 / 50 := by have := Rc_pos.ne'; rw [Gbar]; field_simp

theorem Gbar_nonneg : (0 : ℝ) ≤ Gbar := by
  rw [Gbar]; positivity

/-- The eigenvalue facts at one `G ∈ [0, G₁]` (`hypN_lamC`, `eq:evans-units`). -/
theorem eig_facts {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) :
    211 / 2500 < (lam χ G).re ∧ 0 < (lam χ G).re ∧
      (ringPhiSetting χ).evans 3 (lam χ G) G = 0 ∧
      deriv (fun w => (ringPhiSetting χ).evans 3 w G) (lam χ G) =
        deriv (fun w => evans χ 3 w (Rc ^ 2 * G)) (lam χ G) ∧
      deriv (fun w => (ringPhiSetting χ).evans 3 w G) (lam χ G) ≠ 0 ∧
      ∀ w : ℂ, 9 / 200 ≤ w.re → evans χ 3 w (Rc ^ 2 * G) = 0 → w = lam χ G := by
  obtain ⟨h1, h2, h3, h4⟩ := hypN_lamC χ hN.n1 hN.n2 (Rc_sq_mul_mem hG)
  have hz : 0 < (lam χ G).re := lt_trans (by norm_num) h1
  have hd := evans_units_deriv hχ 3 (by norm_num) (lam χ G) hz G
  refine ⟨h1, hz, ?_, hd, ?_, h4⟩
  · rw [evans_units hχ 3 (by norm_num) _ hz G]; exact h2
  · rw [hd]; exact h3

/-- The sector-`ℓ` profile of `h(|x|) e^{iℓθ}` is `h` on `(0,∞)`. -/
theorem angularSector_ofProfile_self (ℓ : ℤ) (h : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    Polar.angularSector (Ang.ofProfile ℓ h) ℓ r = h r := by
  have hx : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have h1 := Ang.sectorProj_eq_angularSector ℓ (Ang.ofProfile ℓ h) hx
  rw [Ang.sectorProj_ofProfile, ite_eq_left rfl] at h1
  have hn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hphase : Ang.angPhase ℓ (r : ℂ) = 1 := by
    rw [Ang.angPhase, hn, div_self hx, one_zpow]
  rw [Ang.ofProfile, hn, hphase, mul_one, mul_one] at h1
  exact h1.symm

/-- `pout_*(G) = n_*⁻¹ ∫ρ⁴ g_*` (`def:eigendata`, `lem:adjoint`(3)). -/
theorem pout_eq {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) :
    pout χ G = ((nstar χ G : ℝ) : ℂ)⁻¹ * (ringPhiSetting χ).poutStar 3 (lam χ G) G := by
  obtain ⟨-, hz, hE, -, hE', -⟩ := eig_facts hχ hN hG
  have hst := (SectorSetting.adjoint_stream (ringPhiSetting χ) (ringPhiSetting_valid hχ) 3
    (by norm_num) (lam χ G) hz G hE hE').2.2.2.2.1
  rw [hst, pout, BS.pout, Multipole.conjMoment]
  simp only [phi, gstar, mul_assoc, integral_const_mul]
  simp only [Nat.cast_ofNat, zpow_ofNat]
  ring

/-- `β(G) = n_* β^{sector}` (`def:eigendata`). -/
theorem beta_eq (χ : ℝ → ℝ) (G : ℝ) :
    beta χ G = ((nstar χ G : ℝ) : ℂ) * (ringPhiSetting χ).betaStar 3 (lam χ G) G := by
  rw [beta, ellFn, SectorSetting.betaStar, SectorSetting.ellStar, SectorSetting.ellStar]
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  rw [angularSector_ofProfile_self 3 _ hr]
  rfl

theorem key_alg (n e1 e2 ψ D J : ℂ) (hn : n ≠ 0) (he1 : e1 ≠ 0) (he2 : e2 ≠ 0) (hψ : ψ ≠ 0)
    (hD : D ≠ 0) (hJ : e1 * e2 * ψ * D = -J) :
    n * (-(-2 * 3 * e1) / (2 * 3 * J)) * (n⁻¹ * (-2 * 3 * e2 * ψ)) = 6 / D := by
  have hJ' : J = -(e1 * e2 * ψ * D) := by rw [hJ, neg_neg]
  subst hJ'
  field_simp
  ring

/-- **`prop:U`(c)** in complex form: `β(G) pout_*(G) = 6/∂_λE_3(λ_*(G); R_c²G)`. -/
theorem beta_mul_pout {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) :
    beta χ G * pout χ G = 6 / deriv (fun z => evans χ 3 z (Rc ^ 2 * G)) (lam χ G) := by
  obtain ⟨-, hz, hE, hd, hE', -⟩ := eig_facts hχ hN hG
  have hS := ringPhiSetting_valid hχ
  have hn : 0 < nstar χ G := (eigendata_phi χ hχ hN hG).1
  obtain ⟨hψ, hJeq⟩ := SectorSetting.evansSimple_deriv _ hS 3 (by norm_num) _ hz G hE
  have hst := SectorSetting.adjoint_stream _ hS 3 (by norm_num) _ hz G hE hE'
  have hb := (SectorSetting.adjoint_beta _ hS 3 (by norm_num) _ hz G hE hE').1
  rw [beta_eq, pout_eq hχ hN hG, ← hd, hb, hst.2.2.1, hst.2.2.2.1]
  have he : ((Real.exp ((3 : ℕ) * ((ringPhiSetting χ).ξ₂ - (ringPhiSetting χ).ξ₁)) : ℝ) : ℂ) =
      ((Real.exp (-((3 : ℕ) * (ringPhiSetting χ).ξ₁)) : ℝ) : ℂ) *
        ((Real.exp ((3 : ℕ) * (ringPhiSetting χ).ξ₂) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
  rw [he] at hJeq
  simp only [Nat.cast_ofNat] at hJeq ⊢
  exact key_alg _ _ _ _ _ _ (Complex.ofReal_ne_zero.2 hn.ne')
    (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne') (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')
    hψ hE' hJeq

/-- **`prop:U`(c)** (`04_ring.tex:1350-1352`). -/
theorem norm_beta_mul_norm_pout {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) :
    ‖beta χ G‖ * ‖pout χ G‖ = 6 / ‖deriv (fun z => evans χ 3 z (Rc ^ 2 * G)) (lam χ G)‖ := by
  rw [← norm_mul, beta_mul_pout hχ hN hG, norm_div]
  norm_num

end PropUH

end Eig

end NonUniqueEuler
