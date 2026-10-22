import NonUniqueEuler.H.Sec4.PropSemigroup.Basic
import NonUniqueEuler.H.Sec4.PropSemigroup.LsecCont
import NonUniqueEuler.I.Sec4.PropSU
import NonUniqueEuler.I.Sec4.PropU
import NonUniqueEuler.I.Sec4.LargeSectors
import NonUniqueEuler.I.Sec4.SemigroupLaw
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.Dunford.Deflation
import NonUniqueEuler.I.Infra.Dunford.Uniform
import NonUniqueEuler.I.Sec4.PropSemigroup.RieszCont

/-!
# Helpers for `P/Sec4/PropSemigroup`: the sector-wise bounds

`04_ring.tex:1449-1490`. For `w ∈ X^s`, `G ∈ [0,G₁]`, `t ≥ 0` and every `ℓ ∈ ℤ`:
`‖P_ℓ e^{tL}(1 - R)w‖ ≤ C e^{σ't} ‖P_ℓ w‖` with one `C` (`exists_secProj_one_sub_bound`):
* `|ℓ| ≥ max(M_{σ'}, 4)`: `R_ℓ = 0` and `prop:large-sectors` (`largeSectors_opNorm`);
* `ℓ = ±3`: deflation, `Dunford.exists_norm_exp_mul_one_sub_le_uniform` (restructuring R2), with
  the continuity of `L_{±3}(G)` (`Lsec_continuous`), of the projections (`rieszSec_continuousOn`)
  and of `λ_*` (`propU_a`), and the spectral gap of `prop:SU` (`lam_SU`);
* other `ℓ ∈ 3ℤ`: `Dunford.exists_norm_exp_le_of_spectrum_re_lt_uniform` (`lam_SU`);
* `ℓ ∉ 3ℤ`: `P_ℓ w = 0` for `w ∈ X^s`.
Also `‖P_ℓ R w‖ ≤ K‖P_ℓ w‖` and `‖P_ℓ e^{tL}Rw‖ ≤ K e^{σ(G)t}‖P_ℓ w‖` (`exp_mul_proj`).
-/

noncomputable section

open MeasureTheory Set ComplexConjugate

namespace NonUniqueEuler

namespace PropSemigroupH

open Sect RingData

variable {χ : ℝ → ℝ}

theorem Gbar_nonneg : 0 ≤ Gbar := by
  unfold Gbar
  positivity

section Generic

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
theorem norm_apply_sub_le (E P : X →L[ℂ] X) (x : X) {c : ℝ} (h : ‖E * (1 - P)‖ ≤ c) :
    ‖E (x - P x)‖ ≤ c * ‖x‖ :=
  calc ‖E (x - P x)‖ = ‖(E * (1 - P)) x‖ := rfl
    _ ≤ ‖E * (1 - P)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ c * ‖x‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)

theorem norm_exp_proj_apply (A P : X →L[ℂ] X) (z : ℂ) (hAP : A * P = z • P) (t : ℝ) (x : X) :
    ‖NormedSpace.exp ((t : ℂ) • A) (P x)‖ = Real.exp (t * z.re) * ‖P x‖ := by
  have e : NormedSpace.exp ((t : ℂ) • A) (P x) = (NormedSpace.exp ((t : ℂ) • A) * P) x := rfl
  rw [e, Dunford.exp_mul_proj hAP, FunLike.coe_smul, Pi.smul_apply, norm_smul, Complex.norm_exp,
    Complex.re_ofReal_mul]

end Generic

/-- `P_ℓ e^{tL(G)} = exp(tL_ℓ(G)) P_ℓ` (`lem:semigroup-construct`(3)). -/
theorem secProj_S (hχ : IsAdmissibleCutoff χ) (s : ℕ) (G : ℝ) {t : ℝ} (ht : 0 ≤ t) (ℓ : ℤ)
    (w : Y s annN) :
    secProj s annN ℓ (Lin.S χ s G t w) =
      NormedSpace.exp ((t : ℂ) • Lin.Lsec χ s ℓ G) (secProj s annN ℓ w) :=
  (SectorSetting.semigroup_sector _ (ringPhiSetting_valid hχ) s G ht ℓ).1 w

/-- The spectral gap of `prop:SU` in the form used by the Dunford bounds. -/
theorem spectrum_re_lt (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) {σ' : ℝ} (hσ' : 9 / 200 < σ') :
    (∀ z ∈ spectrum ℂ (Lin.Lsec χ s 3 G), z ≠ Eig.lam χ G → z.re < σ') ∧
      (∀ z ∈ spectrum ℂ (Lin.Lsec χ s (-3) G), z ≠ conj (Eig.lam χ G) → z.re < σ') ∧
      ∀ ℓ : ℤ, (3 : ℤ) ∣ ℓ → ℓ ≠ 3 → ℓ ≠ -3 →
        ∀ z ∈ spectrum ℂ (Lin.Lsec χ s ℓ G), z.re < σ' := by
  obtain ⟨-, h3, -, -, hm3, -, -, hother⟩ := Eig.lam_SU χ hχ hN hG s
  refine ⟨fun z hz hne => ?_, fun z hz hne => ?_, fun ℓ hd h3' hm3' z hz => ?_⟩
  · by_contra hle
    have hmem : z ∈ spectrum ℂ (Lin.Lsec χ s 3 G) ∩ {w : ℂ | 9 / 200 < w.re} :=
      ⟨hz, show 9 / 200 < z.re by linarith [not_lt.1 hle]⟩
    rw [h3] at hmem
    exact hne hmem
  · by_contra hle
    have hmem : z ∈ spectrum ℂ (Lin.Lsec χ s (-3) G) ∩ {w : ℂ | 9 / 200 < w.re} :=
      ⟨hz, show 9 / 200 < z.re by linarith [not_lt.1 hle]⟩
    rw [hm3] at hmem
    exact hne hmem
  · by_contra hle
    have hmem : z ∈ spectrum ℂ (Lin.Lsec χ s ℓ G) ∩ {w : ℂ | 9 / 200 < w.re} :=
      ⟨hz, show 9 / 200 < z.re by linarith [not_lt.1 hle]⟩
    rw [hother ℓ hd h3' hm3'] at hmem
    exact hmem

/-- The sector-wise bound for one sector `ℓ`. -/
theorem exists_secProj_one_sub_bound_single (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) (s : ℕ) {σ' : ℝ} (hσ' : 9 / 200 < σ') (ℓ : ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G ∈ Icc (0 : ℝ) Gbar, ∀ t : ℝ, 0 ≤ t → ∀ w : Y s annN, Lin.MemX w →
      ‖secProj s annN ℓ (Lin.S χ s G t (w - Eig.R χ s G w))‖ ≤
        C * Real.exp (σ' * t) * ‖secProj s annN ℓ w‖ := by
  have hcont := Eig.rieszSec_continuousOn χ hχ hN s
  have hlam := (Eig.propU_a χ hχ hN).1
  by_cases h3 : ℓ = 3
  · subst h3
    obtain ⟨C, hC, hb⟩ := Dunford.exists_norm_exp_mul_one_sub_le_uniform (κ := ℝ)
      (A := fun G => Lin.Lsec χ s 3 G)
      (P := fun G => (ringPhiSetting χ).rieszSec s 3 (Eig.lam χ G) G) (z₀ := Eig.lam χ)
      isCompact_Icc (Lsec_continuous hχ s 3).continuousOn hcont.1 hlam
      (fun G hG => (Eig.lam_SU χ hχ hN hG s).2.2.2.1)
      (fun G hG => (spectrum_re_lt hχ hN hG s hσ').1)
    refine ⟨C, hC, fun G hG t ht w _ => ?_⟩
    rw [secProj_S hχ s G ht, map_sub, (Eig.R_sector χ hχ hN hG s).1 w]
    exact norm_apply_sub_le _ _ _ (hb G hG t ht)
  by_cases hm3 : ℓ = -3
  · subst hm3
    obtain ⟨C, hC, hb⟩ := Dunford.exists_norm_exp_mul_one_sub_le_uniform (κ := ℝ)
      (A := fun G => Lin.Lsec χ s (-3) G)
      (P := fun G => (ringPhiSetting χ).rieszSecBar s 3 (Eig.lam χ G) G)
      (z₀ := fun G => conj (Eig.lam χ G))
      isCompact_Icc (Lsec_continuous hχ s (-3)).continuousOn hcont.2
      (Complex.continuous_conj.comp_continuousOn hlam)
      (fun G hG => (Eig.lam_SU χ hχ hN hG s).2.2.2.2.2.2.1)
      (fun G hG => (spectrum_re_lt hχ hN hG s hσ').2.1)
    refine ⟨C, hC, fun G hG t ht w _ => ?_⟩
    rw [secProj_S hχ s G ht, map_sub, (Eig.R_sector χ hχ hN hG s).2.1 w]
    exact norm_apply_sub_le _ _ _ (hb G hG t ht)
  by_cases hd : (3 : ℤ) ∣ ℓ
  · obtain ⟨C, hC, hb⟩ := Dunford.exists_norm_exp_le_of_spectrum_re_lt_uniform (κ := ℝ)
      (A := fun G => Lin.Lsec χ s ℓ G) isCompact_Icc (Lsec_continuous hχ s ℓ).continuousOn
      (fun G hG => (spectrum_re_lt hχ hN hG s hσ').2.2 ℓ hd h3 hm3)
    refine ⟨C, hC, fun G hG t ht w _ => ?_⟩
    rw [secProj_S hχ s G ht, map_sub, (Eig.R_sector χ hχ hN hG s).2.2.1 ℓ h3 hm3 w, sub_zero]
    exact ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hb G hG t ht) (norm_nonneg _)))
  · refine ⟨1, one_pos, fun G hG t ht w hw => ?_⟩
    rw [secProj_S hχ s G ht, map_sub, (Eig.R_sector χ hχ hN hG s).2.2.1 ℓ h3 hm3 w,
      secProj_eq_zero_of_memX hw hd, sub_zero, map_zero, norm_zero]
    positivity

/-- The bound for large sectors (`prop:large-sectors` with `γ = σ'`). -/
theorem exists_secProj_one_sub_bound_large (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) (s : ℕ) {σ' : ℝ} (hσ' : 0 < σ') :
    ∃ M C : ℝ, 0 < C ∧ ∀ ℓ : ℤ, M ≤ |(ℓ : ℝ)| → ∀ G ∈ Icc (0 : ℝ) Gbar, ∀ t : ℝ, 0 ≤ t →
      ∀ w : Y s annN, Lin.MemX w →
        ‖secProj s annN ℓ (Lin.S χ s G t (w - Eig.R χ s G w))‖ ≤
          C * Real.exp (σ' * t) * ‖secProj s annN ℓ w‖ := by
  obtain ⟨M, C, -, hC, hb⟩ := SectorSetting.largeSectors_opNorm (ringPhiSetting χ)
    (ringPhiSetting_valid hχ) s hσ' Gbar_nonneg
  refine ⟨max M 4, C, hC, fun ℓ hℓ G hG t ht w _ => ?_⟩
  have h4 : (4 : ℝ) ≤ |(ℓ : ℝ)| := (le_max_right M 4).trans hℓ
  have h3 : ℓ ≠ 3 := by
    rintro rfl
    norm_num at h4
  have hm3 : ℓ ≠ -3 := by
    rintro rfl
    norm_num at h4
  have hGabs : |G| ≤ Gbar := by
    rw [abs_of_nonneg hG.1]
    exact hG.2
  rw [secProj_S hχ s G ht, map_sub, (Eig.R_sector χ hχ hN hG s).2.2.1 ℓ h3 hm3 w, sub_zero]
  exact ((ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hb ℓ ((le_max_left M 4).trans hℓ) G hGabs t ht)
      (norm_nonneg _)))

/-- **The sector-wise bound** `‖P_ℓ e^{tL}(1 - R)w‖ ≤ C e^{σ't}‖P_ℓ w‖`, uniformly in `ℓ`,
`G ∈ [0,G₁]`, `t ≥ 0`, `w ∈ X^s` (`04_ring.tex:1455-1490`). -/
theorem exists_secProj_one_sub_bound (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) (s : ℕ) {σ' : ℝ} (hσ' : 9 / 200 < σ') :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℤ, ∀ G ∈ Icc (0 : ℝ) Gbar, ∀ t : ℝ, 0 ≤ t →
      ∀ w : Y s annN, Lin.MemX w →
        ‖secProj s annN ℓ (Lin.S χ s G t (w - Eig.R χ s G w))‖ ≤
          C * Real.exp (σ' * t) * ‖secProj s annN ℓ w‖ := by
  have hσ'0 : 0 < σ' := by linarith
  obtain ⟨M, C₀, hC₀, hlarge⟩ := exists_secProj_one_sub_bound_large hχ hN s hσ'0
  refine exists_uniform_of_large
    (fun ℓ C => ∀ G ∈ Icc (0 : ℝ) Gbar, ∀ t : ℝ, 0 ≤ t → ∀ w : Y s annN, Lin.MemX w →
      ‖secProj s annN ℓ (Lin.S χ s G t (w - Eig.R χ s G w))‖ ≤
        C * Real.exp (σ' * t) * ‖secProj s annN ℓ w‖) ?_
    (exists_secProj_one_sub_bound_single hχ hN s hσ') hC₀ hlarge
  intro ℓ C C' hCC' hQ G hG t ht w hw
  exact (hQ G hG t ht w hw).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCC' (Real.exp_pos _).le) (norm_nonneg _))

/-- Uniform bound on the sector projections `R_{±3}(G)` on `[0,G₁]`. -/
theorem exists_rieszSec_bound (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G ∈ Icc (0 : ℝ) Gbar,
      ‖(ringPhiSetting χ).rieszSec s 3 (Eig.lam χ G) G‖ ≤ K ∧
        ‖(ringPhiSetting χ).rieszSecBar s 3 (Eig.lam χ G) G‖ ≤ K := by
  have hcont := Eig.rieszSec_continuousOn χ hχ hN s
  obtain ⟨K₁, hK₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (E := Ysec s (ringPhiSetting χ).Nstar ((3 : ℕ) : ℤ) →L[ℂ]
      Ysec s (ringPhiSetting χ).Nstar ((3 : ℕ) : ℤ)) hcont.1
  obtain ⟨K₂, hK₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (E := Ysec s (ringPhiSetting χ).Nstar (-((3 : ℕ) : ℤ)) →L[ℂ]
      Ysec s (ringPhiSetting χ).Nstar (-((3 : ℕ) : ℤ))) hcont.2
  refine ⟨max (max K₁ K₂) 0, le_max_right _ _, fun G hG => ⟨?_, ?_⟩⟩
  · exact (hK₁ G hG).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hK₂ G hG).trans ((le_max_right _ _).trans (le_max_left _ _))

/-- Sector-wise bounds for `R(G)` and `e^{tL(G)}R(G)`. -/
theorem secProj_R_bounds (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) (s : ℕ)
    {K : ℝ} (hK : 0 ≤ K) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar)
    (hKG : ‖(ringPhiSetting χ).rieszSec s 3 (Eig.lam χ G) G‖ ≤ K ∧
        ‖(ringPhiSetting χ).rieszSecBar s 3 (Eig.lam χ G) G‖ ≤ K)
    {t : ℝ} (ht : 0 ≤ t) (w : Y s annN) (ℓ : ℤ) :
    ‖secProj s annN ℓ (Eig.R χ s G w)‖ ≤ K * ‖secProj s annN ℓ w‖ ∧
      ‖secProj s annN ℓ (Lin.S χ s G t (Eig.R χ s G w))‖ ≤
        K * Real.exp (Eig.sigma χ G * t) * ‖secProj s annN ℓ w‖ := by
  obtain ⟨-, -, -, hsp3, -, -, hspm3, -⟩ := Eig.lam_SU χ hχ hN hG s
  obtain ⟨hR3, hRm3, hRo, -, -⟩ := Eig.R_sector χ hχ hN hG s
  by_cases h3 : ℓ = 3
  · subst h3
    rw [hR3 w, secProj_S hχ s G ht, hR3 w]
    have hP : ‖(ringPhiSetting χ).rieszSec s 3 (Eig.lam χ G) G (secProj s annN 3 w)‖ ≤
        K * ‖secProj s annN 3 w‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hKG.1 (norm_nonneg _))
    refine ⟨hP, ?_⟩
    have h1 := norm_exp_proj_apply _ _ _ hsp3.mul_proj t (secProj s annN 3 w)
    refine (le_of_eq h1).trans ((mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le).trans
      (le_of_eq ?_))
    rw [Eig.sigma, mul_comm t]
    ring
  by_cases hm3 : ℓ = -3
  · subst hm3
    rw [hRm3 w, secProj_S hχ s G ht, hRm3 w]
    have hP : ‖(ringPhiSetting χ).rieszSecBar s 3 (Eig.lam χ G) G (secProj s annN (-3) w)‖ ≤
        K * ‖secProj s annN (-3) w‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hKG.2 (norm_nonneg _))
    refine ⟨hP, ?_⟩
    have h1 := norm_exp_proj_apply _ _ _ hspm3.mul_proj t (secProj s annN (-3) w)
    refine (le_of_eq h1).trans ((mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le).trans
      (le_of_eq ?_))
    rw [Complex.conj_re, Eig.sigma, mul_comm t]
    ring
  · rw [secProj_S hχ s G ht, hRo ℓ h3 hm3 w, map_zero, norm_zero]
    exact ⟨by positivity, by positivity⟩

end PropSemigroupH

end NonUniqueEuler
