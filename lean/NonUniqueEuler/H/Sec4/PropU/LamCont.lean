import NonUniqueEuler.H.Sec4.PropU.Basic
import NonUniqueEuler.I.Sec4.PropSU
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Infra.SectorSpace.RadialMul
import NonUniqueEuler.I.Evans.ODE
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Helpers for `P/Sec4/PropU`: continuity of `λ_*` on `[0, G₁]` (`prop:U`(a), restructuring R9)

* `exists_bound_Lsec`: `sup_{G ∈ [0,G₁]} ‖L_3(G)‖_{X^0_3 → X^0_3} < ∞`, because
  `L_3(G) = -3iΩ(·;0) - 3iG r⁻² + k_3𝒢_3` is affine in `G` (`Omega_eq_add`, `radialMul_add`);
* `exists_bound_lam`: `|λ_*(G)| ≤ ‖L_3(G)‖` (`λ_*(G)` is in the spectrum, `lam_SU`), so the
  `λ_*(G)` are bounded;
* `lam_continuousOn`: every cluster point `μ` of `λ_*(G')` as `G' → G` is a zero of
  `E_3(·;R_c²G)` (joint continuity of `E_3`, `evans_continuousOn`) with `Re μ ≥ 211/2500`, so
  `μ = λ_*(G)` by the uniqueness in (N1) (`hypN_lamC`); compactness gives continuity.
-/

noncomputable section

open MeasureTheory Set Real ComplexConjugate Filter Topology

namespace NonUniqueEuler

namespace Eig

namespace PropUH

open RingData Sect

/-- A function continuous on `(0,∞)` is `C^0` on `[ρ₋, ρ₊]` (`ρ₋ > 0`). -/
theorem memCk_zero_of_continuousOn {f : ℝ → ℂ} {ρm ρp : ℝ} (hρm : 0 < ρm)
    (hf : ContinuousOn f (Ioi 0)) : MemCk 0 (Icc ρm ρp) f := by
  have hsub : Icc ρm ρp ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le hρm hx.1
  refine ⟨⟨Ioi 0, isOpen_Ioi, hsub, ?_⟩, ?_⟩
  · simpa using (contDiffOn_zero (𝕜 := ℝ)).mpr hf
  · obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.mono hsub)
    refine normCkE_ne_top_of_bound (fun _ => C) fun q hq x hx => ?_
    have hq0 : q = 0 := by omega
    subst hq0
    simpa using hC x hx

/-- A point of the spectrum of a bounded operator on a Banach space has modulus at most the
operator norm (generic form; avoids instance search on the concrete operator algebras). -/
theorem norm_le_of_mem_spectrum {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] (T : X →L[ℂ] X) {k : ℂ} (h : k ∈ spectrum ℂ T) : ‖k‖ ≤ ‖T‖ := by
  calc ‖k‖ ≤ ‖T‖ * ‖(1 : X →L[ℂ] X)‖ := spectrum.norm_le_norm_mul_of_mem h
    _ ≤ ‖T‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
    _ = ‖T‖ := mul_one _

/-- The triangle inequality for operators (generic form). -/
theorem opNorm_add_le' {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T U : X →L[ℂ] X) : ‖T + U‖ ≤ ‖T‖ + ‖U‖ := norm_add_le T U

/-- `‖T + c U‖ ≤ ‖T‖ + b ‖U‖` for `|c| ≤ b` (generic form). -/
theorem opNorm_add_smul_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T U : X →L[ℂ] X) {c : ℂ} {b : ℝ} (hc : ‖c‖ ≤ b) : ‖T + c • U‖ ≤ ‖T‖ + b * ‖U‖ := by
  refine (norm_add_le T (c • U)).trans ?_
  rw [norm_smul]
  gcongr

/-- `‖L_3(G)‖` on `X^0_3` is bounded for `G ∈ [0, G₁]`. -/
theorem exists_bound_Lsec {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    ∃ M : ℝ, ∀ G ∈ Icc (0 : ℝ) Gbar, ‖Lin.Lsec χ 0 3 G‖ ≤ M := by
  obtain ⟨-, -, -, -, -, -, -, ha0, ha1⟩ := ringData_order
  have hρm : (0 : ℝ) < a / 2 := by linarith
  have hρ : a / 2 < (2 : ℝ) := by linarith
  have hS := ringPhiSetting_valid hχ
  set A : ℝ → ℂ := fun r => -(Complex.I * ((3 : ℤ) : ℂ) * (((ringPhiSetting χ).Omega 0 r : ℝ) : ℂ))
    with hAdef
  set B : ℝ → ℂ := fun r => -(Complex.I * ((3 : ℤ) : ℂ) * (((r ^ 2)⁻¹ : ℝ) : ℂ)) with hBdef
  have hA : MemCk 0 (Icc (a / 2) 2) A := by
    refine memCk_zero_of_continuousOn hρm ?_
    have h := (SectorSetting.contDiffOn_Omega (ringPhiSetting χ) hS 0).continuousOn
    exact ((Complex.continuous_ofReal.comp_continuousOn h).const_smul
      (Complex.I * ((3 : ℤ) : ℂ))).neg
  have hB : MemCk 0 (Icc (a / 2) 2) B := by
    refine memCk_zero_of_continuousOn hρm ?_
    have h : ContinuousOn (fun r : ℝ => (r ^ 2)⁻¹) (Ioi 0) :=
      (continuous_pow 2).continuousOn.inv₀ fun r hr => pow_ne_zero 2 (ne_of_gt hr)
    exact ((Complex.continuous_ofReal.comp_continuousOn h).const_smul
      (Complex.I * ((3 : ℤ) : ℂ))).neg
  refine ⟨‖radialMul 0 (closedAnnulus (a / 2) 2) 3 A‖ +
    Gbar * ‖radialMul 0 (closedAnnulus (a / 2) 2) 3 B‖ + ‖(ringPhiSetting χ).Ksec 0 3‖,
    fun G hG => ?_⟩
  have htr : (ringPhiSetting χ).transSec 0 3 G =
      radialMul 0 (closedAnnulus (a / 2) 2) 3 A +
        (G : ℂ) • radialMul 0 (closedAnnulus (a / 2) 2) 3 B := by
    rw [← radialMul_add hρm hρ 3 hA hB]
    show radialMul 0 (closedAnnulus (a / 2) 2) 3 _ = _
    congr 1
    funext r
    simp only [hAdef, hBdef, SectorSetting.Omega_eq_add (ringPhiSetting χ) G r]
    push_cast
    ring
  have hG' : ‖(G : ℂ)‖ ≤ Gbar := by
    rw [Complex.norm_real, Real.norm_of_nonneg hG.1]; exact hG.2
  calc ‖Lin.Lsec χ 0 3 G‖
      = ‖(ringPhiSetting χ).transSec 0 3 G + (ringPhiSetting χ).Ksec 0 3‖ := rfl
    _ ≤ ‖(ringPhiSetting χ).transSec 0 3 G‖ + ‖(ringPhiSetting χ).Ksec 0 3‖ :=
        opNorm_add_le' _ _
    _ ≤ _ := by
      rw [htr]
      gcongr
      exact opNorm_add_smul_le _ _ hG'

/-- The `λ_*(G)`, `G ∈ [0, G₁]`, are bounded: `|λ_*(G)| ≤ ‖L_3(G)‖`. -/
theorem exists_bound_lam {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ∃ M : ℝ, ∀ G ∈ Icc (0 : ℝ) Gbar, ‖lam χ G‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_Lsec hχ
  refine ⟨M, fun G hG => ?_⟩
  have h := (lam_SU χ hχ hN hG 0).2.1
  have hmem : lam χ G ∈ spectrum ℂ (Lin.Lsec χ 0 3 G) := by
    have : lam χ G ∈ ({lam χ G} : Set ℂ) := rfl
    rw [← h] at this
    exact this.1
  exact (norm_le_of_mem_spectrum _ hmem).trans (hM G hG)

/-- **`prop:U`(a), continuity (R9)**: `λ_*` is continuous on `[0, G₁]`. -/
theorem lam_continuousOn {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (lam χ) (Icc 0 Gbar) := by
  obtain ⟨M, hM⟩ := exists_bound_lam hχ hN
  set K : Set ℂ := Metric.closedBall 0 M ∩ {z | 211 / 2500 ≤ z.re} with hKdef
  have hK : IsCompact K :=
    (isCompact_closedBall 0 M).inter_right (isClosed_le continuous_const Complex.continuous_re)
  intro G₀ hG₀
  refine hK.tendsto_nhds_of_unique_mapClusterPt ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with G hG
    exact ⟨by simpa using hM G hG, (eig_facts hχ hN hG).1.le⟩
  · intro y hyK hy
    obtain ⟨-, -, -, -, -, huniq⟩ := eig_facts hχ hN hG₀
    have hypos : 0 < y.re := lt_of_lt_of_le (by norm_num) hyK.2
    refine huniq y (le_trans (by norm_num) hyK.2) ?_
    by_contra hne
    have hopen : IsOpen {p : ℂ × ℝ | 0 < p.1.re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)
    have hcont : ContinuousAt (fun p : ℂ × ℝ => evans χ 3 p.1 p.2) (y, Rc ^ 2 * G₀) :=
      (evans_continuousOn χ hχ 3).continuousAt (hopen.mem_nhds hypos)
    have hev : ∀ᶠ p in 𝓝 (y, Rc ^ 2 * G₀), evans χ 3 p.1 p.2 ≠ 0 := hcont.eventually_ne hne
    rw [nhds_prod_eq] at hev
    obtain ⟨pa, hpa, pb, hpb, hpab⟩ := Filter.eventually_prod_iff.1 hev
    have htend : Tendsto (fun G : ℝ => Rc ^ 2 * G) (𝓝[Icc 0 Gbar] G₀) (𝓝 (Rc ^ 2 * G₀)) :=
      ((continuous_const.mul continuous_id).tendsto G₀).mono_left nhdsWithin_le_nhds
    have hV : ∀ᶠ G in 𝓝[Icc 0 Gbar] G₀, pb (Rc ^ 2 * G) ∧ G ∈ Icc 0 Gbar :=
      (htend.eventually hpb).and self_mem_nhdsWithin
    have hfr : ∃ᶠ G in 𝓝[Icc 0 Gbar] G₀, pa (lam χ G) := hy.frequently hpa
    obtain ⟨G, hGa, hGb, hGI⟩ := (hfr.and_eventually hV).exists
    exact hpab hGa hGb (hypN_lamC χ hN.n1 hN.n2 (Rc_sq_mul_mem hGI)).2.1

end PropUH

end Eig

end NonUniqueEuler
