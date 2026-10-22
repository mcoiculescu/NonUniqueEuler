import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec4.PropU
import NonUniqueEuler.I.Sec4.PropSU
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Infra.Polar.RadialDeriv
import NonUniqueEuler.I.Infra.Sobolev.Local
import NonUniqueEuler.I.Infra.CkNorm.Basic

/-!
# Proof: the rate `Λ(s)` of `eq:Lambda` and its ingredients

Proof of `I/Sec5/Lambda.lean` (`eq:Lambda`, `05_single_ring.tex:282-298`; `lem:energy`,
`:302-304`).

* `C^s(N')` controls `W^{1,∞}(N₁)` and `H^s(N₁)` (`Sob.MemCk.memW1infOn`, `Sob.MemCk.memHOn`,
  `I/Infra/Sobolev/Local.lean`) with the constant `3 + (s+1)|N₁|^{1/2}`, so the admissible set of
  `C_{N'}` is nonempty; it is closed and bounded below by `0`, hence contains its infimum
  (`IsClosed.isLeast_csInf`).
* `Ω(·;G)` is smooth on `(0,∞)` (`SectorSetting.contDiffOn_Omega` for the valid setting
  `ringPhiSetting χ`), hence `Ω(|x|;G)x^⊥` is smooth on `ℂ \ {0} ⊇ N'` and lies in `C^s(N')`
  (`IsCkNear.memCk_of_isCompact`). It is affine in `G`:
  `omegaField χ G = omegaField χ 0 + G • (omegaField χ 1 - omegaField χ 0)`, which gives the
  uniform bound on `[0,G₁]` (triangle inequality and homogeneity of `C^s` norms).
* The maximum of `σ` on `[0,G₁]` is attained (`Eig.propU_a`), and `σ(0) > 0` (`Eig.lam_SU`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff

namespace NonUniqueEuler

namespace OneRing

open RingData

namespace LambdaAux

/-- `N₁` has finite measure (it lies in `B_3`). -/
theorem volume_annN1_lt_top : volume annN1 < ⊤ :=
  (measure_mono fun y (hy : y ∈ annN1) => mem_ball_zero_iff.2 hy.2).trans_lt measure_ball_lt_top

/-- The admissible constant `3 + (s+1)|N₁|^{1/2}` for `C_{N'}`. -/
def C0 (s : ℕ) : ℝ := 3 + (s + 1) * Real.sqrt (volume annN1).toReal

theorem C0_nonneg (s : ℕ) : 0 ≤ C0 s := by
  unfold C0
  positivity

/-- `C^s(N')` controls `W^{1,∞}(N₁)` and `H^s(N₁)`, for `s ≥ 1`. -/
theorem ck_control {s : ℕ} (hs : 1 ≤ s) {hf : ℂ → ℂ} (hh : MemCk s annN' hf) :
    Sob.MemW1infOn annN1 hf ∧ Sob.MemHOn s annN1 hf ∧
      Sob.normW1infOn annN1 hf + Sob.normHOn s annN1 hf ≤ C0 s * normCk s annN' hf := by
  have h1 := Sob.MemCk.memW1infOn isOpen_annN1 annN1_subset_annN' (hh.mono_order hs)
  have h2 := Sob.MemCk.memHOn isOpen_annN1 annN1_subset_annN' volume_annN1_lt_top hh
  have h3 : normCk 1 annN' hf ≤ normCk s annN' hf := normCk_mono_order hh hs
  refine ⟨h1.1, h2.1, ?_⟩
  calc Sob.normW1infOn annN1 hf + Sob.normHOn s annN1 hf
      ≤ 3 * normCk s annN' hf +
          (s + 1) * Real.sqrt (volume annN1).toReal * normCk s annN' hf :=
        add_le_add (h1.2.trans (by linarith)) h2.2
    _ = C0 s * normCk s annN' hf := by unfold C0; ring

/-- The admissible set of `C_{N'}` is closed. -/
theorem isClosed_admissible (s : ℕ) :
    IsClosed {C : ℝ | 0 ≤ C ∧ ∀ hf : ℂ → ℂ, MemCk s annN' hf →
      Sob.normW1infOn annN1 hf + Sob.normHOn s annN1 hf ≤ C * normCk s annN' hf} := by
  have : {C : ℝ | 0 ≤ C ∧ ∀ hf : ℂ → ℂ, MemCk s annN' hf →
      Sob.normW1infOn annN1 hf + Sob.normHOn s annN1 hf ≤ C * normCk s annN' hf} =
      Ici 0 ∩ ⋂ hf : ℂ → ℂ, ⋂ (_ : MemCk s annN' hf),
        {C : ℝ | Sob.normW1infOn annN1 hf + Sob.normHOn s annN1 hf ≤ C * normCk s annN' hf} := by
    ext C
    simp
  rw [this]
  refine isClosed_Ici.inter (isClosed_iInter fun hf => isClosed_iInter fun _ => ?_)
  exact isClosed_le continuous_const (continuous_id.mul continuous_const)

/-- `C_{N'}` is the least admissible constant. -/
theorem isLeast_CNprime {s : ℕ} (hs : 1 ≤ s) :
    IsLeast {C : ℝ | 0 ≤ C ∧ ∀ hf : ℂ → ℂ, MemCk s annN' hf →
      Sob.normW1infOn annN1 hf + Sob.normHOn s annN1 hf ≤ C * normCk s annN' hf}
      (CNprime s) :=
  (isClosed_admissible s).isLeast_csInf
    ⟨C0 s, C0_nonneg s, fun _ hh => (ck_control hs hh).2.2⟩ ⟨0, fun _ hC => hC.1⟩

theorem a_pos : 0 < a := Real.exp_pos _

theorem annN'_subset_compl_zero : annN' ⊆ ({0} : Set ℂ)ᶜ := by
  intro x hx
  have hx' : a / 4 ≤ ‖x‖ := hx.1
  have : 0 < ‖x‖ := lt_of_lt_of_le (by have := a_pos; positivity) hx'
  simpa [norm_pos_iff] using this

/-- `Ω(|x|;G)x^⊥` is smooth on `ℂ \ {0}`. -/
theorem omegaField_contDiffOn {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (G : ℝ) :
    ContDiffOn ℝ ∞ (omegaField χ G) ({0} : Set ℂ)ᶜ := by
  have hΩ : ContDiffOn ℝ ∞ (Lin.Omega χ G) (Ioi 0) :=
    SectorSetting.contDiffOn_Omega _ (ringPhiSetting_valid hχ) G
  have hr : ContDiffOn ℝ ∞ (fun x : ℂ => Lin.Omega χ G ‖x‖) ({0} : Set ℂ)ᶜ :=
    Polar.contDiffOn_comp_norm hΩ
  have hc : ContDiffOn ℝ ∞ (fun x : ℂ => ((Lin.Omega χ G ‖x‖ : ℝ) : ℂ)) ({0} : Set ℂ)ᶜ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hr
  have hI : ContDiffOn ℝ ∞ (fun x : ℂ => Complex.I * x) ({0} : Set ℂ)ᶜ :=
    (contDiff_const.mul contDiff_id).contDiffOn
  exact hc.mul hI

theorem memCk_omegaField {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (s : ℕ) (G : ℝ) :
    MemCk s annN' (omegaField χ G) :=
  IsCkNear.memCk_of_isCompact
    ⟨({0} : Set ℂ)ᶜ, isOpen_compl_singleton, annN'_subset_compl_zero,
      (omegaField_contDiffOn hχ G).of_le (by exact_mod_cast le_top)⟩ isCompact_annN'

/-- `Ω(r;G)` is affine in `G`. -/
theorem omegaField_affine (χ : ℝ → ℝ) (G : ℝ) :
    omegaField χ G = omegaField χ 0 + G • (omegaField χ 1 - omegaField χ 0) := by
  funext x
  simp only [omegaField, Lin.Omega, SectorSetting.Omega, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, Complex.real_smul]
  push_cast
  ring

/-- The uniform bound `‖Ω(|x|;G)x^⊥‖_{C^s(N')} ≤ A + G₁ B` on `[0,G₁]`. -/
theorem normCk_omegaField_le {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (s : ℕ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) :
    normCk s annN' (omegaField χ G) ≤ normCk s annN' (omegaField χ 0) +
      Gbar * normCk s annN' (omegaField χ 1 - omegaField χ 0) := by
  have h0 := memCk_omegaField hχ s 0
  have hd' : MemCk s annN' (omegaField χ 1 - omegaField χ 0) :=
    ((memCk_omegaField hχ s 1).sub h0).1
  have hadd := (h0.add (hd'.smul G)).2
  rw [normCk_smul, abs_of_nonneg hG.1] at hadd
  rw [omegaField_affine χ G]
  refine hadd.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_right hG.2 (normCk_nonneg _ _ _)

/-- The maximum of `σ` on `[0,G₁]` is attained, and it is `sigmaMax χ`. -/
theorem isGreatest_sigmaMax {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) : IsGreatest (Eig.sigma χ '' Icc 0 Gbar) (sigmaMax χ) := by
  obtain ⟨-, -, -, -, G₁, hG₁, hmax⟩ := Eig.propU_a χ hχ hN
  have hgr : IsGreatest (Eig.sigma χ '' Icc 0 Gbar) (Eig.sigma χ G₁) :=
    ⟨mem_image_of_mem _ hG₁, by rintro _ ⟨G, hG, rfl⟩; exact hmax G hG⟩
  unfold sigmaMax
  rw [hgr.csSup_eq]
  exact hgr

theorem Gbar_nonneg : 0 ≤ Gbar := by
  unfold Gbar
  positivity

end LambdaAux

open LambdaAux in
/-- **The ingredients of `Λ(s)` are finite** (`05_single_ring.tex:284-298`), for an integer
`s ≥ 3`: the field `Ω(|x|;G)x^⊥` lies in `W^{1,∞}(N₁)` and `H^s(N₁)` for `G ∈ [0,G₁]` and the
sums of its norms are bounded above (`C_Ω < ∞`); every `h ∈ C^s(N';ℝ²)` lies in `W^{1,∞}(N₁)` and
`H^s(N₁)`, and `C_{N'} = CNprime s` is the least admissible constant; the maximum of `σ` on
`[0,G₁]` is attained and is `sigmaMax χ`. -/
theorem lambda_consts (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 3 ≤ s) :
    (∀ G ∈ Icc (0 : ℝ) Gbar,
        Sob.MemW1infOn annN1 (omegaField χ G) ∧ Sob.MemHOn s annN1 (omegaField χ G)) ∧
      BddAbove ((fun G => Sob.normW1infOn annN1 (omegaField χ G) +
        Sob.normHOn s annN1 (omegaField χ G)) '' Icc 0 Gbar) ∧
      (∀ hf : ℂ → ℂ, MemCk s annN' hf → Sob.MemW1infOn annN1 hf ∧ Sob.MemHOn s annN1 hf) ∧
      IsLeast {C : ℝ | 0 ≤ C ∧ ∀ hf : ℂ → ℂ, MemCk s annN' hf →
        Sob.normW1infOn annN1 hf + Sob.normHOn s annN1 hf ≤ C * normCk s annN' hf}
        (CNprime s) ∧
      IsGreatest (Eig.sigma χ '' Icc 0 Gbar) (sigmaMax χ) := by
  have hs1 : 1 ≤ s := by omega
  refine ⟨fun G _ => ?_, ?_, fun hf hh => ?_, isLeast_CNprime hs1, isGreatest_sigmaMax hχ hN⟩
  · have := ck_control hs1 (memCk_omegaField hχ s G)
    exact ⟨this.1, this.2.1⟩
  · refine ⟨C0 s * (normCk s annN' (omegaField χ 0) +
      Gbar * normCk s annN' (omegaField χ 1 - omegaField χ 0)), ?_⟩
    rintro _ ⟨G, hG, rfl⟩
    exact (ck_control hs1 (memCk_omegaField hχ s G)).2.2.trans
      (mul_le_mul_of_nonneg_left (normCk_omegaField_le hχ s hG) (C0_nonneg s))
  · have := ck_control hs1 hh
    exact ⟨this.1, this.2.1⟩

set_option linter.unusedVariables false in
open LambdaAux in
/-- **`Λ(s) ≥ 2 max σ`, and `Λ(s) > 0`** (`05_single_ring.tex:302-304`): for an integer `s ≥ 3`
and every `G ∈ [0,G₁]`, `2σ(G) ≤ Λ(s)`; and `0 < Λ(s)`. -/
theorem lambda_ge (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 3 ≤ s) :
    (∀ G ∈ Icc (0 : ℝ) Gbar, 2 * Eig.sigma χ G ≤ Lam χ s) ∧ 0 < Lam χ s := by
  have hgr := isGreatest_sigmaMax hχ hN
  have hle : ∀ G ∈ Icc (0 : ℝ) Gbar, 2 * Eig.sigma χ G ≤ Lam χ s := fun G hG =>
    (mul_le_mul_of_nonneg_left (hgr.2 (mem_image_of_mem _ hG)) (by norm_num)).trans
      (two_mul_sigmaMax_le_Lam χ s)
  refine ⟨hle, ?_⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) Gbar := ⟨le_rfl, Gbar_nonneg⟩
  have hσ : 211 / 2500 < Eig.sigma χ 0 := (Eig.lam_SU χ hχ hN h0 s).1
  linarith [hle 0 h0]

end OneRing

end NonUniqueEuler
