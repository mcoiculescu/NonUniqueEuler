import NonUniqueEuler.I.Sec2.BSSmooth
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Infra.Sobolev.Local
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv

/-!
# Helper for `P/Sec2/HkCalculus/CutoffBS`: the smooth case of `lem:Hk-calculus`(3)

Manuscript: `02_prelim.tex:748-759`. For a real `h ∈ C_c^∞` with `tsupport h ⊆ B_{2ρ}` and
`u = K_BS ∗ h`:
* `u ∈ H^{j+1}(B_ρ)` with `‖u‖_{H^{j+1}(B_ρ)} ≤ #(multiIdx (j+1))^{1/2} max(1, 3ρ) ‖h‖_{H^j}`
  (`lem:BS-basic`(c) with `R = ρ` and support radius `2ρ` for `γ = 0`; `lem:BS-basic`(d) for
  `γ ≠ 0`: `∂^γ u = ∂_l ∂^β u` with `|β| = |γ| - 1 ≤ j` and `‖∂_l ∂^β u‖_{L²} ≤ ‖∂^β h‖_{L²}`);
* `χ u ∈ H^{j+1}` with `‖χ u‖_{H^{j+1}} ≤ C₁ ‖h‖_{H^j}`, by the cutoff extension
  `Sob.exists_normH_mul_testFn_le` (`I/Infra/Sobolev/Local.lean`).

Deviation (restructuring of the manuscript's argument, same estimate): instead of expanding
`∂^γ(χu)` by the Leibniz formula, the local `H^{j+1}(B_ρ)` norm of `u` is bounded first and the
cutoff extension lemma (which encapsulates the Leibniz formula) is applied.

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob.CutoffBSAux

/-- `∂^γ f = ∂_l ∂^β f` with `|β| + 1 = |γ|`, for `γ ≠ 0` (the first direction of `pdList γ`). -/
theorem exists_partialD_eq_pd {γ : ℕ × ℕ} (hγ : γ ≠ (0, 0)) (f : ℂ → ℂ) :
    ∃ β : ℕ × ℕ, ∃ l : Fin 2, β.1 + β.2 + 1 = γ.1 + γ.2 ∧
      partialD γ f = Prelim.pd l (partialD β f) := by
  obtain ⟨a, b⟩ := γ
  cases a with
  | succ a =>
    refine ⟨(a, b), 0, by simp only; omega, ?_⟩
    funext x
    simp [partialD, pdList, List.replicate_succ, Prelim.pd, Prelim.e2, dirDeriv]
  | zero =>
    cases b with
    | zero => exact absurd rfl hγ
    | succ b =>
      refine ⟨(0, b), 1, by simp only; omega, ?_⟩
      funext x
      simp [partialD, pdList, List.replicate_succ, Prelim.pd, Prelim.e2, dirDeriv]

theorem partialD_zero (f : ℂ → ℂ) : partialD (0, 0) f = f := by
  simp [partialD, pdList]

/-- `‖f‖_{L²(V)} ≤ ‖f‖_{L²}` for `f ∈ L²`. -/
theorem l2On_le_l2 {V : Set ℂ} {f : ℂ → ℂ} (hf : MemLp f 2 volume) : l2On V f ≤ l2 f := by
  unfold l2On l2
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- A term of a sum of squares is at most the square root of the sum. -/
theorem le_sqrt_sum_sq {ι : Type*} {s : Finset ι} {a : ι → ℝ} {i : ι} (hi : i ∈ s)
    (ha : 0 ≤ a i) : a i ≤ Real.sqrt (∑ j ∈ s, a j ^ 2) := by
  rw [Real.le_sqrt ha (Finset.sum_nonneg fun j _ => sq_nonneg (a j))]
  exact Finset.single_le_sum (f := fun j => a j ^ 2) (fun j _ => sq_nonneg (a j)) hi

/-- `‖(h : ℂ)‖_{L²} = ‖h‖_{L²}` for a real function. -/
theorem eLpNorm_ofReal (h : ℂ → ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x => (h x : ℂ)) p volume = eLpNorm h p volume :=
  eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => by simp)

/-- The local `H^{j+1}(B_ρ)` bound for the velocity of a smooth compactly supported real
vorticity with `tsupport h ⊆ B_{2ρ}` (`02_prelim.tex:750-757`). -/
theorem velocity_memHOn_ball (j : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {h : ℂ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (hts : tsupport h ⊆ ball (0 : ℂ) (2 * ρ)) :
    MemHOn (j + 1) (ball (0 : ℂ) ρ) (velocity h) ∧
      normHOn (j + 1) (ball (0 : ℂ) ρ) (velocity h) ≤
        Real.sqrt ((multiIdx (j + 1)).card : ℝ) * max 1 (3 * ρ) *
          normH j (fun x => (h x : ℂ)) := by
  have hu : ContDiff ℝ ∞ (velocity h) := (BS.contDiff_velocity_of_smooth hh hhc).1
  have hhC : ContDiff ℝ ∞ (fun x => (h x : ℂ)) := Complex.ofRealCLM.contDiff.comp hh
  have hhCc : HasCompactSupport (fun x => (h x : ℂ)) := hhc.comp_left Complex.ofReal_zero
  obtain ⟨hH, -, hHnorm⟩ := memH_of_contDiff_hasCompactSupport hhC hhCc j
  have hsupp : ∀ᵐ y, y ∉ ball (0 : ℂ) (2 * ρ) → h y = 0 :=
    Filter.Eventually.of_forall fun y hy => image_eq_zero_of_notMem_tsupport fun h' => hy (hts h')
  have hL2h : MemLp h 2 volume := hh.continuous.memLp_of_hasCompactSupport hhc
  obtain ⟨-, hballL2, hballle⟩ :=
    BS.velocity_L2_ball_le (by linarith : (0 : ℝ) < 2 * ρ) hρ hL2h hsupp
  set A : ℝ := max 1 (3 * ρ) * normH j (fun x => (h x : ℂ)) with hA
  have hHnn : 0 ≤ normH j (fun x => (h x : ℂ)) := normH_nonneg _ _
  have hA0 : 0 ≤ A := mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hHnn
  -- termwise bounds
  have hterm : ∀ γ ∈ multiIdx (j + 1),
      MemLp (partialD γ (velocity h)) 2 (volume.restrict (ball (0 : ℂ) ρ)) ∧
        l2On (ball (0 : ℂ) ρ) (partialD γ (velocity h)) ≤ A := by
    intro γ hγ
    by_cases h0 : γ = (0, 0)
    · subst h0
      rw [partialD_zero]
      refine ⟨hballL2, ?_⟩
      have h1 : l2On (ball (0 : ℂ) ρ) (velocity h) ≤ 3 * ρ * l2 (fun x => (h x : ℂ)) := by
        unfold l2On l2
        rw [eLpNorm_ofReal]
        have hne : ENNReal.ofReal (ρ + 2 * ρ) * eLpNorm h 2 volume ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL2h.eLpNorm_ne_top
        calc (eLpNorm (velocity h) 2 (volume.restrict (ball 0 ρ))).toReal
            ≤ (ENNReal.ofReal (ρ + 2 * ρ) * eLpNorm h 2 volume).toReal :=
              ENNReal.toReal_mono hne hballle
          _ = 3 * ρ * (eLpNorm h 2 volume).toReal := by
              rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
              ring
      have h2 : l2 (fun x => (h x : ℂ)) ≤ normH j (fun x => (h x : ℂ)) := hH.l2_le
      calc l2On (ball (0 : ℂ) ρ) (velocity h) ≤ 3 * ρ * l2 (fun x => (h x : ℂ)) := h1
        _ ≤ 3 * ρ * normH j (fun x => (h x : ℂ)) :=
            mul_le_mul_of_nonneg_left h2 (by linarith)
        _ ≤ A := mul_le_mul_of_nonneg_right (le_max_right _ _) hHnn
    · obtain ⟨β, l, hβ, heq⟩ := exists_partialD_eq_pd h0 (velocity h)
      have hγ1 : 1 ≤ γ.1 + γ.2 := by omega
      have hβj : β ∈ multiIdx j := by
        rw [mem_multiIdx] at hγ ⊢
        omega
      have hmem := (BS.memLp_partialD_velocity_of_smooth hh hhc hγ1).1
      refine ⟨hmem.restrict _, ?_⟩
      obtain ⟨hpdL2, hsum⟩ := BS.sum_l2_pd_partialD_velocity_of_smooth hh hhc β
      have h1 : l2 (partialD γ (velocity h)) ≤ l2 (partialD β (fun y => (h y : ℂ))) := by
        rw [heq]
        have hle : l2 (Prelim.pd l (partialD β (velocity h))) ^ 2 ≤
            l2 (partialD β (fun y => (h y : ℂ))) ^ 2 := by
          rw [← hsum]
          exact Finset.single_le_sum
            (f := fun l' => l2 (Prelim.pd l' (partialD β (velocity h))) ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ l)
        exact (pow_le_pow_iff_left₀ (l2_nonneg _) (l2_nonneg _) (by norm_num)).1 hle
      have h2 : l2 (partialD β (fun y => (h y : ℂ))) ≤ normH j (fun x => (h x : ℂ)) := by
        rw [hHnorm]
        exact le_sqrt_sum_sq (a := fun γ => l2 (partialD γ (fun y => (h y : ℂ)))) hβj
          (l2_nonneg _)
      calc l2On (ball (0 : ℂ) ρ) (partialD γ (velocity h)) ≤ l2 (partialD γ (velocity h)) :=
            l2On_le_l2 hmem
        _ ≤ normH j (fun x => (h x : ℂ)) := h1.trans h2
        _ = 1 * normH j (fun x => (h x : ℂ)) := (one_mul _).symm
        _ ≤ A := mul_le_mul_of_nonneg_right (le_max_left _ _) hHnn
  have hcd : ContDiffOn ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (velocity h) (ball (0 : ℂ) ρ) :=
    (contDiff_infty.1 hu (j + 1)).contDiffOn
  have hL2 : ∀ γ ∈ multiIdx (j + 1),
      MemLp (partialD γ (velocity h)) 2 (volume.restrict (ball (0 : ℂ) ρ)) :=
    fun γ hγ => (hterm γ hγ).1
  refine ⟨(memHOn_of_contDiffOn isOpen_ball hcd hL2).1, ?_⟩
  rw [normHOn_eq_of_contDiffOn isOpen_ball hcd hL2]
  calc Real.sqrt (∑ γ ∈ multiIdx (j + 1), l2On (ball 0 ρ) (partialD γ (velocity h)) ^ 2)
      ≤ Real.sqrt (∑ _γ ∈ multiIdx (j + 1), A ^ 2) := by
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun γ hγ => ?_)
        exact pow_le_pow_left₀ (l2On_nonneg _ _) (hterm γ hγ).2 2
    _ = Real.sqrt ((multiIdx (j + 1)).card : ℝ) * A := by
        rw [Finset.sum_const, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hA0]
    _ = Real.sqrt ((multiIdx (j + 1)).card : ℝ) * max 1 (3 * ρ) *
          normH j (fun x => (h x : ℂ)) := by
        rw [hA]
        ring

/-- The smooth case of `lem:Hk-calculus`(3) (`02_prelim.tex:748-759`), with smooth real
vorticities supported in `B_{2ρ}`. -/
theorem exists_cutoffBS_smooth (j : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ ball (0 : ℂ) ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℂ → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
      tsupport h ⊆ ball (0 : ℂ) (2 * ρ) →
      MemH (j + 1) (fun x => (χ x : ℂ) * velocity h x) ∧
        normH (j + 1) (fun x => (χ x : ℂ) * velocity h x) ≤
          C * normH j (fun x => (h x : ℂ)) := by
  have hχtest : IsTestFn (ball (0 : ℂ) ρ) (fun x => (χ x : ℂ)) := by
    refine ⟨Complex.ofRealCLM.contDiff.comp hχ, hχc.comp_left Complex.ofReal_zero, ?_⟩
    exact (tsupport_comp_subset Complex.ofReal_zero χ).trans hχs
  obtain ⟨C₀, hC₀, hext⟩ := exists_normH_mul_testFn_le (k := j + 1) isOpen_ball hχtest
  set D : ℝ := Real.sqrt ((multiIdx (j + 1)).card : ℝ) * max 1 (3 * ρ) with hD
  have hD0 : 0 ≤ D := mul_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one (le_max_left _ _))
  refine ⟨C₀ * D + 1, by positivity, fun h hh hhc hts => ?_⟩
  obtain ⟨hmemOn, hnormOn⟩ := velocity_memHOn_ball j hρ hh hhc hts
  obtain ⟨hmem, hnorm⟩ := hext (velocity h) hmemOn
  refine ⟨hmem, hnorm.trans ?_⟩
  have hHnn : 0 ≤ normH j (fun x => (h x : ℂ)) := normH_nonneg _ _
  calc C₀ * normHOn (j + 1) (ball (0 : ℂ) ρ) (velocity h)
      ≤ C₀ * (D * normH j (fun x => (h x : ℂ))) := mul_le_mul_of_nonneg_left hnormOn hC₀
    _ = (C₀ * D) * normH j (fun x => (h x : ℂ)) := by ring
    _ ≤ (C₀ * D + 1) * normH j (fun x => (h x : ℂ)) := by nlinarith

end NonUniqueEuler.Sob.CutoffBSAux
