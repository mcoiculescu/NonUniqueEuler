import NonUniqueEuler.Defs.Verify.Profile
import NonUniqueEuler.Defs.Verify.Taylor
import NonUniqueEuler.I.Verify.TaylorRecurrence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Proof: the functions `H`, `A`, `Ā`, `B`, `B̄` and the profile `ϖ = χAB`

Proof of the interface `NonUniqueEuler/I/Verify/ProfileBasic.lean` (same declarations, same
statements). Manuscript: proof of Lemma A.1(1) (`A_verification.tex:153-170`) and step (i) of
the proof of Proposition A.3 (`A_verification.tex:346-362`).

The only interface used is `I/Verify/TaylorRecurrence.lean`
(`iteratedDeriv_eq_of_eqOn_Icc`, `taylorCoeff_eq_of_eqOn_Icc`).
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler

namespace AppA

open RingData

/-! ### Auxiliary facts -/

private theorem d_pos : 0 < d := by norm_num [d]

private theorem ξa_lt_ξb : ξa < ξb := by norm_num [ξa, ξb]

private theorem H_eq (x : ℝ) : H x = (1 + Real.exp (-2 * x))⁻¹ := rfl

private theorem one_add_exp_pos (x : ℝ) : 0 < 1 + Real.exp (-2 * x) := by positivity

/-! ### The logistic function `H` -/

theorem H_add_H_neg (x : ℝ) : H x + H (-x) = 1 := by
  rw [H_eq, H_eq, show -2 * -x = -(-2 * x) by ring, Real.exp_neg]
  have hu : 0 < Real.exp (-2 * x) := Real.exp_pos _
  field_simp
  ring

theorem hasDerivAt_H (x : ℝ) : HasDerivAt H (2 * (H x * H (-x))) x := by
  have hin : HasDerivAt (fun y : ℝ => 1 + Real.exp (-2 * y))
      (Real.exp (-2 * x) * (-2)) x := by
    have h1 : HasDerivAt (fun y : ℝ => -2 * y) (-2) x := by
      simpa using (hasDerivAt_id x).const_mul (-2 : ℝ)
    exact (h1.exp).const_add 1
  have h := hin.inv (one_add_exp_pos x).ne'
  refine h.congr_deriv ?_
  rw [H_eq, H_eq, show -2 * -x = -(-2 * x) by ring, Real.exp_neg]
  have hu : 0 < Real.exp (-2 * x) := Real.exp_pos _
  field_simp
  ring

theorem contDiff_H : ContDiff ℝ ∞ H := by
  have h : ContDiff ℝ ∞ (fun y : ℝ => 1 + Real.exp (-2 * y)) :=
    contDiff_const.add (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  exact h.inv (fun y => (one_add_exp_pos y).ne')

theorem H_pos (x : ℝ) : 0 < H x := inv_pos.mpr (one_add_exp_pos x)

theorem H_le_one (x : ℝ) : H x ≤ 1 :=
  inv_le_one_of_one_le₀ (le_add_of_nonneg_right (Real.exp_pos _).le)

theorem H_le_exp (x : ℝ) : H x ≤ Real.exp (2 * x) := by
  have h : (1 + Real.exp (-2 * x))⁻¹ ≤ (Real.exp (-2 * x))⁻¹ :=
    inv_anti₀ (Real.exp_pos _) (le_add_of_nonneg_left zero_le_one)
  rw [← Real.exp_neg, show -(-2 * x) = 2 * x by ring] at h
  exact h

theorem strictMono_H : StrictMono H := by
  intro x y hxy
  rw [H_eq, H_eq]
  rw [inv_lt_inv₀ (one_add_exp_pos x) (one_add_exp_pos y)]
  have : Real.exp (-2 * y) < Real.exp (-2 * x) := Real.exp_lt_exp.mpr (by linarith)
  linarith

/-! ### `A`, `Ā`, `B`, `B̄` -/

private theorem profAbar_eq (ξ : ℝ) : profAbar ξ = H (-((ξ - a₀) / d)) := by
  unfold profAbar
  congr 1
  ring

private theorem profBbar_eq (ξ : ℝ) : profBbar ξ = H (-(-ξ / d)) := by
  unfold profBbar
  congr 1
  ring

theorem profA_add_profAbar (ξ : ℝ) : profA ξ + profAbar ξ = 1 := by
  rw [profAbar_eq]
  exact H_add_H_neg _

theorem profB_add_profBbar (ξ : ℝ) : profB ξ + profBbar ξ = 1 := by
  rw [profBbar_eq]
  exact H_add_H_neg _

/-- `A' = (2/d) A Ā`. -/
theorem hasDerivAt_profA (ξ : ℝ) : HasDerivAt profA ((2 / d) * (profA ξ * profAbar ξ)) ξ := by
  have hin : HasDerivAt (fun t : ℝ => (t - a₀) / d) (1 / d) ξ :=
    ((hasDerivAt_id ξ).sub_const a₀).div_const d
  have h := (hasDerivAt_H ((ξ - a₀) / d)).comp ξ hin
  refine h.congr_deriv ?_
  rw [profAbar_eq]
  simp only [profA]
  ring

/-- `B' = -(2/d) B B̄`. -/
theorem hasDerivAt_profB (ξ : ℝ) :
    HasDerivAt profB (-(2 / d) * (profB ξ * profBbar ξ)) ξ := by
  have hin : HasDerivAt (fun t : ℝ => -t / d) (-1 / d) ξ :=
    ((hasDerivAt_id ξ).neg).div_const d
  have h := (hasDerivAt_H (-ξ / d)).comp ξ hin
  refine h.congr_deriv ?_
  rw [profBbar_eq]
  simp only [profB]
  ring

theorem contDiff_profA : ContDiff ℝ ∞ profA :=
  contDiff_H.comp ((contDiff_id.sub contDiff_const).div_const d)

theorem contDiff_profAbar : ContDiff ℝ ∞ profAbar :=
  contDiff_H.comp ((contDiff_const.sub contDiff_id).div_const d)

theorem contDiff_profB : ContDiff ℝ ∞ profB :=
  contDiff_H.comp (contDiff_id.neg.div_const d)

theorem contDiff_profBbar : ContDiff ℝ ∞ profBbar :=
  contDiff_H.comp (contDiff_id.div_const d)

theorem contDiff_profW : ContDiff ℝ ∞ profW :=
  contDiff_profA.mul contDiff_profB

private theorem contDiff_exp_two_mul : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (2 * t)) :=
  Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)

theorem contDiff_profQ : ContDiff ℝ ∞ profQ :=
  contDiff_profW.mul contDiff_exp_two_mul

/-- `A` is increasing and `B` is decreasing. -/
theorem strictMono_profA : StrictMono profA := by
  intro x y hxy
  exact strictMono_H (div_lt_div_of_pos_right (sub_lt_sub_right hxy a₀) d_pos)

theorem strictAnti_profB : StrictAnti profB := by
  intro x y hxy
  exact strictMono_H (div_lt_div_of_pos_right (neg_lt_neg hxy) d_pos)

/-! ### The profile `ϖ = χ A B` -/

private theorem profW_nonneg (ξ : ℝ) : 0 ≤ profW ξ :=
  mul_nonneg (H_pos _).le (H_pos _).le

theorem contDiff_prof {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) : ContDiff ℝ ∞ (prof χ) := by
  show ContDiff ℝ ∞ (fun ξ => χ ξ * profA ξ * profB ξ)
  exact (hχ.contDiff.mul contDiff_profA).mul contDiff_profB

theorem prof_nonneg {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) : 0 ≤ prof χ ξ := by
  rw [prof_eq_mul_profW]
  exact mul_nonneg (hχ.mem_Icc ξ).1 (profW_nonneg ξ)

theorem prof_le_profW {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) :
    prof χ ξ ≤ profW ξ := by
  rw [prof_eq_mul_profW]
  exact mul_le_of_le_one_left (profW_nonneg ξ) (hχ.mem_Icc ξ).2

theorem profW_le_one (ξ : ℝ) : profW ξ ≤ 1 :=
  mul_le_one₀ (H_le_one _) (H_pos _).le (H_le_one _)

theorem prof_eq_zero_of_not_mem {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ξ : ℝ}
    (hξ : ξ ∉ Icc ξL ξR) : prof χ ξ = 0 := by
  have h : ξ ∉ tsupport χ := fun h => hξ (hχ.tsupport_subset h)
  rw [prof_eq_mul_profW, image_eq_zero_of_notMem_tsupport h, zero_mul]

theorem deriv_prof_eq_zero_of_not_mem {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ξ : ℝ}
    (hξ : ξ ∉ Icc ξL ξR) : deriv (prof χ) ξ = 0 := by
  have h : ξ ∉ tsupport χ := fun h => hξ (hχ.tsupport_subset h)
  rw [notMem_tsupport_iff_eventuallyEq] at h
  have h' : prof χ =ᶠ[𝓝 ξ] fun _ => (0 : ℝ) :=
    h.mono fun t ht => by rw [prof_eq_mul_profW, ht, Pi.zero_apply, zero_mul]
  rw [h'.deriv_eq, deriv_const]

/-- On `[ξa, ξb]`, where `χ = 1`, the profile is `AB`. -/
theorem prof_eq_profW_of_mem {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ξ : ℝ}
    (hξ : ξ ∈ Icc ξa ξb) : prof χ ξ = profW ξ := by
  rw [prof_eq_mul_profW, hχ.eq_one ξ hξ, one_mul]

/-- On the closed interval `[ξa, ξb]`, the Taylor coefficients of `ϖ` are those of `AB`. -/
theorem taylorCoeff_prof_eq {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ξ : ℝ}
    (hξ : ξ ∈ Icc ξa ξb) (k : ℕ) : taylorCoeff (prof χ) k ξ = taylorCoeff profW k ξ :=
  taylorCoeff_eq_of_eqOn_Icc ξa_lt_ξb (contDiff_prof hχ) contDiff_profW
    (fun _ ht => prof_eq_profW_of_mem hχ ht) hξ k

/-- On `[ξa, ξb]`, the Taylor coefficients of `ϖ e^{2ξ}` are those of `q = AB e^{2ξ}`. -/
theorem taylorCoeff_prof_exp_eq {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ξ : ℝ}
    (hξ : ξ ∈ Icc ξa ξb) (k : ℕ) :
    taylorCoeff (fun t => prof χ t * Real.exp (2 * t)) k ξ = taylorCoeff profQ k ξ :=
  taylorCoeff_eq_of_eqOn_Icc ξa_lt_ξb ((contDiff_prof hχ).mul contDiff_exp_two_mul)
    contDiff_profQ (fun t ht => by
      show prof χ t * Real.exp (2 * t) = profW t * Real.exp (2 * t)
      rw [prof_eq_profW_of_mem hχ ht]) hξ k

/-- On `[ξa, ξb]`, the Taylor coefficients of `ϖ'` are those of `(AB)'`. -/
theorem taylorCoeff_deriv_prof_eq {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ξ : ℝ}
    (hξ : ξ ∈ Icc ξa ξb) (k : ℕ) :
    taylorCoeff (deriv (prof χ)) k ξ = taylorCoeff (deriv profW) k ξ := by
  unfold taylorCoeff
  rw [← iteratedDeriv_succ', ← iteratedDeriv_succ',
    iteratedDeriv_eq_of_eqOn_Icc ξa_lt_ξb (contDiff_prof hχ) contDiff_profW
      (fun _ ht => prof_eq_profW_of_mem hχ ht) hξ (k + 1)]

end AppA

end NonUniqueEuler
