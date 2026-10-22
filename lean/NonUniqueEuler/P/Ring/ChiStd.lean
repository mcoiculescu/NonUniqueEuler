import NonUniqueEuler.Statement.Ring

/-!
# Proof: the explicit cutoff is admissible

Proof of `I/Ring/ChiStd.lean` (`lem:ring-facts`, `04_ring.tex:71-76`).
-/

namespace NonUniqueEuler.RingData

open Set

theorem chiStd_admissible : ChiStdAdmissible := by
  have hLa : ξL < ξa := by norm_num [ξL, ξa]
  have hab : ξa ≤ ξb := by norm_num [ξa, ξb]
  have hbR : ξb < ξR := by norm_num [ξb, ξR]
  have h1 : 0 < ξa - ξL := sub_pos.2 hLa
  have h2 : 0 < ξR - ξb := sub_pos.2 hbR
  -- right factor is 1 left of ξb, left factor is 1 right of ξa
  have hw1 : ∀ ξ, ξ ≤ ξb → Real.smoothTransition ((ξR - ξ) / (ξR - ξb)) = 1 := by
    intro ξ hξ
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ h2]; linarith
  have hu1 : ∀ ξ, ξa ≤ ξ → Real.smoothTransition ((ξ - ξL) / (ξa - ξL)) = 1 := by
    intro ξ hξ
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ h1]; linarith
  refine
    { contDiff := ?_, mem_Icc := ?_, monotoneOn := ?_, eq_one := ?_, antitoneOn := ?_,
      tsupport_subset := ?_ }
  · unfold chiStd
    apply ContDiff.mul
    · exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    · exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)
  · intro ξ
    unfold chiStd
    exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
      mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
        (Real.smoothTransition.le_one _)⟩
  · intro x hx y hy hxy
    simp only [mem_Iic] at hx hy
    unfold chiStd
    rw [hw1 x (hx.trans hab), hw1 y (hy.trans hab), mul_one, mul_one]
    apply Real.smoothTransition.monotone
    exact div_le_div_of_nonneg_right (by linarith) h1.le
  · intro ξ hξ
    unfold chiStd
    rw [hu1 ξ hξ.1, hw1 ξ hξ.2, mul_one]
  · intro x hx y hy hxy
    simp only [mem_Ici] at hx hy
    unfold chiStd
    rw [hu1 x (hab.trans hx), hu1 y (hab.trans hy), one_mul, one_mul]
    apply Real.smoothTransition.monotone
    exact div_le_div_of_nonneg_right (by linarith) h2.le
  · apply closure_minimal _ isClosed_Icc
    intro ξ hξ
    rw [Function.mem_support] at hξ
    unfold chiStd at hξ
    constructor
    · by_contra h
      apply hξ
      rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) h1.le
    · by_contra h
      apply hξ
      rw [Real.smoothTransition.zero_of_nonpos (x := (ξR - ξ) / (ξR - ξb)), mul_zero]
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) h2.le

end NonUniqueEuler.RingData
