import NonUniqueEuler.H.Sec3.RenormAllT.Basic
import NonUniqueEuler.I.Sec2.Velocity

/-!
# Helpers for `lem:renorm-all-t`: the flux bound

Helper file of `P/Sec3/RenormAllT.lean` (fully proved).

`flux_bound` (`03_compactness.tex:597-600`): with `C_v = C(2,1)` of `lem:velocity`(a),
`‖ω(t)v(t)‖_{L¹} ≤ ∫|ω(t)|(|K|∗|ω(t)|) ≤ C_v‖ω(t)‖²_{L¹∩L²} ≤ C_v M²` for every
`t ∈ (0,T)`, and Tonelli gives `‖ωv‖_{L¹((0,T)×ℝ²)} ≤ C_v T M²`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Weak.RenormAllTH

/-- `‖g‖_{L¹∩L²}² ≤ M²` from `‖g‖_{L¹∩L²} ≤ M` in `ℝ≥0∞` form. -/
theorem normL1Lp_sq_le {g : ℂ → ℝ} {M : ℝ} (h1 : MemLp g 1 volume) (h2 : MemLp g 2 volume)
    (hM : normL1LpE 2 g ≤ ENNReal.ofReal M) : Prelim.normL1Lp 2 g ^ 2 ≤ M ^ 2 := by
  rw [normL1Lp_eq_toReal h1 h2]
  have h0 : 0 ≤ (normL1LpE 2 g).toReal := ENNReal.toReal_nonneg
  rcases le_or_gt 0 M with hM0 | hM0
  · exact pow_le_pow_left₀ h0 (ENNReal.toReal_le_of_le_ofReal hM0 hM) 2
  · have : normL1LpE 2 g = 0 := by
      rw [ENNReal.ofReal_of_nonpos hM0.le] at hM
      exact nonpos_iff_eq_zero.1 hM
    rw [this, ENNReal.toReal_zero]
    simpa using sq_nonneg M

/-- The flux bound `‖ωv‖_{L¹((0,T)×ℝ²)} ≤ C_v T M²`. -/
theorem flux_bound :
    ∃ Cv : ℝ, 0 < Cv ∧ ∀ (T M : ℝ) (ωin : ℂ → ℝ) (ω : ℝ → ℂ → ℝ),
      IsWeakSolution 2 T ωin ω → IsWeakContL2On (Icc 0 T) ω →
      (∀ t ∈ Icc 0 T, normL1LpE 2 (ω t) ≤ ENNReal.ofReal M) →
      ∫⁻ p in slab T, ‖ω p.1 p.2 • velocityField ω p.1 p.2‖ₑ ≤
        ENNReal.ofReal (Cv * T * M ^ 2) := by
  obtain ⟨C, hC, hCb⟩ := BS.velocity_bounds_two (R := 1) one_pos
  refine ⟨C, hC, fun T M ωin ω h hc hM => ?_⟩
  have hT := h.T_pos
  have hslice : ∀ t ∈ Ioo 0 T,
      ∫⁻ x, ‖ω t x • velocityField ω t x‖ₑ ≤ ENNReal.ofReal (C * M ^ 2) := by
    intro t ht
    have ht' : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
    have h2 : MemLp (ω t) 2 volume := hc.memLp t ht'
    have hfin : normL1LpE 2 (ω t) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hM t ht')
    have h1 : MemLp (ω t) 1 volume :=
      ⟨h2.1, lt_of_le_of_lt (eLpNorm_one_le_normL1LpE 2 (ω t)) hfin.lt_top⟩
    have hb := (hCb (ω t) h1 h2).2.2.2.2
    calc ∫⁻ x, ‖ω t x • velocityField ω t x‖ₑ
        ≤ ∫⁻ x, ‖ω t x‖ₑ * Conv.convAbs biotSavartKernel (ω t) x := by
          refine lintegral_mono fun x => ?_
          rw [enorm_smul]
          gcongr
          exact Conv.enorm_velocity_le (ω t) x
      _ ≤ ENNReal.ofReal (C * Prelim.normL1Lp 2 (ω t) ^ 2) := hb
      _ ≤ ENNReal.ofReal (C * M ^ 2) :=
          ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (normL1Lp_sq_le h1 h2 (hM t ht')) hC.le)
  rw [JointRep.volume_restrict_slab]
  calc ∫⁻ p, ‖ω p.1 p.2 • velocityField ω p.1 p.2‖ₑ ∂((volume.restrict (Ioo 0 T)).prod volume)
      ≤ ∫⁻ t in Ioo 0 T, ∫⁻ x, ‖ω t x • velocityField ω t x‖ₑ := lintegral_prod_le _
    _ ≤ ∫⁻ _ in Ioo 0 T, ENNReal.ofReal (C * M ^ 2) := setLIntegral_mono' measurableSet_Ioo hslice
    _ = ENNReal.ofReal (C * T * M ^ 2) := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end NonUniqueEuler.Weak.RenormAllTH
