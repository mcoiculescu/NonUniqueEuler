import NonUniqueEuler.I.Sec2.ExtMultipole
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Helper for `lem:transfer-step`: a radial vorticity has only its monopole outside its support

Helper of `P/Sec9/TransferStep.lean`: the "third fact" of the proof of `lem:transfer-step`
(`09_relay.tex:190-196`). Let `g ∈ L¹(ℝ²)` be real and radial with `supp g ⊂ \bar B_ρ`. Then `g` is
`m'`-fold symmetric for every `m' ≥ 1`, and `lem:ext-multipole` with no derivatives bounds the
non-monopole field `E = K_BS * g - monopole` at `|x| ≥ 2ρ` by `C_{m',0}‖g‖_{L¹}ρ^{m'}|x|^{-m'-1}`,
with `C_{m',0} ≤ 1/π`. Letting `m' → ∞` gives `E(x) = 0`.

* `cExtMultipole_zero_le`: `C_{m,0} ≤ 1/π` for `m ≥ 1`;
* `iterDerivArrayNorm_zero`: `|∇^0 h(x)| = |h(x)|`;
* `extField_eq_zero_of_radial`: `E(x) = 0` for `|x| ≥ 2ρ`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler.Relay.TransferStepAux

/-- `C_{m,0} = (2π)⁻¹ sup_{0<ρ≤1/2} (1 - ρ^m)⁻¹ ≤ 1/π` for `m ≥ 1` (`09_relay.tex:193-194`). -/
theorem cExtMultipole_zero_le {m : ℕ} (hm : 1 ≤ m) : BS.cExtMultipole m 0 ≤ 1 / Real.pi := by
  have : Nonempty (Ioc (0 : ℝ) (1 / 2)) := ⟨⟨1 / 2, by norm_num, le_rfl⟩⟩
  have hsup : (⨆ ρ : Ioc (0 : ℝ) (1 / 2),
      ((ρ : ℝ) ^ m)⁻¹ * ∑' j : ℕ, (((m * (j + 1) + 0 : ℕ) : ℝ)) ^ 0 * (ρ : ℝ) ^ (m * (j + 1))) ≤
      2 := by
    refine ciSup_le fun ρ => ?_
    obtain ⟨ρ, hρ0, hρ1⟩ := ρ
    simp only [pow_zero, one_mul]
    have hpm0 : 0 < ρ ^ m := pow_pos hρ0 m
    have hpm1 : ρ ^ m ≤ 1 / 2 :=
      (pow_le_of_le_one hρ0.le (by linarith) (by omega)).trans hρ1
    have hgeom : ∑' j : ℕ, ρ ^ (m * (j + 1)) = ρ ^ m * (1 - ρ ^ m)⁻¹ := by
      have : (fun j : ℕ => ρ ^ (m * (j + 1))) = fun j : ℕ => ρ ^ m * (ρ ^ m) ^ j := by
        funext j
        rw [← pow_mul, ← pow_add]
        congr 1
        ring
      rw [this, tsum_mul_left, tsum_geometric_of_lt_one hpm0.le (by linarith)]
    rw [hgeom, ← mul_assoc, inv_mul_cancel₀ hpm0.ne', one_mul]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hpi := Real.pi_pos
  unfold BS.cExtMultipole
  rw [pow_zero]
  calc 1 / (2 * Real.pi) * _ ≤ 1 / (2 * Real.pi) * 2 :=
        mul_le_mul_of_nonneg_left hsup (by positivity)
    _ = 1 / Real.pi := by field_simp

/-- `|∇^0 h(x)| = |h(x)|`. -/
theorem iterDerivArrayNorm_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : ℂ → F) (x : ℂ) : iterDerivArrayNorm 0 h x = ‖h x‖ := by
  unfold iterDerivArrayNorm
  rw [Fintype.sum_unique, iteratedFDeriv_zero_apply, Real.sqrt_sq (norm_nonneg _)]

/-- **A radial vorticity has no non-monopole field outside its support** (`09_relay.tex:190-196`):
for real radial `g ∈ L¹` vanishing outside `\bar B_ρ`, `ρ > 0`, and `|x| ≥ 2ρ`,
`K_BS * g(x) = (2π)⁻¹(∫ g) x^⊥/|x|²`, i.e. `E(x) = 0`. -/
theorem extField_eq_zero_of_radial {g : ℂ → ℝ} (hg : MemLp g 1 volume)
    (hrad : IsRadialPointwise g) {ρ : ℝ} (hρ : 0 < ρ) (hsupp : ∀ x : ℂ, ρ < ‖x‖ → g x = 0)
    {x : ℂ} (hx : 2 * ρ ≤ ‖x‖) : BS.extField g x = 0 := by
  set L : ℝ := (eLpNorm g 1 volume).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hpi := Real.pi_pos
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (by linarith) hx
  set C : ℝ := 1 / Real.pi * L * (‖x‖)⁻¹
  have hC : 0 ≤ C := by positivity
  have hbound : ∀ m : ℕ, 1 ≤ m → ‖BS.extField g x‖ ≤ C * (1 / 2) ^ m := by
    intro m hm
    have hsym : IsMFoldSymmetric m g := Filter.Eventually.of_forall fun y => hrad _ y
    have h := BS.iterDerivArrayNorm_extField_le (q := 0) hm hρ hg hsym
      (Filter.Eventually.of_forall fun y hy => hsupp y hy) hx
    rw [iterDerivArrayNorm_zero] at h
    have hc := cExtMultipole_zero_le hm
    have hc0 : 0 ≤ BS.cExtMultipole m 0 := (BS.cExtMultipole_finite hm 0).2.2.le
    have hratio : ρ / ‖x‖ ≤ 1 / 2 := by
      rw [div_le_iff₀ hxpos]
      linarith
    have hpow : ρ ^ m * (‖x‖ ^ (m + 1 + 0))⁻¹ = (ρ / ‖x‖) ^ m * (‖x‖)⁻¹ := by
      rw [div_pow, add_zero, pow_succ]
      field_simp
    have hpow2 : (ρ / ‖x‖) ^ m ≤ (1 / 2) ^ m :=
      pow_le_pow_left₀ (div_nonneg hρ.le hxpos.le) hratio m
    calc ‖BS.extField g x‖
        ≤ BS.cExtMultipole m 0 * L * ρ ^ m * (‖x‖ ^ (m + 1 + 0))⁻¹ := h
      _ = BS.cExtMultipole m 0 * L * (ρ / ‖x‖) ^ m * (‖x‖)⁻¹ := by
          rw [mul_assoc _ (ρ ^ m), hpow, ← mul_assoc]
      _ ≤ 1 / Real.pi * L * (1 / 2) ^ m * (‖x‖)⁻¹ := by
          gcongr
      _ = C * (1 / 2) ^ m := by
          simp only [C]
          ring
  have hlim : Tendsto (fun m : ℕ => C * (1 / 2 : ℝ) ^ m) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul C
    simpa using this
  have hle : ‖BS.extField g x‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨1, hbound⟩)
  exact norm_le_zero_iff.mp hle

end NonUniqueEuler.Relay.TransferStepAux
