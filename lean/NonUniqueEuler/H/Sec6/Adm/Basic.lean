import NonUniqueEuler.Defs.Sec6.Datum
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Helpers for `lem:adm`: radii, scaling of `L^p` norms, small balls

Helper of `P/Sec6/Adm.lean` (`06_datum.tex:93-136`).

* `AdmH.ratio_le_sbar`, `AdmH.radius_antitone`, `AdmH.radius_succ_lt`, `AdmH.tendsto_radius`:
  `s_k ≤ s̄`, `r_{k+1} ≤ r_k`, `r_{k+1} < a r_k` (`06_datum.tex:36-38`), `r_k → 0`;
* `AdmH.eLpNorm_comp_mp_div`: `‖g ∘ Y ∘ (·/r)‖_p = ‖g ∘ (·/r)‖_p` for a measure-preserving `Y`
  (equimeasurability of `Φ^κ` and `Φ` survives the dilation, `06_datum.tex:103-104`);
* `AdmH.tendsto_eLpNorm_indicator_closedBall`: `‖1_{B̄_{ρ_n}} F‖_p → 0` for `F ∈ L^p` and
  `ρ_n → 0` (absolute continuity of the `L^p` norm).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace NonUniqueEuler.Datum.AdmH

open RingData

/-- `s_k = s̄(2μ)^{-k} ≤ s̄`. -/
theorem ratio_le_sbar {sbar μ : ℝ} (hs : 0 ≤ sbar) (hμ : 1 ≤ 2 * μ) (k : ℕ) :
    ratio sbar μ k ≤ sbar :=
  div_le_self hs (one_le_pow₀ hμ)

/-- `r_{k+1} ≤ r_k` for every `k` (for `k = 0` both are `1`). -/
theorem radius_succ_le {sbar μ : ℝ} (hs : 0 < sbar) (hs1 : sbar ≤ 1) (hμ : 1 ≤ 2 * μ) (k : ℕ) :
    radius sbar μ (k + 1) ≤ radius sbar μ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [radius]
  · rw [radius_succ sbar μ hk]
    have hr : 0 < radius sbar μ k := radius_pos hs (by linarith) k
    have : ratio sbar μ k ≤ 1 := (ratio_le_sbar hs.le hμ k).trans hs1
    nlinarith

theorem radius_antitone {sbar μ : ℝ} (hs : 0 < sbar) (hs1 : sbar ≤ 1) (hμ : 1 ≤ 2 * μ) :
    Antitone (radius sbar μ) :=
  antitone_nat_of_succ_le (radius_succ_le hs hs1 hμ)

/-- `r_{k+1} < a r_k` for `k ≥ 1` (`06_datum.tex:36-38`). -/
theorem radius_succ_lt {A₁ sbar μ : ℝ} (hp : DatumParams A₁ μ sbar) (ha : 0 < a) {k : ℕ}
    (hk : 1 ≤ k) : radius sbar μ (k + 1) < a * radius sbar μ k := by
  rw [radius_succ sbar μ hk]
  have hr : 0 < radius sbar μ k := radius_pos hp.sbar_pos (by linarith [hp.one_lt_μ]) k
  have h1 : ratio sbar μ k ≤ sbar := ratio_le_sbar hp.sbar_pos.le (by linarith [hp.one_lt_μ]) k
  have h2 : ratio sbar μ k < a := by linarith [hp.sbar_le]
  exact mul_lt_mul_of_pos_right h2 hr

/-- `r_k ≤ s̄^{k-1}`. -/
theorem radius_le_pow {sbar μ : ℝ} (hs : 0 < sbar) (hμ : 1 ≤ 2 * μ) (k : ℕ) :
    radius sbar μ k ≤ sbar ^ (k - 1) := by
  rw [radius]
  calc ∏ j ∈ Finset.Ico 1 k, ratio sbar μ j ≤ ∏ _j ∈ Finset.Ico 1 k, sbar :=
        Finset.prod_le_prod (fun j _ => (ratio_pos hs (by linarith) j).le)
          (fun j _ => ratio_le_sbar hs.le hμ j)
    _ = sbar ^ (k - 1) := by rw [Finset.prod_const, Nat.card_Ico]

/-- `r_k → 0`. -/
theorem tendsto_radius {sbar μ : ℝ} (hs : 0 < sbar) (hs1 : sbar < 1) (hμ : 1 ≤ 2 * μ) :
    Tendsto (radius sbar μ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => sbar ^ (k - 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hs.le hs1).comp (tendsto_sub_atTop_nat 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
    (fun k => (radius_pos hs (by linarith) k).le) (fun k => radius_le_pow hs hμ k)

/-- Dilation and a measure-preserving map: `‖g(Y(·/r))‖_p = ‖g(·/r)‖_p` (`r ≠ 0`). -/
theorem eLpNorm_comp_mp_div {g : ℂ → ℝ} (hg : Continuous g) {Y : ℂ → ℂ}
    (hY : MeasurePreserving Y volume volume) {r : ℝ} (hr : r ≠ 0) (p : ℝ≥0∞) :
    eLpNorm (fun x => g (Y (x / (r : ℂ)))) p volume =
      eLpNorm (fun x => g (x / (r : ℂ))) p volume := by
  set D : ℂ → ℂ := fun x => (r⁻¹ : ℝ) • x with hD
  have hDx : ∀ x : ℂ, x / (r : ℂ) = D x := by
    intro x
    simp only [D, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
  have hDm : Measurable D := (continuous_const_smul _).measurable
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, Measure.map D volume = c • volume :=
    ⟨_, Measure.map_addHaar_smul volume (inv_ne_zero hr)⟩
  have hYc : MeasurePreserving Y (c • volume) (c • volume) :=
    ⟨hY.measurable, by rw [Measure.map_smul, hY.map_eq]⟩
  have e1 : (fun x => g (Y (x / (r : ℂ)))) = (g ∘ Y) ∘ D := by
    funext x; simp only [Function.comp, hDx]
  have e2 : (fun x => g (x / (r : ℂ))) = g ∘ D := by
    funext x; simp only [Function.comp, hDx]
  rw [e1, e2, ← eLpNorm_map_measure ((hg.measurable.comp hY.measurable).aestronglyMeasurable)
    hDm.aemeasurable, ← eLpNorm_map_measure hg.aestronglyMeasurable hDm.aemeasurable, hc]
  exact eLpNorm_comp_measurePreserving hg.aestronglyMeasurable hYc

/-- `|B̄_ρ| → 0` as `ρ → 0`. -/
theorem tendsto_volume_closedBall {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝 0)) :
    Tendsto (fun n => volume (closedBall (0 : ℂ) (ρ n))) atTop (𝓝 0) := by
  simp only [Complex.volume_closedBall]
  have h1 : Tendsto (fun n => ENNReal.ofReal (ρ n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hρ
  have h2 : Tendsto (fun n => ENNReal.ofReal (ρ n) ^ 2) atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_pow 2).tendsto 0).comp h1
    rw [show ((0 : ℝ≥0∞)) ^ 2 = 0 by simp] at h
    exact h
  simpa using ENNReal.Tendsto.mul_const h2 (Or.inr ENNReal.coe_ne_top)

/-- Absolute continuity of the `L^p` norm on small balls: `‖1_{B̄_{ρ_n}} F‖_p → 0` for
`F ∈ L^p` (`1 ≤ p < ∞`) and `ρ_n → 0`. -/
theorem tendsto_eLpNorm_indicator_closedBall {F : ℂ → ℝ} {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hptop : p ≠ ⊤) (hF : MemLp F p volume) {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm ((closedBall (0 : ℂ) (ρ n)).indicator F) p volume) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hF.eLpNorm_indicator_le hp1 hptop hε
  filter_upwards [(tendsto_order.1 (tendsto_volume_closedBall hρ)).2 δ hδ] with n hn
  exact h _ measurableSet_closedBall hn.le

end NonUniqueEuler.Datum.AdmH
