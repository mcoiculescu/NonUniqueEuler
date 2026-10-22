import NonUniqueEuler.H.Sec6.Integrability.Terms
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Helpers for `prop:integrability`: `f ∈ L^q` for `q < ∞`, `f ∉ L^∞`

Helper of `P/Sec6/Integrability.lean` (`06_datum.tex:46-66`).

* `IntegrabilityH.memLp_datum`: `f ∈ L^q` for `1 ≤ q < ∞`. Instead of the identity
  `∫ f^q = Σ_k A_k^q r_k² ‖Φ‖_q^q` (`06_datum.tex:47-50`) we use the bound
  `|f|^q ≤ Σ_k A_k^q 1_{B̄_{r_k}}` (`0 ≤ Φ < 1`, `supp Φ(·/r_k) ⊆ B̄_{r_k}`, at most one nonzero
  term), whence `∫ |f|^q ≤ π Σ_k A_k^q r_k² < ∞` by monotone convergence (`lintegral_tsum`).
* `IntegrabilityH.not_memLp_top`: `f ∉ L^∞` (`06_datum.tex:61-66`): `Φ > c` on a disk
  `B_ρ(y₀)`, so `f > A_k c` on `B_{ρ r_k}(r_k y₀)`, of positive measure, and `A_k → ∞`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace NonUniqueEuler.Datum.IntegrabilityH

open RingData

variable {χ : ℝ → ℝ} {A₁ μ sbar : ℝ}

/-- Pointwise bound `|f(x)|^q ≤ Σ_k A_k^q 1_{B̄_{r_k}}(x)`. -/
theorem enorm_datum_rpow_le (hR : RingFacts χ) (hp : DatumParams A₁ μ sbar) {q : ℝ}
    (hq : 0 < q) (x : ℂ) :
    ‖datum χ A₁ μ sbar x‖ₑ ^ q ≤
      ∑' j : ℕ, (closedBall (0 : ℂ) (radius sbar μ (j + 1))).indicator
        (fun _ => ENNReal.ofReal (amp A₁ μ (j + 1) ^ q)) x := by
  by_cases h : ∃ j : ℕ, ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) ≠ 0
  · obtain ⟨j, hj⟩ := h
    have hμ0 : 0 < μ := by linarith [hp.one_lt_μ]
    have hr := radius_pos hp.sbar_pos hμ0 (j + 1)
    have hA := amp_pos hp.A₁_pos hμ0 (j + 1)
    have hf0 := datum_nonneg hR hp x
    have hx : x ∈ closedBall (0 : ℂ) (radius sbar μ (j + 1)) := by
      rw [mem_closedBall_zero_iff]
      exact (mem_annulus_of_ne_zero hR hr hj).2
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [indicator_of_mem hx, Real.enorm_eq_ofReal hf0, ENNReal.ofReal_rpow_of_nonneg hf0 hq.le]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow hf0 _ hq.le
    rw [datum_eq_single hR hp hj]
    have hR' := hR
    unfold RingFacts at hR'
    exact mul_le_of_le_one_right hA.le (hR'.2.2.2.1 _).2.le
  · push Not at h
    rw [datum_eq_zero h, enorm_zero, ENNReal.zero_rpow_of_pos hq]
    exact zero_le

/-- `∫ |f|^q < ∞` for `q > 0`. -/
theorem lintegral_enorm_datum_rpow_lt_top (hR : RingFacts χ) (hp : DatumParams A₁ μ sbar)
    {q : ℝ} (hq : 0 < q) : ∫⁻ x, ‖datum χ A₁ μ sbar x‖ₑ ^ q < ∞ := by
  have hμ0 : 0 < μ := by linarith [hp.one_lt_μ]
  calc ∫⁻ x, ‖datum χ A₁ μ sbar x‖ₑ ^ q
      ≤ ∫⁻ x, ∑' j : ℕ, (closedBall (0 : ℂ) (radius sbar μ (j + 1))).indicator
          (fun _ => ENNReal.ofReal (amp A₁ μ (j + 1) ^ q)) x :=
        lintegral_mono fun x => enorm_datum_rpow_le hR hp hq x
    _ = ∑' j : ℕ, ENNReal.ofReal (amp A₁ μ (j + 1) ^ q) *
          volume (closedBall (0 : ℂ) (radius sbar μ (j + 1))) := by
        rw [lintegral_tsum fun j =>
          (measurable_const.indicator measurableSet_closedBall).aemeasurable]
        congr 1
        funext j
        exact lintegral_indicator_const measurableSet_closedBall _
    _ = (∑' j : ℕ, ENNReal.ofReal (amp A₁ μ (j + 1) ^ q * radius sbar μ (j + 1) ^ 2)) *
          (NNReal.pi : ℝ≥0∞) := by
        rw [← ENNReal.tsum_mul_right]
        congr 1
        funext j
        rw [Complex.volume_closedBall,
          ENNReal.ofReal_mul (Real.rpow_nonneg (amp_pos hp.A₁_pos hμ0 _).le _),
          ENNReal.ofReal_pow (radius_pos hp.sbar_pos hμ0 _).le, mul_assoc]
    _ < ∞ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg
          (Real.rpow_nonneg (amp_pos hp.A₁_pos hμ0 _).le _) (sq_nonneg _))
          (summable_amp_rpow_mul_radius_sq hp q)]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top

/-- `f ∈ L^q` for every `q ∈ [1, ∞)` (`06_datum.tex:46-60`). -/
theorem memLp_datum (hR : RingFacts χ) (hp : DatumParams A₁ μ sbar) {q : ℝ} (hq : 1 ≤ q) :
    MemLp (datum χ A₁ μ sbar) (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := by linarith
  refine ⟨(measurable_datum hR hp).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by simpa using hq0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le]
  exact lintegral_enorm_datum_rpow_lt_top hR hp hq0

/-- `Φ > c > 0` on some disk `B_ρ(y₀)`. -/
theorem exists_ball_phi_gt (hR : RingFacts χ) :
    ∃ y₀ : ℂ, ∃ c > 0, ∃ ρ > 0, ∀ y ∈ ball y₀ ρ, c < ringPhi χ y := by
  unfold RingFacts at hR
  obtain ⟨y₀, hy₀⟩ := hR.2.2.2.2.1
  have hpos : 0 < ringPhi χ y₀ := lt_of_le_of_ne (hR.2.2.2.1 y₀).1 (Ne.symm hy₀)
  have hev : ∀ᶠ y in 𝓝 y₀, ringPhi χ y₀ / 2 < ringPhi χ y :=
    hR.1.continuous.continuousAt.eventually (lt_mem_nhds (by linarith))
  obtain ⟨ρ, hρ, h⟩ := Metric.eventually_nhds_iff_ball.1 hev
  exact ⟨y₀, ringPhi χ y₀ / 2, by linarith, ρ, hρ, h⟩

/-- `f ∉ L^∞` (`06_datum.tex:61-66`). -/
theorem not_memLp_top (hR : RingFacts χ) (hp : DatumParams A₁ μ sbar) :
    ¬ MemLp (datum χ A₁ μ sbar) ⊤ volume := by
  intro hf
  have hμ0 : 0 < μ := by linarith [hp.one_lt_μ]
  have hMtop : eLpNormEssSup (datum χ A₁ μ sbar) volume ≠ ⊤ := by
    have h := hf.2
    rw [eLpNorm_exponent_top] at h
    exact h.ne
  have hae := ae_le_eLpNormEssSup (f := datum χ A₁ μ sbar) (μ := volume)
  obtain ⟨y₀, c, hc0, ρ, hρ, hball⟩ := exists_ball_phi_gt hR
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    ((eLpNormEssSup (datum χ A₁ μ sbar) volume).toReal / (A₁ * c)) hp.one_lt_μ
  have hAc : (eLpNormEssSup (datum χ A₁ μ sbar) volume).toReal < amp A₁ μ (n + 1) * c := by
    have h1 : amp A₁ μ (n + 1) = A₁ * μ ^ n := by simp [amp]
    rw [div_lt_iff₀ (mul_pos hp.A₁_pos hc0)] at hn
    rw [h1]
    calc _ < μ ^ n * (A₁ * c) := hn
      _ = A₁ * μ ^ n * c := by ring
  have hr : 0 < radius sbar μ (n + 1) := radius_pos hp.sbar_pos hμ0 _
  have hr' : ((radius sbar μ (n + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsub : ball (((radius sbar μ (n + 1) : ℝ) : ℂ) * y₀) (ρ * radius sbar μ (n + 1)) ⊆
      {x | ¬ ‖datum χ A₁ μ sbar x‖ₑ ≤ eLpNormEssSup (datum χ A₁ μ sbar) volume} := by
    intro x hx
    have hx' : x / ((radius sbar μ (n + 1) : ℝ) : ℂ) ∈ ball y₀ ρ := by
      rw [mem_ball, dist_eq_norm] at hx ⊢
      have he : x / ((radius sbar μ (n + 1) : ℝ) : ℂ) - y₀ =
          (x - ((radius sbar μ (n + 1) : ℝ) : ℂ) * y₀) / ((radius sbar μ (n + 1) : ℝ) : ℂ) := by
        field_simp
      rw [he, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_lt_iff₀ hr]
      exact hx
    have h1 := hball _ hx'
    have h2 := term_le_datum hR hp x n
    have h3 : amp A₁ μ (n + 1) * c <
        amp A₁ μ (n + 1) * ringPhi χ (x / ((radius sbar μ (n + 1) : ℝ) : ℂ)) :=
      mul_lt_mul_of_pos_left h1 (amp_pos hp.A₁_pos hμ0 _)
    have h4 : 0 ≤ (eLpNormEssSup (datum χ A₁ μ sbar) volume).toReal := ENNReal.toReal_nonneg
    simp only [Set.mem_ofPred_eq, not_le]
    rw [Real.enorm_eq_ofReal (datum_nonneg hR hp x), ← ENNReal.ofReal_toReal hMtop]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have h0 : volume (ball (((radius sbar μ (n + 1) : ℝ) : ℂ) * y₀) (ρ * radius sbar μ (n + 1)))
      = 0 := measure_mono_null hsub (ae_iff.1 hae)
  exact (measure_ball_pos volume _ (mul_pos hρ hr)).ne' h0

end NonUniqueEuler.Datum.IntegrabilityH
