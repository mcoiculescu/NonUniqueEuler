import NonUniqueEuler.Defs.Sec6.All
import NonUniqueEuler.I.Sec6.Integrability
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.H.Sec6.LqGrowth.Calculus
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Proof: `lem:Lq-growth` (growth of `‖f‖_{L^q}`; off the path to the main theorem, R13)

Proof of `I/Sec6/LqGrowth.lean` (`06_datum.tex:504-527`, proof `:529-591`). Same declarations,
statements copied verbatim.

**Part (1)** follows the manuscript: `Φ ≥ m = Φ(y₀)/2` on `B_ρ(y₀)` (continuity), so
`f ≥ A_k m` on `B_{ρ r_k}(r_k y₀)` (one term of the nonnegative series is below `f`), hence
`‖f‖_q ≥ A_k m (πρ² r_k²)^{1/q}` (the `L^q` norm of a constant on a disk; this replaces the
change of variables `x = r_k y`). With `j = ⌊q log μ/(2 log 2μ)⌋` and `log(1/r_k)` from
`prop:integrability` one gets `‖f‖_q ≥ c e^{α_μ q}` with
`c = m · min(1, πρ²) · A₁ · e^{-log μ - S log μ/L}` (`= c_Φ A₁ μ^{-1-S/L}` of the manuscript).

**Part (2)** (deviation): instead of the arithmetic–geometric mean inequality we use
`e^a e^b ≥ (1 + ab/2)²` (`LqGrowthH.sq_one_add_half_mul_le_exp_mul_exp`) with `a = ε log y`,
`b = α_μ/ε`; it gives `ψ_θ(y) ≥ (c p₀/K₀)(1 + γ log y)²`, `γ = α_μ/2`, and
`y ↦ 1/(y(1 + γ log y)²)` is integrable on `(1, ∞)` (an explicit antiderivative). Measurability of
`ψ_θ` on `(1, ∞)`: `ψ_θ` is monotone there (each `y ↦ y^ε` is), instead of upper semicontinuous.

**Part (3)** follows the manuscript: `θ(p) ≥ (c/K₀) e^{α_μ p}`, so `1/(pθ(p)) ≤ (K₀/c) e^{-α_μ p}`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Datum

open RingData

/-- One term of the series is below the datum: `A_k Φ(x/r_k) ≤ f(x)` (all terms are `≥ 0` and the
series is summable, `prop:integrability`, `lem:ring-facts`). -/
private theorem LqGrowthP_term_le_datum (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {A₁ μ sbar : ℝ}
    (hp : DatumParams A₁ μ sbar) (j : ℕ) (x : ℂ) :
    amp A₁ μ (j + 1) * ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) ≤
      datum χ A₁ μ sbar x := by
  obtain ⟨-, -, hsum, -, -⟩ := integrability χ hχ hp
  obtain ⟨-, -, -, hrange, -⟩ := ringFacts_of_admissible hχ
  have hμ0 : 0 < μ := by linarith [hp.one_lt_μ]
  exact (hsum x).le_tsum j fun i _ =>
    mul_nonneg (amp_pos hp.A₁_pos hμ0 _).le (hrange _).1

/-- `‖f‖_{L^q} ≥ A_k m (ρ² r_k² π)^{1/q}` when `Φ ≥ m` on `B_ρ(y₀)`: `f ≥ A_k m` on the disk
`B_{ρ r_k}(r_k y₀)`, whose area is `π ρ² r_k²`. -/
private theorem LqGrowthP_eLpNorm_ge_ball (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    {A₁ μ sbar : ℝ} (hp : DatumParams A₁ μ sbar) {m ρ : ℝ} (hm : 0 ≤ m) (hρ : 0 < ρ) {y₀ : ℂ}
    (hball : ∀ y ∈ ball y₀ ρ, m ≤ ringPhi χ y) (j : ℕ) {q : ℝ} (hq : 1 ≤ q) :
    ENNReal.ofReal (amp A₁ μ (j + 1) * m *
        (ρ ^ 2 * radius sbar μ (j + 1) ^ 2 * Real.pi) ^ (1 / q)) ≤
      eLpNorm (datum χ A₁ μ sbar) (ENNReal.ofReal q) volume := by
  obtain ⟨hD, -⟩ := integrability χ hχ hp
  have hnonneg : ∀ x, 0 ≤ datum χ A₁ μ sbar x := hD.2.2.1
  have hμ0 : 0 < μ := by linarith [hp.one_lt_μ]
  have hr : 0 < radius sbar μ (j + 1) := radius_pos hp.sbar_pos hμ0 _
  have hA : 0 < amp A₁ μ (j + 1) := amp_pos hp.A₁_pos hμ0 _
  have hq0 : 0 < q := by linarith
  set r := radius sbar μ (j + 1) with hr_def
  set A := amp A₁ μ (j + 1) with hA_def
  set s : Set ℂ := ball ((r : ℂ) * y₀) (ρ * r) with hs_def
  have hind : ∀ x, ‖s.indicator (fun _ => A * m) x‖ ≤ datum χ A₁ μ sbar x := by
    intro x
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx, Real.norm_of_nonneg (mul_nonneg hA.le hm)]
      have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have hx' : x / (r : ℂ) ∈ ball y₀ ρ := by
        rw [hs_def, mem_ball, dist_eq_norm] at hx
        rw [mem_ball, dist_eq_norm]
        have hdiv : x / (r : ℂ) - y₀ = (x - (r : ℂ) * y₀) / (r : ℂ) := by
          field_simp
        rw [hdiv, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_lt_iff₀ hr]
        exact hx
      calc A * m ≤ A * ringPhi χ (x / (r : ℂ)) :=
            mul_le_mul_of_nonneg_left (hball _ hx') hA.le
        _ ≤ datum χ A₁ μ sbar x := LqGrowthP_term_le_datum χ hχ hp j x
    · rw [indicator_of_notMem hx, norm_zero]
      exact hnonneg x
  have hmono := eLpNorm_mono_real (p := ENNReal.ofReal q) (μ := volume) hind
  have hq_ne : ENNReal.ofReal q ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hq0
  rw [eLpNorm_indicator_const measurableSet_ball hq_ne ENNReal.ofReal_ne_top,
    Complex.volume_ball, ENNReal.toReal_ofReal hq0.le] at hmono
  refine le_trans (le_of_eq ?_) hmono
  have hV : ENNReal.ofReal (ρ * r) ^ 2 * (NNReal.pi : ENNReal) =
      ENNReal.ofReal (ρ ^ 2 * r ^ 2 * Real.pi) := by
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
      ← ENNReal.ofReal_mul (by positivity), mul_pow]
  rw [hV, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    Real.enorm_eq_ofReal (mul_nonneg hA.le hm), ← ENNReal.ofReal_mul (mul_nonneg hA.le hm)]

/-- **`lem:Lq-growth`(1)** (`06_datum.tex:509-510`): there is `c > 0` with
`‖f‖_{L^q} ≥ c e^{α_μ q}` for every real `q ≥ 1`. -/
theorem Lq_growth_lower (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {A₁ μ sbar : ℝ}
    (hp : DatumParams A₁ μ sbar) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℝ, 1 ≤ q →
      ENNReal.ofReal (c * Real.exp (alphaMu μ * q)) ≤
        eLpNorm (datum χ A₁ μ sbar) (ENNReal.ofReal q) volume := by
  obtain ⟨-, -, -, hlog, -⟩ := integrability χ hχ hp
  obtain ⟨hsmooth, -, -, hrange, ⟨y₀, hy₀⟩, -, -, ha1⟩ := ringFacts_of_admissible hχ
  have hμ1 : 1 < μ := hp.one_lt_μ
  have hμ0 : 0 < μ := by linarith
  have hΦ0 : 0 < ringPhi χ y₀ := lt_of_le_of_ne (hrange y₀).1 (Ne.symm hy₀)
  have hm : 0 < ringPhi χ y₀ / 2 := by positivity
  -- `Φ ≥ Φ(y₀)/2` on a disk `B_ρ(y₀)`
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ y ∈ ball y₀ ρ, ringPhi χ y₀ / 2 ≤ ringPhi χ y := by
    have hc : ContinuousAt (ringPhi χ) y₀ := hsmooth.continuous.continuousAt
    have hev : ∀ᶠ y in 𝓝 y₀, ringPhi χ y₀ / 2 < ringPhi χ y :=
      hc.eventually (lt_mem_nhds (by linarith))
    obtain ⟨ρ, hρ, h⟩ := Metric.eventually_nhds_iff_ball.1 hev
    exact ⟨ρ, hρ, fun y hy => (h y hy).le⟩
  have hl : 0 < Real.log μ := Real.log_pos hμ1
  have hL : 0 < Real.log (2 * μ) := Real.log_pos (by linarith)
  have hS : 0 ≤ Real.log (1 / sbar) := by
    have hs1 : sbar ≤ 1 := by
      have := hp.sbar_le
      linarith
    exact Real.log_nonneg (by rw [le_div_iff₀ hp.sbar_pos]; linarith)
  have hV0 : 0 < ρ ^ 2 * Real.pi := by positivity
  refine ⟨ringPhi χ y₀ / 2 * min 1 (ρ ^ 2 * Real.pi) * A₁ *
      Real.exp (-Real.log μ - Real.log (1 / sbar) * Real.log μ / Real.log (2 * μ)),
    by have := hp.A₁_pos; positivity, fun q hq => ?_⟩
  have hq0 : 0 < q := by linarith
  have ht : 0 ≤ q * Real.log μ / (2 * Real.log (2 * μ)) := by positivity
  obtain ⟨j, hj1, hj2⟩ : ∃ j : ℕ, (j : ℝ) ≤ q * Real.log μ / (2 * Real.log (2 * μ)) ∧
      q * Real.log μ / (2 * Real.log (2 * μ)) < j + 1 :=
    ⟨_, Nat.floor_le ht, Nat.lt_floor_add_one _⟩
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (LqGrowthP_eLpNorm_ge_ball χ hχ hp hm.le hρ hball j hq)
  have hr : 0 < radius sbar μ (j + 1) := radius_pos hp.sbar_pos hμ0 _
  have hlogr : Real.log (1 / radius sbar μ (j + 1)) =
      j * Real.log (1 / sbar) + (j + 1) * j / 2 * Real.log (2 * μ) := by
    rw [hlog (j + 1) (by omega)]
    push_cast
    ring
  have hA : amp A₁ μ (j + 1) = A₁ * Real.exp (j * Real.log μ) := by
    rw [amp, Nat.add_sub_cancel, Real.exp_nat_mul, Real.exp_log hμ0]
  have hsplit : (ρ ^ 2 * radius sbar μ (j + 1) ^ 2 * Real.pi) ^ (1 / q) =
      (ρ ^ 2 * Real.pi) ^ (1 / q) *
        Real.exp (-(2 / q) * Real.log (1 / radius sbar μ (j + 1))) := by
    rw [show ρ ^ 2 * radius sbar μ (j + 1) ^ 2 * Real.pi =
        (ρ ^ 2 * Real.pi) * radius sbar μ (j + 1) ^ 2 by ring,
      Real.mul_rpow hV0.le (by positivity), Real.rpow_def_of_pos (pow_pos hr 2), Real.log_pow,
      one_div (radius sbar μ (j + 1)), Real.log_inv]
    congr 2
    push_cast
    ring
  have hmin : min 1 (ρ ^ 2 * Real.pi) ≤ (ρ ^ 2 * Real.pi) ^ (1 / q) := by
    rcases le_total 1 (ρ ^ 2 * Real.pi) with h | h
    · exact (min_le_left _ _).trans (Real.one_le_rpow h (by positivity))
    · calc min 1 (ρ ^ 2 * Real.pi) ≤ ρ ^ 2 * Real.pi := min_le_right _ _
        _ = (ρ ^ 2 * Real.pi) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (ρ ^ 2 * Real.pi) ^ (1 / q) :=
          Real.rpow_le_rpow_of_exponent_ge hV0 h (by rw [div_le_one hq0]; exact hq)
  have hE := LqGrowthH.floor_exponent_ineq hl hL hS hq (Nat.cast_nonneg j) hj1 hj2
  rw [hA, hsplit, hlogr]
  have halpha : alphaMu μ = Real.log μ ^ 2 / (4 * Real.log (2 * μ)) := rfl
  rw [halpha]
  have hA₁ := hp.A₁_pos
  calc ringPhi χ y₀ / 2 * min 1 (ρ ^ 2 * Real.pi) * A₁ *
        Real.exp (-Real.log μ - Real.log (1 / sbar) * Real.log μ / Real.log (2 * μ)) *
        Real.exp (Real.log μ ^ 2 / (4 * Real.log (2 * μ)) * q)
      = ringPhi χ y₀ / 2 * min 1 (ρ ^ 2 * Real.pi) * A₁ *
        Real.exp (-Real.log μ - Real.log (1 / sbar) * Real.log μ / Real.log (2 * μ) +
          Real.log μ ^ 2 / (4 * Real.log (2 * μ)) * q) := by
        rw [Real.exp_add]
        ring
    _ ≤ ringPhi χ y₀ / 2 * (ρ ^ 2 * Real.pi) ^ (1 / q) * A₁ *
        Real.exp (j * Real.log μ - 2 / q *
          (j * Real.log (1 / sbar) + (j + 1) * j / 2 * Real.log (2 * μ))) := by
        have h1 : ringPhi χ y₀ / 2 * min 1 (ρ ^ 2 * Real.pi) * A₁ ≤
            ringPhi χ y₀ / 2 * (ρ ^ 2 * Real.pi) ^ (1 / q) * A₁ := by
          gcongr
        exact mul_le_mul h1 (Real.exp_le_exp.2 hE) (Real.exp_pos _).le (by positivity)
    _ = A₁ * Real.exp (j * Real.log μ) * (ringPhi χ y₀ / 2) *
        ((ρ ^ 2 * Real.pi) ^ (1 / q) * Real.exp (-(2 / q) *
          (j * Real.log (1 / sbar) + (j + 1) * j / 2 * Real.log (2 * μ)))) := by
        rw [sub_eq_add_neg, Real.exp_add, neg_mul]
        ring

/-- `α_μ > 0` for `μ > 1`. -/
private theorem LqGrowthP_alphaMu_pos {μ : ℝ} (hμ : 1 < μ) : 0 < alphaMu μ := by
  unfold alphaMu
  have h1 : 0 < Real.log μ := Real.log_pos hμ
  have h2 : 0 < Real.log (2 * μ) := Real.log_pos (by linarith)
  positivity

/-- **`lem:Lq-growth`(2)** (`06_datum.tex:511-520`): if `p₀ ≥ 1`, `K₀ > 0`, `θ > 0` on `[p₀, ∞)`
and `‖f‖_{L^p} ≤ K₀θ(p)` for `p ≥ p₀`, then `y ↦ 1/(y ψ_θ(y))` is integrable on `(1, ∞)`. -/
theorem Lq_growth_psi (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {A₁ μ sbar : ℝ}
    (hp : DatumParams A₁ μ sbar) {p₀ K₀ : ℝ} {θ : ℝ → ℝ} (hp₀ : 1 ≤ p₀) (hK₀ : 0 < K₀)
    (hθ : ∀ p : ℝ, p₀ ≤ p → 0 < θ p)
    (hf : ∀ p : ℝ, p₀ ≤ p →
      eLpNorm (datum χ A₁ μ sbar) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (K₀ * θ p)) :
    IntegrableOn (fun y : ℝ => (y * psiTheta p₀ θ y)⁻¹) (Ioi 1) := by
  obtain ⟨c, hc, hlow⟩ := Lq_growth_lower χ hχ hp
  have hα : 0 < alphaMu μ := LqGrowthP_alphaMu_pos hp.one_lt_μ
  have hp₀0 : 0 < p₀ := by linarith
  -- `c e^{α p} ≤ K₀ θ(p)` for `p ≥ p₀`
  have hθlow : ∀ p, p₀ ≤ p → c * Real.exp (alphaMu μ * p) ≤ K₀ * θ p := by
    intro p hpp
    have h := (hlow p (hp₀.trans hpp)).trans (hf p hpp)
    exact (ENNReal.ofReal_le_ofReal_iff (mul_pos hK₀ (hθ p hpp)).le).1 h
  have hp₀ε : ∀ ε ∈ Ioc (0 : ℝ) (1 / p₀), p₀ ≤ 1 / ε := by
    intro ε hε
    rw [le_div_iff₀ hε.1]
    have := (le_div_iff₀ hp₀0).1 hε.2
    linarith
  have hel_pos : ∀ y : ℝ, 0 < y → ∀ ε ∈ Ioc (0 : ℝ) (1 / p₀),
      0 < y ^ ε * ε⁻¹ * θ (1 / ε) := fun y hy ε hε =>
    mul_pos (mul_pos (Real.rpow_pos_of_pos hy ε) (inv_pos.2 hε.1)) (hθ _ (hp₀ε ε hε))
  have hne : ∀ y : ℝ,
      ((fun ε : ℝ => y ^ ε * ε⁻¹ * θ (1 / ε)) '' Ioc 0 (1 / p₀)).Nonempty := fun y =>
    ⟨_, mem_image_of_mem _ (⟨by positivity, le_rfl⟩ : 1 / p₀ ∈ Ioc (0 : ℝ) (1 / p₀))⟩
  have hbdd : ∀ y : ℝ, 0 < y →
      BddBelow ((fun ε : ℝ => y ^ ε * ε⁻¹ * θ (1 / ε)) '' Ioc 0 (1 / p₀)) := by
    intro y hy
    refine ⟨0, ?_⟩
    rintro _ ⟨ε, hε, rfl⟩
    exact (hel_pos y hy ε hε).le
  have hγ : 0 < alphaMu μ / 2 := half_pos hα
  -- the lower bound `ψ_θ(y) ≥ (c p₀/K₀) (1 + γ log y)²`
  have hψlow : ∀ y : ℝ, 1 < y →
      c * p₀ / K₀ * (1 + alphaMu μ / 2 * Real.log y) ^ 2 ≤ psiTheta p₀ θ y := by
    intro y hy
    unfold psiTheta
    apply le_csInf (hne y)
    rintro _ ⟨ε, hε, rfl⟩
    have hs : 0 ≤ Real.log y := Real.log_nonneg hy.le
    have hθε := hθlow (1 / ε) (hp₀ε ε hε)
    have hinv : p₀ ≤ ε⁻¹ := by
      rw [← one_div]
      exact hp₀ε ε hε
    have hkey := LqGrowthH.sq_one_add_half_mul_le_exp_mul_exp (mul_nonneg hε.1.le hs)
      (mul_nonneg hα.le (one_div_nonneg.2 hε.1.le))
    have hε0 : ε ≠ 0 := hε.1.ne'
    have hab : ε * Real.log y * (alphaMu μ * (1 / ε)) / 2 = alphaMu μ / 2 * Real.log y := by
      field_simp
    rw [hab] at hkey
    beta_reduce
    rw [Real.rpow_def_of_pos (by linarith)]
    have hθε' : c * Real.exp (alphaMu μ * (1 / ε)) / K₀ ≤ θ (1 / ε) := by
      rw [div_le_iff₀ hK₀]
      linarith
    calc c * p₀ / K₀ * (1 + alphaMu μ / 2 * Real.log y) ^ 2
        ≤ c * p₀ / K₀ * (Real.exp (ε * Real.log y) * Real.exp (alphaMu μ * (1 / ε))) := by
          gcongr
      _ = (p₀ * Real.exp (Real.log y * ε)) * (c * Real.exp (alphaMu μ * (1 / ε)) / K₀) := by
          rw [mul_comm ε]
          ring
      _ ≤ (ε⁻¹ * Real.exp (Real.log y * ε)) * θ (1 / ε) := by
          apply mul_le_mul _ hθε' (by positivity)
            (mul_pos (inv_pos.2 hε.1) (Real.exp_pos _)).le
          exact mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
      _ = Real.exp (Real.log y * ε) * ε⁻¹ * θ (1 / ε) := by ring
  -- `ψ_θ` is monotone on `(1, ∞)`, hence measurable there
  have hmono : MonotoneOn (psiTheta p₀ θ) (Ioi 1) := by
    intro y₁ hy₁ y₂ hy₂ hy
    have hy₁0 : 0 < y₁ := lt_trans zero_lt_one hy₁
    unfold psiTheta
    apply le_csInf (hne y₂)
    rintro _ ⟨ε, hε, rfl⟩
    beta_reduce
    calc sInf ((fun ε : ℝ => y₁ ^ ε * ε⁻¹ * θ (1 / ε)) '' Ioc 0 (1 / p₀))
        ≤ y₁ ^ ε * ε⁻¹ * θ (1 / ε) := csInf_le (hbdd y₁ hy₁0) (mem_image_of_mem _ hε)
      _ ≤ y₂ ^ ε * ε⁻¹ * θ (1 / ε) := by
          apply mul_le_mul_of_nonneg_right _ (hθ _ (hp₀ε ε hε)).le
          exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hy₁0.le hy hε.1.le)
            (inv_nonneg.2 hε.1.le)
  have hmeas : AEStronglyMeasurable (fun y : ℝ => (y * psiTheta p₀ θ y)⁻¹)
      (volume.restrict (Ioi 1)) :=
    ((measurable_id.aemeasurable.mul
      (aemeasurable_restrict_of_monotoneOn measurableSet_Ioi hmono)).inv).aestronglyMeasurable
  have hint := Integrable.const_mul (LqGrowthH.integrableOn_Ioi_one_log_decay hγ)
    (K₀ / (c * p₀ * (alphaMu μ / 2)))
  refine hint.mono' hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_)
  have hy1 : 1 < y := hy
  have hy0 : 0 < y := by linarith
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy1.le
  have hX : 0 < 1 + alphaMu μ / 2 * Real.log y := by positivity
  have hB : 0 < c * p₀ / K₀ * (1 + alphaMu μ / 2 * Real.log y) ^ 2 := by positivity
  have hψ := hψlow y hy1
  have hψpos : 0 < psiTheta p₀ θ y := hB.trans_le hψ
  rw [Real.norm_of_nonneg (inv_nonneg.2 (mul_pos hy0 hψpos).le)]
  calc (y * psiTheta p₀ θ y)⁻¹
      ≤ (y * (c * p₀ / K₀ * (1 + alphaMu μ / 2 * Real.log y) ^ 2))⁻¹ :=
        inv_anti₀ (mul_pos hy0 hB) (mul_le_mul_of_nonneg_left hψ hy0.le)
    _ = K₀ / (c * p₀ * (alphaMu μ / 2)) *
        (alphaMu μ / 2 * y⁻¹ / (1 + alphaMu μ / 2 * Real.log y) ^ 2) := by
        field_simp

/-- **`lem:Lq-growth`(3)** (`06_datum.tex:521-526`): if `K₀ > 0`, `θ` is measurable and positive on
`[1, ∞)`, and `‖f‖_{L^p} ≤ K₀θ(p)` for `p ≥ 1`, then `p ↦ 1/(p θ(p))` is integrable on `(1, ∞)`. -/
theorem Lq_growth_theta (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {A₁ μ sbar : ℝ}
    (hp : DatumParams A₁ μ sbar) {K₀ : ℝ} {θ : ℝ → ℝ} (hK₀ : 0 < K₀) (hθm : Measurable θ)
    (hθ : ∀ p : ℝ, 1 ≤ p → 0 < θ p)
    (hf : ∀ p : ℝ, 1 ≤ p →
      eLpNorm (datum χ A₁ μ sbar) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (K₀ * θ p)) :
    IntegrableOn (fun p : ℝ => (p * θ p)⁻¹) (Ioi 1) := by
  obtain ⟨c, hc, hlow⟩ := Lq_growth_lower χ hχ hp
  have hα : 0 < alphaMu μ := LqGrowthP_alphaMu_pos hp.one_lt_μ
  have hmeas : AEStronglyMeasurable (fun p : ℝ => (p * θ p)⁻¹) (volume.restrict (Ioi 1)) :=
    (measurable_id.mul hθm).inv.aestronglyMeasurable
  refine (Integrable.const_mul (exp_neg_integrableOn_Ioi 1 hα) (K₀ / c)).mono' hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun p hp1 => ?_)
  have hp1' : 1 < p := hp1
  have hp0 : 0 < p := by linarith
  have hθpos := hθ p hp1'.le
  have hθp : c * Real.exp (alphaMu μ * p) ≤ K₀ * θ p :=
    (ENNReal.ofReal_le_ofReal_iff (mul_pos hK₀ hθpos).le).1
      ((hlow p hp1'.le).trans (hf p hp1'.le))
  have hlow' : c / K₀ * Real.exp (alphaMu μ * p) ≤ p * θ p := by
    have h1 : c / K₀ * Real.exp (alphaMu μ * p) ≤ θ p := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hK₀]
      linarith
    have h2 : θ p ≤ p * θ p := le_mul_of_one_le_left hθpos.le hp1'.le
    linarith
  rw [Real.norm_of_nonneg (inv_nonneg.2 (mul_pos hp0 hθpos).le)]
  calc (p * θ p)⁻¹ ≤ (c / K₀ * Real.exp (alphaMu μ * p))⁻¹ :=
        inv_anti₀ (by positivity) hlow'
    _ = K₀ / c * Real.exp (-alphaMu μ * p) := by
        rw [neg_mul, Real.exp_neg]
        field_simp

end Datum

end NonUniqueEuler
