import NonUniqueEuler.Statement.WeakSolution
import NonUniqueEuler.I.Infra.LpInterp.Interp
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Proof: convergence in `L^q` by interpolation (P-LPINT, `I/Infra/LpInterp/Tendsto.lean`)

Proof of the interface `NonUniqueEuler/I/Infra/LpInterp/Tendsto.lean`, following its sketch.

* `exists_theta_of_lt`: for `0 < p ≤ q < r` there is `θ ∈ [0,1)` with
  `1/q = (1-θ)/p + θ/r`, namely `θ = (1/p - 1/q)/(1/p - 1/r)`.
* `tendsto_eLpNorm_of_interp`: `‖F_i‖_q ≤ ‖F_i‖_p^{1-θ} ‖F_i‖_r^θ ≤ ‖F_i‖_p^{1-θ} C^θ → 0`
  (log-convexity, `I/Infra/LpInterp/Interp.lean`).
* `continuousIntoLp_of_interp`: apply the previous result to `ω t - ω t₀` along
  `𝓝[Ici 0] t₀`, with the bound `‖ω t - ω t₀‖_r ≤ 2C`, and `L^p ∩ L^r ⊆ L^q`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace NonUniqueEuler.LpInterp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*} [NormedAddCommGroup E]

/-- The interpolation parameter: for `0 < p ≤ q < r` there is `θ ∈ [0,1)` with
`1/q = (1-θ)/p + θ/r`. -/
lemma exists_theta_of_lt {p q r : ℝ≥0∞} (hp : 0 < p) (hpq : p ≤ q) (hqr : q < r) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      q⁻¹ = ENNReal.ofReal (1 - θ) * p⁻¹ + ENNReal.ofReal θ * r⁻¹ := by
  have hq0 : q ≠ 0 := (hp.trans_le hpq).ne'
  have hpinv : p⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hp.ne'
  have hqinv : q⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hq0
  have hrinv : r⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 ((hp.trans_le hpq).trans hqr).ne'
  have hab : q⁻¹.toReal ≤ p⁻¹.toReal :=
    ENNReal.toReal_mono hpinv (ENNReal.inv_le_inv.2 hpq)
  have hbc : r⁻¹.toReal < q⁻¹.toReal :=
    (ENNReal.toReal_lt_toReal hrinv hqinv).2 (ENNReal.inv_lt_inv.2 hqr)
  have hc : 0 ≤ r⁻¹.toReal := ENNReal.toReal_nonneg
  have hac : 0 < p⁻¹.toReal - r⁻¹.toReal := by linarith
  set θ : ℝ := (p⁻¹.toReal - q⁻¹.toReal) / (p⁻¹.toReal - r⁻¹.toReal) with hθdef
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hac.le
  have hθ1 : θ < 1 := (div_lt_one hac).2 (by linarith)
  refine ⟨θ, hθ0, hθ1, ?_⟩
  have hkey : (1 - θ) * p⁻¹.toReal + θ * r⁻¹.toReal = q⁻¹.toReal := by
    rw [hθdef]
    field_simp
    ring
  calc q⁻¹ = ENNReal.ofReal q⁻¹.toReal := (ENNReal.ofReal_toReal hqinv).symm
    _ = ENNReal.ofReal ((1 - θ) * p⁻¹.toReal + θ * r⁻¹.toReal) := by rw [hkey]
    _ = ENNReal.ofReal (1 - θ) * ENNReal.ofReal p⁻¹.toReal
          + ENNReal.ofReal θ * ENNReal.ofReal r⁻¹.toReal := by
        rw [ENNReal.ofReal_add (mul_nonneg (by linarith) ENNReal.toReal_nonneg)
          (mul_nonneg hθ0 hc), ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_mul hθ0]
    _ = ENNReal.ofReal (1 - θ) * p⁻¹ + ENNReal.ofReal θ * r⁻¹ := by
        rw [ENNReal.ofReal_toReal hpinv, ENNReal.ofReal_toReal hrinv]

/-- Convergence to `0` in `L^p`, plus a uniform `L^r` bound, gives convergence in `L^q`,
`0 < p ≤ q < r`. -/
theorem tendsto_eLpNorm_of_interp {ι : Type*} {l : Filter ι} {F : ι → α → E}
    (hF : ∀ i, AEStronglyMeasurable (F i) μ) {p q r : ℝ≥0∞} (hp : 0 < p) (hpq : p ≤ q)
    (hqr : q < r) {C : ℝ≥0∞} (hC : C ≠ ∞) (hbound : ∀ᶠ i in l, eLpNorm (F i) r μ ≤ C)
    (hlim : Tendsto (fun i => eLpNorm (F i) p μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (F i) q μ) l (𝓝 0) := by
  obtain ⟨θ, hθ0, hθ1, hθ⟩ := exists_theta_of_lt hp hpq hqr
  have h1θ : 0 < 1 - θ := by linarith
  have hupper : Tendsto (fun i => eLpNorm (F i) p μ ^ (1 - θ) * C ^ θ) l (𝓝 0) := by
    have h0 : Tendsto (fun i => eLpNorm (F i) p μ ^ (1 - θ)) l (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := 1 - θ)).tendsto 0).comp hlim
      rwa [ENNReal.zero_rpow_of_pos h1θ] at this
    have := ENNReal.Tendsto.mul_const h0 (Or.inr (ENNReal.rpow_ne_top_of_nonneg hθ0 hC))
    rwa [zero_mul] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hbound] with i hi
  calc eLpNorm (F i) q μ ≤ eLpNorm (F i) p μ ^ (1 - θ) * eLpNorm (F i) r μ ^ θ :=
        eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow (hF i) hθ0 hθ1.le hθ
    _ ≤ eLpNorm (F i) p μ ^ (1 - θ) * C ^ θ := by
        gcongr

/-- `C([0,∞); L^p)` plus a uniform `L^r` bound gives `C([0,∞); L^q)`, `1 ≤ p ≤ q < r`. -/
theorem continuousIntoLp_of_interp {ω : ℝ → ℂ → ℝ} {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hqr : q < r) (hcont : ContinuousIntoLp p ω) (hr : ∀ t, 0 ≤ t → MemLp (ω t) r volume)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hbd : ∀ t, 0 ≤ t → eLpNorm (ω t) r volume ≤ C) :
    ContinuousIntoLp q ω := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hr1 : 1 ≤ r := hp.trans (hpq.trans hqr.le)
  refine ⟨fun t ht => memLp_of_memLp_of_memLp hp0 hpq hqr.le (hcont.1 t ht) (hr t ht), ?_⟩
  intro t₀ ht₀
  let F : ℝ → ℂ → ℝ := fun t => if 0 ≤ t then ω t - ω t₀ else 0
  have hFeq : ∀ᶠ t in 𝓝[Ici 0] t₀, F t = ω t - ω t₀ := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 ≤ t)
    simp [F, ht]
  have hFm : ∀ t, AEStronglyMeasurable (F t) volume := by
    intro t
    by_cases ht : 0 ≤ t
    · simp only [F, ht, ite_true]
      exact (hcont.1 t ht).1.sub (hcont.1 t₀ ht₀).1
    · simp only [F, ht, ite_false]
      exact aestronglyMeasurable_const
  have hbound : ∀ᶠ t in 𝓝[Ici 0] t₀, eLpNorm (F t) r volume ≤ C + C := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 ≤ t)
    simp only [F, ht, ite_true]
    calc eLpNorm (ω t - ω t₀) r volume ≤ eLpNorm (ω t) r volume + eLpNorm (ω t₀) r volume :=
          eLpNorm_sub_le (hr t ht).1 (hr t₀ ht₀).1 hr1
      _ ≤ C + C := add_le_add (hbd t ht) (hbd t₀ ht₀)
  have hlim : Tendsto (fun t => eLpNorm (F t) p volume) (𝓝[Ici 0] t₀) (𝓝 0) :=
    (hcont.2 t₀ ht₀).congr'
      (hFeq.mono fun t ht => congrArg (fun g => eLpNorm g p volume) ht.symm)
  have hq := tendsto_eLpNorm_of_interp hFm hp0 hpq hqr (ENNReal.add_ne_top.2 ⟨hC, hC⟩)
    hbound hlim
  exact hq.congr' (hFeq.mono fun t ht => by rw [ht])

end NonUniqueEuler.LpInterp
