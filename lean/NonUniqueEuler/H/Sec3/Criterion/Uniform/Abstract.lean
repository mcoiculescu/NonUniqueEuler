import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Helper for `P/Sec3/Criterion/Uniform`: abstract lemmas

Manuscript: proof of `thm:criterion`(iv), `03_compactness.tex:1023-1056`.

* `tendsto_iSup_of_seq`: the sequential criterion for uniform convergence on a compact set used
  in the contradiction argument (`03_compactness.tex:1027-1033`): if `D (nᵢ) (tᵢ) → 0` whenever
  `nᵢ → ∞` and `tᵢ → t₀` in `K`, then `sup_{t ∈ K} D n t → 0`.
* `tendsto_lintegral_tail`: `∫_{|x| ≥ R} |g| → 0` as `R → ∞` for `g ∈ L¹` (the tails of
  `f` and `ω_∞(t)` in the claim, `03_compactness.tex:1047-1055`).
* `tendsto_zero_of_le_add`: "let `n → ∞`, then `R → ∞`" (`03_compactness.tex:1055-1056`).
* `tendsto_rpow_mul_rpow_zero`: the interpolation limit `S₁^{2/q-1} S₂^{2-2/q} → 0`
  (`03_compactness.tex:1034-1035`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.UniformAux

/-- Sequential criterion for uniform convergence to `0` on a compact set: if `D (nᵢ) (tᵢ) → 0`
whenever `nᵢ → ∞` and `tᵢ ∈ K`, `tᵢ → t₀ ∈ K`, then `sup_{t ∈ K} D n t → 0`
(`03_compactness.tex:1027-1033`). -/
theorem tendsto_iSup_of_seq {K : Set ℝ} (hK : IsCompact K) (D : ℕ → ℝ → ℝ≥0∞)
    (h : ∀ (n : ℕ → ℕ) (t : ℕ → ℝ) (t₀ : ℝ), Tendsto n atTop atTop → (∀ i, t i ∈ K) →
      t₀ ∈ K → Tendsto t atTop (𝓝 t₀) → Tendsto (fun i => D (n i) (t i)) atTop (𝓝 0)) :
    Tendsto (fun n => ⨆ t ∈ K, D n t) atTop (𝓝 0) := by
  by_contra hne
  rw [ENNReal.tendsto_nhds_zero] at hne
  push Not at hne
  obtain ⟨ε, hε, hfreq⟩ := hne
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hfreq
  have hex : ∀ k, ∃ t ∈ K, ε < D (φ k) t := by
    intro k
    have hk := hP k
    simp only [lt_iSup_iff] at hk
    obtain ⟨t, ht, hlt⟩ := hk
    exact ⟨t, ht, hlt⟩
  choose t htK hlt using hex
  obtain ⟨t₀, ht₀, ψ, hψ, hlim⟩ := hK.tendsto_subseq htK
  have hD := h (fun i => φ (ψ i)) (fun i => t (ψ i)) t₀ (hφ.comp hψ).tendsto_atTop
    (fun i => htK _) ht₀ hlim
  obtain ⟨i, hi⟩ := (hD.eventually (gt_mem_nhds hε)).exists
  exact lt_asymm hi (hlt (ψ i))

/-- The tails of an integrable function vanish: `∫_{|x| ≥ R} |g| → 0` as `R → ∞`. -/
theorem tendsto_lintegral_tail {E : Type*} [NormedAddCommGroup E] {g : ℂ → E}
    (hg : ∫⁻ x, ‖g x‖ₑ ≠ ∞) :
    Tendsto (fun R : ℝ => ∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖g x‖ₑ) atTop (𝓝 0) := by
  set ν : Measure ℂ := volume.withDensity (fun x => ‖g x‖ₑ) with hν
  have hs : ∀ R : ℝ, MeasurableSet {x : ℂ | R ≤ ‖x‖} := fun R =>
    measurableSet_le measurable_const measurable_norm
  have hanti : Antitone fun R : ℝ => {x : ℂ | R ≤ ‖x‖} := fun R R' hRR' x hx =>
    le_trans hRR' hx
  have hfin : ∃ R : ℝ, ν {x : ℂ | R ≤ ‖x‖} ≠ ∞ := by
    refine ⟨0, ne_top_of_le_ne_top hg ?_⟩
    rw [hν, withDensity_apply _ (hs 0)]
    exact setLIntegral_le_lintegral _ _
  have h := tendsto_measure_iInter_atTop (μ := ν) (s := fun R : ℝ => {x : ℂ | R ≤ ‖x‖})
    (fun R => (hs R).nullMeasurableSet) hanti hfin
  have hempty : (⋂ R : ℝ, {x : ℂ | R ≤ ‖x‖}) = ∅ := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_le]
    exact ⟨‖x‖ + 1, by linarith⟩
  rw [hempty, measure_empty] at h
  refine h.congr fun R => ?_
  simp only [Function.comp_apply, hν, withDensity_apply _ (hs R)]

/-- "Let `n → ∞`, then `R → ∞`": if `aᵢ ≤ x_R(i) + τ(R)` eventually for every `R > 0`, with
`x_R(i) → 0` for every `R > 0` and `τ(R) → 0` as `R → ∞`, then `aᵢ → 0`. -/
theorem tendsto_zero_of_le_add {ι : Type*} {l : Filter ι} {a : ι → ℝ≥0∞}
    {x : ℝ → ι → ℝ≥0∞} {τ : ℝ → ℝ≥0∞} (hτ : Tendsto τ atTop (𝓝 0))
    (hx : ∀ R, 0 < R → Tendsto (x R) l (𝓝 0))
    (hle : ∀ R, 0 < R → ∀ᶠ i in l, a i ≤ x R i + τ R) : Tendsto a l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨R, hRτ, hR⟩ :=
    ((hτ.eventually (gt_mem_nhds hε2)).and (eventually_gt_atTop (0 : ℝ))).exists
  filter_upwards [hle R hR, ENNReal.tendsto_nhds_zero.1 (hx R hR) (ε / 2) hε2] with i hi hxi
  calc a i ≤ x R i + τ R := hi
    _ ≤ ε / 2 + ε / 2 := add_le_add hxi hRτ.le
    _ = ε := ENNReal.add_halves ε

/-- The interpolation limit: if `S₁ → 0`, `S₂ → 0` and `a, b ≥ 0` with `a + b = 1`, then
`S₁^a S₂^b → 0`. -/
theorem tendsto_rpow_mul_rpow_zero {ι : Type*} {l : Filter ι} {S₁ S₂ : ι → ℝ≥0∞} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (h₁ : Tendsto S₁ l (𝓝 0))
    (h₂ : Tendsto S₂ l (𝓝 0)) :
    Tendsto (fun i => S₁ i ^ a * S₂ i ^ b) l (𝓝 0) := by
  have h₁' : Tendsto (fun i => S₁ i ^ a) l (𝓝 ((0 : ℝ≥0∞) ^ a)) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp h₁
  have h₂' : Tendsto (fun i => S₂ i ^ b) l (𝓝 ((0 : ℝ≥0∞) ^ b)) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp h₂
  have hfin : ∀ c : ℝ, 0 ≤ c → (0 : ℝ≥0∞) ^ c ≠ ∞ := fun c hc => by
    rcases hc.eq_or_lt with rfl | hc
    · simp
    · simp [ENNReal.zero_rpow_of_pos hc]
  have hlim := ENNReal.Tendsto.mul h₁' (Or.inr (hfin b hb)) h₂' (Or.inr (hfin a ha))
  have hzero : (0 : ℝ≥0∞) ^ a * (0 : ℝ≥0∞) ^ b = 0 := by
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      subst hab
      simp
    · simp [ENNReal.zero_rpow_of_pos ha']
  rwa [hzero] at hlim

end NonUniqueEuler.Compact.UniformAux
