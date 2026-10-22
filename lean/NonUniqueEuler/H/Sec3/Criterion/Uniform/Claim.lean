import NonUniqueEuler.Defs.Sec3.Criterion
import NonUniqueEuler.I.Sec3.BoundedAdm
import NonUniqueEuler.I.Sec3.RR
import NonUniqueEuler.H.Sec3.Criterion.Uniform.Abstract

/-!
# Helper for `P/Sec3/Criterion/Uniform`: the claim of `thm:criterion`(iv)

Manuscript: proof of `thm:criterion`(iv), the claim and its proof, `03_compactness.tex:1023-1056`:
if `nᵢ → ∞` and `tᵢ ∈ [0, T']`, `tᵢ → t₀`, then `ω^{(nᵢ)}(tᵢ) → ω_∞(t₀)` in `L²` and in `L¹`.

* `tendsto_eLpNorm_sub_one`, `tendsto_eLpNorm_two`: `‖f⁽ⁿ⁾ - f‖₁ → 0` and
  `‖f⁽ⁿ⁾‖₂ → ‖f‖₂` for a `2`-admissible sequence.
* `claim_two` (`03_compactness.tex:1038-1046`): weak convergence in `L²` from the uniform weak
  convergence and the weak continuity of `ω_∞`, norm convergence from `lem:bounded-adm`(ii) and
  the conservation `‖ω_∞(t)‖₂ = ‖f‖₂`, then `lem:RR` (`radonRiesz_filter`).
* `eLpNorm_one_le_ball_add_tail`: `‖g - h‖₁ ≤ |B_{2R}|^{1/2} ‖g - h‖₂ + ∫_{|x|≥2R}|g| + ∫_{|x|≥2R}|h|`
  (Hölder on `B_{2R}`, `03_compactness.tex:1054-1055`).
* `claim_one` (`03_compactness.tex:1046-1056`): the `L¹` convergence, from the `L²` convergence
  and a uniform tail bound of the form eq:tail (an abstract hypothesis here; the P file derives
  it from `renormAllT_tail` and `renormAllT_flux_bound`).
* `tendsto_eLpNorm_sub_sub`: the triangle inequality step `03_compactness.tex:1031-1033`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.UniformAux

open Weak

variable {T₀ : ℝ≥0∞} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ} {ωinf : ℝ → ℂ → ℝ}

/-- `‖f⁽ⁿ⁾ - f‖₁ → 0` for a `2`-admissible sequence. -/
theorem tendsto_eLpNorm_sub_one (hadm : IsAdmissibleSeq 2 T₀ f fs ωs) :
    Tendsto (fun n => eLpNorm (fs n - f) 1 volume) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hadm.tendsto
    (fun _ => zero_le) fun _ => eLpNorm_one_le_normL1LpE _ _

/-- `‖f⁽ⁿ⁾ - f‖₂ → 0` for a `2`-admissible sequence. -/
theorem tendsto_eLpNorm_sub_two (hadm : IsAdmissibleSeq 2 T₀ f fs ωs) :
    Tendsto (fun n => eLpNorm (fs n - f) 2 volume) atTop (𝓝 0) := by
  have h := hadm.tendsto
  rw [ENNReal.ofReal_ofNat] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun _ => zero_le) fun _ => eLpNorm_le_normL1LpE _ _

/-- `‖f⁽ⁿ⁾‖₂ → ‖f‖₂` for a `2`-admissible sequence. -/
theorem tendsto_eLpNorm_two (hadm : IsAdmissibleSeq 2 T₀ f fs ωs) :
    Tendsto (fun n => eLpNorm (fs n) 2 volume) atTop (𝓝 (eLpNorm f 2 volume)) := by
  have hf : MemLp f 2 volume := by simpa using hadm.memLp_q
  have hfs : ∀ n, MemLp (fs n) 2 volume := fun n => by simpa using hadm.memLp_q_seq n
  have he := tendsto_eLpNorm_sub_two hadm
  have hF : eLpNorm f 2 volume ≠ ∞ := hf.eLpNorm_ne_top
  have hup : Tendsto (fun n => eLpNorm (fs n - f) 2 volume + eLpNorm f 2 volume) atTop
      (𝓝 (eLpNorm f 2 volume)) := by
    simpa using he.add (tendsto_const_nhds (x := eLpNorm f 2 volume))
  have hlow : Tendsto (fun n => eLpNorm f 2 volume - eLpNorm (fs n - f) 2 volume) atTop
      (𝓝 (eLpNorm f 2 volume)) := by
    simpa using ENNReal.Tendsto.sub (tendsto_const_nhds (x := eLpNorm f 2 volume)) he
      (Or.inl hF)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun n => ?_) fun n => ?_
  · rw [tsub_le_iff_right]
    calc eLpNorm f 2 volume = eLpNorm (fs n - (fs n - f)) 2 volume := by rw [sub_sub_cancel]
      _ ≤ eLpNorm (fs n) 2 volume + eLpNorm (fs n - f) 2 volume :=
        eLpNorm_sub_le (hfs n).1 ((hfs n).1.sub hf.1) one_le_two
  · calc eLpNorm (fs n) 2 volume = eLpNorm ((fs n - f) + f) 2 volume := by rw [sub_add_cancel]
      _ ≤ eLpNorm (fs n - f) 2 volume + eLpNorm f 2 volume :=
        eLpNorm_add_le ((hfs n).1.sub hf.1) hf.1 one_le_two

/-- Composition of a uniform convergence on `K` with `nᵢ → ∞`, `tᵢ ∈ K`. -/
theorem tendsto_sub_of_tendstoUniformlyOn {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {K : Set ℝ}
    (hFG : TendstoUniformlyOn F G atTop K) {n : ℕ → ℕ} {t : ℕ → ℝ}
    (hn : Tendsto n atTop atTop) (ht : ∀ i, t i ∈ K) :
    Tendsto (fun i => F (n i) (t i) - G (t i)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hn.eventually (Metric.tendstoUniformlyOn_iff.1 hFG ε hε)] with i hi
  have := hi (t i) (ht i)
  rwa [Real.dist_eq, sub_zero, ← Real.dist_eq, dist_comm]

/-- **The claim, `L²` part** (`03_compactness.tex:1038-1046`): if `nᵢ → ∞` and `tᵢ ∈ K`,
`tᵢ → t₀ ∈ K` (with `K ⊆ [0, T₀)` and uniform weak convergence on `K`), then
`ω^{(nᵢ)}(tᵢ) → ω_∞(t₀)` in `L²`. -/
theorem claim_two (hadm : IsAdmissibleSeq 2 T₀ f fs ωs)
    (hcont : ∀ n, IsWeakContL2On (timeInterval T₀) (ωs n))
    (hwc : IsWeakContL2On (timeInterval T₀) ωinf)
    (hnorm2 : ∀ t ∈ timeInterval T₀, eLpNorm (ωinf t) 2 volume = eLpNorm f 2 volume)
    {K : Set ℝ} (hK : K ⊆ timeInterval T₀) (hunif : WeakTendstoUnifL2On ωs ωinf K)
    {n : ℕ → ℕ} {t : ℕ → ℝ} {t₀ : ℝ} (hn : Tendsto n atTop atTop) (ht : ∀ i, t i ∈ K)
    (ht₀ : t₀ ∈ K) (hlim : Tendsto t atTop (𝓝 t₀)) :
    Tendsto (fun i => eLpNorm (ωs (n i) (t i) - ωinf t₀) 2 volume) atTop (𝓝 0) := by
  have htw : Tendsto t atTop (𝓝[timeInterval T₀] t₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun i => hK (ht i)⟩
  refine radonRiesz_filter (gs := fun i => ωs (n i) (t i)) (g := ωinf t₀)
    (fun i => (hcont (n i)).memLp (t i) (hK (ht i))) (hwc.memLp t₀ (hK ht₀)) ?_ ?_
  · intro ψ hψ
    have hA := tendsto_sub_of_tendstoUniformlyOn (hunif ψ hψ) hn ht
    have hB : Tendsto (fun i => ∫ x, ωinf (t i) x * ψ x) atTop (𝓝 (∫ x, ωinf t₀ x * ψ x)) :=
      ((hwc.continuousOn ψ hψ) t₀ (hK ht₀)).tendsto.comp htw
    have hsum := hA.add hB
    rw [zero_add] at hsum
    refine hsum.congr fun i => ?_
    ring
  · have hnorms : ∀ i, eLpNorm (ωs (n i) (t i)) 2 volume = eLpNorm (fs (n i)) 2 volume := by
      intro i
      have := boundedAdm_eLpNorm_eq hadm hcont (n i) (t i) (hK (ht i)) 2 one_le_two le_rfl
      simpa using this
    simp only [hnorms, hnorm2 t₀ (hK ht₀)]
    exact (tendsto_eLpNorm_two hadm).comp hn

/-- `‖g - h‖₁ ≤ ‖g - h‖₂ |B_{2R}|^{1/2} + ∫_{|x|≥2R}|g| + ∫_{|x|≥2R}|h|` (Hölder on the ball
`B_{2R}`, the triangle inequality outside it). -/
theorem eLpNorm_one_le_ball_add_tail {g h : ℂ → ℝ} (hg : AEStronglyMeasurable g volume)
    (hh : AEStronglyMeasurable h volume) (R : ℝ) :
    eLpNorm (g - h) 1 volume ≤
      eLpNorm (g - h) 2 volume * volume (ball (0 : ℂ) (2 * R)) ^ (1 / 2 : ℝ) +
        ((∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖g x‖ₑ) + ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖h x‖ₑ) := by
  set B : Set ℂ := ball (0 : ℂ) (2 * R) with hBdef
  have hB : MeasurableSet B := measurableSet_ball
  have hBc : Bᶜ = {x : ℂ | 2 * R ≤ ‖x‖} := by
    ext x
    simp [hBdef]
  have hsplit : eLpNorm (g - h) 1 volume =
      eLpNorm (g - h) 1 (volume.restrict B) + eLpNorm (g - h) 1 (volume.restrict Bᶜ) := by
    rw [← eLpNorm_one_add_measure, Measure.restrict_add_restrict_compl hB]
  have hball : eLpNorm (g - h) 1 (volume.restrict B) ≤
      eLpNorm (g - h) 2 volume * volume B ^ (1 / 2 : ℝ) := by
    have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) one_le_two
      (hg.sub hh).restrict (μ := volume.restrict B)
    rw [Measure.restrict_apply_univ] at h1
    have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by
      simp only [ENNReal.toReal_one, ENNReal.toReal_ofNat]
      norm_num
    rw [hexp] at h1
    refine h1.trans (mul_le_mul_left ?_ _)
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hout : eLpNorm (g - h) 1 (volume.restrict Bᶜ) ≤
      (∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖g x‖ₑ) + ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖h x‖ₑ := by
    refine (eLpNorm_sub_le hg.restrict hh.restrict le_rfl).trans (le_of_eq ?_)
    rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm, hBc]
  rw [hsplit]
  exact add_le_add hball hout

/-- `∫_S |f⁽ⁿ⁾| ≤ ‖f⁽ⁿ⁾ - f‖₁ + ∫_S |f|`. -/
theorem setLIntegral_le_eLpNorm_sub_add {g h : ℂ → ℝ} (hg : AEStronglyMeasurable g volume)
    (hh : AEStronglyMeasurable h volume) (S : Set ℂ) :
    ∫⁻ x in S, ‖g x‖ₑ ≤ eLpNorm (g - h) 1 volume + ∫⁻ x in S, ‖h x‖ₑ := by
  rw [← eLpNorm_one_eq_lintegral_enorm, ← eLpNorm_one_eq_lintegral_enorm]
  calc eLpNorm g 1 (volume.restrict S) = eLpNorm ((g - h) + h) 1 (volume.restrict S) := by
        rw [sub_add_cancel]
    _ ≤ eLpNorm (g - h) 1 (volume.restrict S) + eLpNorm h 1 (volume.restrict S) :=
        eLpNorm_add_le (hg.sub hh).restrict hh.restrict le_rfl
    _ ≤ eLpNorm (g - h) 1 volume + eLpNorm h 1 (volume.restrict S) :=
        add_le_add (eLpNorm_mono_measure _ Measure.restrict_le_self) le_rfl

/-- `ofReal (G / R) * c → 0` as `R → ∞`. -/
theorem tendsto_ofReal_div_mul (G : ℝ) (c : ℝ≥0∞) (hc : c ≠ ∞) :
    Tendsto (fun R : ℝ => ENNReal.ofReal (G / R) * c) atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ => G / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h2 := ENNReal.Tendsto.mul_const (b := c) (ENNReal.tendsto_ofReal h1) (Or.inr hc)
  simpa using h2

/-- **The claim, `L¹` part** (`03_compactness.tex:1046-1056`): if `nᵢ → ∞`, `tᵢ ∈ K`,
`ω^{(nᵢ)}(tᵢ) → ω_∞(t₀)` in `L²`, and the tails of `ω⁽ⁿ⁾(s)`, `s ∈ K`, obey a bound of the
form eq:tail, `∫_{|x|≥2R}|ω⁽ⁿ⁾(s)| ≤ ∫_{|x|≥R}|f⁽ⁿ⁾| + (G/R) C`, then
`ω^{(nᵢ)}(tᵢ) → ω_∞(t₀)` in `L¹`. -/
theorem claim_one (hadm : IsAdmissibleSeq 2 T₀ f fs ωs) {K : Set ℝ}
    (hmeas : ∀ m, ∀ s ∈ K, AEStronglyMeasurable (ωs m s) volume) {g : ℂ → ℝ}
    (hg : AEStronglyMeasurable g volume) (hg1 : eLpNorm g 1 volume ≠ ∞) {G C : ℝ}
    (htail : ∀ R : ℝ, 0 < R → ∀ m, ∀ s ∈ K,
      ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖ωs m s x‖ₑ ≤
        (∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖fs m x‖ₑ) + ENNReal.ofReal (G / R) * ENNReal.ofReal C)
    {n : ℕ → ℕ} {t : ℕ → ℝ} (hn : Tendsto n atTop atTop) (ht : ∀ i, t i ∈ K)
    (hL2 : Tendsto (fun i => eLpNorm (ωs (n i) (t i) - g) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun i => eLpNorm (ωs (n i) (t i) - g) 1 volume) atTop (𝓝 0) := by
  have hf1 : ∫⁻ x, ‖f x‖ₑ ≠ ∞ := by
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact hadm.memLp_one.eLpNorm_ne_top
  have hg1' : ∫⁻ x, ‖g x‖ₑ ≠ ∞ := by
    rwa [← eLpNorm_one_eq_lintegral_enorm]
  set τ : ℝ → ℝ≥0∞ := fun R => (∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖f x‖ₑ) +
    ENNReal.ofReal (G / R) * ENNReal.ofReal C + ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖g x‖ₑ with hτdef
  set x : ℝ → ℕ → ℝ≥0∞ := fun R i =>
    eLpNorm (ωs (n i) (t i) - g) 2 volume * volume (ball (0 : ℂ) (2 * R)) ^ (1 / 2 : ℝ) +
      eLpNorm (fs (n i) - f) 1 volume with hxdef
  have hτ : Tendsto τ atTop (𝓝 0) := by
    have h1 := tendsto_lintegral_tail hf1
    have h2 := tendsto_ofReal_div_mul G (ENNReal.ofReal C) ENNReal.ofReal_ne_top
    have h3 := (tendsto_lintegral_tail hg1').comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    have := (h1.add h2).add h3
    rw [add_zero, add_zero] at this
    exact this.congr fun R => rfl
  have hx : ∀ R, 0 < R → Tendsto (x R) atTop (𝓝 0) := by
    intro R _
    have hball : volume (ball (0 : ℂ) (2 * R)) ^ (1 / 2 : ℝ) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne
    have h1 := ENNReal.Tendsto.mul_const hL2 (Or.inr hball)
    have h2 := (tendsto_eLpNorm_sub_one hadm).comp hn
    have := h1.add h2
    rw [zero_mul, add_zero] at this
    exact this.congr fun i => rfl
  refine tendsto_zero_of_le_add hτ hx fun R hR => Eventually.of_forall fun i => ?_
  have hmi := hmeas (n i) (t i) (ht i)
  have hfsm : AEStronglyMeasurable (fs (n i)) volume := (hadm.memLp_one_seq (n i)).1
  have hfm : AEStronglyMeasurable f volume := hadm.memLp_one.1
  have hA := eLpNorm_one_le_ball_add_tail hmi hg R
  have hB := htail R hR (n i) (t i) (ht i)
  have hC := setLIntegral_le_eLpNorm_sub_add hfsm hfm {x : ℂ | R ≤ ‖x‖}
  calc eLpNorm (ωs (n i) (t i) - g) 1 volume
      ≤ eLpNorm (ωs (n i) (t i) - g) 2 volume * volume (ball (0 : ℂ) (2 * R)) ^ (1 / 2 : ℝ) +
        ((∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖ωs (n i) (t i) x‖ₑ) +
          ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖g x‖ₑ) := hA
    _ ≤ eLpNorm (ωs (n i) (t i) - g) 2 volume * volume (ball (0 : ℂ) (2 * R)) ^ (1 / 2 : ℝ) +
        ((eLpNorm (fs (n i) - f) 1 volume + ∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖f x‖ₑ) +
          ENNReal.ofReal (G / R) * ENNReal.ofReal C +
          ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖g x‖ₑ) := by
        gcongr
        exact hB.trans (add_le_add hC le_rfl)
    _ = x R i + τ R := by
        simp only [hxdef, hτdef]
        ring

/-- The triangle inequality step (`03_compactness.tex:1031-1033`): if `aᵢ → c` and `bᵢ → c`
in `L^p`, `p ≥ 1`, then `‖aᵢ - bᵢ‖_p → 0`. -/
theorem tendsto_eLpNorm_sub_sub {p : ℝ≥0∞} (hp : 1 ≤ p) {a b : ℕ → ℂ → ℝ} {c : ℂ → ℝ}
    (ha : ∀ i, AEStronglyMeasurable (a i) volume) (hb : ∀ i, AEStronglyMeasurable (b i) volume)
    (hc : AEStronglyMeasurable c volume)
    (h1 : Tendsto (fun i => eLpNorm (a i - c) p volume) atTop (𝓝 0))
    (h2 : Tendsto (fun i => eLpNorm (b i - c) p volume) atTop (𝓝 0)) :
    Tendsto (fun i => eLpNorm (a i - b i) p volume) atTop (𝓝 0) := by
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) fun i => ?_
  calc eLpNorm (a i - b i) p volume = eLpNorm ((a i - c) - (b i - c)) p volume := by
        rw [sub_sub_sub_cancel_right]
    _ ≤ eLpNorm (a i - c) p volume + eLpNorm (b i - c) p volume :=
        eLpNorm_sub_le ((ha i).sub hc) ((hb i).sub hc) hp

end NonUniqueEuler.Compact.UniformAux
