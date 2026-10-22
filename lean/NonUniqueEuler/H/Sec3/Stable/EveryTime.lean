import NonUniqueEuler.H.Sec3.Stable.SpaceTime
import NonUniqueEuler.I.Sec3.RenormAllT
import NonUniqueEuler.I.Sec3.RR
import NonUniqueEuler.I.Infra.LpInterp.Tendsto

/-!
# Helpers for `prop:stable`: convergence at every time

Helper file of `P/Sec3/Stable.lean`. Manuscript: proof of `prop:stable`, last paragraph
(`03_compactness.tex:817-827`). Once `ω` is renormalized: fix `t ∈ [0,T)`.
* `L²`: `‖ωₙ(t)‖₂ = ‖gₙ‖₂ → ‖g‖₂ = ‖ω(t)‖₂` (`lem:renorm-all-t`, `Weak.renormAllT_eLpNorm_eq`),
  `ωₙ(t) ⇀ ω(t)` (`prop:compact`(i)), and `lem:RR` (`radonRiesz`).
* `L¹`: eq:tail for `ωₙ` and `ω` (`Weak.renormAllT_tail`, `Weak.renormAllT_flux_bound`), Hölder on
  `B_{2R}`, then `n → ∞` and `R → ∞`.
* `q ∈ (1,2)`: interpolation (`LpInterp.tendsto_eLpNorm_of_interp`).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.StableAux

open Weak

variable {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ} {ω : ℝ → ℂ → ℝ}

theorem enorm_sub_le_add (a b : ℝ) : ‖a - b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := by
  rw [sub_eq_add_neg]
  exact (enorm_add_le a (-b)).trans_eq (by rw [enorm_neg])

/-- A two-parameter `ℝ≥0∞` squeeze: `eₙ ≤ d_R(n) + A(R)` with `d_R → 0` for every `R > 0` and
`A(R) → 0` as `R → ∞`. -/
theorem tendsto_zero_of_le_add_two {e : ℕ → ℝ≥0∞} {d : ℝ → ℕ → ℝ≥0∞} {A : ℝ → ℝ≥0∞}
    (hle : ∀ R : ℝ, 0 < R → ∀ n, e n ≤ d R n + A R)
    (hd : ∀ R : ℝ, 0 < R → Tendsto (d R) atTop (𝓝 0)) (hA : Tendsto A atTop (𝓝 0)) :
    Tendsto e atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨R, hRA, hR⟩ := ((hA.eventually (gt_mem_nhds hε2)).and (eventually_gt_atTop 0)).exists
  filter_upwards [(hd R hR).eventually (gt_mem_nhds hε2)] with n hn
  calc e n ≤ d R n + A R := hle R hR n
    _ ≤ ε / 2 + ε / 2 := add_le_add hn.le hRA.le
    _ = ε := ENNReal.add_halves ε

/-- `ℝ≥0∞` triangle inequality for `L^p` norms of a difference, both directions. -/
theorem eLpNorm_le_sub_add {f h : ℂ → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : AEStronglyMeasurable f volume) (hh : AEStronglyMeasurable h volume) :
    eLpNorm f p volume ≤ eLpNorm (f - h) p volume + eLpNorm h p volume := by
  calc eLpNorm f p volume = eLpNorm ((f - h) + h) p volume := by rw [sub_add_cancel]
    _ ≤ _ := eLpNorm_add_le (hf.sub hh) hh hp

/-- `‖ω(t)‖_{L¹ ∩ L²} ≤ 2 max(M, 0)` for the limit, at every `t ∈ [0,T]`. -/
theorem limit_normL1LpE_le (hseq : IsCompactSeq T M gs g ωs) (hlim : IsCompactLimit T g ωs ω) :
    ∀ t ∈ Icc 0 T, normL1LpE 2 (ω t) ≤ ENNReal.ofReal (2 * max M 0) := by
  intro t ht
  have h1 := limit_eLpNorm_le hseq hlim ht (Or.inl rfl)
  have h2 := limit_eLpNorm_le hseq hlim ht (Or.inr rfl)
  have hM : ENNReal.ofReal M = ENNReal.ofReal (max M 0) := by
    rcases le_or_gt 0 M with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h.le, ENNReal.ofReal_of_nonpos h.le, ENNReal.ofReal_zero]
  calc normL1LpE 2 (ω t) ≤ ENNReal.ofReal M + ENNReal.ofReal M := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * max M 0) := by
      rw [hM, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _), two_mul]

/-- The tails of `g ∈ L¹` tend to `0`. -/
theorem tendsto_tail_zero {g : ℂ → ℝ} (hg : MemLp g 1 volume) :
    Tendsto (fun R : ℝ => ∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖g x‖ₑ) atTop (𝓝 0) := by
  set ν := volume.withDensity (fun x => ‖g x‖ₑ)
  have hmeas : ∀ R : ℝ, MeasurableSet {x : ℂ | R ≤ ‖x‖} := fun R =>
    measurableSet_le measurable_const measurable_norm
  have heq : (fun R : ℝ => ∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖g x‖ₑ) =
      ν ∘ fun R : ℝ => {x : ℂ | R ≤ ‖x‖} := by
    funext R
    simp only [Function.comp, ν, withDensity_apply _ (hmeas R)]
  rw [heq]
  have hanti : Antitone fun R : ℝ => {x : ℂ | R ≤ ‖x‖} := fun a b hab x hx =>
    le_trans hab hx
  have hfin : ∃ R : ℝ, ν {x : ℂ | R ≤ ‖x‖} ≠ ∞ := by
    refine ⟨0, ?_⟩
    simp only [ν, withDensity_apply _ (hmeas 0)]
    refine ne_top_of_le_ne_top ?_ (setLIntegral_le_lintegral _ _)
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact hg.eLpNorm_ne_top
  have h := tendsto_measure_iInter_atTop (μ := ν) (fun R => (hmeas R).nullMeasurableSet) hanti
    hfin
  have hempty : (⋂ R : ℝ, {x : ℂ | R ≤ ‖x‖}) = ∅ := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_le]
    exact ⟨‖x‖ + 1, by linarith⟩
  rwa [hempty, measure_empty] at h

/-- `ωₙ(t) → ω(t)` in `L²` (`lem:renorm-all-t`, `prop:compact`(i), `lem:RR`). -/
theorem tendsto_eLpNorm_two_time (hseq : IsCompactSeq T M gs g ωs)
    (hlim : IsCompactLimit T g ωs ω)
    (hstrong : Tendsto (fun n => normL1LpE 2 (gs n - g)) atTop (𝓝 0))
    (hren : ∀ n, IsRenormalizedWeakSolution 2 T (gs n) (ωs n))
    (hω : IsRenormalizedWeakSolution 2 T g ω) {t : ℝ} (ht : t ∈ Ico 0 T) :
    Tendsto (fun n => eLpNorm (ωs n t - ω t) 2 volume) atTop (𝓝 0) := by
  have htI : t ∈ Icc 0 T := Ico_subset_Icc_self ht
  have hw : Prelim.WeakTendstoLp 2 (fun n => ωs n t) (ω t) :=
    weakTendstoLp_two_iff.2 ⟨fun n => (hseq.weakCont n).memLp t htI, hlim.weakCont.memLp t htI,
      fun φ hφ => (hlim.weakTendstoUnif φ hφ).tendsto_at htI⟩
  have e1 : ∀ n, eLpNorm (ωs n t) 2 volume = eLpNorm (gs n) 2 volume := by
    intro n
    have := renormAllT_eLpNorm_eq (hren n) (hseq.weakCont n) t ht 2 one_le_two le_rfl
    simpa using this
  have e2 : eLpNorm (ω t) 2 volume = eLpNorm g 2 volume := by
    have := renormAllT_eLpNorm_eq hω hlim.weakCont t ht 2 one_le_two le_rfl
    simpa using this
  have hL2g : Tendsto (fun n => eLpNorm (gs n - g) 2 volume) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hstrong (fun _ => zero_le)
      (fun n => eLpNorm_le_normL1LpE 2 _)
  have hnorm : Tendsto (fun n => eLpNorm (ωs n t) 2 volume) atTop (𝓝 (eLpNorm (ω t) 2 volume)) := by
    simp_rw [e1, e2]
    refine tendsto_of_le_add_of_le_add hseq.memLp_two.eLpNorm_ne_top (fun n => ?_) (fun n => ?_)
      hL2g
    · exact eLpNorm_le_sub_add one_le_two (hseq.memLp_two_seq n).1 hseq.memLp_two.1
    · refine (eLpNorm_le_sub_add one_le_two hseq.memLp_two.1 (hseq.memLp_two_seq n).1).trans ?_
      rw [eLpNorm_sub_comm]
  exact radonRiesz hw hnorm

/-- `ωₙ(t) → ω(t)` in `L¹` (eq:tail and Hölder on `B_{2R}`). -/
theorem tendsto_eLpNorm_one_time (hseq : IsCompactSeq T M gs g ωs)
    (hlim : IsCompactLimit T g ωs ω)
    (hstrong : Tendsto (fun n => normL1LpE 2 (gs n - g)) atTop (𝓝 0))
    (hren : ∀ n, IsRenormalizedWeakSolution 2 T (gs n) (ωs n))
    (hω : IsRenormalizedWeakSolution 2 T g ω) {t : ℝ} (ht : t ∈ Ico 0 T) :
    Tendsto (fun n => eLpNorm (ωs n t - ω t) 1 volume) atTop (𝓝 0) := by
  have htI : t ∈ Icc 0 T := Ico_subset_Icc_self ht
  obtain ⟨Cv, -, hflux⟩ := renormAllT_flux_bound
  set G := Smooth.gradSup sigmaCut
  set K : ℝ≥0∞ := ENNReal.ofReal (Cv * T * M ^ 2)
  set K' : ℝ≥0∞ := ENNReal.ofReal (Cv * T * (2 * max M 0) ^ 2)
  have hFn : ∀ n, ∫⁻ p in slab T, ‖ωs n p.1 p.2 • velocityField (ωs n) p.1 p.2‖ₑ ≤ K :=
    fun n => hflux T M (gs n) (ωs n) (hseq.weakSolution n) (hseq.weakCont n) (hseq.bound n)
  have hF : ∫⁻ p in slab T, ‖ω p.1 p.2 • velocityField ω p.1 p.2‖ₑ ≤ K' :=
    hflux T _ g ω hlim.weakSolution hlim.weakCont (limit_normL1LpE_le hseq hlim)
  set τ : ℝ → ℝ≥0∞ := fun R => ∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖g x‖ₑ
  have hL1g : Tendsto (fun n => eLpNorm (gs n - g) 1 volume) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hstrong (fun _ => zero_le)
      (fun n => eLpNorm_one_le_normL1LpE 2 _)
  have hL2 := tendsto_eLpNorm_two_time hseq hlim hstrong hren hω ht
  set c : ℝ → ℝ≥0∞ := fun R => volume (ball (0 : ℂ) (2 * R)) ^ (1 / 2 : ℝ)
  set A : ℝ → ℝ≥0∞ := fun R =>
    (τ R + ENNReal.ofReal (G / R) * K) + (τ R + ENNReal.ofReal (G / R) * K')
  set d : ℝ → ℕ → ℝ≥0∞ := fun R n =>
    c R * eLpNorm (ωs n t - ω t) 2 volume + eLpNorm (gs n - g) 1 volume
  refine tendsto_zero_of_le_add_two (d := d) (A := A) (fun R hR n => ?_) (fun R hR => ?_) ?_
  · -- the main estimate
    have hmn : AEStronglyMeasurable (ωs n t) volume := ((hseq.weakCont n).memLp t htI).1
    have hm : AEStronglyMeasurable (ω t) volume := (hlim.weakCont.memLp t htI).1
    have hcompl : (ball (0 : ℂ) (2 * R))ᶜ = {x : ℂ | 2 * R ≤ ‖x‖} := by
      ext x; simp [mem_ball, not_lt]
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← lintegral_add_compl (fun x => ‖(ωs n t - ω t) x‖ₑ)
        (measurableSet_ball : MeasurableSet (ball (0 : ℂ) (2 * R))), hcompl]
    -- inner part
    have hin : ∫⁻ x in ball (0 : ℂ) (2 * R), ‖(ωs n t - ω t) x‖ₑ ≤
        c R * eLpNorm (ωs n t - ω t) 2 volume := by
      have h := eLpNorm_one_le_two_mul (μ := volume.restrict (ball (0 : ℂ) (2 * R)))
        (hmn.sub hm).restrict
      rw [eLpNorm_one_eq_lintegral_enorm, Measure.restrict_apply_univ] at h
      refine h.trans ?_
      rw [mul_comm]
      gcongr
      exact Measure.restrict_le_self
    -- outer part
    have hout1 : ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖ωs n t x‖ₑ ≤
        eLpNorm (gs n - g) 1 volume + τ R + ENNReal.ofReal (G / R) * K := by
      refine (renormAllT_tail (hren n) (hseq.weakCont n) R hR t ht).trans ?_
      refine add_le_add ?_ (by gcongr; exact hFn n)
      have hpt : ∀ x, ‖gs n x‖ₑ ≤ ‖(gs n - g) x‖ₑ + ‖g x‖ₑ := fun x => by
        have e : gs n x = (gs n - g) x + g x := by simp
        rw [e]; exact enorm_add_le _ _
      refine (lintegral_mono hpt).trans ?_
      rw [lintegral_add_left' (((hseq.memLp_one_seq n).1.sub hseq.memLp_one.1).enorm.restrict)]
      refine add_le_add ?_ le_rfl
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact setLIntegral_le_lintegral _ _
    have hout2 : ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖ω t x‖ₑ ≤ τ R + ENNReal.ofReal (G / R) * K' :=
      (renormAllT_tail hω hlim.weakCont R hR t ht).trans
        (add_le_add le_rfl (by gcongr))
    have hout : ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖(ωs n t - ω t) x‖ₑ ≤
        (eLpNorm (gs n - g) 1 volume + τ R + ENNReal.ofReal (G / R) * K) +
          (τ R + ENNReal.ofReal (G / R) * K') := by
      refine (lintegral_mono fun x => enorm_sub_le_add (ωs n t x) (ω t x)).trans ?_
      rw [lintegral_add_left' hmn.enorm.restrict]
      exact add_le_add hout1 hout2
    calc (∫⁻ x in ball (0 : ℂ) (2 * R), ‖(ωs n t - ω t) x‖ₑ) +
          ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖(ωs n t - ω t) x‖ₑ
        ≤ c R * eLpNorm (ωs n t - ω t) 2 volume +
          ((eLpNorm (gs n - g) 1 volume + τ R + ENNReal.ofReal (G / R) * K) +
            (τ R + ENNReal.ofReal (G / R) * K')) := add_le_add hin hout
      _ = d R n + A R := by simp only [d, A]; ring
  · -- `d_R → 0`
    have hc : c R ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne
    have h := (ENNReal.Tendsto.const_mul hL2 (Or.inr hc)).add hL1g
    simpa [d] using h
  · -- `A → 0`
    have hG : Tendsto (fun R : ℝ => ENNReal.ofReal (G / R)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := G)).div_atTop tendsto_id)
      simpa using this
    have hK : K ≠ ∞ := ENNReal.ofReal_ne_top
    have hK' : K' ≠ ∞ := ENNReal.ofReal_ne_top
    have hτ := tendsto_tail_zero hseq.memLp_one
    have h1 := hτ.add (ENNReal.Tendsto.mul_const hG (Or.inr hK))
    have h2 := hτ.add (ENNReal.Tendsto.mul_const hG (Or.inr hK'))
    simpa [A] using h1.add h2

/-- **Convergence at every time** (`03_compactness.tex:817-827`). -/
theorem stable_tendsto_time (hseq : IsCompactSeq T M gs g ωs) (hlim : IsCompactLimit T g ωs ω)
    (hstrong : Tendsto (fun n => normL1LpE 2 (gs n - g)) atTop (𝓝 0))
    (hren : ∀ n, IsRenormalizedWeakSolution 2 T (gs n) (ωs n))
    (hω : IsRenormalizedWeakSolution 2 T g ω) :
    ∀ t ∈ Ico 0 T, ∀ q : ℝ, 1 ≤ q → q ≤ 2 →
      Tendsto (fun n => eLpNorm (ωs n t - ω t) (ENNReal.ofReal q) volume) atTop (𝓝 0) := by
  intro t ht q hq1 hq2
  have htI : t ∈ Icc 0 T := Ico_subset_Icc_self ht
  have hL2 := tendsto_eLpNorm_two_time hseq hlim hstrong hren hω ht
  rcases hq2.lt_or_eq with hq2 | rfl
  · have hL1 := tendsto_eLpNorm_one_time hseq hlim hstrong hren hω ht
    refine LpInterp.tendsto_eLpNorm_of_interp (p := 1) (r := 2) (C := 1)
      (fun n => ((hseq.weakCont n).memLp t htI).1.sub (hlim.weakCont.memLp t htI).1)
      one_pos (ENNReal.one_le_ofReal.2 hq1) ?_ ENNReal.one_ne_top
      ((hL2.eventually (gt_mem_nhds one_pos)).mono fun n hn => hn.le) hL1
    rw [← ENNReal.ofReal_ofNat 2]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hq2
  · simpa using hL2

end NonUniqueEuler.Compact.StableAux
