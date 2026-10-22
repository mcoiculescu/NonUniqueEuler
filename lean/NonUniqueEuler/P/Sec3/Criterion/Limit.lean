import NonUniqueEuler.Defs.Sec3.Criterion
import NonUniqueEuler.Defs.Sec3.Compact
import NonUniqueEuler.I.Sec3.BoundedAdm
import NonUniqueEuler.I.Sec3.Compact
import NonUniqueEuler.I.Sec3.Stable
import NonUniqueEuler.I.Sec3.WeakContRep
import NonUniqueEuler.I.Infra.WeakL2.Compact
import NonUniqueEuler.I.Infra.JointRep.Representative
import NonUniqueEuler.I.Infra.JointRep.Slab
import NonUniqueEuler.H.Sec3.Criterion.Limit.Restrict

/-!
# Proof: `thm:criterion`, step 1 — construction of the limit `ω_∞` on `[0, T₀)`

Proof of `I/Sec3/Criterion/Limit.lean` (`Compact.criterion_limit`). Manuscript: proof of
`thm:criterion`, first paragraph, `03_compactness.tex:974-994`.

Structure.
1. `exists_times`: real times `T_j ∈ (0, T₀)`, cofinal in `[0, T₀)` (an enumeration of the
   positive rationals below `T₀`; no monotonicity is needed).
2. `isCompactSeq_of_admissible`: with `M = sup_n ‖f⁽ⁿ⁾‖_{L¹∩L²}` (`lem:bounded-adm`(ii)), the
   hypotheses of `prop:compact` hold on every `[0, T]`, `T < T₀`.
3. For each `j`, `prop:compact` + `prop:stable` along any subsequence give a further subsequence
   converging (uniformly weakly in `L²` on `[0, T_j]`) to a renormalized weak solution
   `ω^{[j]}` in `X₂(T_j)`, weakly continuous on `[0, T_j]`; diagonal extraction
   (`WeakL2.exists_diagonal_subseq`) gives one subsequence `φ` for all `j`.
4. Weak `L²` limits are unique, so `ω^{[i]}(t) = ω^{[k]}(t)` for `t ≤ T_i, T_k`; the glued
   function `t ↦ ω^{[j(t)]}(t)` is weakly continuous on `[0, T₀)` (`isWeakContL2On_of_local`),
   and `ω_∞` is a jointly measurable representative of it, correct at every `t ∈ [0, T₀)`
   (I-JOINT).
5. For `T < T₀` pick `T_k > T`: the restriction of `ω^{[k]}` to `[0, T]` is a renormalized weak
   solution (`isRenormalizedWeakSolution_mono`), and `ω_∞ = ω^{[k]}` a.e. on `(0, T) × ℝ²`
   (`JointRep.ae_eq_slab_of_ae_ae`), so `ω_∞` is one (`IsRenormalizedWeakSolution.congr_ae`).

Deviation (inessential): the manuscript first passes to the subsequence realizing the `limsup`
of eq:defect; this is done by the consumer (`P/Sec3/Criterion`), see the docstring of the
interface file.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.CriterionLimitAux

open Weak

/-- For `ofReal t < T₀` there is a positive rational `q > t` with `ofReal q < T₀`. -/
theorem exists_rat_gt_of_lt {T₀ : ℝ≥0∞} {t : ℝ} (ht : ENNReal.ofReal t < T₀) :
    ∃ q : ℚ, (0 : ℝ) < q ∧ ENNReal.ofReal q < T₀ ∧ t < q := by
  obtain ⟨r, -, htr, hrT⟩ := ENNReal.lt_iff_exists_real_btwn.1 ht
  have hr := ENNReal.ofReal_lt_ofReal_iff'.1 htr
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hr.1 hr.2)
  refine ⟨q, (le_max_right _ _).trans_lt hq1, ?_, (le_max_left _ _).trans_lt hq1⟩
  exact ((ENNReal.ofReal_lt_ofReal_iff hr.2).2 hq2).trans hrT

/-- Countably many times `T_j ∈ (0, T₀)`, cofinal in `[0, T₀)`. -/
theorem exists_times {T₀ : ℝ≥0∞} (hT₀ : 0 < T₀) :
    ∃ T : ℕ → ℝ, (∀ j, 0 < T j) ∧ (∀ j, ENNReal.ofReal (T j) < T₀) ∧
      ∀ t : ℝ, ENNReal.ofReal t < T₀ → ∃ j, t < T j := by
  set S : Set ℚ := {q | (0 : ℝ) < q ∧ ENNReal.ofReal q < T₀} with hS
  have hne : S.Nonempty := by
    obtain ⟨q, h1, h2, -⟩ := exists_rat_gt_of_lt (t := 0) (by simpa using hT₀)
    exact ⟨q, h1, h2⟩
  obtain ⟨e, he⟩ := S.to_countable.exists_eq_range hne
  have hmem : ∀ j, e j ∈ S := fun j => by rw [he]; exact mem_range_self j
  refine ⟨fun j => (e j : ℝ), fun j => (hmem j).1, fun j => (hmem j).2, fun t ht => ?_⟩
  obtain ⟨q, h1, h2, h3⟩ := exists_rat_gt_of_lt ht
  have hq : q ∈ range e := by rw [← he]; exact ⟨h1, h2⟩
  obtain ⟨j, rfl⟩ := hq
  exact ⟨j, h3⟩

/-- `[0, T₀)` is measurable. -/
theorem measurableSet_timeInterval (T₀ : ℝ≥0∞) : MeasurableSet (timeInterval T₀) :=
  (measurableSet_le measurable_const measurable_id).inter
    (measurableSet_lt ENNReal.measurable_ofReal measurable_const)

/-- Pairings against `ψ` only depend on the a.e. class. -/
theorem integral_mul_congr {g h : ℂ → ℝ} (e : g =ᵐ[volume] h) (ψ : ℂ → ℝ) :
    ∫ x, g x * ψ x = ∫ x, h x * ψ x :=
  integral_congr_ae (by filter_upwards [e] with x hx; rw [hx])

/-- Two `L²` functions with the same integrals against every `L²` function agree a.e. -/
theorem ae_eq_of_forall_integral_mul_eq {g h : ℂ → ℝ} (hg : MemLp g 2 volume)
    (hh : MemLp h 2 volume)
    (H : ∀ ψ : ℂ → ℝ, MemLp ψ 2 volume → ∫ x, g x * ψ x = ∫ x, h x * ψ x) :
    g =ᵐ[volume] h := by
  have hd : MemLp (g - h) 2 volume := hg.sub hh
  have i1 : Integrable (g * (g - h)) volume := hg.integrable_mul hd
  have i2 : Integrable (h * (g - h)) volume := hh.integrable_mul hd
  have i3 : Integrable ((g - h) * (g - h)) volume := hd.integrable_mul hd
  have h0 : ∫ x, ((g - h) * (g - h)) x = 0 := by
    have e : (g - h) * (g - h) = g * (g - h) - h * (g - h) := by ring
    rw [e, Pi.sub_def, integral_sub i1 i2]
    exact sub_eq_zero.2 (H (g - h) hd)
  have hnn : 0 ≤ (g - h) * (g - h) := fun x => mul_self_nonneg _
  have hz := (integral_eq_zero_iff_of_nonneg hnn i3).1 h0
  filter_upwards [hz] with x hx
  have : (g x - h x) * (g x - h x) = 0 := by simpa using hx
  exact sub_eq_zero.1 (mul_self_eq_zero.1 this)

/-- Strong convergence in `L²` implies weak convergence in `L²`. -/
theorem weakTendstoLp_two_of_tendsto {fs : ℕ → ℂ → ℝ} {f : ℂ → ℝ}
    (hfs : ∀ n, MemLp (fs n) 2 volume) (hf : MemLp f 2 volume)
    (h : Tendsto (fun n => eLpNorm (fs n - f) 2 volume) atTop (𝓝 0)) :
    Prelim.WeakTendstoLp 2 fs f := by
  rw [weakTendstoLp_two_iff]
  refine ⟨hfs, hf, fun ψ hψ => ?_⟩
  have hL : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hf.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hfs f hf).2 h
  exact (WeakL2.weakTendsto_toLp_iff hfs hf).1 (fun y => hL.inner tendsto_const_nhds) ψ hψ

/-- Weak continuity only depends on the a.e. classes of the slices. -/
theorem isWeakContL2On_congr {s : Set ℝ} {ω ω' : ℝ → ℂ → ℝ} (h : IsWeakContL2On s ω)
    (h' : ∀ t ∈ s, ω' t =ᵐ[volume] ω t) : IsWeakContL2On s ω' :=
  ⟨fun t ht => (h.memLp t ht).ae_eq (h' t ht).symm,
    fun ψ hψ => (h.continuousOn ψ hψ).congr fun t ht => integral_mul_congr (h' t ht) ψ⟩

/-- Weak continuity on `[0, T₀)` is local: it follows from agreement with paths weakly continuous
on `[0, T_j]`, for cofinal times `T_j`. -/
theorem isWeakContL2On_of_local {T₀ : ℝ≥0∞} {ω : ℝ → ℂ → ℝ} {Tj : ℕ → ℝ}
    {ωj : ℕ → ℝ → ℂ → ℝ} (hcof : ∀ t : ℝ, ENNReal.ofReal t < T₀ → ∃ j, t < Tj j)
    (hc : ∀ j, IsWeakContL2On (Icc 0 (Tj j)) (ωj j))
    (heq : ∀ j, ∀ t ∈ Icc 0 (Tj j), ω t =ᵐ[volume] ωj j t) :
    IsWeakContL2On (timeInterval T₀) ω := by
  refine ⟨fun t ht => ?_, fun ψ hψ t₀ ht₀ => ?_⟩
  · obtain ⟨k, hk⟩ := hcof t ht.2
    exact ((hc k).memLp t ⟨ht.1, hk.le⟩).ae_eq (heq k t ⟨ht.1, hk.le⟩).symm
  · obtain ⟨k, hk⟩ := hcof t₀ ht₀.2
    have h1 : ContinuousWithinAt (fun t => ∫ x, ωj k t x * ψ x)
        (timeInterval T₀ ∩ Iio (Tj k)) t₀ :=
      ((hc k).continuousOn ψ hψ t₀ ⟨ht₀.1, hk.le⟩).mono fun s hs => ⟨hs.1.1, hs.2.le⟩
    have h2 : ContinuousWithinAt (fun t => ∫ x, ω t x * ψ x)
        (timeInterval T₀ ∩ Iio (Tj k)) t₀ :=
      h1.congr (fun s hs => integral_mul_congr (heq k s ⟨hs.1.1, hs.2.le⟩) ψ)
        (integral_mul_congr (heq k t₀ ⟨ht₀.1, hk.le⟩) ψ)
    exact (continuousWithinAt_inter (Iio_mem_nhds hk)).1 h2

/-- Step 1 of the proof: with `M = sup_n ‖f⁽ⁿ⁾‖_{L¹∩L²}` (`lem:bounded-adm`(ii)), the hypotheses of
`prop:compact` hold on every `[0, T]`, `0 < T < T₀`, with `gₙ = f⁽ⁿ⁾`, `g = f`. -/
theorem isCompactSeq_of_admissible {T₀ : ℝ≥0∞} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ}
    {ωs : ℕ → ℝ → ℂ → ℝ} (hadm : IsAdmissibleSeq 2 T₀ f fs ωs)
    (hcont : ∀ n, IsWeakContL2On (timeInterval T₀) (ωs n)) :
    ∃ M : ℝ, ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ → IsCompactSeq T M fs f ωs := by
  obtain ⟨hsup, hfin⟩ := boundedAdm_iSup_eq hadm hcont
  refine ⟨(⨆ n, normL1LpE 2 (fs n)).toReal, fun T hT hTT₀ => ?_⟩
  have hstrong : Tendsto (fun n => normL1LpE 2 (fs n - f)) atTop (𝓝 0) := by
    simpa using hadm.tendsto
  have hf2 : MemLp f 2 volume := by simpa using hadm.memLp_q
  have hfs2 : ∀ n, MemLp (fs n) 2 volume := fun n => by simpa using hadm.memLp_q_seq n
  have hweak : Prelim.WeakTendstoLp 2 fs f :=
    weakTendstoLp_two_of_tendsto hfs2 hf2
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hstrong
        (fun _ => zero_le) (fun n => eLpNorm_le_normL1LpE 2 _))
  refine
    { T_pos := hT
      memLp_one := hadm.memLp_one
      memLp_two := hf2
      memLp_one_seq := hadm.memLp_one_seq
      memLp_two_seq := hfs2
      weakTendsto := hweak
      weakSolution := fun n => (hadm.renormalized n T hT hTT₀).toIsWeakSolution
      weakCont := fun n => (hcont n).mono (Icc_subset_timeInterval hTT₀)
      bound := fun n t ht => ?_ }
  rw [ENNReal.ofReal_toReal hfin.ne, ← hsup]
  exact (le_iSup₂ (f := fun t (_ : t ∈ timeInterval T₀) => normL1LpE 2 (ωs n t)) t
    (Icc_subset_timeInterval hTT₀ ht)).trans
      (le_iSup (fun n => ⨆ t ∈ timeInterval T₀, normL1LpE 2 (ωs n t)) n)

end NonUniqueEuler.Compact.CriterionLimitAux

namespace NonUniqueEuler.Compact

open Weak CriterionLimitAux

/-- Step 1 of the proof of **`thm:criterion`** (`03_compactness.tex:974-994`): a `2`-admissible
sequence for `f` on `[0, T₀)` (weakly continuous representatives) has a subsequence `φ` and a
limit `ω_∞` that is a renormalized weak solution on `[0, T₀)` with datum `f`, weakly continuous
into `L²` on `[0, T₀)`, with `ω^{(φ n)} → ω_∞` uniformly weakly in `L²` on every `[0, T']`,
`T' < T₀`. -/
theorem criterion_limit {T₀ : ℝ≥0∞} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}
    (hadm : IsAdmissibleSeq 2 T₀ f fs ωs)
    (hcont : ∀ n, IsWeakContL2On (timeInterval T₀) (ωs n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ωinf : ℝ → ℂ → ℝ,
      IsRenormalizedWeakSolutionUpTo 2 T₀ f ωinf ∧
      IsWeakContL2On (timeInterval T₀) ωinf ∧
      ∀ T' : ℝ, ENNReal.ofReal T' < T₀ →
        WeakTendstoUnifL2On (fun n => ωs (φ n)) ωinf (Icc 0 T') := by
  classical
  obtain ⟨Tj, hTpos, hTlt, hcof⟩ := exists_times hadm.T₀_pos
  obtain ⟨M, hcs⟩ := isCompactSeq_of_admissible hadm hcont
  have hstrong : Tendsto (fun n => normL1LpE 2 (fs n - f)) atTop (𝓝 0) := by
    simpa using hadm.tendsto
  -- the subsequence properties `Q j` of the diagonal argument
  let Q : ℕ → (ℕ → ℕ) → Prop := fun j φ => ∃ ω : ℝ → ℂ → ℝ,
    IsRenormalizedWeakSolution 2 (Tj j) f ω ∧ IsWeakContL2On (Icc 0 (Tj j)) ω ∧
      WeakTendstoUnifL2On (fun n => ωs (φ n)) ω (Icc 0 (Tj j))
  have htail : ∀ (k : ℕ) (φ ψ : ℕ → ℕ), Q k φ → (∀ᶠ n in atTop, φ n = ψ n) → Q k ψ := by
    rintro k φ ψ ⟨ω, h1, h2, h3⟩ hev
    refine ⟨ω, h1, h2, fun χ hχ => (h3 χ hχ).congr ?_⟩
    filter_upwards [hev] with n hn t _
    simp only [hn]
  have hsub : ∀ (k : ℕ) (φ ψ : ℕ → ℕ), Q k φ → StrictMono ψ → Q k (φ ∘ ψ) := by
    rintro k φ ψ ⟨ω, h1, h2, h3⟩ hψ
    exact ⟨ω, h1, h2, h3.subseq hψ⟩
  have hex : ∀ (k : ℕ) (φ : ℕ → ℕ), StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Q k (φ ∘ ψ) := by
    intro k φ hφ
    have hcsφ := (hcs (Tj k) (hTpos k) (hTlt k)).subseq hφ
    obtain ⟨ψ, hψ, ω, hlim, -⟩ := compact hcsφ
    obtain ⟨-, -, hren, -⟩ := stable (hcsφ.subseq hψ) hlim
      (hstrong.comp (hφ.comp hψ).tendsto_atTop)
      (fun n => hadm.renormalized (φ (ψ n)) (Tj k) (hTpos k) (hTlt k))
    exact ⟨ψ, hψ, ω, hren, hlim.weakCont, hlim.weakTendstoUnif⟩
  obtain ⟨φ, hφ, hQ⟩ := WeakL2.exists_diagonal_subseq Q htail hsub hex
  choose ωj hωj using hQ
  -- uniqueness of weak limits: the `ω^{[j]}` agree where they are both defined
  have huniq : ∀ i k t, t ∈ Icc 0 (Tj i) → t ∈ Icc 0 (Tj k) →
      ωj i t =ᵐ[volume] ωj k t := by
    intro i k t hi hk
    refine ae_eq_of_forall_integral_mul_eq ((hωj i).2.1.memLp t hi) ((hωj k).2.1.memLp t hk)
      fun ψ hψ => ?_
    exact tendsto_nhds_unique (((hωj i).2.2 ψ hψ).tendsto_at hi)
      (((hωj k).2.2 ψ hψ).tendsto_at hk)
  -- the glued function
  obtain ⟨ωg, hg⟩ : ∃ ωg : ℝ → ℂ → ℝ, ∀ k, ∀ t ∈ Icc 0 (Tj k), ωg t =ᵐ[volume] ωj k t := by
    refine ⟨fun t => if h : ∃ j, t ≤ Tj j then ωj (Classical.choose h) t else 0,
      fun k t ht => ?_⟩
    have h : ∃ j, t ≤ Tj j := ⟨k, ht.2⟩
    beta_reduce
    rw [dite_eq_left_of_eq_true (eq_true h)]
    exact huniq _ _ t ⟨ht.1, Classical.choose_spec h⟩ ht
  have hgc : IsWeakContL2On (timeInterval T₀) ωg :=
    isWeakContL2On_of_local hcof (fun j => (hωj j).2.1) hg
  -- a jointly measurable representative, correct at every time of `[0, T₀)`
  obtain ⟨U, hU⟩ := JointRep.exists_isJointRep_of_weakContinuousOn
    (measurableSet_timeInterval T₀) (isWeakContL2On_iff_toPath.1 hgc).2
  have hUg : ∀ t ∈ timeInterval T₀, U t =ᵐ[volume] ωg t := fun t ht =>
    (hU.ae_eq t ht).trans (JointRep.coeFn_toPath (hgc.memLp t ht))
  have hUk : ∀ k, ∀ t ∈ Icc 0 (Tj k), U t =ᵐ[volume] ωj k t := fun k t ht =>
    (hUg t (Icc_subset_timeInterval (hTlt k) ht)).trans (hg k t ht)
  refine ⟨φ, hφ, U, ?_, isWeakContL2On_congr hgc hUg, ?_⟩
  · intro T hT hTT₀
    obtain ⟨k, hk⟩ := hcof T hTT₀
    have h1 := isRenormalizedWeakSolution_mono (hωj k).1 hT hk.le
    refine h1.congr_ae ?_
    refine JointRep.ae_eq_slab_of_ae_ae hU.measurable.aestronglyMeasurable
      h1.memX.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioo fun t ht =>
      hUk k t ⟨ht.1.le, ht.2.le.trans hk.le⟩
  · intro T' hT' ψ hψ
    obtain ⟨k, hk⟩ := hcof T' hT'
    refine (((hωj k).2.2 ψ hψ).mono (Icc_subset_Icc_right hk.le)).congr_right fun t ht => ?_
    exact integral_mul_congr (hUk k t ⟨ht.1, ht.2.trans hk.le⟩).symm ψ

end NonUniqueEuler.Compact
