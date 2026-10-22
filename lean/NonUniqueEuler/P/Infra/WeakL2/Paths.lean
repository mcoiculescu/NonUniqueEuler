import NonUniqueEuler.Defs.Infra.WeakL2
import NonUniqueEuler.I.Infra.WeakL2.Norm
import NonUniqueEuler.I.Infra.WeakL2.LpNorm
import NonUniqueEuler.I.Infra.WeakL2.Compact
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.Nat.Pairing

/-!
# Proof of the interface (I-WEAKL2): weakly continuous paths; weak Arzelà–Ascoli

Proof of `NonUniqueEuler/I/Infra/WeakL2/Paths.lean` (same declarations, same statements).

Used by `lem:weak-cont` (`03_compactness.tex:160-246`), `prop:compact`(i)
(`03_compactness.tex:277-292`), the gluing of representatives (`03_compactness.tex:251-262`)
and `thm:criterion`.

Structure of the proof.
* `PathsAux.neBot_nhdsWithin_of_ae`: if a property holds for a.e. `t ∈ (a, b)`, then every
  `t ∈ [a, b]` is adherent to the set of "good" times of `(a, b)` (a nonempty open subinterval of
  `(a, b)` near `t` has positive measure). The three "a.e. ⇒ everywhere" statements follow by
  testing the weak continuity along `𝓝[good times] t`, with `WeakTendsto.unique`,
  `WeakTendsto.norm_le` (`I/Infra/WeakL2/Norm.lean`) and `eLpNorm_le_of_weakTendsto`
  (`I/Infra/WeakL2/LpNorm.lean`).
* `exists_weakTendstoUniformlyOn_of_dense`: pointwise weak limits by
  `exists_weakTendsto_of_dense` (`I/Infra/WeakL2/Compact.lean`), then the estimate
  `|⟪U t - u n t, y⟫| ≤ 2|M| ‖y - e k‖ + |⟪U t - u n t, e k⟫|`.
* Weak Arzelà–Ascoli: `exists_subseq_tendsto_forall` (`I/Infra/WeakL2/Compact.lean`) along a
  countable dense set of times `d j ∈ [a, b]`, for all pairs `(k, j)` at once (`Nat.pair`);
  equi-Lipschitz bounds and a finite `δ`-net of `[a, b]` (compactness) make the sequences
  `⟪u (φ n) ·, e k⟫` uniformly Cauchy (`PathsAux.exists_tendstoUniformlyOn_of_lipschitz`);
  then `exists_weakTendstoUniformlyOn_of_dense`. The limit is weakly continuous because
  `⟪U ·, e k⟫` is `L_k`-Lipschitz and `⟪U ·, y⟫` is a uniform limit of such functions
  (`PathsAux.weakContinuousOn_of_dense`).
-/

noncomputable section

open Filter Topology Set MeasureTheory
open scoped InnerProductSpace ENNReal

namespace NonUniqueEuler.WeakL2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace PathsAux

/-- If a property holds for a.e. `t ∈ (a, b)`, every `t ∈ [a, b]` is adherent to the set of times
of `(a, b)` with the property. -/
theorem neBot_nhdsWithin_of_ae {P : ℝ → Prop} {a b : ℝ} (hab : a < b)
    (h : ∀ᵐ t ∂(volume.restrict (Ioo a b)), P t) {t : ℝ} (ht : t ∈ Icc a b) :
    (𝓝[{s | s ∈ Ioo a b ∧ P s}] t).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  have hAsub : Ioo (max a (t - ε)) (min b (t + ε)) ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
  have hlt : max a (t - ε) < min b (t + ε) := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨hab, by linarith [ht.1]⟩, ⟨by linarith [ht.2], by linarith⟩⟩
  have hApos : volume (Ioo (max a (t - ε)) (min b (t + ε))) ≠ 0 := by
    rw [Real.volume_Ioo, Ne, ENNReal.ofReal_eq_zero, not_le, sub_pos]
    exact hlt
  have h1 : ∀ᵐ s ∂(volume.restrict (Ioo (max a (t - ε)) (min b (t + ε)))), P s :=
    ae_restrict_of_ae_restrict_of_subset hAsub h
  have h2 : ∀ᵐ s ∂(volume.restrict (Ioo (max a (t - ε)) (min b (t + ε)))),
      s ∈ Ioo (max a (t - ε)) (min b (t + ε)) :=
    ae_restrict_mem measurableSet_Ioo
  have : (ae (volume.restrict (Ioo (max a (t - ε)) (min b (t + ε))))).NeBot :=
    ae_neBot.2 (by rwa [Ne, Measure.restrict_eq_zero])
  obtain ⟨s, hsP, hsA⟩ := (h1.and h2).exists
  refine ⟨s, ⟨hAsub hsA, hsP⟩, ?_⟩
  rw [Real.dist_eq, abs_lt]
  have h3 := hsA.1
  have h4 := hsA.2
  have h5 := le_max_right a (t - ε)
  have h6 := min_le_right b (t + ε)
  constructor <;> linarith

/-- A path bounded by `M` on `s` whose inner products with the vectors of a dense sequence are
continuous on `s` is weakly continuous on `s`. -/
theorem weakContinuousOn_of_dense {τ : Type*} [TopologicalSpace τ] {e : ℕ → E}
    (he : DenseRange e) {U : τ → E} {s : Set τ} {M : ℝ} (hU : ∀ t ∈ s, ‖U t‖ ≤ M)
    (hc : ∀ k, ContinuousOn (fun t => ⟪U t, e k⟫_ℝ) s) : WeakContinuousOn U s := by
  intro y
  have hunif : TendstoUniformlyOn (fun z t => ⟪U t, z⟫_ℝ) (fun t => ⟪U t, y⟫_ℝ) (𝓝 y) s := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hM1 : 0 < |M| + 1 := by positivity
    filter_upwards [Metric.ball_mem_nhds y (div_pos hε hM1)] with z hz t ht
    rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hz
    rw [Real.dist_eq, ← inner_sub_right]
    calc |⟪U t, y - z⟫_ℝ| ≤ ‖U t‖ * ‖y - z‖ := abs_real_inner_le_norm _ _
      _ ≤ (|M| + 1) * ‖y - z‖ := by
          gcongr
          linarith [hU t ht, le_abs_self M]
      _ < (|M| + 1) * (ε / (|M| + 1)) := by gcongr
      _ = ε := by field_simp
  refine hunif.continuousOn ?_
  have hfreq : ∃ᶠ z in 𝓝 y, z ∈ range e := mem_closure_iff_frequently.1 (he y)
  exact hfreq.mono (by rintro _ ⟨k, rfl⟩; exact hc k)

/-- An equi-Lipschitz sequence of real functions on `[a, b]` which is Cauchy at every point of a
dense sequence `d j ∈ [a, b]` converges uniformly on `[a, b]`. -/
theorem exists_tendstoUniformlyOn_of_lipschitz {g : ℕ → ℝ → ℝ} {a b L : ℝ} {d : ℕ → ℝ}
    (hd : ∀ x ∈ Icc a b, ∀ δ > 0, ∃ j, dist x (d j) < δ) (hdmem : ∀ j, d j ∈ Icc a b)
    (hlip : ∀ n, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |g n t - g n s| ≤ L * |t - s|)
    (hconv : ∀ j, CauchySeq (fun n => g n (d j))) :
    ∃ f : ℝ → ℝ, TendstoUniformlyOn g f atTop (Icc a b) := by
  have hUC : UniformCauchySeqOn g atTop (Icc a b) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    have hL1 : 0 < |L| + 1 := by positivity
    have hδpos : 0 < ε / (3 * (|L| + 1)) := by positivity
    obtain ⟨J, hJ⟩ := isCompact_Icc.elim_finite_subcover
      (fun j => Metric.ball (d j) (ε / (3 * (|L| + 1)))) (fun _ => Metric.isOpen_ball)
      (fun x hx => by
        obtain ⟨j, hj⟩ := hd x hx _ hδpos
        exact mem_iUnion.2 ⟨j, hj⟩)
    have hN : ∀ j, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (g m (d j)) (g n (d j)) < ε / 3 :=
      fun j => Metric.cauchySeq_iff.1 (hconv j) (ε / 3) (by positivity)
    choose N hN using hN
    refine ⟨J.sup N, fun m hm n hn x hx => ?_⟩
    obtain ⟨j, hjJ, hxj⟩ := mem_iUnion₂.1 (hJ hx)
    have hjN : N j ≤ J.sup N := Finset.le_sup hjJ
    have h1 := hN j m (hjN.trans hm) n (hjN.trans hn)
    rw [Metric.mem_ball, Real.dist_eq] at hxj
    rw [Real.dist_eq] at h1 ⊢
    have hL : L * |x - d j| ≤ ε / 3 := by
      calc L * |x - d j| ≤ |L| * |x - d j| :=
            mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)
        _ ≤ (|L| + 1) * (ε / (3 * (|L| + 1))) :=
            mul_le_mul (by linarith) hxj.le (abs_nonneg _) hL1.le
        _ = ε / 3 := by field_simp
    have h2 := abs_le.1 ((hlip m (d j) (hdmem j) x hx).trans hL)
    have h3 := abs_le.1 ((hlip n (d j) (hdmem j) x hx).trans hL)
    have h1' := abs_lt.1 h1
    rw [abs_lt]
    constructor <;> linarith [h1'.1, h1'.2, h2.1, h2.2, h3.1, h3.2]
  have hpt : ∀ x, ∃ c : ℝ, x ∈ Icc a b → Tendsto (fun n => g n x) atTop (𝓝 c) := by
    intro x
    by_cases hx : x ∈ Icc a b
    · obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete (hUC.cauchySeq hx)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose f hf using hpt
  exact ⟨f, hUC.tendstoUniformlyOn_of_tendsto hf⟩

end PathsAux

open PathsAux

/-- Two weakly continuous paths on `[a, b]` that agree for almost every `t ∈ (a, b)` agree on
`[a, b]`. -/
theorem WeakContinuousOn.eqOn_of_ae_eq {u v : ℝ → E} {a b : ℝ} (hab : a < b)
    (hu : WeakContinuousOn u (Icc a b)) (hv : WeakContinuousOn v (Icc a b))
    (h : ∀ᵐ t ∂(volume.restrict (Ioo a b)), u t = v t) : EqOn u v (Icc a b) := by
  intro t ht
  have := neBot_nhdsWithin_of_ae hab h ht
  have hS : {s | s ∈ Ioo a b ∧ u s = v s} ⊆ Icc a b := fun s hs => Ioo_subset_Icc_self hs.1
  have hu' := (hu.weakTendsto ht).mono_left (nhdsWithin_mono t hS)
  have hv' := (hv.weakTendsto ht).mono_left (nhdsWithin_mono t hS)
  have huv : WeakTendsto u (𝓝[{s | s ∈ Ioo a b ∧ u s = v s}] t) (v t) := by
    intro y
    refine (hv' y).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hs.2]
  exact hu'.unique huv

/-- An a.e. bound on the norm of a weakly continuous path holds at every time of `[a, b]`. -/
theorem WeakContinuousOn.norm_le_of_ae {u : ℝ → E} {a b M : ℝ} (hab : a < b)
    (hu : WeakContinuousOn u (Icc a b)) (h : ∀ᵐ t ∂(volume.restrict (Ioo a b)), ‖u t‖ ≤ M) :
    ∀ t ∈ Icc a b, ‖u t‖ ≤ M := by
  intro t ht
  have := neBot_nhdsWithin_of_ae hab h ht
  have hS : {s | s ∈ Ioo a b ∧ ‖u s‖ ≤ M} ⊆ Icc a b := fun s hs => Ioo_subset_Icc_self hs.1
  refine ((hu.weakTendsto ht).mono_left (nhdsWithin_mono t hS)).norm_le ?_
  filter_upwards [self_mem_nhdsWithin] with s hs using hs.2

/-- An a.e. bound on the `L^q` norm (`q ∈ [1, ∞]`) of a weakly continuous path in `L²(μ)` holds
at every time of `[a, b]`. -/
theorem WeakContinuousOn.eLpNorm_le_of_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] {u : ℝ → Lp ℝ 2 μ} {a b : ℝ} (hab : a < b)
    (hu : WeakContinuousOn u (Icc a b)) {q : ℝ≥0∞} (hq : 1 ≤ q) {M : ℝ≥0∞}
    (h : ∀ᵐ t ∂(volume.restrict (Ioo a b)), eLpNorm (u t) q μ ≤ M) :
    ∀ t ∈ Icc a b, eLpNorm (u t) q μ ≤ M := by
  intro t ht
  have := neBot_nhdsWithin_of_ae hab h ht
  have hS : {s | s ∈ Ioo a b ∧ eLpNorm (u s) q μ ≤ M} ⊆ Icc a b :=
    fun s hs => Ioo_subset_Icc_self hs.1
  refine eLpNorm_le_of_weakTendsto hq
    ((hu.weakTendsto ht).mono_left (nhdsWithin_mono t hS)) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs using hs.2

/-- Identification of a uniform weak limit from uniform convergence against a dense
sequence. -/
theorem exists_weakTendstoUniformlyOn_of_dense [CompleteSpace E] {τ : Type*} {e : ℕ → E}
    (he : DenseRange e) {u : ℕ → τ → E} {s : Set τ} {M : ℝ}
    (hu : ∀ n, ∀ t ∈ s, ‖u n t‖ ≤ M)
    (hc : ∀ k, ∃ f : τ → ℝ, TendstoUniformlyOn (fun n t => ⟪u n t, e k⟫_ℝ) f atTop s) :
    ∃ U : τ → E, (∀ t ∈ s, ‖U t‖ ≤ M) ∧ WeakTendstoUniformlyOn u U atTop s := by
  choose f hf using hc
  have key : ∀ t, ∃ x : E, t ∈ s → ‖x‖ ≤ M ∧ WeakTendsto (fun n => u n t) atTop x := by
    intro t
    by_cases ht : t ∈ s
    · obtain ⟨x, hxM, hx⟩ := exists_weakTendsto_of_dense (l := atTop) (u := fun n => u n t)
        (Eventually.of_forall fun n => hu n t ht) (D := range e) he
        (by rintro _ ⟨k, rfl⟩; exact ⟨f k t, (hf k).tendsto_at ht⟩)
      exact ⟨x, fun _ => ⟨hxM, hx⟩⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose U hU using key
  refine ⟨U, fun t ht => (hU t ht).1, ?_⟩
  have hfU : ∀ k, TendstoUniformlyOn (fun n t => ⟪u n t, e k⟫_ℝ) (fun t => ⟪U t, e k⟫_ℝ)
      atTop s := by
    intro k
    refine (hf k).congr_right ?_
    intro t ht
    exact tendsto_nhds_unique ((hf k).tendsto_at ht) ((hU t ht).2 (e k))
  intro y
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hCpos : 0 < 2 * (|M| + 1) := by positivity
  obtain ⟨k, hk⟩ := he.exists_dist_lt y (show 0 < ε / (2 * (2 * (|M| + 1))) by positivity)
  rw [dist_eq_norm] at hk
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hfU k) (ε / 2) (half_pos hε)] with n hn t ht
  have hn' := hn t ht
  rw [Real.dist_eq] at hn' ⊢
  have h1 : ‖U t - u n t‖ ≤ 2 * (|M| + 1) := by
    have := norm_sub_le (U t) (u n t)
    linarith [(hU t ht).1, hu n t ht, le_abs_self M]
  calc |⟪U t, y⟫_ℝ - ⟪u n t, y⟫_ℝ|
        = |⟪U t - u n t, y - e k⟫_ℝ + (⟪U t, e k⟫_ℝ - ⟪u n t, e k⟫_ℝ)| := by
          congr 1
          simp only [inner_sub_left, inner_sub_right]
          ring
    _ ≤ |⟪U t - u n t, y - e k⟫_ℝ| + |⟪U t, e k⟫_ℝ - ⟪u n t, e k⟫_ℝ| := abs_add_le _ _
    _ ≤ ‖U t - u n t‖ * ‖y - e k‖ + |⟪U t, e k⟫_ℝ - ⟪u n t, e k⟫_ℝ| := by
          gcongr
          exact abs_real_inner_le_norm _ _
    _ < 2 * (|M| + 1) * (ε / (2 * (2 * (|M| + 1)))) + ε / 2 :=
          add_lt_add_of_le_of_lt (mul_le_mul h1 hk.le (norm_nonneg _) hCpos.le) hn'
    _ = ε := by field_simp; ring

/-- **Weak Arzelà–Ascoli.** Let `e` have dense range. A sequence of paths bounded by `M` on `[a, b]`,
whose inner products with each `e k` are equi-Lipschitz on `[a, b]`, has a subsequence
converging weakly, uniformly on `[a, b]`, to a weakly continuous path bounded by `M`. -/
theorem exists_subseq_weakTendstoUniformlyOn [CompleteSpace E] {e : ℕ → E}
    (he : DenseRange e) {u : ℕ → ℝ → E} {a b M : ℝ}
    (hu : ∀ n, ∀ t ∈ Icc a b, ‖u n t‖ ≤ M)
    (hlip : ∀ k, ∃ L : ℝ, ∀ n, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |⟪u n t, e k⟫_ℝ - ⟪u n s, e k⟫_ℝ| ≤ L * |t - s|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ U : ℝ → E, (∀ t ∈ Icc a b, ‖U t‖ ≤ M) ∧
      WeakContinuousOn U (Icc a b) ∧
      WeakTendstoUniformlyOn (fun n => u (φ n)) U atTop (Icc a b) := by
  rcases (Icc a b).eq_empty_or_nonempty with hempty | hne
  · refine ⟨id, strictMono_id, 0, ?_, ?_, ?_⟩
    · intro t ht
      rw [hempty] at ht
      exact absurd ht (by simp)
    · rw [hempty]
      intro y
      exact continuousOn_empty _
    · rw [hempty]
      intro y
      exact tendstoUniformlyOn_empty
  choose L hL using hlip
  -- a dense sequence of times in `[a, b]`
  have : Nonempty (Icc a b) := hne.to_subtype
  obtain ⟨d', hd'⟩ := TopologicalSpace.exists_dense_seq (Icc a b)
  have hdmem : ∀ j, (d' j : ℝ) ∈ Icc a b := fun j => (d' j).2
  have hd : ∀ x ∈ Icc a b, ∀ δ > 0, ∃ j, dist x (d' j : ℝ) < δ := by
    intro x hx δ hδ
    obtain ⟨j, hj⟩ := hd'.exists_dist_lt (⟨x, hx⟩ : Icc a b) hδ
    exact ⟨j, by rwa [Subtype.dist_eq] at hj⟩
  -- a common subsequence along which `⟪u n (d j), e k⟫` converges for all `(k, j)`
  obtain ⟨φ, hφ, hconv⟩ := exists_subseq_tendsto_forall
    (fun m n => ⟪u n (d' (Nat.unpair m).2 : ℝ), e (Nat.unpair m).1⟫_ℝ)
    (fun m => ⟨M * ‖e (Nat.unpair m).1‖, fun n =>
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hu n _ (hdmem _)) (norm_nonneg _))⟩)
  have hunif : ∀ k, ∃ f : ℝ → ℝ,
      TendstoUniformlyOn (fun n t => ⟪u (φ n) t, e k⟫_ℝ) f atTop (Icc a b) := by
    intro k
    refine exists_tendstoUniformlyOn_of_lipschitz (g := fun n t => ⟪u (φ n) t, e k⟫_ℝ)
      (L := L k) hd hdmem (fun n s hs t ht => hL k (φ n) s hs t ht) (fun j => ?_)
    obtain ⟨c, hc⟩ := hconv (Nat.pair k j)
    simp only [Nat.unpair_pair] at hc
    exact hc.cauchySeq
  obtain ⟨U, hUM, hUconv⟩ :=
    exists_weakTendstoUniformlyOn_of_dense he (fun n t ht => hu (φ n) t ht) hunif
  refine ⟨φ, hφ, U, hUM, ?_, hUconv⟩
  refine weakContinuousOn_of_dense he hUM (fun k => ?_)
  have hlipU : ∀ t ∈ Icc a b, ∀ s ∈ Icc a b,
      dist ⟪U t, e k⟫_ℝ ⟪U s, e k⟫_ℝ ≤ L k * dist t s := by
    intro t ht s hs
    rw [Real.dist_eq, Real.dist_eq]
    have h1 := (hUconv (e k)).tendsto_at ht
    have h2 := (hUconv (e k)).tendsto_at hs
    exact le_of_tendsto (h1.sub h2).abs (Eventually.of_forall fun n => hL k (φ n) s hs t ht)
  exact (LipschitzOnWith.of_dist_le' hlipU).continuousOn

end NonUniqueEuler.WeakL2
