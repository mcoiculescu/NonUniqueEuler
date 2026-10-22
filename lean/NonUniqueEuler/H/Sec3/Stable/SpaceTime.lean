import NonUniqueEuler.H.Sec3.Stable.BddRenorm

/-!
# Helpers for `prop:stable`: strong convergence in space–time

Helper file of `P/Sec3/Stable.lean`. Manuscript: proof of `prop:stable`, fourth paragraph
(`03_compactness.tex:791-800`): `ωₙ → ω` in `L¹((0,T) × B_R)` for every `R > 0`.

Restructured argument (deviation, same ingredients): instead of a diagonal subsequence over
`k ∈ ℕ` and a Cauchy argument, we use a sub-subsequence argument, which gives the convergence of
the **whole** sequence. Suppose `aₙ = ‖ωₙ - ω‖_{L¹((0,T)×B_R)} > ε` along a subsequence `ψ`. Pick
`k` with `2TM²/k < ε`. Along a further subsequence `φ`, `T_k(ω_{ψφn}) → ū` in `L¹((0,T)×B_R)`
(`stable_bddRenorm`), and `‖ū - ω‖_{L¹((0,T)×B_R)} ≤ TM²/k` (`lintegral_sub_limit_le`: test the
weak convergence `ωₙ ⇀ ω` on the slab (`tendsto_integral_slab_mul`, from `prop:compact`(i) and
dominated convergence in `t`) with `Φ = sgn(ū - ω) 1_{B_R}`, and use
`‖ωₙ - T_k ωₙ‖_{L¹((0,T)×ℝ²)} ≤ TM²/k`, `lintegral_sub_trunc_le`). Hence
`a_{ψφn} ≤ TM²/k + ‖T_k ω_{ψφn} - ū‖ + TM²/k < ε` eventually, a contradiction.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.StableAux

open Weak

variable {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ} {ω : ℝ → ℂ → ℝ}

/-! ### Slice bounds -/

theorem seq_eLpNorm_one_le (hseq : IsCompactSeq T M gs g ωs) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) : eLpNorm (ωs n t) 1 volume ≤ ENNReal.ofReal M :=
  (eLpNorm_one_le_normL1LpE 2 _).trans (hseq.bound n t ht)

theorem seq_eLpNorm_two_le (hseq : IsCompactSeq T M gs g ωs) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) : eLpNorm (ωs n t) 2 volume ≤ ENNReal.ofReal M :=
  (eLpNorm_le_normL1LpE 2 _).trans (hseq.bound n t ht)

/-- The bounds pass to the limit (`prop:compact`(ii)). -/
theorem limit_eLpNorm_le (hseq : IsCompactSeq T M gs g ωs) (hlim : IsCompactLimit T g ωs ω)
    {t : ℝ} (ht : t ∈ Icc 0 T) {p : ℝ≥0∞} (hp : p = 1 ∨ p = 2) :
    eLpNorm (ω t) p volume ≤ ENNReal.ofReal M := by
  rcases hp with rfl | rfl
  · have h := hlim.eLpNorm_le_liminf t ht 1 le_rfl one_le_two
    rw [ENNReal.ofReal_one] at h
    exact h.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n =>
      seq_eLpNorm_one_le hseq n ht))
  · have h := hlim.eLpNorm_le_liminf t ht 2 one_le_two le_rfl
    rw [ENNReal.ofReal_ofNat] at h
    exact h.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n =>
      seq_eLpNorm_two_le hseq n ht))

theorem seq_integrableOn_slab (hseq : IsCompactSeq T M gs g ωs) (n : ℕ) :
    IntegrableOn (Function.uncurry (ωs n)) (slab T) :=
  integrableOn_slab_of_bound (hseq.weakSolution n).memX.aestronglyMeasurable
    fun _t ht => seq_eLpNorm_one_le hseq n (Ioo_subset_Icc_self ht)

theorem limit_integrableOn_slab (hseq : IsCompactSeq T M gs g ωs)
    (hlim : IsCompactLimit T g ωs ω) : IntegrableOn (Function.uncurry ω) (slab T) :=
  integrableOn_slab_of_bound hlim.weakSolution.memX.aestronglyMeasurable
    fun _t ht => limit_eLpNorm_le hseq hlim (Ioo_subset_Icc_self ht) (Or.inl rfl)

/-! ### The truncation error -/

/-- `‖ωₙ - T_k ωₙ‖_{L¹((0,T) × ℝ²)} ≤ T M²/k`. -/
theorem lintegral_sub_trunc_le (hseq : IsCompactSeq T M gs g ωs) (n : ℕ) {k : ℝ} (hk : 0 < k) :
    ∫⁻ p in slab T, ‖ωs n p.1 p.2 - trunc k (ωs n p.1 p.2)‖ₑ ≤
      ENNReal.ofReal T * (ENNReal.ofReal (1 / k) * ENNReal.ofReal M ^ 2) := by
  refine lintegral_slab_le_of_slice univ (fun p => ‖ωs n p.1 p.2 - trunc k (ωs n p.1 p.2)‖ₑ)
    (fun t ht => ?_)
  rw [Measure.restrict_univ]
  have hpt : ∀ x, ‖ωs n t x - trunc k (ωs n t x)‖ₑ ≤
      ENNReal.ofReal (1 / k) * ‖ωs n t x‖ₑ ^ (2 : ℝ) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity), sq_abs]
    refine ENNReal.ofReal_le_ofReal ((abs_sub_trunc_le hk _).trans_eq ?_)
    ring
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  gcongr
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := ωs n t) (p := 2) two_ne_zero
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at h2
  rw [← h2, ENNReal.rpow_two]
  gcongr
  exact seq_eLpNorm_two_le hseq n (Ioo_subset_Icc_self ht)

/-! ### Weak convergence on the slab against bounded test functions -/

/-- `∫∫ ωₙ Φ → ∫∫ ω Φ` for bounded measurable `Φ` vanishing outside `ℝ × B_R`
(`prop:compact`(i) and dominated convergence in `t`, `03_compactness.tex:798-800`). -/
theorem tendsto_integral_slab_mul (hseq : IsCompactSeq T M gs g ωs)
    (hlim : IsCompactLimit T g ωs ω) {Φ : ℝ × ℂ → ℝ} (hΦ : Measurable Φ) {C R : ℝ}
    (hC : ∀ p, |Φ p| ≤ C) (hR : ∀ p : ℝ × ℂ, R ≤ ‖p.2‖ → Φ p = 0) :
    Tendsto (fun n => ∫ p in slab T, ωs n p.1 p.2 * Φ p) atTop
      (𝓝 (∫ p in slab T, ω p.1 p.2 * Φ p)) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hΦb : ∀ᵐ p ∂(volume.restrict (slab T)), ‖Φ p‖ ≤ C :=
    Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hC p
  have hint : ∀ n, IntegrableOn (fun p : ℝ × ℂ => ωs n p.1 p.2 * Φ p) (slab T) := fun n =>
    (seq_integrableOn_slab hseq n).mul_bdd hΦ.aestronglyMeasurable hΦb
  have hintω : IntegrableOn (fun p : ℝ × ℂ => ω p.1 p.2 * Φ p) (slab T) :=
    (limit_integrableOn_slab hseq hlim).mul_bdd hΦ.aestronglyMeasurable hΦb
  have hiter : ∀ {F : ℝ × ℂ → ℝ}, IntegrableOn F (slab T) →
      ∫ p in slab T, F p = ∫ t in Ioo 0 T, ∫ x : ℂ, F (t, x) := fun hF =>
    (integral_Ioo_integral_eq (t₀ := 0) hF).symm
  simp_rw [hiter (hint _), hiter hintω]
  -- slices of `Φ` are in `L²`
  have hmem : ∀ t, MemLp (fun x => Φ (t, x)) 2 volume := by
    intro t
    have hfin : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) R)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have heq : (fun x => Φ (t, x)) = (ball (0 : ℂ) R).indicator (fun x => Φ (t, x)) := by
      funext x
      by_cases hx : x ∈ ball (0 : ℂ) R
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, hR (t, x) (by simpa using hx)]
    rw [heq, memLp_indicator_iff_restrict measurableSet_ball]
    exact MemLp.of_bound (hΦ.comp measurable_prodMk_left).aestronglyMeasurable C
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC _)
  refine tendsto_integral_of_dominated_convergence (fun _ => (ENNReal.ofReal (C * M)).toReal)
    (fun n => ?_)
    (integrable_const _) (fun n => ?_) ?_
  · have h := (hint n)
    rw [IntegrableOn, JointRep.volume_restrict_slab] at h
    exact h.integral_prod_left.aestronglyMeasurable
  · refine (ae_restrict_mem measurableSet_Ioo).mono fun t ht => ?_
    have h1 : ‖∫ x : ℂ, ωs n t x * Φ (t, x)‖ₑ ≤ ENNReal.ofReal (C * M) := by
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      have hpt : ∀ x, ‖ωs n t x * Φ (t, x)‖ₑ ≤ ENNReal.ofReal C * ‖ωs n t x‖ₑ := by
        intro x
        rw [enorm_mul, mul_comm, Real.enorm_eq_ofReal_abs (Φ _)]
        gcongr
        exact hC _
      refine (lintegral_mono hpt).trans ?_
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← eLpNorm_one_eq_lintegral_enorm,
        ENNReal.ofReal_mul hC0]
      gcongr
      exact seq_eLpNorm_one_le hseq n (Ioo_subset_Icc_self ht)
    rw [← ofReal_norm] at h1
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at h2
  · refine (ae_restrict_mem measurableSet_Ioo).mono fun t ht => ?_
    exact (hlim.weakTendstoUnif _ (hmem t)).tendsto_at (Ioo_subset_Icc_self ht)

/-! ### Identification of the limit of `T_k(ωₙ)` up to `TM²/k` -/

theorem prod_ball_inter_slab (T R : ℝ) :
    ((univ : Set ℝ) ×ˢ ball (0 : ℂ) R) ∩ slab T = Ioo 0 T ×ˢ ball (0 : ℂ) R := by
  rw [slab, prod_inter_prod, univ_inter, inter_univ]

/-- `∫∫_{slab} ‖h Φ‖ ≤ ∫∫_{(0,T) × B_R} ‖h‖` for `|Φ| ≤ 1`, `Φ = 0` off `ℝ × B_R`. -/
theorem lintegral_slab_mul_le {Φ : ℝ × ℂ → ℝ} {R : ℝ} (hC : ∀ p, |Φ p| ≤ 1)
    (hR : ∀ p : ℝ × ℂ, R ≤ ‖p.2‖ → Φ p = 0) (h : ℝ × ℂ → ℝ) :
    ∫⁻ p in slab T, ‖h p * Φ p‖ₑ ≤ ∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖h p‖ₑ := by
  have hS : MeasurableSet ((univ : Set ℝ) ×ˢ ball (0 : ℂ) R) :=
    MeasurableSet.univ.prod measurableSet_ball
  have hpt : ∀ p, ‖h p * Φ p‖ₑ ≤
      ((univ : Set ℝ) ×ˢ ball (0 : ℂ) R).indicator (fun p => ‖h p‖ₑ) p := by
    intro p
    by_cases hp : p ∈ (univ : Set ℝ) ×ˢ ball (0 : ℂ) R
    · rw [indicator_of_mem hp, enorm_mul]
      calc ‖h p‖ₑ * ‖Φ p‖ₑ ≤ ‖h p‖ₑ * 1 := by
            gcongr
            rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (hC p)
        _ = ‖h p‖ₑ := mul_one _
    · rw [indicator_of_notMem hp]
      have : R ≤ ‖p.2‖ := by
        simp only [mem_prod, mem_univ, true_and, mem_ball, dist_zero_right, not_lt] at hp
        exact hp
      rw [hR p this, mul_zero, enorm_zero]
  refine (lintegral_mono hpt).trans_eq ?_
  rw [lintegral_indicator hS, Measure.restrict_restrict hS, prod_ball_inter_slab]

/-- **Identification** (`03_compactness.tex:797-800`): if `T_k(ωₙ) → ū` in `L¹((0,T) × B_R)`,
then `‖ū - ω‖_{L¹((0,T) × B_R)} ≤ TM²/k`. -/
theorem lintegral_sub_limit_le (hseq : IsCompactSeq T M gs g ωs)
    (hlim : IsCompactLimit T g ωs ω) {k : ℝ} (hk : 0 < k) {ub : ℝ → ℂ → ℝ}
    (hub : Prelim.MemLinfLp (Ioo 0 T) univ 1 ub) {R : ℝ}
    (hconv : Tendsto (fun n => ∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R,
      ‖trunc k (ωs n p.1 p.2) - ub p.1 p.2‖ₑ) atTop (𝓝 0)) :
    ∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖ub p.1 p.2 - ω p.1 p.2‖ₑ ≤
      ENNReal.ofReal T * (ENNReal.ofReal (1 / k) * ENNReal.ofReal M ^ 2) := by
  classical
  set Ck := ENNReal.ofReal T * (ENNReal.ofReal (1 / k) * ENNReal.ofReal M ^ 2) with hCk
  have hG : AEStronglyMeasurable (fun p : ℝ × ℂ => ub p.1 p.2 - ω p.1 p.2)
      (volume.restrict (slab T)) :=
    hub.aestronglyMeasurable.sub hlim.weakSolution.memX.aestronglyMeasurable
  set G' := hG.mk _ with hG'
  have hG'm : Measurable G' := hG.stronglyMeasurable_mk.measurable
  have hGG' := hG.ae_eq_mk
  set Φ : ℝ × ℂ → ℝ := fun p =>
    if p.2 ∈ ball (0 : ℂ) R then (if 0 ≤ G' p then 1 else -1) else 0 with hΦdef
  have hΦm : Measurable Φ :=
    Measurable.ite (measurableSet_ball.preimage measurable_snd)
      (Measurable.ite (measurableSet_le measurable_const hG'm) measurable_const measurable_const)
      measurable_const
  have hΦb : ∀ p, |Φ p| ≤ 1 := by
    intro p; simp only [hΦdef]; split_ifs <;> norm_num
  have hΦR : ∀ p : ℝ × ℂ, R ≤ ‖p.2‖ → Φ p = 0 := by
    intro p hp
    have : p.2 ∉ ball (0 : ℂ) R := by simpa using hp
    simp only [hΦdef, this, ↓reduceIte]
  have hΦb' : ∀ᵐ p ∂(volume.restrict (slab T)), ‖Φ p‖ ≤ 1 :=
    Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hΦb p
  -- integrability
  have hiub : Integrable (fun p : ℝ × ℂ => ub p.1 p.2 * Φ p) (volume.restrict (slab T)) :=
    (integrableOn_slab_of_memLinfLp hub).mul_bdd hΦm.aestronglyMeasurable hΦb'
  have hiω : Integrable (fun p : ℝ × ℂ => ω p.1 p.2 * Φ p) (volume.restrict (slab T)) :=
    (limit_integrableOn_slab hseq hlim).mul_bdd hΦm.aestronglyMeasurable hΦb'
  have hiωn : ∀ n, Integrable (fun p : ℝ × ℂ => ωs n p.1 p.2 * Φ p)
      (volume.restrict (slab T)) := fun n =>
    (seq_integrableOn_slab hseq n).mul_bdd hΦm.aestronglyMeasurable hΦb'
  have hitn : ∀ n, Integrable (fun p : ℝ × ℂ => trunc k (ωs n p.1 p.2) * Φ p)
      (volume.restrict (slab T)) := by
    intro n
    have hti : Integrable (fun p : ℝ × ℂ => trunc k (ωs n p.1 p.2)) (volume.restrict (slab T)) :=
      Integrable.mono' (seq_integrableOn_slab hseq n).norm
        ((lipschitzWith_trunc k).continuous.comp_aestronglyMeasurable
          (hseq.weakSolution n).memX.aestronglyMeasurable)
        (Eventually.of_forall fun p => by
          simp only [Real.norm_eq_abs]
          exact abs_trunc_le_abs hk.le _)
    exact hti.mul_bdd hΦm.aestronglyMeasurable hΦb'
  -- (A) the `L¹` norm is the pairing with `Φ`
  have hA : ∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖ub p.1 p.2 - ω p.1 p.2‖ₑ =
      ‖∫ p in slab T, (ub p.1 p.2 - ω p.1 p.2) * Φ p‖ₑ := by
    have hS : MeasurableSet ((univ : Set ℝ) ×ˢ ball (0 : ℂ) R) :=
      MeasurableSet.univ.prod measurableSet_ball
    have heq : (fun p : ℝ × ℂ => (ub p.1 p.2 - ω p.1 p.2) * Φ p) =ᵐ[volume.restrict (slab T)]
        ((univ : Set ℝ) ×ˢ ball (0 : ℂ) R).indicator
          (fun p : ℝ × ℂ => ‖ub p.1 p.2 - ω p.1 p.2‖) := by
      filter_upwards [hGG'] with p hp
      have hp' : ub p.1 p.2 - ω p.1 p.2 = G' p := hp
      by_cases hpb : p.2 ∈ ball (0 : ℂ) R
      · have hmem : p ∈ (univ : Set ℝ) ×ˢ ball (0 : ℂ) R := ⟨mem_univ _, hpb⟩
        rw [indicator_of_mem hmem, Real.norm_eq_abs, hp']
        simp only [hΦdef, hpb, ↓reduceIte]
        split_ifs with h0
        · rw [mul_one, abs_of_nonneg h0]
        · rw [mul_neg_one, abs_of_neg (not_le.1 h0)]
      · have hmem : p ∉ (univ : Set ℝ) ×ˢ ball (0 : ℂ) R := fun h => hpb h.2
        rw [indicator_of_notMem hmem]
        simp only [hΦdef, hpb, ↓reduceIte, mul_zero]
    have hGS : Integrable (fun p : ℝ × ℂ => ub p.1 p.2 - ω p.1 p.2)
        (volume.restrict (Ioo 0 T ×ˢ ball (0 : ℂ) R)) :=
      ((integrableOn_slab_of_memLinfLp hub).sub (limit_integrableOn_slab hseq hlim)).mono_set
        (Ioo_prod_ball_subset_slab T R)
    rw [integral_congr_ae heq, integral_indicator hS, Measure.restrict_restrict hS,
      prod_ball_inter_slab, Real.enorm_of_nonneg (integral_nonneg fun p => norm_nonneg _),
      ofReal_integral_norm_eq_lintegral_enorm hGS]
  -- (B) the bound for every `n`
  have hB : ∀ n, ‖∫ p in slab T, (ub p.1 p.2 - ω p.1 p.2) * Φ p‖ₑ ≤
      (∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖trunc k (ωs n p.1 p.2) - ub p.1 p.2‖ₑ) + Ck +
        ‖(∫ p in slab T, ωs n p.1 p.2 * Φ p) - ∫ p in slab T, ω p.1 p.2 * Φ p‖ₑ := by
    intro n
    have e1 : ∫ p in slab T, (ub p.1 p.2 - ω p.1 p.2) * Φ p =
        (∫ p in slab T, (ub p.1 p.2 - trunc k (ωs n p.1 p.2)) * Φ p) +
        (∫ p in slab T, (trunc k (ωs n p.1 p.2) - ωs n p.1 p.2) * Φ p) +
        ((∫ p in slab T, ωs n p.1 p.2 * Φ p) - ∫ p in slab T, ω p.1 p.2 * Φ p) := by
      simp only [sub_mul]
      rw [integral_sub hiub hiω, integral_sub hiub (hitn n), integral_sub (hitn n) (hiωn n)]
      ring
    rw [e1]
    refine (enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans
      (add_le_add ?_ ?_)) le_rfl)
    · refine (enorm_integral_le_lintegral_enorm _).trans
        ((lintegral_slab_mul_le hΦb hΦR _).trans ?_)
      exact le_of_eq (lintegral_congr fun p => enorm_sub_rev _ _)
    · refine (enorm_integral_le_lintegral_enorm _).trans
        ((lintegral_slab_mul_le hΦb hΦR _).trans ?_)
      refine (lintegral_mono_set (Ioo_prod_ball_subset_slab T R)).trans ?_
      refine (le_of_eq (lintegral_congr fun p => enorm_sub_rev _ _)).trans ?_
      exact lintegral_sub_trunc_le hseq n hk
  -- (C) pass to the limit
  have hlimB : Tendsto (fun n =>
      (∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖trunc k (ωs n p.1 p.2) - ub p.1 p.2‖ₑ) + Ck +
        ‖(∫ p in slab T, ωs n p.1 p.2 * Φ p) - ∫ p in slab T, ω p.1 p.2 * Φ p‖ₑ) atTop
      (𝓝 (0 + Ck + 0)) := by
    refine (hconv.add tendsto_const_nhds).add ?_
    have h := tendsto_integral_slab_mul hseq hlim hΦm hΦb hΦR
    have h' : Tendsto (fun n => (∫ p in slab T, ωs n p.1 p.2 * Φ p) -
        ∫ p in slab T, ω p.1 p.2 * Φ p) atTop (𝓝 0) := by
      simpa using h.sub_const (∫ p in slab T, ω p.1 p.2 * Φ p)
    have h'' := (continuous_enorm.tendsto (0 : ℝ)).comp h'
    rw [enorm_zero] at h''
    exact h''
  rw [hA]
  simpa using ge_of_tendsto' hlimB hB

/-! ### Strong convergence in `L¹((0,T) × B_R)` -/

theorem tendsto_truncConst (T M : ℝ) :
    Tendsto (fun j : ℕ => ENNReal.ofReal T *
      (ENNReal.ofReal (1 / ((j : ℝ) + 1)) * ENNReal.ofReal M ^ 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) :
    (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal M ^ 2 ≠ ∞)
  have h3 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal T) h2
    (Or.inr ENNReal.ofReal_ne_top)
  simpa using h3

/-- **Strong convergence in space–time** (`03_compactness.tex:791-800`): `ωₙ → ω` in
`L¹((0,T) × B_R)` for every `R > 0` (for the whole sequence). -/
theorem stable_tendsto_slab (hseq : IsCompactSeq T M gs g ωs) (hlim : IsCompactLimit T g ωs ω)
    (hstrong : Tendsto (fun n => normL1LpE 2 (gs n - g)) atTop (𝓝 0))
    (hren : ∀ n, IsRenormalizedWeakSolution 2 T (gs n) (ωs n)) :
    ∀ R : ℝ, 0 < R →
      Tendsto (fun n => ∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖ωs n p.1 p.2 - ω p.1 p.2‖ₑ) atTop
        (𝓝 0) := by
  intro R hR
  by_contra hcon
  rw [ENNReal.tendsto_atTop_zero] at hcon
  push Not at hcon
  obtain ⟨ε, hε, hfreq⟩ := hcon
  have hfr : ∃ᶠ n in atTop,
      ε < ∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖ωs n p.1 p.2 - ω p.1 p.2‖ₑ :=
    Filter.frequently_atTop.2 hfreq
  obtain ⟨ψ, hψ, hψε⟩ := extraction_of_frequently_atTop hfr
  set C : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal T *
    (ENNReal.ofReal (1 / ((j : ℝ) + 1)) * ENNReal.ofReal M ^ 2) with hCdef
  have hC2 : Tendsto (fun j => C j + C j) atTop (𝓝 0) := by
    have h := (tendsto_truncConst T M).add (tendsto_truncConst T M)
    rw [add_zero] at h
    exact h
  obtain ⟨j, hj⟩ := (hC2.eventually (gt_mem_nhds hε)).exists
  set k : ℝ := (j : ℝ) + 1 with hkdef
  have hk : 0 < k := by positivity
  have hseq' := hseq.subseq hψ
  have hlim' := hlim.subseq hψ
  have hstrong' : Tendsto (fun n => normL1LpE 2 (gs (ψ n) - g)) atTop (𝓝 0) :=
    hstrong.comp hψ.tendsto_atTop
  obtain ⟨φ, hφ, ub, hub, hconv⟩ := stable_bddRenorm hseq' hlim' hstrong'
    (fun n => hren (ψ n)) (isLipO_trunc hk.le) (abs_trunc_le hk.le)
  have hconvR := hconv R hR
  have hseq'' := hseq'.subseq hφ
  have hlim'' := hlim'.subseq hφ
  have hid := lintegral_sub_limit_le hseq'' hlim'' hk hub hconvR
  -- the bound along `ψ ∘ φ`
  have hS : MeasurableSet (Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R) :=
    measurableSet_Ioo.prod measurableSet_ball
  have hbound : ∀ n, (∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R,
      ‖ωs (ψ (φ n)) p.1 p.2 - ω p.1 p.2‖ₑ) ≤ (C j + C j) +
        ∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖trunc k (ωs (ψ (φ n)) p.1 p.2) - ub p.1 p.2‖ₑ := by
    intro n
    set m := ψ (φ n)
    have hmS : AEStronglyMeasurable (Function.uncurry (ωs m))
        (volume.restrict (Ioo 0 T ×ˢ ball (0 : ℂ) R)) :=
      (hseq.weakSolution m).memX.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono (Ioo_prod_ball_subset_slab T R) le_rfl)
    have hubS : AEStronglyMeasurable (Function.uncurry ub)
        (volume.restrict (Ioo 0 T ×ˢ ball (0 : ℂ) R)) :=
      hub.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono (Ioo_prod_ball_subset_slab T R) le_rfl)
    have htS : AEStronglyMeasurable (fun p : ℝ × ℂ => trunc k (ωs m p.1 p.2))
        (volume.restrict (Ioo 0 T ×ˢ ball (0 : ℂ) R)) :=
      (lipschitzWith_trunc k).continuous.comp_aestronglyMeasurable hmS
    have hpt : ∀ p : ℝ × ℂ, ‖ωs m p.1 p.2 - ω p.1 p.2‖ₑ ≤
        ‖ωs m p.1 p.2 - trunc k (ωs m p.1 p.2)‖ₑ +
          ‖trunc k (ωs m p.1 p.2) - ub p.1 p.2‖ₑ + ‖ub p.1 p.2 - ω p.1 p.2‖ₑ := by
      intro p
      have e : ωs m p.1 p.2 - ω p.1 p.2 = (ωs m p.1 p.2 - trunc k (ωs m p.1 p.2)) +
          (trunc k (ωs m p.1 p.2) - ub p.1 p.2) + (ub p.1 p.2 - ω p.1 p.2) := by ring
      rw [e]
      exact (enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)
    refine (lintegral_mono hpt).trans ?_
    have hf1 : AEMeasurable (fun p : ℝ × ℂ => ‖ωs m p.1 p.2 - trunc k (ωs m p.1 p.2)‖ₑ)
        (volume.restrict (Ioo 0 T ×ˢ ball (0 : ℂ) R)) := (hmS.sub htS).enorm
    have hf2 : AEMeasurable (fun p : ℝ × ℂ => ‖trunc k (ωs m p.1 p.2) - ub p.1 p.2‖ₑ)
        (volume.restrict (Ioo 0 T ×ˢ ball (0 : ℂ) R)) := (htS.sub hubS).enorm
    have hf12 : AEMeasurable (fun p : ℝ × ℂ => ‖ωs m p.1 p.2 - trunc k (ωs m p.1 p.2)‖ₑ +
        ‖trunc k (ωs m p.1 p.2) - ub p.1 p.2‖ₑ)
        (volume.restrict (Ioo 0 T ×ˢ ball (0 : ℂ) R)) := hf1.add hf2
    rw [lintegral_add_left' hf12, lintegral_add_left' hf1]
    have h1 : (∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖ωs m p.1 p.2 - trunc k (ωs m p.1 p.2)‖ₑ) ≤
        C j :=
      (lintegral_mono_set (Ioo_prod_ball_subset_slab T R)).trans
        (lintegral_sub_trunc_le hseq m hk)
    calc (∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖ωs m p.1 p.2 - trunc k (ωs m p.1 p.2)‖ₑ) +
          (∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖trunc k (ωs m p.1 p.2) - ub p.1 p.2‖ₑ) +
          (∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖ub p.1 p.2 - ω p.1 p.2‖ₑ)
        ≤ C j + (∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖trunc k (ωs m p.1 p.2) - ub p.1 p.2‖ₑ) +
            C j := add_le_add (add_le_add h1 le_rfl) hid
      _ = (C j + C j) +
            ∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖trunc k (ωs m p.1 p.2) - ub p.1 p.2‖ₑ := by
          ring
  -- contradiction
  have hδ : 0 < ε - (C j + C j) := tsub_pos_of_lt hj
  obtain ⟨n, hn⟩ := (hconvR.eventually (gt_mem_nhds hδ)).exists
  have hfin : C j + C j ≠ ∞ := hj.ne_top
  have hlt : (∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖ωs (ψ (φ n)) p.1 p.2 - ω p.1 p.2‖ₑ) < ε :=
    calc _ ≤ _ := hbound n
      _ < (C j + C j) + (ε - (C j + C j)) := ENNReal.add_lt_add_left hfin hn
      _ = ε := add_tsub_cancel_of_le hj.le
  exact lt_asymm (hψε (φ n)) hlt

end NonUniqueEuler.Compact.StableAux
