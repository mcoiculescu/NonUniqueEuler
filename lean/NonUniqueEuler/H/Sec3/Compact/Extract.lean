import NonUniqueEuler.H.Sec3.Compact.Basic
import NonUniqueEuler.I.Sec3.WeakCont
import NonUniqueEuler.I.Sec3.WeakContRep
import NonUniqueEuler.I.Sec3.VelocityField
import NonUniqueEuler.I.Sec2.Velocity
import NonUniqueEuler.I.Infra.WeakL2.Paths
import NonUniqueEuler.I.Infra.WeakL2.TestFamily

/-!
# Helpers for `prop:compact`: extraction of a weakly convergent subsequence

Helper file of `P/Sec3/Compact.lean`. Manuscript: proof of `prop:compact`, first paragraph
(`03_compactness.tex:273-290`).

* `seq_lipschitz`: by `lem:weak-cont`(b) (`Weak.weakCont`, applied to `ωₙ` with field `vₙ`, and
  identified with `ωₙ` by uniqueness of weakly continuous representatives,
  `Weak.ae_eq_of_isWeakContL2On`) and `lem:velocity`(a) (`‖vₙ(t)‖_{L²(B_R)} ≤ C(2,R) M`), the
  functions `t ↦ ∫ ωₙ(t) ψ`, `ψ ∈ C_c^∞(B_R)`, are Lipschitz on `[0,T]` uniformly in `n`.
* `exists_subseq_weakLimit`: weak Arzelà–Ascoli over the countable test family
  (`WeakL2.exists_subseq_weakTendstoUniformlyOn`, `WeakL2.exists_isTestFamily`) gives a
  subsequence and a weakly continuous `L²`-valued limit path `U` with `‖U(t)‖₂ ≤ M`, the uniform
  weak limit of the paths `t ↦ [ωₙ(t)]`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace

namespace NonUniqueEuler.Compact.PropCompact

open Weak

variable {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}

/-- A smooth function with `tsupport ψ ⊆ B_R` has compact support. -/
theorem hasCompactSupport_of_tsupport_subset_ball {ψ : ℂ → ℝ} {R : ℝ}
    (hψR : tsupport ψ ⊆ ball (0 : ℂ) R) : HasCompactSupport ψ :=
  (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset (isClosed_tsupport ψ)
    (hψR.trans ball_subset_closedBall)

/-- `lem:weak-cont`(b) for the members of the sequence: `t ↦ ∫ ωₙ(t) ψ` is Lipschitz on `[0,T]`
with constant `M · C M · G`, independent of `n` (`03_compactness.tex:277-281`). -/
theorem seq_lipschitz (h : IsCompactSeq T M gs g ωs) (hM : 0 ≤ M) {R : ℝ}
    {C : ℝ} (hC0 : 0 < C)
    (hC : ∀ ω : ℂ → ℝ, MemLp ω 1 volume → MemLp ω 2 volume →
      eLpNorm (velocity ω) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
        ENNReal.ofReal (C * Prelim.normL1Lp 2 ω))
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψR : tsupport ψ ⊆ ball (0 : ℂ) R) {G : ℝ} (hG : ∀ x, ‖fderiv ℝ ψ x‖ ≤ G) (n : ℕ)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    |(∫ x, ωs n t x * ψ x) - ∫ x, ωs n s x * ψ x| ≤ M * (C * M) * G * |t - s| := by
  have hT := h.T_pos
  have hws := h.weakSolution n
  have hw : ∀ R' : ℝ, 0 < R' →
      Prelim.MemLinfLp (Ioo 0 T) (ball (0 : ℂ) R') 2 (velocityField (ωs n)) :=
    fun R' hR' => (hws.memLinfLp_velocityField hR').1
  have hu : Prelim.MemLinfLp (Ioo 0 T) univ 2 (ωs n) := by
    have := (Prelim.memX_iff.1 hws.memX).2
    simpa using this
  have hu₀ : LocallyIntegrable (gs n) volume :=
    (memLp_one_iff_integrable.1 (h.memLp_one_seq n)).locallyIntegrable
  have hN : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)), eLpNorm (ωs n τ) 2 volume ≤ ENNReal.ofReal M :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun τ hτ =>
      seq_eLpNorm_two_le h n (Ioo_subset_Icc_self hτ)
  obtain ⟨ũ, -, hũc, -, hũae, -, -, -, -, -, hlip, -⟩ :=
    weakCont hT hM hw hu hu₀ hws.solvesTE hN
  have heq : ∀ τ ∈ Icc 0 T, ũ τ =ᵐ[volume] ωs n τ :=
    ae_eq_of_isWeakContL2On hT hũc (h.weakCont n) hũae
  have hW : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      eLpNorm (velocityField (ωs n) τ) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
        ENNReal.ofReal (C * M) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioo fun τ hτ => ?_
    have hτ' := Ioo_subset_Icc_self hτ
    refine (hC _ (seq_memLp_one h n hτ') (seq_memLp_two h n hτ')).trans ?_
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (seq_normL1Lp_le h hM n hτ') hC0.le)
  have hb := hlip ψ R (C * M) G hψ hψR (mul_nonneg hC0.le hM) hW hG s hs t ht
  have hψ2 : MemLp ψ 2 volume :=
    hψ.continuous.memLp_of_hasCompactSupport (hasCompactSupport_of_tsupport_subset_ball hψR)
  have hint : ∫ x, (ũ t x - ũ s x) * ψ x =
      (∫ x, ωs n t x * ψ x) - ∫ x, ωs n s x * ψ x := by
    rw [← integral_sub (integrable_mul_of_L2 (seq_memLp_two h n ht) hψ2)
      (integrable_mul_of_L2 (seq_memLp_two h n hs) hψ2)]
    refine integral_congr_ae ?_
    filter_upwards [heq t ht, heq s hs] with x hxt hxs
    rw [hxt, hxs, sub_mul]
  rw [← hint]
  exact hb

/-- **Step 1 of the proof of `prop:compact`** (`03_compactness.tex:273-290`): a subsequence of
the `L²` paths `t ↦ [ωₙ(t)]` converges weakly, uniformly on `[0,T]`, to a weakly continuous path
`U` with `‖U(t)‖₂ ≤ M`. -/
theorem exists_subseq_weakLimit (h : IsCompactSeq T M gs g ωs) (hM : 0 ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ U : ℝ → Lp ℝ 2 (volume : Measure ℂ),
      (∀ t ∈ Icc 0 T, ‖U t‖ ≤ M) ∧ WeakL2.WeakContinuousOn U (Icc 0 T) ∧
      WeakL2.WeakTendstoUniformlyOn
        (fun n t => (JointRep.toPath (μ := (volume : Measure ℂ)) (ωs (φ n)) t)) U atTop
        (Icc 0 T) := by
  obtain ⟨F, hF⟩ := WeakL2.exists_isTestFamily
  refine WeakL2.exists_subseq_weakTendstoUniformlyOn hF.denseRange_toL2
    (u := fun n t => (JointRep.toPath (μ := (volume : Measure ℂ)) (ωs n) t)) ?_ ?_
  · intro n t ht
    rw [JointRep.toPath_of_memLp (seq_memLp_two h n ht), Lp.norm_toLp]
    exact seq_toReal_eLpNorm_two_le h hM n ht
  · intro k
    obtain ⟨r₀, hr₀⟩ := (hF.hasCompactSupport k).isCompact.isBounded.subset_ball (0 : ℂ)
    have hR : 0 < max r₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hsub : tsupport (F k) ⊆ ball (0 : ℂ) (max r₀ 1) :=
      hr₀.trans (ball_subset_ball (le_max_left _ _))
    obtain ⟨G, hG⟩ := ((hF.contDiff k).continuous_fderiv (by simp)).bounded_above_of_compact_support
      ((hF.hasCompactSupport k).fderiv (𝕜 := ℝ))
    obtain ⟨C, hC0, hC⟩ := BS.velocity_bounds_two hR
    refine ⟨M * (C * M) * G, fun n s hs t ht => ?_⟩
    rw [WeakL2.IsTestFamily.toL2, inner_toPath_toLp (seq_memLp_two h n ht) (hF.memLp k 2),
      inner_toPath_toLp (seq_memLp_two h n hs) (hF.memLp k 2)]
    exact seq_lipschitz h hM hC0 (fun ω h1 h2 => (hC ω h1 h2).2.2.2.1) (hF.contDiff k) hsub
      hG n hs ht

end NonUniqueEuler.Compact.PropCompact
