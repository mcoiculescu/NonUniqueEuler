import NonUniqueEuler.Defs.SmoothB.Iteration
import NonUniqueEuler.I.SmoothB.Iterates
import NonUniqueEuler.I.SmoothB.IterHs
import NonUniqueEuler.I.SmoothB.IterCauchy
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Infra.Sobolev.EmbedLinf
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.Interp
import NonUniqueEuler.I.Infra.Sobolev.Norm
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Proof: `prop:iter-limit`, step 1 — the spatial derivatives of the iterates are uniformly Cauchy

Proof of `I/SmoothB/IterLimit/Cauchy.lean` (`B_global_smooth.tex:401-411`).

For `t ∈ [-T, T]`, `i ≤ j`, `d = ω^{[j]}(t) - ω^{[i]}(t)` (complex valued, a test function) and
`K = 2 + |γ|`:
* `|∂^γ d(x)|² ≤ ‖∂^γ d‖²_{H²} = ‖weakPartial γ d‖²_{H²} ≤ ‖d‖²_{H^K} ≤ 3^K ‖d‖_{L²} ‖d‖_{H^{2K}}`
  (`norm_partialD_sq_le`: (E2), `MemH.congr_ae`, `MemH.weakPartial`, (E3));
* `‖d‖_{H^{2K}} ≤ 2 𝓜_{2K}(T)` (`iter_Hs`, `MemH.sub`);
* `‖d‖_{L²} ≤ ∑_{m ≥ i} 2‖ω₀‖₂ (|2R(T)Ψ(T)| T)^m / m!` (telescoping and `iter_cauchy`), the tail
  of a convergent series (`exists_l2_bound`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff Nat

namespace NonUniqueEuler.Smooth

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

namespace IterLimitCauchyAux

/-! ### Classical derivatives of smooth functions -/

theorem contDiff_iterDirDeriv {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (vs : List ℂ) :
    ContDiff ℝ ∞ (Sob.iterDirDeriv vs f) := by
  induction vs with
  | nil => simpa using hf
  | cons v vs ih =>
    simp only [Sob.iterDirDeriv_cons]
    exact (ContDiff.fderiv_right (m := ∞) ih (by simp)).clm_apply contDiff_const

theorem iterDirDeriv_sub {f g : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (vs : List ℂ) :
    Sob.iterDirDeriv vs (f - g) = Sob.iterDirDeriv vs f - Sob.iterDirDeriv vs g := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [Sob.iterDirDeriv_cons, ih]
    funext x
    have h1 : DifferentiableAt ℝ (Sob.iterDirDeriv vs f) x :=
      ((contDiff_iterDirDeriv hf vs).differentiable (by simp)) x
    have h2 : DifferentiableAt ℝ (Sob.iterDirDeriv vs g) x :=
      ((contDiff_iterDirDeriv hg vs).differentiable (by simp)) x
    simp only [Sob.dirDeriv, Pi.sub_apply, fderiv_sub h1 h2, _root_.sub_apply]

/-! ### The slices of the iterates -/

theorem contDiff_iter_slice (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (iter ω₀ j t) :=
  (iterates_smooth_support h hne j).1.comp (contDiff_const.prodMk contDiff_id)

theorem contDiff_ofRealST_iter (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (ofRealST (iter ω₀ j) t) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_iter_slice h hne j t)

theorem iter_eq_zero_of_far (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) (x : ℂ)
    (hx : R₀ + Ustar ω₀ * |t| < ‖x‖) : iter ω₀ j t x = 0 := by
  refine (iterates_smooth_support h hne j).2 R₀ (fun y hy => ?_) t x hx
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hb := h.tsupport_subset hmem
  rw [mem_ball_zero_iff] at hb
  linarith

theorem hasCompactSupport_ofRealST_iter (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ)
    (t : ℝ) : HasCompactSupport (ofRealST (iter ω₀ j) t) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R₀ + Ustar ω₀ * |t|))
    fun x hx => ?_
  rw [mem_closedBall_zero_iff, not_le] at hx
  simp [ofRealST, iter_eq_zero_of_far h hne j t x hx]

/-- `d = ω^{[j]}(t) - ω^{[i]}(t)` (complex valued) is a test function. -/
theorem isTestFn_sub (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (i j : ℕ) (t : ℝ) :
    Sob.IsTestFn univ (ofRealST (iter ω₀ j) t - ofRealST (iter ω₀ i) t) :=
  ⟨ContDiff.sub (contDiff_ofRealST_iter h hne j t) (contDiff_ofRealST_iter h hne i t),
    (hasCompactSupport_ofRealST_iter h hne j t).sub (hasCompactSupport_ofRealST_iter h hne i t),
    subset_univ _⟩

/-! ### The pointwise bound by (E2) and (E3) -/

/-- `|∂^γ d(x)|² ≤ 3^K ‖d‖_{L²} ‖d‖_{H^{2K}}` for a test function `d`, `K = 2 + |γ|`
(`B_global_smooth.tex:405-408`). -/
theorem norm_partialD_sq_le {d : ℂ → ℂ} (hd : Sob.IsTestFn univ d) (γ : ℕ × ℕ) (x : ℂ) :
    ‖Sob.partialD γ d x‖ ^ 2 ≤
      3 ^ (2 + (γ.1 + γ.2)) * Sob.l2 d * Sob.normH (2 * (2 + (γ.1 + γ.2))) d := by
  obtain ⟨hdK, hae, -⟩ :=
    Sob.memH_of_contDiff_hasCompactSupport hd.smooth hd.compact (2 + (γ.1 + γ.2))
  have hpd := hd.partialD γ
  have h1 : ‖Sob.partialD γ d x‖ ≤ Sob.normH 2 (Sob.partialD γ d) :=
    Sob.norm_le_normH_two_of_continuous (hpd.memH 2) hpd.continuous x
  obtain ⟨hw, hwle⟩ := Sob.MemH.weakPartial (k := 2) (γ := γ) hdK
  have hγ : γ ∈ Sob.multiIdx (2 + (γ.1 + γ.2)) := Sob.mem_multiIdx.2 (by omega)
  have h2 : Sob.normH 2 (Sob.partialD γ d) = Sob.normH 2 (Sob.weakPartial γ d) :=
    (hw.congr_ae (hae γ hγ)).2
  have h3 := Sob.interp (k := 2 + (γ.1 + γ.2))
    (Sob.memH_of_contDiff_hasCompactSupport hd.smooth hd.compact _).1
  calc ‖Sob.partialD γ d x‖ ^ 2 ≤ Sob.normH 2 (Sob.partialD γ d) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = Sob.normH 2 (Sob.weakPartial γ d) ^ 2 := by rw [h2]
    _ ≤ Sob.normH (2 + (γ.1 + γ.2)) d ^ 2 := pow_le_pow_left₀ (Sob.normH_nonneg _ _) hwle 2
    _ ≤ _ := h3

/-! ### The `L²` bound -/

theorem continuous_iter_slice (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) :
    Continuous (iter ω₀ j t) :=
  (contDiff_iter_slice h hne j t).continuous

/-- Telescoping: `‖ω^{[i+n]}(t) - ω^{[i]}(t)‖₂ ≤ ∑_{m < n} ‖ω^{[i+m+1]}(t) - ω^{[i+m]}(t)‖₂`. -/
theorem eLpNorm_iter_sub_le_sum (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) (i : ℕ) :
    ∀ n : ℕ, eLpNorm (iter ω₀ (i + n) t - iter ω₀ i t) 2 volume ≤
      ∑ m ∈ Finset.range n, eLpNorm (iter ω₀ (i + m + 1) t - iter ω₀ (i + m) t) 2 volume
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ]
    have hdec : iter ω₀ (i + (n + 1)) t - iter ω₀ i t =
        (iter ω₀ (i + n) t - iter ω₀ i t) + (iter ω₀ (i + n + 1) t - iter ω₀ (i + n) t) := by
      rw [show i + (n + 1) = i + n + 1 by omega]
      abel
    rw [hdec]
    refine (eLpNorm_add_le ?_ ?_ (by norm_num)).trans
      (add_le_add (eLpNorm_iter_sub_le_sum h hne t i n) le_rfl)
    · exact ((continuous_iter_slice h hne _ t).sub
        (continuous_iter_slice h hne _ t)).aestronglyMeasurable
    · exact ((continuous_iter_slice h hne _ t).sub
        (continuous_iter_slice h hne _ t)).aestronglyMeasurable

theorem coeff_le {L x y : ℝ} (hL : 0 ≤ L) (hxy : |x| ≤ y) (n : ℕ) :
    2 * L * x ^ n / (n ! : ℝ) ≤ 2 * L * (y ^ n / (n ! : ℝ)) := by
  rw [mul_div_assoc]
  have hx : x ^ n ≤ y ^ n :=
    (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hxy n)
  gcongr

/-- `sup_{|t| ≤ T} ‖ω^{[j]}(t) - ω^{[i]}(t)‖_{L²} ≤ b i` for `i ≤ j`, with `b i → 0`
(`B_global_smooth.tex:401-404`). -/
theorem exists_l2_bound (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) {T : ℝ} (hT : 0 < T) :
    ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧ (∀ i, 0 ≤ b i) ∧
      ∀ i j : ℕ, i ≤ j → ∀ t ∈ Icc (-T) T,
        eLpNorm (iter ω₀ j t - iter ω₀ i t) 2 volume ≤ ENNReal.ofReal (b i) := by
  set L : ℝ := (eLpNorm ω₀ 2 volume).toReal with hLdef
  set c : ℝ := |2 * suppRadius ω₀ R₀ T * Psi ω₀ T| * T with hcdef
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  set a : ℕ → ℝ := fun m => 2 * L * (c ^ m / (m ! : ℝ)) with hadef
  have ha0 : ∀ m, 0 ≤ a m := fun m => by
    have hc : 0 ≤ c := mul_nonneg (abs_nonneg _) hT.le
    positivity
  have has : Summable a := (Real.summable_pow_div_factorial c).mul_left (2 * L)
  refine ⟨fun i => ∑' m, a (m + i), tendsto_sum_nat_add a, fun i => tsum_nonneg fun m => ha0 _,
    fun i j hij t ht => ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hij
  refine (eLpNorm_iter_sub_le_sum h hne t i n).trans ?_
  have hterm : ∀ m ∈ Finset.range n,
      eLpNorm (iter ω₀ (i + m + 1) t - iter ω₀ (i + m) t) 2 volume ≤
        ENNReal.ofReal (a (m + i)) := by
    intro m _
    have hc := iter_cauchy h hne hT (j := i + m + 1) (by omega) ht
    rw [show i + m + 1 - 1 = i + m by omega] at hc
    refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [show m + i = i + m by omega]
    refine coeff_le hL ?_ _
    rw [abs_mul, abs_abs]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith [ht.1], ht.2⟩) (abs_nonneg _)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun m _ => ha0 _]
  refine ENNReal.ofReal_le_ofReal ?_
  exact ((summable_nat_add_iff i).2 has).sum_le_tsum _ fun m _ => ha0 _

/-! ### The uniform bound on the derivatives -/

theorem l2_sub_eq (j i : ℕ) (t : ℝ) :
    Sob.l2 (ofRealST (iter ω₀ j) t - ofRealST (iter ω₀ i) t) =
      (eLpNorm (iter ω₀ j t - iter ω₀ i t) 2 volume).toReal := by
  unfold Sob.l2
  congr 1
  refine eLpNorm_congr_norm_ae (ae_of_all _ fun x => ?_)
  simp only [Pi.sub_apply, ofRealST]
  rw [← Complex.ofReal_sub, Complex.norm_real]

theorem exists_spaceD_bound (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) {T : ℝ} (hT : 0 < T)
    (γ : ℕ × ℕ) :
    ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧
      ∀ i j : ℕ, i ≤ j → ∀ t ∈ Icc (-T) T, ∀ x : ℂ,
        ‖spaceD γ (ofRealST (iter ω₀ j)) t x - spaceD γ (ofRealST (iter ω₀ i)) t x‖ ≤ b i := by
  obtain ⟨b, hb0, hbnn, hb⟩ := exists_l2_bound h hne hT
  set K : ℕ := 2 + (γ.1 + γ.2) with hK
  set M : ℝ := calM ω₀ R₀ (2 * K) T with hM
  refine ⟨fun i => Real.sqrt (3 ^ K * b i * (2 * M)), ?_, fun i j hij t ht x => ?_⟩
  · have := ((hb0.const_mul ((3 : ℝ) ^ K)).mul_const (2 * M)).sqrt
    simpa using this
  have htT : |t| ≤ T := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
  have hd := isTestFn_sub h hne i j t
  have hsub : spaceD γ (ofRealST (iter ω₀ j)) t x - spaceD γ (ofRealST (iter ω₀ i)) t x =
      Sob.partialD γ (ofRealST (iter ω₀ j) t - ofRealST (iter ω₀ i) t) x := by
    simp only [spaceD, Sob.partialD]
    rw [iterDirDeriv_sub (contDiff_ofRealST_iter h hne j t) (contDiff_ofRealST_iter h hne i t)]
    rfl
  rw [hsub]
  refine (abs_norm _).symm.le.trans (Real.abs_le_sqrt ?_)
  refine (norm_partialD_sq_le hd γ x).trans ?_
  have hHs : 1 ≤ 2 * K := by omega
  obtain ⟨hmj, hnj⟩ := iter_Hs h hne hHs hT j htT
  obtain ⟨hmi, hni⟩ := iter_Hs h hne hHs hT i htT
  have hH : Sob.normH (2 * K) (ofRealST (iter ω₀ j) t - ofRealST (iter ω₀ i) t) ≤ 2 * M := by
    have := (Sob.MemH.sub hmj hmi).2
    refine this.trans ((add_le_add hnj hni).trans ?_)
    rw [hM]
    linarith
  have hl2 : Sob.l2 (ofRealST (iter ω₀ j) t - ofRealST (iter ω₀ i) t) ≤ b i := by
    rw [l2_sub_eq]
    exact ENNReal.toReal_le_of_le_ofReal (hbnn i) (hb i j hij t ht)
  have h3 : (0 : ℝ) ≤ 3 ^ K := by positivity
  calc 3 ^ K * Sob.l2 (ofRealST (iter ω₀ j) t - ofRealST (iter ω₀ i) t) *
        Sob.normH (2 * K) (ofRealST (iter ω₀ j) t - ofRealST (iter ω₀ i) t)
      ≤ 3 ^ K * b i * (2 * M) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hl2 h3) hH (Sob.normH_nonneg _ _)
          (mul_nonneg h3 (hbnn i))

end IterLimitCauchyAux

open IterLimitCauchyAux in
/-- `prop:iter-limit`, step 1 (`B_global_smooth.tex:401-411`): for `T > 0` and every multi-index
`γ`, `(∂_x^γ ω^{[j]})_j` is a uniform Cauchy sequence on `[-T, T] × ℝ²`. -/
theorem iter_spaceD_uniformCauchySeqOn (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) {T : ℝ}
    (hT : 0 < T) (γ : ℕ × ℕ) :
    UniformCauchySeqOn (fun (j : ℕ) (p : ℝ × ℂ) => spaceD γ (ofRealST (iter ω₀ j)) p.1 p.2)
      atTop (Icc (-T) T ×ˢ univ) := by
  obtain ⟨b, hb0, hb⟩ := exists_spaceD_bound h hne hT γ
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hb0).2 ε hε)
  refine ⟨N, fun m hm n hn p hp => ?_⟩
  rw [dist_eq_norm]
  rcases le_total m n with hmn | hnm
  · rw [norm_sub_rev]
    exact (hb m n hmn p.1 hp.1 p.2).trans_lt (hN m hm)
  · exact (hb n m hnm p.1 hp.1 p.2).trans_lt (hN n hn)

end NonUniqueEuler.Smooth
