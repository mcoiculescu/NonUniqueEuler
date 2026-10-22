import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import NonUniqueEuler.Defs.Infra.Sobolev
import NonUniqueEuler.I.Infra.Sobolev.Density
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.H.Infra.Sobolev.EmbedL4.Smooth

/-!
# Proof of `lem:embed` (E1), the Ladyzhenskaya inequality (library I-HK)

Manuscript: `02_prelim.tex:597-622`. Proof of `I/Infra/Sobolev/EmbedL4.lean`.

* The smooth case `∫ |φ|⁴ ≤ 2 ‖φ‖₂² (‖∂₁φ‖₂² + ‖∂₂φ‖₂²)` for `φ ∈ C¹_c` is
  `EmbedL4H.lintegral_enorm_pow_four_le_ofReal` (`H/Infra/Sobolev/EmbedL4/Smooth.lean`), following
  the manuscript (FTC on lines, Tonelli, Cauchy–Schwarz).
* Extension to `H^1`: approximate `g` by test functions `φ_n` in `H^1`
  (`MemH.exists_testFn_approx`); then `‖φ_n‖₂ → ‖g‖₂` and `‖∂_jφ_n‖₂ → ‖∂_jg‖₂`, and along a
  subsequence `φ_n → g` a.e. (convergence in measure); Fatou's lemma gives the inequality for
  `g`, in particular `g ∈ L⁴`.
* `‖g‖_{L⁴} ≤ ‖g‖_{H^1}` from `2a²(b² + c²) ≤ (a² + b² + c²)²`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace NonUniqueEuler.Sob

namespace EmbedL4P

/-- `|‖f‖₂ - ‖h‖₂| ≤ ‖f - h‖₂`. -/
theorem abs_l2_sub_le {f h : ℂ → ℂ} (hf : MemLp f 2 volume) (hh : MemLp h 2 volume) :
    |l2 f - l2 h| ≤ l2 (f - h) := by
  have e1 : l2 f = ‖hf.toLp f‖ := (Lp.norm_toLp f hf).symm
  have e2 : l2 h = ‖hh.toLp h‖ := (Lp.norm_toLp h hh).symm
  have e3 : l2 (f - h) = ‖hf.toLp f - hh.toLp h‖ := by
    rw [← MemLp.toLp_sub hf hh, Lp.norm_toLp]; rfl
  rw [e1, e2, e3]
  exact abs_norm_sub_norm_le _ _

theorem l2_sub_comm (f h : ℂ → ℂ) : l2 (f - h) = l2 (h - f) := by
  simp only [l2]
  rw [eLpNorm_sub_comm]

theorem partialD_zero_zero (φ : ℂ → ℂ) : partialD (0, 0) φ = φ := rfl

/-- The order-zero weak derivative of an `H^1` function is the function itself. -/
theorem l2_weakPartial_zero {g : ℂ → ℂ} (hg : MemH 1 g) : l2 (weakPartial (0, 0) g) = l2 g := by
  have hgL : MemLp g 2 volume := (memH_iff.1 hg).1
  have h0 : HasWeakDerivOn univ (pdList (0, 0)) g g := by
    intro φ _
    simp [pdList]
  have := hg.weakPartial_ae_eq (zero_mem_multiIdx 1) hgL h0
  simp only [l2]
  rw [eLpNorm_congr_ae this]

/-- `∂^γ (g - φ) = ∂^γ g - ∂^γ φ` a.e. for a test function `φ`. -/
theorem weakPartial_sub_testFn_ae {g φ : ℂ → ℂ} (hg : MemH 1 g) (hφ : IsTestFn univ φ)
    (hgφ : MemH 1 (g - φ)) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx 1) :
    weakPartial γ (g - φ) =ᵐ[volume] weakPartial γ g - partialD γ φ := by
  have h1 := hg.memLp_weakPartial hγ
  have hgL : MemLp g 2 volume := (memH_iff.1 hg).1
  have hφL : MemLp (partialD γ φ) 2 volume := (hφ.partialD γ).memLp 2 volume
  have hφs : ContDiff ℝ (γ.1 + γ.2 : ℕ) φ := contDiff_infty.1 hφ.smooth _
  have h2 : HasWeakDerivOn univ (pdList γ) φ (partialD γ φ) :=
    hasWeakDerivOn_of_contDiffOn isOpen_univ (by simp) hφs.contDiffOn
  have h3 := h2.const_mul (-1)
  have hli : ∀ {f : ℂ → ℂ}, MemLp f 2 volume → LocallyIntegrableOn f univ volume :=
    fun hf => (hf.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have h4 := HasWeakDerivOn.add isOpen_univ (hli hgL)
    (hli ((hφ.memLp 2 volume).const_mul (-1))) (hli h1.1) (hli (hφL.const_mul (-1))) h1.2 h3
  have e1 : (g + fun x => (-1 : ℂ) * φ x) = g - φ := by
    funext x; simp [sub_eq_add_neg]
  have e2 : (weakPartial γ g + fun x => (-1 : ℂ) * partialD γ φ x) =
      weakPartial γ g - partialD γ φ := by
    funext x; simp [sub_eq_add_neg]
  rw [e1, e2] at h4
  exact hgφ.weakPartial_ae_eq hγ (h1.1.sub hφL) h4

/-- Convergence of the `L²` norms of the derivatives along an `H^1` approximation by test
functions. -/
theorem tendsto_l2_partialD {g : ℂ → ℂ} (hg : MemH 1 g) {φ : ℕ → ℂ → ℂ}
    (hφ : ∀ n, IsTestFn univ (φ n)) (hgφ : ∀ n, MemH 1 (g - φ n))
    (hd : Tendsto (fun n => normH 1 (g - φ n)) atTop (𝓝 0)) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx 1) :
    Tendsto (fun n => l2 (partialD γ (φ n))) atTop (𝓝 (l2 (weakPartial γ g))) := by
  have h1 := hg.memLp_weakPartial hγ
  have hbound : ∀ n, ‖l2 (partialD γ (φ n)) - l2 (weakPartial γ g)‖ ≤ normH 1 (g - φ n) := by
    intro n
    have hφL : MemLp (partialD γ (φ n)) 2 volume := ((hφ n).partialD γ).memLp 2 volume
    rw [Real.norm_eq_abs]
    refine (abs_l2_sub_le hφL h1.1).trans ?_
    rw [l2_sub_comm]
    have hae := weakPartial_sub_testFn_ae hg (hφ n) (hgφ n) hγ
    have : l2 (weakPartial γ g - partialD γ (φ n)) = l2 (weakPartial γ (g - φ n)) := by
      simp only [l2]
      rw [eLpNorm_congr_ae hae]
    rw [this]
    exact (hgφ n).l2_weakPartial_le hγ
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun n => norm_nonneg _) hbound hd)

theorem one_zero_mem : ((1 : ℕ), (0 : ℕ)) ∈ multiIdx 1 := mem_multiIdx.2 (by norm_num)

theorem zero_one_mem : ((0 : ℕ), (1 : ℕ)) ∈ multiIdx 1 := mem_multiIdx.2 (by norm_num)

/-- The lower-integral form of (E1). -/
theorem lintegral_le {g : ℂ → ℂ} (hg : MemH 1 g) :
    ∫⁻ x, ‖g x‖ₑ ^ 4 ≤ ENNReal.ofReal (2 * l2 g ^ 2 *
      (l2 (weakPartial (1, 0) g) ^ 2 + l2 (weakPartial (0, 1) g) ^ 2)) := by
  have hgL : MemLp g 2 volume := (memH_iff.1 hg).1
  choose φ hφ hgφ hlt using fun n : ℕ =>
    hg.exists_testFn_approx (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  have hd : Tendsto (fun n => normH 1 (g - φ n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => normH_nonneg _ _) (fun n => (hlt n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hφL : ∀ n, MemLp (φ n) 2 volume := fun n => (hφ n).memLp 2 volume
  -- convergence of the three `L²` norms
  have ha : Tendsto (fun n => l2 (φ n)) atTop (𝓝 (l2 g)) := by
    have := tendsto_l2_partialD hg hφ hgφ hd (zero_mem_multiIdx 1)
    simpa only [partialD_zero_zero, l2_weakPartial_zero hg] using this
  have hb := tendsto_l2_partialD hg hφ hgφ hd one_zero_mem
  have hc := tendsto_l2_partialD hg hφ hgφ hd zero_one_mem
  set Q : ℝ := 2 * l2 g ^ 2 * (l2 (weakPartial (1, 0) g) ^ 2 + l2 (weakPartial (0, 1) g) ^ 2)
  set Qn : ℕ → ℝ := fun n => 2 * l2 (φ n) ^ 2 *
    (l2 (partialD (1, 0) (φ n)) ^ 2 + l2 (partialD (0, 1) (φ n)) ^ 2)
  have hQ : Tendsto Qn atTop (𝓝 Q) :=
    (tendsto_const_nhds.mul (ha.pow 2)).mul ((hb.pow 2).add (hc.pow 2))
  -- a.e. convergence along a subsequence
  have hconv : Tendsto (fun n => eLpNorm (φ n - g) 2 volume) atTop (𝓝 0) := by
    have hup : ∀ n, eLpNorm (φ n - g) 2 volume ≤ ENNReal.ofReal (normH 1 (g - φ n)) := by
      intro n
      rw [eLpNorm_sub_comm, ← ENNReal.ofReal_toReal ((hgL.sub (hφL n)).eLpNorm_ne_top)]
      exact ENNReal.ofReal_le_ofReal ((hgφ n).l2_le)
    have h0 : Tendsto (fun n => ENNReal.ofReal (normH 1 (g - φ n))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hd
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
      (fun n => zero_le) hup
  have hmeas : TendstoInMeasure volume φ atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun n => (hφL n).1) hgL.1 hconv
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hlim : ∀ᵐ x, Tendsto (fun i => ‖φ (ns i) x‖ₑ ^ 4) atTop (𝓝 (‖g x‖ₑ ^ 4)) :=
    hae.mono fun x hx =>
      ((ENNReal.continuous_pow 4).tendsto _).comp ((continuous_enorm.tendsto _).comp hx)
  have hsmooth : ∀ n, ∫⁻ x, ‖φ n x‖ₑ ^ 4 ≤ ENNReal.ofReal (Qn n) := fun n =>
    EmbedL4H.lintegral_enorm_pow_four_le_ofReal (by simpa using contDiff_infty.1 (hφ n).smooth 1)
      (hφ n).compact
  calc ∫⁻ x, ‖g x‖ₑ ^ 4 = ∫⁻ x, liminf (fun i => ‖φ (ns i) x‖ₑ ^ 4) atTop :=
        lintegral_congr_ae (hlim.mono fun x hx => hx.liminf_eq.symm)
    _ ≤ liminf (fun i => ∫⁻ x, ‖φ (ns i) x‖ₑ ^ 4) atTop :=
        lintegral_liminf_le' fun i =>
          ((hφ (ns i)).continuous.enorm.measurable.pow_const 4).aemeasurable
    _ ≤ liminf (fun i => ENNReal.ofReal (Qn (ns i))) atTop :=
        liminf_le_liminf (Eventually.of_forall fun i => hsmooth (ns i))
    _ = ENNReal.ofReal Q :=
        (ENNReal.tendsto_ofReal (hQ.comp hns.tendsto_atTop)).liminf_eq

end EmbedL4P

open EmbedL4P in
/-- (E1) `‖g‖⁴_{L⁴} ≤ 2 ‖g‖²_{L²} (‖∂₁g‖²_{L²} + ‖∂₂g‖²_{L²})` for `g ∈ H^1`. -/
theorem L4_le {g : ℂ → ℂ} (hg : MemH 1 g) :
    MemLp g 4 volume ∧
      ∫ x, ‖g x‖ ^ 4 ≤
        2 * l2 g ^ 2 * (l2 (weakPartial (1, 0) g) ^ 2 + l2 (weakPartial (0, 1) g) ^ 2) := by
  have hgL : MemLp g 2 volume := (memH_iff.1 hg).1
  have hF := lintegral_le hg
  have hpow : ∀ x, ‖g x‖ₑ ^ ((4 : ℝ≥0∞).toReal) = ‖g x‖ₑ ^ (4 : ℕ) := by
    intro x
    rw [show ((4 : ℝ≥0∞).toReal) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  refine ⟨⟨hgL.1, ?_⟩, ?_⟩
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    simp_rw [hpow]
    exact hF.trans_lt ENNReal.ofReal_lt_top
  · have hmeas4 : AEStronglyMeasurable (fun x => ‖g x‖ ^ 4) volume := hgL.1.norm.pow 4
    have hnn : 0 ≤ᵐ[volume] fun x => ‖g x‖ ^ 4 :=
      Eventually.of_forall fun x => by simp only [Pi.zero_apply]; positivity
    rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas4]
    have : ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 4) = ∫⁻ x, ‖g x‖ₑ ^ 4 := by
      refine lintegral_congr fun x => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [this]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hF

open EmbedL4P in
/-- (E1), second form: `‖g‖_{L⁴} ≤ ‖g‖_{H^1}`. -/
theorem L4_le_normH {g : ℂ → ℂ} (hg : MemH 1 g) :
    MemLp g 4 volume ∧ (eLpNorm g 4 volume).toReal ≤ normH 1 g := by
  obtain ⟨hL4, hI⟩ := L4_le hg
  refine ⟨hL4, ?_⟩
  set a := l2 g
  set b := l2 (weakPartial (1, 0) g)
  set c := l2 (weakPartial (0, 1) g)
  set N := normH 1 g
  have hN0 : 0 ≤ N := normH_nonneg _ _
  have hidx : multiIdx 1 = {((0 : ℕ), (0 : ℕ)), ((1 : ℕ), (0 : ℕ)), ((0 : ℕ), (1 : ℕ))} := by
    decide
  have hN : N ^ 2 = a ^ 2 + (b ^ 2 + c ^ 2) := by
    have hs : N = Real.sqrt (∑ γ ∈ multiIdx 1, l2 (weakPartial γ g) ^ 2) := normH_eq 1 g
    rw [hs, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), hidx,
      Finset.sum_insert (by decide), Finset.sum_pair (by decide), l2_weakPartial_zero hg]
  have h4 : ∫ x, ‖g x‖ ^ 4 ≤ N ^ 4 := by
    refine hI.trans ?_
    have : N ^ 4 = (N ^ 2) ^ 2 := by ring
    rw [this, hN]
    nlinarith [sq_nonneg (a ^ 2 - (b ^ 2 + c ^ 2)), sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hI0 : 0 ≤ ∫ x, ‖g x‖ ^ 4 := integral_nonneg fun x => by positivity
  rw [hL4.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  have hpow : ∀ x : ℂ, ‖g x‖ ^ ((4 : ℝ≥0∞).toReal) = ‖g x‖ ^ (4 : ℕ) := by
    intro x
    rw [show ((4 : ℝ≥0∞).toReal) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp_rw [hpow]
  have h44 : ((4 : ℝ≥0∞).toReal)⁻¹ = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
  rw [h44]
  calc (∫ x, ‖g x‖ ^ 4) ^ ((4 : ℕ) : ℝ)⁻¹ ≤ (N ^ 4) ^ ((4 : ℕ) : ℝ)⁻¹ :=
        Real.rpow_le_rpow hI0 h4 (by positivity)
    _ = N := Real.pow_rpow_inv_natCast hN0 (by norm_num)

end NonUniqueEuler.Sob
