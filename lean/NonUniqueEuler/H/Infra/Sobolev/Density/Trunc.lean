import NonUniqueEuler.H.Infra.Sobolev.Density.Moll
import NonUniqueEuler.I.Infra.Sobolev.Leibniz
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Infra.CkNorm.Scaling

/-!
# Helper for `P/Infra/Sobolev/Density`: truncation

Step 1 of the proof sketch of `I/Infra/Sobolev/Density.lean`. With a fixed smooth cutoff
`cut = 1` on `closedBall 0 1`, `0` off `ball 0 2`, and `cutR R x = cut (x / R)`:
`cutR R · f ∈ H^k`, it vanishes outside `closedBall 0 (2R)`, and `‖f - cutR R · f‖_{H^k} → 0`
as `R → ∞` (`exists_trunc_approx`).

Proof: by the weak Leibniz formula (`MemH.weakPartial_mul_ae_eq`,
`I/Infra/Sobolev/Leibniz.lean`) `∂^γ(cutR R f) = ∑_{β ≤ γ} C(γ,β) ∂^β cutR_R ∂^{γ-β} f`; by the
scaling rule (`iteratedFDeriv_comp_smul`, `I/Infra/CkNorm/Scaling.lean`)
`∂^β cutR_R (x) = R^{-|β|} (∂^β cut)(x/R)`, which is bounded by `‖cut‖_{C^k}` and tends to
`0` for `β ≠ 0` and to `cut 0 = 1` for `β = 0`; dominated convergence in `L²` concludes.
-/

noncomputable section

open MeasureTheory Set Filter Metric Function
open scoped ENNReal ContDiff Topology Pointwise

namespace NonUniqueEuler.Sob.DensityAux

/-- The fixed real cutoff: `1` on `closedBall 0 1`, support `ball 0 2`. -/
def cutBump : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The fixed complex cutoff. -/
def cut (x : ℂ) : ℂ := ((cutBump x : ℝ) : ℂ)

/-- The rescaled cutoff `x ↦ cut (x / R)` (written `1 • cut (R⁻¹ • x)` to match the scaling
rule). -/
def cutR (R : ℝ) (x : ℂ) : ℂ := (1 : ℝ) • cut (R⁻¹ • x)

theorem contDiff_cut : ContDiff ℝ ∞ cut :=
  Complex.ofRealCLM.contDiff.comp cutBump.contDiff

theorem hasCompactSupport_cut : HasCompactSupport cut :=
  cutBump.hasCompactSupport.comp_left Complex.ofReal_zero

theorem cut_zero : cut 0 = 1 := by
  simp only [cut]
  rw [cutBump.one_of_mem_closedBall (mem_closedBall_self (by norm_num [cutBump]))]
  simp

theorem contDiff_cutR (R : ℝ) : ContDiff ℝ ∞ (cutR R) :=
  (contDiff_cut.comp (contDiff_id.const_smul R⁻¹)).const_smul (1 : ℝ)

theorem cutR_eq_zero {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : 2 * R ≤ ‖x‖) : cutR R x = 0 := by
  have hnot : R⁻¹ • x ∉ ball (0 : ℂ) cutBump.rOut := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le), not_lt,
      le_inv_mul_iff₀ hR]
    simp only [cutBump]
    linarith
  have h0 : cutBump (R⁻¹ • x) = 0 := by
    rw [← Function.notMem_support, cutBump.support_eq]
    exact hnot
  simp only [cutR, cut, one_smul, h0, Complex.ofReal_zero]

theorem hasCompactSupport_cutR {R : ℝ} (hR : 0 < R) : HasCompactSupport (cutR R) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (2 * R)) fun x hx => by
    refine cutR_eq_zero hR ?_
    rw [mem_closedBall_zero_iff, not_le] at hx
    exact hx.le

theorem isTestFn_cutR {R : ℝ} (hR : 0 < R) : IsTestFn univ (cutR R) :=
  ⟨contDiff_cutR R, hasCompactSupport_cutR hR, subset_univ _⟩

theorem bounded_iteratedFDeriv_cut (q : ℕ) : ∃ C, ∀ x, ‖iteratedFDeriv ℝ q cut x‖ ≤ C := by
  have hc : Continuous (iteratedFDeriv ℝ q cut) :=
    contDiff_cut.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hs : HasCompactSupport (iteratedFDeriv ℝ q cut) := hasCompactSupport_cut.iteratedFDeriv q
  obtain ⟨C, hC⟩ := hc.norm.bddAbove_range_of_hasCompactSupport hs.norm
  exact ⟨C, fun x => hC ⟨x, rfl⟩⟩

theorem memCk_cut (k : ℕ) : MemCk k univ cut := by
  refine ⟨⟨univ, isOpen_univ, subset_rfl,
    (contDiff_cut.of_le (by exact_mod_cast le_top)).contDiffOn⟩, ?_⟩
  unfold normCkE
  refine (ENNReal.sum_lt_top.2 fun q _ => ?_).ne
  obtain ⟨C, hC⟩ := bounded_iteratedFDeriv_cut q
  unfold supIterDerivE
  refine lt_of_le_of_lt (b := ENNReal.ofReal C) (iSup₂_le fun x _ => ?_) ENNReal.ofReal_lt_top
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hC x)

theorem memCk_cutR (k : ℕ) {R : ℝ} (hR : 0 < R) : MemCk k univ (cutR R) := by
  have h' : MemCk k (R⁻¹ • (univ : Set ℂ)) cut := by
    rw [smul_set_univ₀ (inv_ne_zero hR.ne')]
    exact memCk_cut k
  exact (MemCk.comp_smul h' 1).1

/-- The scaling rule for the classical derivatives of the rescaled cutoff. -/
theorem partialD_cutR (R : ℝ) (β : ℕ × ℕ) (x : ℂ) :
    partialD β (cutR R) x = ((R⁻¹ ^ (β.1 + β.2) : ℝ) : ℂ) * partialD β cut (R⁻¹ • x) := by
  have h1 := partialD_eq_iteratedFDeriv (γ := β) (f := cutR R) (x := x)
    ((contDiff_cutR R).of_le (by exact_mod_cast le_top)).contDiffAt
  have h2 := partialD_eq_iteratedFDeriv (γ := β) (f := cut) (x := R⁻¹ • x)
    (contDiff_cut.of_le (by exact_mod_cast le_top)).contDiffAt
  rw [h1, h2]
  have h3 := iteratedFDeriv_comp_smul (β.1 + β.2) cut (1 : ℝ) R⁻¹ x
  rw [show cutR R = fun z => (1 : ℝ) • cut (R⁻¹ • z) from rfl, h3,
    smul_apply, one_mul, Complex.real_smul]

/-- The constant bounding all derivatives of `cut` of order `≤ k`. -/
def cutC (k : ℕ) : ℝ := normCk k univ cut

theorem cutC_nonneg (k : ℕ) : 0 ≤ cutC k := normCk_nonneg _ _ _

theorem norm_partialD_cutR_le {k : ℕ} {R : ℝ} (hR : 0 < R) {β : ℕ × ℕ} (hβ : β.1 + β.2 ≤ k)
    (x : ℂ) : ‖partialD β (cutR R) x‖ ≤ R⁻¹ ^ (β.1 + β.2) * cutC k := by
  rw [partialD_cutR, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_partialD_le_normCk (memCk_cut k) hβ (mem_univ _))
    (by positivity)

theorem norm_partialD_cutR_le' {k : ℕ} {R : ℝ} (hR : 1 ≤ R) {β : ℕ × ℕ} (hβ : β.1 + β.2 ≤ k)
    (x : ℂ) : ‖partialD β (cutR R) x‖ ≤ cutC k := by
  refine (norm_partialD_cutR_le (by linarith) hβ x).trans ?_
  have h1 : R⁻¹ ^ (β.1 + β.2) ≤ 1 :=
    pow_le_one₀ (inv_nonneg.2 (by linarith)) (inv_le_one_of_one_le₀ hR)
  nlinarith [cutC_nonneg k, pow_nonneg (inv_nonneg.2 (by linarith : (0 : ℝ) ≤ R)) (β.1 + β.2)]

theorem tendsto_inv_succ : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  simpa [Function.comp_def] using h

/-- Pointwise limits of the derivatives of the rescaled cutoffs. -/
theorem tendsto_partialD_cutR {k : ℕ} {β : ℕ × ℕ} (hβ : β.1 + β.2 ≤ k) (x : ℂ) :
    Tendsto (fun n : ℕ => partialD β (cutR ((n : ℝ) + 1)) x) atTop
      (𝓝 (if β = (0, 0) then 1 else 0)) := by
  split_ifs with h0
  · subst h0
    have hpd : ∀ R, partialD (0, 0) (cutR R) x = cut (R⁻¹ • x) := by
      intro R
      simp [partialD, pdList, cutR]
    simp only [hpd]
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • x) atTop (𝓝 0) := by
      simpa using tendsto_inv_succ.smul_const x
    have h2 := (contDiff_cut.continuous.tendsto 0).comp h1
    rw [cut_zero] at h2
    simpa [Function.comp_def] using h2
  · have hpos : 1 ≤ β.1 + β.2 := by
      rcases β with ⟨a, b⟩
      simp only [Prod.mk.injEq, not_and_or] at h0
      omega
    refine squeeze_zero_norm (a := fun n : ℕ => ((n : ℝ) + 1)⁻¹ * cutC k) (fun n => ?_) ?_
    · have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      refine (norm_partialD_cutR_le hR hβ x).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (cutC_nonneg k)
      refine pow_le_of_le_one (by positivity) ?_ (by omega)
      exact inv_le_one_of_one_le₀ (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
    · simpa using tendsto_inv_succ.mul_const (cutC k)

/-! ### The truncation estimate -/

theorem sub_mem_multiIdx {k : ℕ} {γ β : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    ((γ.1 - β.1, γ.2 - β.2) : ℕ × ℕ) ∈ multiIdx k := by
  rw [mem_multiIdx] at hγ ⊢
  simp only
  omega

theorem le_of_mem_leIdx {k : ℕ} {γ β : ℕ × ℕ} (hγ : γ ∈ multiIdx k) (hβ : β ∈ leIdx γ) :
    β.1 + β.2 ≤ k := by
  rw [mem_multiIdx] at hγ
  simp only [leIdx, Finset.mem_product, Finset.mem_range] at hβ
  omega

/-- The Leibniz sum for `cutR R · f`. -/
def leibSum (R : ℝ) (f : ℂ → ℂ) (γ : ℕ × ℕ) (x : ℂ) : ℂ :=
  ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ) * partialD β (cutR R) x *
    weakPartial (γ.1 - β.1, γ.2 - β.2) f x

theorem tendsto_leibSum {k : ℕ} {f : ℂ → ℂ} {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) (x : ℂ) :
    Tendsto (fun n : ℕ => leibSum ((n : ℝ) + 1) f γ x) atTop (𝓝 (weakPartial γ f x)) := by
  have h := tendsto_finsetSum (leIdx γ) fun β hβ =>
    ((tendsto_const_nhds (x := ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ))).mul
      (tendsto_partialD_cutR (le_of_mem_leIdx hγ hβ) x)).mul
      (tendsto_const_nhds (x := weakPartial (γ.1 - β.1, γ.2 - β.2) f x))
  have h0 : ((0 : ℕ), (0 : ℕ)) ∈ leIdx γ := by
    simp [leIdx]
  have hsum : (∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ) *
      (if β = (0, 0) then 1 else 0) * weakPartial (γ.1 - β.1, γ.2 - β.2) f x) =
        weakPartial γ f x := by
    rw [Finset.sum_eq_single_of_mem _ h0]
    · simp
    · intro β _ hne
      simp [hne]
  rw [← hsum]
  exact h

/-- Truncation: `cutR R · f → f` in `H^k`. -/
theorem exists_trunc_approx {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ MemH k (fun x => cutR R x * f x) ∧
      MemH k (f - fun x => cutR R x * f x) ∧ normH k (f - fun x => cutR R x * f x) < ε := by
  set T : ℕ → ℂ → ℂ := fun n x => cutR ((n : ℝ) + 1) x * f x with hTdef
  have hRpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hR1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hT : ∀ n, MemH k (T n) := fun n =>
    (MemH.mul_of_memCk isClosed_univ hf (Eventually.of_forall fun x hx => absurd (mem_univ x) hx)
      (memCk_cutR k (hRpos n))).1
  have hfT : ∀ n, MemH k (f - T n) := fun n => (MemH.sub hf (hT n)).1
  set G : ℕ → ℕ × ℕ → ℂ → ℂ := fun n γ => weakPartial γ f - weakPartial γ (T n) with hGdef
  have hG : ∀ n, ∀ γ ∈ multiIdx k, MemLp (G n γ) 2 volume ∧
      HasWeakDerivOn univ (pdList γ) (f - T n) (G n γ) := by
    intro n γ hγ
    obtain ⟨h1, h1w⟩ := hf.memLp_weakPartial hγ
    obtain ⟨h2, h2w⟩ := (hT n).memLp_weakPartial hγ
    refine ⟨h1.sub h2, hasWeakDerivOn_sub (locInt_of_memLp (memH_iff.1 hf).1)
      (locInt_of_memLp (memH_iff.1 (hT n)).1) (locInt_of_memLp h1) (locInt_of_memLp h2) h1w h2w⟩
  have hnorm : ∀ n, normH k (f - T n) = Real.sqrt (∑ γ ∈ multiIdx k, l2 (G n γ) ^ 2) :=
    fun n => normH_eq_of_hasWeakDeriv (hfT n) (hG n)
  -- the a.e. Leibniz identity
  have hleib : ∀ n, ∀ γ ∈ multiIdx k,
      G n γ =ᵐ[volume] fun x => weakPartial γ f x - leibSum ((n : ℝ) + 1) f γ x := by
    intro n γ hγ
    filter_upwards [MemH.weakPartial_mul_ae_eq hf (memCk_cutR k (hRpos n)) hγ] with x hx
    simp only [hGdef, Pi.sub_apply, hTdef]
    rw [hx]
    rfl
  have hlim : ∀ γ ∈ multiIdx k, Tendsto (fun n => l2 (G n γ)) atTop (𝓝 0) := by
    intro γ hγ
    refine tendsto_l2_of_eLpNorm ?_
    have heq : ∀ n, eLpNorm (G n γ) 2 volume =
        eLpNorm (fun x => weakPartial γ f x - leibSum ((n : ℝ) + 1) f γ x) 2 volume :=
      fun n => eLpNorm_congr_ae (hleib n γ hγ)
    simp_rw [heq]
    -- the dominating function
    set B : ℂ → ℝ := fun x => ‖weakPartial γ f x‖ + ∑ β ∈ leIdx γ,
      ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℝ) * cutC k *
        ‖weakPartial (γ.1 - β.1, γ.2 - β.2) f x‖ with hBdef
    have hB : MemLp B 2 volume := by
      refine (hf.memLp_weakPartial hγ).1.norm.add (memLp_finsetSum _ fun β _ => ?_)
      exact ((hf.memLp_weakPartial (sub_mem_multiIdx hγ)).1.norm.const_mul _)
    refine tendsto_eLpNorm_two_of_dominated (G := B) (fun n => ?_) hB (fun n => ?_)
      (Eventually.of_forall fun x => ?_)
    · exact (hG n γ hγ).1.1.congr (hleib n γ hγ)
    · refine Eventually.of_forall fun x => ?_
      simp only [hBdef, leibSum]
      refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β hβ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have hb := norm_partialD_cutR_le' (hR1 n) (le_of_mem_leIdx hγ hβ) x
      have hc : (0 : ℝ) ≤ ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hw := norm_nonneg (weakPartial (γ.1 - β.1, γ.2 - β.2) f x)
      have := mul_le_mul_of_nonneg_left hb hc
      exact mul_le_mul_of_nonneg_right this hw
    · have := (tendsto_leibSum (f := f) hγ x)
      have h2 := (tendsto_const_nhds (x := weakPartial γ f x)).sub this
      simpa using h2
  have hlimN : Tendsto (fun n => normH k (f - T n)) atTop (𝓝 0) :=
    (tendsto_sqrt_sum_sq hlim).congr fun n => (hnorm n).symm
  obtain ⟨n, hn⟩ := (hlimN.eventually (gt_mem_nhds hε)).exists
  exact ⟨(n : ℝ) + 1, hRpos n, hT n, hfT n, hn⟩

theorem cutR_mul_eq_zero {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ) :
    ∀ x, x ∉ closedBall (0 : ℂ) (2 * R) → cutR R x * f x = 0 := by
  intro x hx
  rw [mem_closedBall_zero_iff, not_le] at hx
  rw [cutR_eq_zero hR hx.le, zero_mul]

end NonUniqueEuler.Sob.DensityAux
