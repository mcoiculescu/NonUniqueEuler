import NonUniqueEuler.Defs.Sec3.Auxiliary
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Proof: `lem:dbr` (du Bois-Reymond lemma on a half-open time interval)

Proof of `I/Sec3/Dbr.lean` (`03_compactness.tex:68-90`).

We follow the alternative route recorded in the interface docstring (a restructuring of the
manuscript's mollification argument, same statement):

1. (`Dbr.primitive_spec`) If `χ ∈ C_c^∞((t₀,T))` has `∫χ = 0`, its primitive
   `α(t) = ∫_{t₀}^t χ` lies in `C_c^∞((-∞,T))`, vanishes at `t₀` and has `α' = χ`; the
   hypothesis then gives `∫_{t₀}^T χ B = 0` (`Dbr.integral_mul_eq_zero_of_integral_eq_zero`).
2. Fix `η ∈ C_c^∞((t₀,T))` with `∫η = 1` (`Dbr.exists_bump`) and put `c = ∫ η B`. For every
   `g ∈ C_c^∞((t₀,T))`, `χ = g - (∫g) η` has zero mean, so `∫ g B = (∫ g) c`, i.e.
   `∫ g (B - c) = 0`. The fundamental lemma of the calculus of variations on the open set
   `(t₀,T)` (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) gives `B = c` a.e.
3. Testing with a bump `α` with `α(t₀) = 1` supported in `(-∞,T)` gives
   `∫_{t₀}^T α' c = c (α(T) - α(t₀)) = -c`, so `b₀ = c`.

Deviation from the manuscript: the mollification step (`B_δ' = 0`, `B_δ → B` in `L¹_loc`) is
replaced by step 2 (primitive of a zero-mean test function plus the fundamental lemma). The
conclusion is the same.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.Weak

namespace Dbr

/-- A compact set inside `(t₀,T)` lies below some `b ∈ [t₀,T)`. -/
theorem exists_bound_of_tsupport_subset {t₀ T : ℝ} (hT : t₀ < T) {χ : ℝ → ℝ}
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo t₀ T) :
    ∃ b, t₀ ≤ b ∧ b < T ∧ tsupport χ ⊆ Iic b := by
  rcases (tsupport χ).eq_empty_or_nonempty with he | hne
  · exact ⟨t₀, le_rfl, hT, by simp [he]⟩
  · obtain ⟨x, hx⟩ := hχc.isCompact.exists_isGreatest hne
    exact ⟨x, (hχs hx.1).1.le, (hχs hx.1).2, fun y hy => hx.2 hy⟩

/-- The primitive `α(t) = ∫_{t₀}^t χ` of a smooth `χ` with compact support in `(t₀,T)` and zero
mean lies in `C_c^∞((-∞,T))` and satisfies `α' = χ`. -/
theorem primitive_spec {t₀ T : ℝ} (hT : t₀ < T) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo t₀ T) (hχ0 : ∫ t, χ t = 0) :
    IsTimeTestFn T (fun t => ∫ s in t₀..t, χ s) ∧
      deriv (fun t => ∫ s in t₀..t, χ s) = χ := by
  set α : ℝ → ℝ := fun t => ∫ s in t₀..t, χ s with hα
  have hcont : Continuous χ := hχ.continuous
  have hderiv : deriv α = χ := funext fun t => Continuous.deriv_integral χ hcont t₀ t
  have hdiff : Differentiable ℝ α := fun t =>
    (hcont.integral_hasStrictDerivAt t₀ t).hasDerivAt.differentiableAt
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α :=
    contDiff_infty_iff_deriv.mpr ⟨hdiff, hderiv ▸ hχ⟩
  obtain ⟨b, htb, hbT, hb⟩ := exists_bound_of_tsupport_subset hT hχc hχs
  have hχ_left : ∀ s ≤ t₀, χ s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport fun h => absurd (hχs h).1 (not_lt.mpr hs)
  have hχ_right : ∀ s, b < s → χ s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport fun h => absurd (hb h) (not_le.mpr hs)
  have hleft : ∀ t ≤ t₀, α t = 0 := by
    intro t ht
    have hEq : EqOn χ 0 (uIcc t₀ t) := by
      intro s hs
      rw [uIcc_of_ge ht] at hs
      exact hχ_left s hs.2
    simp only [hα]
    rw [intervalIntegral.integral_congr hEq]
    simp
  have hright : ∀ t, b ≤ t → α t = 0 := by
    intro t ht
    have htt : t₀ ≤ t := htb.trans ht
    simp only [hα]
    rw [intervalIntegral.integral_of_le htt, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hχ0
    · intro s hs
      rw [mem_Ioc, not_and_or, not_lt, not_le] at hs
      rcases hs with hs | hs
      · exact hχ_left s hs
      · exact hχ_right s (lt_of_le_of_lt ht hs)
  have hsupp : Function.support α ⊆ Icc t₀ b := by
    intro t ht
    by_contra hn
    rw [mem_Icc, not_and_or, not_le, not_le] at hn
    apply ht
    rcases hn with hn | hn
    · exact hleft t hn.le
    · exact hright t hn.le
  have hts : tsupport α ⊆ Icc t₀ b := closure_minimal hsupp isClosed_Icc
  refine ⟨⟨hsmooth, ?_, fun t ht => lt_of_le_of_lt (hts ht).2 hbT⟩, hderiv⟩
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport α) hts

/-- Step 1: for `χ ∈ C_c^∞((t₀,T))` with `∫χ = 0`, the hypothesis of `lem:dbr` gives
`∫_{t₀}^T χ B = 0`. -/
theorem integral_mul_eq_zero_of_integral_eq_zero {t₀ T b₀ : ℝ} (hT : t₀ < T) {B : ℝ → ℝ}
    (h : ∀ α : ℝ → ℝ, IsTimeTestFn T α →
      (∫ t in Ioo t₀ T, deriv α t * B t) + α t₀ * b₀ = 0)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo t₀ T) (hχ0 : ∫ t, χ t = 0) :
    ∫ t in Ioo t₀ T, χ t * B t = 0 := by
  obtain ⟨hα, hd⟩ := primitive_spec hT hχ hχc hχs hχ0
  have := h _ hα
  rw [hd] at this
  simpa using this

/-- A smooth bump `η` with compact support in `(t₀,T)` and `∫η = 1`. -/
theorem exists_bump {t₀ T : ℝ} (hT : t₀ < T) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Ioo t₀ T ∧ ∫ t, η t = 1 := by
  have hd : 0 < (T - t₀) / 8 := by linarith
  let f : ContDiffBump ((t₀ + T) / 2) := ⟨(T - t₀) / 8, (T - t₀) / 4, hd, by linarith⟩
  refine ⟨f.normed volume, f.contDiff_normed, f.hasCompactSupport_normed, ?_, f.integral_normed⟩
  rw [f.tsupport_normed_eq, Real.closedBall_eq_Icc]
  change Icc ((t₀ + T) / 2 - (T - t₀) / 4) ((t₀ + T) / 2 + (T - t₀) / 4) ⊆ Ioo t₀ T
  exact Icc_subset_Ioo (by linarith) (by linarith)

/-- A bump `α ∈ C_c^∞((-∞,T))` with `α(t₀) = 1`. -/
theorem exists_test_one {t₀ T : ℝ} (hT : t₀ < T) :
    ∃ α : ℝ → ℝ, IsTimeTestFn T α ∧ α t₀ = 1 ∧ α T = 0 := by
  have hr : 0 < (T - t₀) / 4 := by linarith
  let f : ContDiffBump t₀ := ⟨(T - t₀) / 4, (T - t₀) / 2, hr, by linarith⟩
  refine ⟨f, ⟨f.contDiff, f.hasCompactSupport, fun t ht => ?_⟩,
    f.one_of_mem_closedBall (mem_closedBall_self hr.le), f.zero_of_le_dist ?_⟩
  · rw [f.tsupport_eq, Real.closedBall_eq_Icc] at ht
    have : t ≤ t₀ + (T - t₀) / 2 := ht.2
    linarith
  · rw [Real.dist_eq, abs_of_pos (by linarith)]
    change (T - t₀) / 2 ≤ T - t₀
    linarith

end Dbr

/-- `lem:dbr` (`03_compactness.tex:68-76`): if `B ∈ L^∞(t₀,T)` satisfies
`∫_{t₀}^T α' B + α(t₀) b₀ = 0` for every `α ∈ C_c^∞((-∞,T))`, then `B = b₀` a.e. on `(t₀,T)`. -/
theorem duBoisReymond {t₀ T b₀ : ℝ} (hT : t₀ < T) {B : ℝ → ℝ}
    (hB : MemLp B ⊤ (volume.restrict (Ioo t₀ T)))
    (h : ∀ α : ℝ → ℝ, IsTimeTestFn T α →
      (∫ t in Ioo t₀ T, deriv α t * B t) + α t₀ * b₀ = 0) :
    B =ᵐ[volume.restrict (Ioo t₀ T)] fun _ => b₀ := by
  have hBi : IntegrableOn B (Ioo t₀ T) := hB.integrable le_top
  -- products with continuous compactly supported functions are integrable on `(t₀,T)`
  have hint : ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
      IntegrableOn (fun t => g t * B t) (Ioo t₀ T) := by
    intro g hg hgc
    obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
    exact hBi.bdd_mul hg.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  obtain ⟨η, hη, hηc, hηs, hη1⟩ := Dbr.exists_bump hT
  set c : ℝ := ∫ t in Ioo t₀ T, η t * B t with hc
  -- Step 2: `∫ g B = (∫ g) c` for `g ∈ C_c^∞((t₀,T))`
  have hkey : ∀ g : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ Ioo t₀ T → ∫ t in Ioo t₀ T, g t * B t = (∫ t, g t) * c := by
    intro g hg hgc hgs
    set k : ℝ := ∫ t, g t with hk
    set χ : ℝ → ℝ := fun t => g t - k * η t with hχ
    have hsub : tsupport χ ⊆ tsupport g ∪ tsupport η := by
      refine closure_minimal (fun t ht => ?_) ((isClosed_tsupport g).union (isClosed_tsupport η))
      by_contra hn
      rw [mem_union, not_or] at hn
      apply ht
      simp [χ, image_eq_zero_of_notMem_tsupport hn.1, image_eq_zero_of_notMem_tsupport hn.2]
    have hχs : tsupport χ ⊆ Ioo t₀ T := hsub.trans (union_subset hgs hηs)
    have hχc : HasCompactSupport χ :=
      (hgc.isCompact.union hηc.isCompact).of_isClosed_subset (isClosed_tsupport χ) hsub
    have hχ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := hg.sub (contDiff_const.mul hη)
    have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
    have hηi : Integrable η := hη.continuous.integrable_of_hasCompactSupport hηc
    have hχ0 : ∫ t, χ t = 0 := by
      simp only [χ]
      rw [integral_sub hgi (hηi.const_mul _), integral_const_mul, hη1, mul_one, sub_self]
    have h0 := Dbr.integral_mul_eq_zero_of_integral_eq_zero hT h hχ' hχc hχs hχ0
    have e : (fun t => χ t * B t) = fun t => g t * B t - k * (η t * B t) := by
      funext t
      simp only [χ]
      ring
    rw [e, integral_sub (hint g hg.continuous hgc) ((hint η hη.continuous hηc).const_mul _),
      integral_const_mul] at h0
    linarith
  -- the fundamental lemma on the open set `(t₀,T)`
  have hloc : LocallyIntegrableOn (fun t => B t - c) (Ioo t₀ T) :=
    (hBi.sub (integrable_const c)).locallyIntegrableOn
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
    intro g hg hgc hgs
    have hg0 : ∀ t, t ∉ Ioo t₀ T → g t = 0 := fun t ht =>
      image_eq_zero_of_notMem_tsupport fun h => ht (hgs h)
    have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
    simp only [smul_eq_mul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo t₀ T)
      (fun t ht => by rw [hg0 t ht, zero_mul])]
    have e : (fun t => g t * (B t - c)) = fun t => g t * B t - c * g t := by
      funext t
      ring
    rw [e, integral_sub (hint g hg.continuous hgc) (hgi.integrableOn.const_mul c),
      integral_const_mul, hkey g hg hgc hgs,
      setIntegral_eq_integral_of_forall_compl_eq_zero hg0]
    ring)
  have hBc : B =ᵐ[volume.restrict (Ioo t₀ T)] fun _ => c := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hae] with t ht htU
    exact sub_eq_zero.mp (ht htU)
  -- Step 3: `c = b₀`
  obtain ⟨α, hα, hα0, hαT⟩ := Dbr.exists_test_one hT
  have hαd : Differentiable ℝ α := hα.contDiff.differentiable (by simp)
  have hαc : Continuous (deriv α) := hα.contDiff.continuous_deriv (by simp)
  have hI : ∫ t in Ioo t₀ T, deriv α t * B t = -c := by
    have hcongr : (fun t => deriv α t * B t) =ᵐ[volume.restrict (Ioo t₀ T)]
        fun t => deriv α t * c := by
      filter_upwards [hBc] with t ht
      rw [ht]
    rw [integral_congr_ae hcongr, integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hT.le,
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hαd x) (hαc.intervalIntegrable _ _),
      hα0, hαT]
    ring
  have hcb : c = b₀ := by
    have := h α hα
    rw [hI, hα0] at this
    linarith
  rw [hcb] at hBc
  exact hBc

end NonUniqueEuler.Weak
