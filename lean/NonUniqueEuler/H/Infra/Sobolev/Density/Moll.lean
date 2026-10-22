import Mathlib.Analysis.SpecificLimits.Basic
import NonUniqueEuler.H.Infra.Sobolev.Density.L2
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv

/-!
# Helper for `P/Infra/Sobolev/Density`: approximation by mollification

`exists_conv_approx`: if `f ∈ H^k` vanishes a.e. outside the compact set `K` and `r > 0`, then
for every `ε > 0` there is a test function `φ` supported in `cthickening r K` with
`‖f - φ‖_{H^k} < ε`; `φ = ρ_n ⋆ f` for a normed bump `ρ_n` of radius `≤ r/(n+1)`.

Proof: `∂^γ(f - ρ_n ⋆ f) = ∂^γ f - ρ_n ⋆ ∂^γ f` weakly (`hasWeakDerivOn_conv`), so
`‖f - ρ_n ⋆ f‖²_{H^k} = ∑_γ ‖∂^γ f - ρ_n ⋆ ∂^γ f‖²₂ → 0` (`tendsto_eLpNorm_conv_sub`).
-/

noncomputable section

open MeasureTheory Set Filter Metric Function
open scoped ENNReal ContDiff Topology Convolution

namespace NonUniqueEuler.Sob.DensityAux

/-- Bump functions on the plane of outer radius `r/(n+1)`. -/
def bump (r : ℝ) (hr : 0 < r) (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := r / (2 * ((n : ℝ) + 1))
  rOut := r / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply div_lt_div_of_pos_left hr (by positivity)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

theorem bump_rOut (r : ℝ) (hr : 0 < r) (n : ℕ) : (bump r hr n).rOut = r / ((n : ℝ) + 1) := rfl

theorem bump_rOut_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (bump r hr n).rOut) atTop (𝓝 0) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat r).comp (tendsto_add_atTop_nat 1)
  refine h.congr fun n => ?_
  simp [bump_rOut]

theorem bump_rOut_le (r : ℝ) (hr : 0 < r) (n : ℕ) : (bump r hr n).rOut ≤ r := by
  rw [bump_rOut]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact div_le_self hr.le (by linarith)

/-! ### Generic `H^k` bookkeeping -/

theorem locInt_of_memLp {g : ℂ → ℂ} (hg : MemLp g 2 volume) : LocallyIntegrable g volume :=
  hg.locallyIntegrable (by norm_num)

theorem hasWeakDerivOn_sub {vs : List ℂ} {f₁ f₂ g₁ g₂ : ℂ → ℂ}
    (hf₁ : LocallyIntegrable f₁ volume) (hf₂ : LocallyIntegrable f₂ volume)
    (hg₁ : LocallyIntegrable g₁ volume) (hg₂ : LocallyIntegrable g₂ volume)
    (h₁ : HasWeakDerivOn univ vs f₁ g₁) (h₂ : HasWeakDerivOn univ vs f₂ g₂) :
    HasWeakDerivOn univ vs (f₁ - f₂) (g₁ - g₂) := by
  have hn := h₂.const_mul (-1)
  have key := HasWeakDerivOn.add isOpen_univ (hf₁.locallyIntegrableOn univ)
    ((hf₂.neg.congr (by simp [Pi.neg_def])).locallyIntegrableOn univ)
    (hg₁.locallyIntegrableOn univ)
    ((hg₂.neg.congr (by simp [Pi.neg_def])).locallyIntegrableOn univ) h₁ hn
  have e1 : f₁ + (fun x => -1 * f₂ x) = f₁ - f₂ := by
    funext x; simp [sub_eq_add_neg]
  have e2 : g₁ + (fun x => -1 * g₂ x) = g₁ - g₂ := by
    funext x; simp [sub_eq_add_neg]
  rwa [e1, e2] at key

theorem memH_of_hasWeakDeriv {k : ℕ} {f : ℂ → ℂ} (hf : MemLp f 2 volume)
    {G : ℕ × ℕ → ℂ → ℂ}
    (hG : ∀ γ ∈ multiIdx k, MemLp (G γ) 2 volume ∧ HasWeakDerivOn univ (pdList γ) f (G γ)) :
    MemH k f :=
  memH_iff.2 ⟨hf, fun γ hγ => ⟨G γ, hG γ hγ⟩⟩

/-- The `H^k` norm computed with any family of `L²` weak derivatives. -/
theorem normH_eq_of_hasWeakDeriv {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {G : ℕ × ℕ → ℂ → ℂ}
    (hG : ∀ γ ∈ multiIdx k, MemLp (G γ) 2 volume ∧ HasWeakDerivOn univ (pdList γ) f (G γ)) :
    normH k f = Real.sqrt (∑ γ ∈ multiIdx k, l2 (G γ) ^ 2) := by
  rw [normH_eq]
  congr 1
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [l2, l2, eLpNorm_congr_ae (hf.weakPartial_ae_eq hγ (hG γ hγ).1 (hG γ hγ).2)]

theorem tendsto_sqrt_sum_sq {ι : Type*} {s : Finset ι} {a : ℕ → ι → ℝ}
    (h : ∀ i ∈ s, Tendsto (fun n => a n i) atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (∑ i ∈ s, a n i ^ 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => ∑ i ∈ s, a n i ^ 2) atTop (𝓝 (∑ i ∈ s, (0 : ℝ) ^ 2)) :=
    tendsto_finsetSum _ fun i hi => (h i hi).pow 2
  have h2 := (Real.continuous_sqrt.tendsto _).comp h1
  simpa [Function.comp_def] using h2

theorem tendsto_l2_of_eLpNorm {F : ℕ → ℂ → ℂ}
    (h : Tendsto (fun n => eLpNorm (F n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => l2 (F n)) atTop (𝓝 0) := by
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [l2, Function.comp_def] using this

/-! ### Approximation by mollification -/

/-- Mollification approximates `f ∈ H^k` vanishing outside a compact `K` by test functions
supported in `cthickening r K`. -/
theorem exists_conv_approx {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {K : Set ℂ} (hK : IsCompact K)
    (hfK : ∀ᵐ x, x ∉ K → f x = 0) {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ℂ → ℂ, IsTestFn (cthickening r K) φ ∧ MemH k (f - φ) ∧ normH k (f - φ) < ε := by
  set r' := min r 1 with hr'def
  have hr' : 0 < r' := lt_min hr one_pos
  set b := bump r' hr' with hbdef
  have hbr : ∀ n, (b n).rOut ≤ r' := bump_rOut_le r' hr'
  set G : ℕ × ℕ → ℂ → ℂ := fun γ => weakPartial γ f with hGdef
  have hG : ∀ γ ∈ multiIdx k, MemLp (G γ) 2 volume ∧ HasWeakDerivOn univ (pdList γ) f (G γ) :=
    fun γ hγ => hf.memLp_weakPartial hγ
  have hfL : MemLp f 2 volume := (memH_iff.1 hf).1
  have hmem : ∀ n, MemH k (f - conv ((b n).normed volume) f) ∧
      normH k (f - conv ((b n).normed volume) f) =
        Real.sqrt (∑ γ ∈ multiIdx k, l2 (G γ - conv ((b n).normed volume) (G γ)) ^ 2) := by
    intro n
    have hD : ∀ γ ∈ multiIdx k, MemLp (G γ - conv ((b n).normed volume) (G γ)) 2 volume ∧
        HasWeakDerivOn univ (pdList γ) (f - conv ((b n).normed volume) f)
          (G γ - conv ((b n).normed volume) (G γ)) := by
      intro γ hγ
      obtain ⟨hGL, hGw⟩ := hG γ hγ
      refine ⟨hGL.sub (memLp_conv_normed _ hGL), ?_⟩
      exact hasWeakDerivOn_sub (locInt_of_memLp hfL) (locInt_of_memLp (memLp_conv_normed _ hfL))
        (locInt_of_memLp hGL) (locInt_of_memLp (memLp_conv_normed _ hGL)) hGw
        (hasWeakDerivOn_conv (b n).continuous_normed (b n).hasCompactSupport_normed
          (locInt_of_memLp hfL) (locInt_of_memLp hGL) hGw)
    have hM : MemH k (f - conv ((b n).normed volume) f) :=
      memH_of_hasWeakDeriv (hfL.sub (memLp_conv_normed _ hfL)) hD
    exact ⟨hM, normH_eq_of_hasWeakDeriv hM hD⟩
  have hlim : Tendsto (fun n => normH k (f - conv ((b n).normed volume) f)) atTop (𝓝 0) := by
    refine (tendsto_sqrt_sum_sq fun γ hγ => tendsto_l2_of_eLpNorm ?_).congr
      fun n => ((hmem n).2).symm
    have := tendsto_eLpNorm_conv_sub (bump_rOut_tendsto r' hr')
      (fun n => (hbr n).trans (min_le_right _ _)) (hG γ hγ).1
    exact this.congr fun n => eLpNorm_sub_comm _ _ _ _
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  have hsupp : support ((b n).normed volume) ⊆ ball 0 (b n).rOut :=
    (b n).support_normed_eq.subset
  refine ⟨conv ((b n).normed volume) f, ⟨?_, ?_, ?_⟩, (hmem n).1, hn⟩
  · exact contDiff_conv (b n).contDiff_normed (b n).hasCompactSupport_normed
      (locInt_of_memLp hfL)
  · exact hasCompactSupport_conv hsupp hK hfK
  · exact (tsupport_conv_subset hsupp hfK).trans
      (cthickening_mono ((hbr n).trans (min_le_left _ _)) _)

end NonUniqueEuler.Sob.DensityAux
