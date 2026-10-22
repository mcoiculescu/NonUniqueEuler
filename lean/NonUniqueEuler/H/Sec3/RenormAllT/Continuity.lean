import NonUniqueEuler.H.Sec3.RenormAllT.Basic
import NonUniqueEuler.I.Sec3.RR

/-!
# Helpers for `lem:renorm-all-t`: strong continuity in `L²`

Helper file of `P/Sec3/RenormAllT.lean` (fully proved).

Restructured argument (deviation from `03_compactness.tex:640-656`).
Once `‖ω(t)‖₂ = ‖ω^in‖₂` for every `t ∈ [0,T)` (from eq:conservation), weak continuity and
`lem:RR` (`radonRiesz_filter`) give `ω ∈ C([0,T);L²)` directly
(`tendsto_eLpNorm_two_of_norm_eq`); the manuscript's argument shows the same thing for `U_k`.
Then `|ω|` is continuous into `L²` on `[0,T)`, hence weakly continuous on every `[0,T']`,
`T' < T` (`isWeakContL2On_abs`).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology InnerProductSpace

namespace NonUniqueEuler.Weak.RenormAllTH

theorem memLp_abs {f : ℂ → ℝ} {p : ℝ≥0∞} (hf : MemLp f p volume) :
    MemLp (fun x => |f x|) p volume :=
  hf.of_le_mul (c := 1) (continuous_abs.comp_aestronglyMeasurable hf.1)
    (Eventually.of_forall fun x => by simp)

/-- `|∫ f ψ - ∫ g ψ| ≤ ‖f - g‖₂ ‖ψ‖₂`. -/
theorem abs_integral_mul_sub_le {f g ψ : ℂ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hψ : MemLp ψ 2 volume) :
    |(∫ x, f x * ψ x) - ∫ x, g x * ψ x| ≤
      (eLpNorm (f - g) 2 volume).toReal * (eLpNorm ψ 2 volume).toReal := by
  have hint : (∫ x, f x * ψ x) - ∫ x, g x * ψ x = ∫ x, (f - g) x * ψ x := by
    rw [← WeakL2.inner_toLp_toLp hf hψ, ← WeakL2.inner_toLp_toLp hg hψ,
      ← WeakL2.inner_toLp_toLp (hf.sub hg) hψ, ← inner_sub_left, MemLp.toLp_sub]
  rw [hint]
  exact abs_integral_mul_le (hf.sub hg) hψ

/-- Weak continuity on `[0,T]` and constant `L²` norm on `[0,T)` give strong continuity into `L²`
on `[0,T)` (`lem:RR`). -/
theorem tendsto_eLpNorm_two_of_norm_eq {T : ℝ} {ω : ℝ → ℂ → ℝ} {g : ℂ → ℝ}
    (hc : IsWeakContL2On (Icc 0 T) ω)
    (hn : ∀ t ∈ Ico 0 T, eLpNorm (ω t) 2 volume = eLpNorm g 2 volume) :
    ∀ t₀ ∈ Ico 0 T,
      Tendsto (fun t => eLpNorm (ω t - ω t₀) 2 volume) (𝓝[Ico 0 T] t₀) (𝓝 0) := by
  intro t₀ ht₀
  set gs : ℝ → ℂ → ℝ := fun t => if t ∈ Icc 0 T then ω t else 0 with hgs_def
  have hgs : ∀ t, MemLp (gs t) 2 volume := by
    intro t
    by_cases ht : t ∈ Icc 0 T
    · simp only [gs, ht, ite_true]
      exact hc.memLp t ht
    · simp only [gs, ht, ite_false]
      exact MemLp.zero
  have hev : ∀ᶠ t in 𝓝[Ico 0 T] t₀, gs t = ω t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [gs, Ico_subset_Icc_self ht, ite_true]
  have hw : ∀ ψ : ℂ → ℝ, MemLp ψ 2 volume →
      Tendsto (fun t => ∫ x, gs t x * ψ x) (𝓝[Ico 0 T] t₀) (𝓝 (∫ x, ω t₀ x * ψ x)) := by
    intro ψ hψ
    have hcw : ContinuousWithinAt (fun t => ∫ x, ω t x * ψ x) (Ico 0 T) t₀ :=
      (hc.continuousOn ψ hψ t₀ (Ico_subset_Icc_self ht₀)).mono Ico_subset_Icc_self
    exact Tendsto.congr' (hev.mono fun t ht => by simp only [ht]) hcw
  have hn' : Tendsto (fun t => eLpNorm (gs t) 2 volume) (𝓝[Ico 0 T] t₀)
      (𝓝 (eLpNorm (ω t₀) 2 volume)) := by
    rw [hn t₀ ht₀]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [gs, Ico_subset_Icc_self ht, ite_true, hn t ht]
  have := Compact.radonRiesz_filter hgs (hc.memLp t₀ (Ico_subset_Icc_self ht₀)) hw hn'
  refine this.congr' ?_
  filter_upwards [hev] with t ht
  rw [ht]

/-- If `ω` is weakly continuous on `[0,T]` and strongly continuous into `L²` on `[0,T)`, then
`|ω|` is weakly continuous on `[0,T']` for every `T' < T`. -/
theorem isWeakContL2On_abs {T T' : ℝ} {ω : ℝ → ℂ → ℝ} (hc : IsWeakContL2On (Icc 0 T) ω)
    (hT' : T' < T)
    (hL2 : ∀ t₀ ∈ Ico 0 T,
      Tendsto (fun t => eLpNorm (ω t - ω t₀) 2 volume) (𝓝[Ico 0 T] t₀) (𝓝 0)) :
    IsWeakContL2On (Icc 0 T') (fun t x => |ω t x|) := by
  have hsub : Icc 0 T' ⊆ Ico 0 T := fun t ht => ⟨ht.1, ht.2.trans_lt hT'⟩
  have hm : ∀ t ∈ Icc 0 T', MemLp (ω t) 2 volume :=
    fun t ht => hc.memLp t (Ico_subset_Icc_self (hsub ht))
  refine ⟨fun t ht => memLp_abs (hm t ht), fun ψ hψ s₀ hs₀ => ?_⟩
  have hlim : Tendsto (fun t => (eLpNorm (ω t - ω s₀) 2 volume).toReal *
      (eLpNorm ψ 2 volume).toReal) (𝓝[Icc 0 T'] s₀) (𝓝 0) := by
    have h1 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (hL2 s₀ (hsub hs₀))).mono_left (nhdsWithin_mono s₀ hsub)
    simpa using h1.mul_const (eLpNorm ψ 2 volume).toReal
  have hbound : ∀ᶠ t in 𝓝[Icc 0 T'] s₀,
      ‖(∫ x, |ω t x| * ψ x) - ∫ x, |ω s₀ x| * ψ x‖ ≤
        (eLpNorm (ω t - ω s₀) 2 volume).toReal * (eLpNorm ψ 2 volume).toReal := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [Real.norm_eq_abs]
    refine (abs_integral_mul_sub_le (memLp_abs (hm t ht)) (memLp_abs (hm s₀ hs₀)) hψ).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
    refine ENNReal.toReal_mono ((hm t ht).sub (hm s₀ hs₀)).eLpNorm_ne_top ?_
    refine eLpNorm_mono fun x => ?_
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    exact abs_abs_sub_abs_le_abs_sub _ _
  have := squeeze_zero_norm' hbound hlim
  exact tendsto_sub_nhds_zero_iff.1 this

end NonUniqueEuler.Weak.RenormAllTH
