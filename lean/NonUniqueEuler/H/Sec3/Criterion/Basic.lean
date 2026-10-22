import NonUniqueEuler.Defs.Sec3.Criterion
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Helper for `P/Sec3/Criterion`: elementary facts

* times in `[0, T₀)` lie below some `T₁ < T₀` (`exists_lt_of_mem_timeInterval`), and
  continuity into `L^p` on `[0, T₀)` is local (`continuousIntoLpOn_timeInterval_of_Ico`);
* a sequence in `ℝ≥0∞` has a subsequence converging to its `limsup`
  (`exists_strictMono_tendsto_limsup`);
* two `L²` functions with the same pairings against `L²` agree a.e.
  (`ae_eq_of_forall_integral_mul_eq`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.CriterionAux

open Weak

/-- Every `t ∈ [0, T₀)` lies below some real `T₁` with `T₁ < T₀`. -/
theorem exists_lt_of_mem_timeInterval {T₀ : ℝ≥0∞} {t : ℝ} (ht : t ∈ timeInterval T₀) :
    ∃ T₁ : ℝ, t < T₁ ∧ ENNReal.ofReal T₁ < T₀ := by
  obtain ⟨r, -, htr, hrT⟩ := ENNReal.lt_iff_exists_real_btwn.1 ht.2
  exact ⟨r, (ENNReal.ofReal_lt_ofReal_iff'.1 htr).1, hrT⟩

/-- `[0, T₁) ⊆ [0, T₀)` for `T₁ < T₀`. -/
theorem Ico_subset_timeInterval {T₀ : ℝ≥0∞} {T₁ : ℝ} (hT₁ : ENNReal.ofReal T₁ < T₀) :
    Ico 0 T₁ ⊆ timeInterval T₀ :=
  Ico_subset_Icc_self.trans (Icc_subset_timeInterval hT₁)

/-- Near `t₀ < T₁`, the time sets `[0, T₀)` and `[0, T₁)` coincide. -/
theorem Ico_mem_nhdsWithin_timeInterval {T₀ : ℝ≥0∞} {T₁ t₀ : ℝ} (ht₀ : t₀ < T₁) :
    Ico 0 T₁ ∈ 𝓝[timeInterval T₀] t₀ :=
  mem_nhdsWithin.2 ⟨Iio T₁, isOpen_Iio, ht₀, fun _ hs => ⟨hs.2.1, hs.1⟩⟩

/-- Continuity into `L^p` on `[0, T₀)` follows from continuity on every `[0, T₁)`, `T₁ < T₀`. -/
theorem continuousIntoLpOn_timeInterval_of_Ico {T₀ : ℝ≥0∞} {p : ℝ≥0∞} {ω : ℝ → ℂ → ℝ}
    (h : ∀ T₁ : ℝ, 0 < T₁ → ENNReal.ofReal T₁ < T₀ → ContinuousIntoLpOn p (Ico 0 T₁) ω) :
    ContinuousIntoLpOn p (timeInterval T₀) ω := by
  refine ⟨fun t ht => ?_, fun t₀ ht₀ => ?_⟩
  · obtain ⟨T₁, htT₁, hT₁⟩ := exists_lt_of_mem_timeInterval ht
    exact (h T₁ (ht.1.trans_lt htT₁) hT₁).1 t ⟨ht.1, htT₁⟩
  · obtain ⟨T₁, htT₁, hT₁⟩ := exists_lt_of_mem_timeInterval ht₀
    exact ((h T₁ (ht₀.1.trans_lt htT₁) hT₁).2 t₀ ⟨ht₀.1, htT₁⟩).mono_left
      (nhdsWithin_le_of_mem (Ico_mem_nhdsWithin_timeInterval htT₁))

/-- A sequence in `ℝ≥0∞` has a subsequence converging to its `limsup`. -/
theorem exists_strictMono_tendsto_limsup (u : ℕ → ℝ≥0∞) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 (limsup u atTop)) :=
  (MapClusterPt.limsup (u := u) (f := atTop)).tendsto_subseq

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

end NonUniqueEuler.Compact.CriterionAux
