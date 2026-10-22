import NonUniqueEuler.Defs.Sec3.Compact
import NonUniqueEuler.Defs.Sec3.Transport
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Helpers for `prop:stable`: generic lemmas

Helper file of `P/Sec3/Stable.lean` (`prop:stable`, `03_compactness.tex:716-827`).

* Tonelli bounds on `I × s` (`lintegral_prodSet_le`, `lintegral_slab_le_of_slice`) and
  integrability on the slab from slice bounds (`integrableOn_slab_of_bound`).
* `abs_sub_trunc_le`: `|s - T_k(s)| ≤ s²/k`.
* `eLpNorm_one_le_two_mul`: `‖f‖_{L¹(μ)} ≤ ‖f‖_{L²(μ)} μ(univ)^{1/2}`.
* `tendsto_of_le_add_of_le_add`: an `ℝ≥0∞` squeeze.
* `Lip₀` and `L^∞(I; L^b(Ω))`: `IsLipO.exists_abs_le`, `memLp_comp_lipO`, `memLinfLp_comp_lipO`,
  `memLinfLp_sub`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.StableAux

open Weak

/-! ### Tonelli bounds -/

/-- Tonelli inequality on a product set `I × s` (no measurability needed). -/
theorem lintegral_prodSet_le (I : Set ℝ) (s : Set ℂ) (F : ℝ × ℂ → ℝ≥0∞) :
    ∫⁻ p in I ×ˢ s, F p ≤ ∫⁻ t in I, ∫⁻ x in s, F (t, x) := by
  rw [Measure.volume_eq_prod ℝ ℂ, ← Measure.prod_restrict]
  exact lintegral_prod_le F

/-- A slice-wise bound gives a bound on `(0,T) × s`. -/
theorem lintegral_slab_le_of_slice {T : ℝ} (s : Set ℂ) (F : ℝ × ℂ → ℝ≥0∞) {C : ℝ≥0∞}
    (hC : ∀ t ∈ Ioo 0 T, ∫⁻ x in s, F (t, x) ≤ C) :
    ∫⁻ p in Ioo 0 T ×ˢ s, F p ≤ ENNReal.ofReal T * C := by
  refine (lintegral_prodSet_le _ s F).trans ?_
  refine (setLIntegral_mono' measurableSet_Ioo hC).trans ?_
  rw [setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm]

/-- An a.e. slice-wise bound gives a bound on `(0,T) × s`. -/
theorem lintegral_slab_le_of_ae_slice {T : ℝ} (s : Set ℂ) (F : ℝ × ℂ → ℝ≥0∞) {C : ℝ≥0∞}
    (hC : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∫⁻ x in s, F (t, x) ≤ C) :
    ∫⁻ p in Ioo 0 T ×ˢ s, F p ≤ ENNReal.ofReal T * C := by
  refine (lintegral_prodSet_le _ s F).trans ?_
  refine (lintegral_mono_ae hC).trans ?_
  rw [setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm]

/-- A function with an a.e. `L¹` slice bound on `(0,T)` is integrable on the slab. -/
theorem integrableOn_slab_of_ae_bound {T M : ℝ} {u : ℝ → ℂ → ℝ}
    (hu : AEStronglyMeasurable (Function.uncurry u) (volume.restrict (slab T)))
    (hb : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), eLpNorm (u t) 1 volume ≤ ENNReal.ofReal M) :
    IntegrableOn (Function.uncurry u) (slab T) := by
  refine ⟨hu, ?_⟩
  have h := lintegral_slab_le_of_ae_slice (T := T) univ (fun p => ‖Function.uncurry u p‖ₑ)
    (C := ENNReal.ofReal M) (hb.mono fun t ht => by
      rw [Measure.restrict_univ, ← eLpNorm_one_eq_lintegral_enorm]
      exact ht)
  exact h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

/-- `L^∞(0,T; L¹) ⊆ L¹((0,T) × ℝ²)`. -/
theorem integrableOn_slab_of_memLinfLp {T : ℝ} {u : ℝ → ℂ → ℝ}
    (hu : Prelim.MemLinfLp (Ioo 0 T) univ 1 u) : IntegrableOn (Function.uncurry u) (slab T) := by
  obtain ⟨M, hM⟩ := hu.essBounded
  refine integrableOn_slab_of_ae_bound (M := M) hu.aestronglyMeasurable (hM.mono fun t ht => ?_)
  rw [Measure.restrict_univ] at ht
  rw [← ENNReal.ofReal_toReal ht.1.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal ht.2

/-- A function with an `L¹` slice bound on `(0,T)` is integrable on the slab. -/
theorem integrableOn_slab_of_bound {T M : ℝ} {u : ℝ → ℂ → ℝ}
    (hu : AEStronglyMeasurable (Function.uncurry u) (volume.restrict (slab T)))
    (hb : ∀ t ∈ Ioo 0 T, eLpNorm (u t) 1 volume ≤ ENNReal.ofReal M) :
    IntegrableOn (Function.uncurry u) (slab T) := by
  refine ⟨hu, ?_⟩
  have h := lintegral_slab_le_of_slice (T := T) univ (fun p => ‖Function.uncurry u p‖ₑ)
    (C := ENNReal.ofReal M) (fun t ht => by
      rw [Measure.restrict_univ, ← eLpNorm_one_eq_lintegral_enorm]
      exact hb t ht)
  exact h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

/-! ### Truncation -/

/-- `|s - T_k(s)| ≤ s²/k` for `k > 0`. -/
theorem abs_sub_trunc_le {k : ℝ} (hk : 0 < k) (s : ℝ) : |s - trunc k s| ≤ s ^ 2 / k := by
  rcases le_or_gt |s| k with h | h
  · rw [trunc_of_abs_le h, sub_self, abs_zero]; positivity
  · rw [le_div_iff₀ hk]
    rcases lt_abs.mp h with h' | h'
    · have : trunc k s = k := by
        simp only [trunc]; rw [min_eq_left h'.le, max_eq_right (by linarith)]
      rw [this, abs_of_pos (by linarith)]; nlinarith
    · have : trunc k s = -k := by
        simp only [trunc]; rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      rw [this, abs_of_neg (by linarith)]; nlinarith

/-! ### `L¹` versus `L²` on finite measure spaces -/

theorem eLpNorm_one_le_two_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 1 μ ≤ eLpNorm f 2 μ * μ univ ^ (1 / 2 : ℝ) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hf
  have he : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = 1 / 2 := by norm_num
  rwa [he] at h

/-! ### An `ℝ≥0∞` squeeze -/

theorem tendsto_of_le_add_of_le_add {a d : ℕ → ℝ≥0∞} {b : ℝ≥0∞} (hb : b ≠ ∞)
    (h1 : ∀ n, a n ≤ d n + b) (h2 : ∀ n, b ≤ d n + a n) (hd : Tendsto d atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 b) := by
  have hlow : Tendsto (fun n => b - d n) atTop (𝓝 b) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds hd (Or.inl hb)
  have hup : Tendsto (fun n => d n + b) atTop (𝓝 b) := by
    simpa using hd.add (tendsto_const_nhds (x := b))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun n => ?_) h1
  rw [tsub_le_iff_right, add_comm]
  exact h2 n

/-! ### `Lip₀` and `L^∞(I; L^b(Ω))` -/

theorem _root_.NonUniqueEuler.Equimeas.IsLipO.exists_abs_le {β : ℝ → ℝ}
    (hβ : Equimeas.IsLipO β) : ∃ K : ℝ, 0 ≤ K ∧ ∀ s, |β s| ≤ K * |s| := by
  obtain ⟨⟨K, hK⟩, h0⟩ := hβ
  refine ⟨K, K.2, fun s => ?_⟩
  have := hK.dist_le_mul s 0
  rwa [Real.dist_eq, Real.dist_eq, h0, sub_zero, sub_zero] at this

theorem _root_.NonUniqueEuler.Equimeas.IsLipO.continuous {β : ℝ → ℝ}
    (hβ : Equimeas.IsLipO β) : Continuous β := by
  obtain ⟨⟨K, hK⟩, _⟩ := hβ
  exact hK.continuous

theorem memLp_comp_lipO {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    {f : α → ℝ} (hf : MemLp f p μ) {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β) :
    MemLp (fun x => β (f x)) p μ := by
  obtain ⟨K, -, hK⟩ := hβ.exists_abs_le
  exact hf.of_le_mul (hβ.continuous.comp_aestronglyMeasurable hf.1)
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hK (f x))

theorem eLpNorm_comp_lipO_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (f : α → ℝ) {β : ℝ → ℝ} {K : ℝ} (hK : ∀ s, |β s| ≤ K * |s|) :
    eLpNorm (fun x => β (f x)) p μ ≤ ENNReal.ofReal K * eLpNorm f p μ :=
  eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hK (f x)) p

theorem memLinfLp_comp_lipO {I : Set ℝ} {Ω : Set ℂ} {b : ℝ≥0∞} {u : ℝ → ℂ → ℝ}
    (hu : Prelim.MemLinfLp I Ω b u) {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β) :
    Prelim.MemLinfLp I Ω b (fun t x => β (u t x)) := by
  obtain ⟨K, hK0, hK⟩ := hβ.exists_abs_le
  refine ⟨hβ.continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable, ?_⟩
  obtain ⟨M, hM⟩ := hu.essBounded
  refine ⟨K * M, hM.mono fun t ht => ⟨memLp_comp_lipO ht.1 hβ, ?_⟩⟩
  have h := eLpNorm_comp_lipO_le (μ := volume.restrict Ω) (p := b) (u t) hK
  have hfin : eLpNorm (u t) b (volume.restrict Ω) ≠ ∞ := ht.1.eLpNorm_ne_top
  calc (eLpNorm (fun x => β (u t x)) b (volume.restrict Ω)).toReal
      ≤ (ENNReal.ofReal K * eLpNorm (u t) b (volume.restrict Ω)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h
    _ = K * (eLpNorm (u t) b (volume.restrict Ω)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0]
    _ ≤ K * M := mul_le_mul_of_nonneg_left ht.2 hK0

theorem memLinfLp_sub {I : Set ℝ} {Ω : Set ℂ} {b : ℝ≥0∞} (hb : 1 ≤ b) {u v : ℝ → ℂ → ℝ}
    (hu : Prelim.MemLinfLp I Ω b u) (hv : Prelim.MemLinfLp I Ω b v) :
    Prelim.MemLinfLp I Ω b (fun t x => u t x - v t x) := by
  refine ⟨hu.aestronglyMeasurable.sub hv.aestronglyMeasurable, ?_⟩
  obtain ⟨M, hM⟩ := hu.essBounded
  obtain ⟨N, hN⟩ := hv.essBounded
  refine ⟨M + N, (hM.and hN).mono fun t ht => ⟨ht.1.1.sub ht.2.1, ?_⟩⟩
  have h := eLpNorm_sub_le (p := b) ht.1.1.1 ht.2.1.1 hb
  calc (eLpNorm (fun x => u t x - v t x) b (volume.restrict Ω)).toReal
      ≤ (eLpNorm (u t) b (volume.restrict Ω) + eLpNorm (v t) b (volume.restrict Ω)).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ht.1.1.eLpNorm_ne_top,
          ht.2.1.eLpNorm_ne_top⟩) h
    _ = (eLpNorm (u t) b (volume.restrict Ω)).toReal +
          (eLpNorm (v t) b (volume.restrict Ω)).toReal :=
        ENNReal.toReal_add ht.1.1.eLpNorm_ne_top ht.2.1.eLpNorm_ne_top
    _ ≤ M + N := add_le_add ht.1.2 ht.2.2

end NonUniqueEuler.Compact.StableAux
