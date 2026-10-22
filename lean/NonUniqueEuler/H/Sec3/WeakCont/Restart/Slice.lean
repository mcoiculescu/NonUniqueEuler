import NonUniqueEuler.Defs.Sec3.Transport
import NonUniqueEuler.Defs.Sec3.Paths
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Helpers for `P/Sec3/WeakCont/Restart.lean`: time slices of a compactly supported function

For `φ : ℝ × ℂ → ℝ` with compact support, the slices `φ(t, ·)` vanish off the fixed compact set
`K = Prod.snd '' tsupport φ` (the projection of the support to `ℝ²`). If `φ` is continuous, the
slices are in every `L^p`; if `φ` is `C`-Lipschitz, then
`‖φ(t, ·) - φ(s, ·)‖_{L²} ≤ C |t - s| |K|^{1/2}`. Together with the Cauchy–Schwarz inequality
`|∫ f g| ≤ ‖f‖₂ ‖g‖₂` (`abs_integral_mul_le`) this is the estimate of `03_compactness.tex:216-219`.

All lemmas are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal InnerProductSpace

namespace NonUniqueEuler.Weak.WeakCont.Restart

variable {φ : ℝ × ℂ → ℝ}

/-- The projection of the support of a compactly supported `φ` to `ℝ²` is compact. -/
theorem isCompact_snd_tsupport (hφc : HasCompactSupport φ) :
    IsCompact (Prod.snd '' tsupport φ) :=
  hφc.isCompact.image continuous_snd

/-- Every slice `φ(t, ·)` vanishes off `Prod.snd '' tsupport φ`. -/
theorem slice_eq_zero {t : ℝ} {x : ℂ} (hx : x ∉ Prod.snd '' tsupport φ) : φ (t, x) = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx ⟨(t, x), h, rfl⟩

/-- The slices of a compactly supported `φ` have compact support. -/
theorem hasCompactSupport_slice (hφc : HasCompactSupport φ) (t : ℝ) :
    HasCompactSupport (fun x : ℂ => φ (t, x)) :=
  HasCompactSupport.intro (isCompact_snd_tsupport hφc) fun _ hx => slice_eq_zero hx

/-- The slices of a continuous compactly supported `φ` are in every `L^p`. -/
theorem memLp_slice (hφ : Continuous φ) (hφc : HasCompactSupport φ) (t : ℝ) (p : ℝ≥0∞) :
    MemLp (fun x : ℂ => φ (t, x)) p volume :=
  (hφ.comp (Continuous.prodMk_right t)).memLp_of_hasCompactSupport (hasCompactSupport_slice hφc t)

/-- Cauchy–Schwarz in `L²(ℝ²)`: `|∫ f g| ≤ ‖f‖₂ ‖g‖₂`. -/
theorem abs_integral_mul_le {f g : ℂ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    |∫ x, f x * g x| ≤ (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  rw [← WeakL2.inner_toLp_toLp hf hg, ← Lp.norm_toLp f hf, ← Lp.norm_toLp g hg]
  exact abs_real_inner_le_norm _ _

/-- For a `C`-Lipschitz `φ`, `|φ(t, x) - φ(s, x)| ≤ C |t - s|`, and the difference vanishes off
`Prod.snd '' tsupport φ`. -/
theorem norm_slice_sub_le_indicator {C : ℝ≥0} (hL : LipschitzWith C φ) (t s : ℝ) (x : ℂ) :
    ‖φ (t, x) - φ (s, x)‖ ≤
      (Prod.snd '' tsupport φ).indicator (fun _ => (C : ℝ) * |t - s|) x := by
  by_cases hx : x ∈ Prod.snd '' tsupport φ
  · rw [indicator_of_mem hx, ← dist_eq_norm]
    have h := hL.dist_le_mul (t, x) (s, x)
    rwa [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq] at h
  · rw [indicator_of_notMem hx, slice_eq_zero hx, slice_eq_zero hx, sub_self, norm_zero]

/-- `‖φ(t, ·) - φ(s, ·)‖_{L²} ≤ C |t - s| |K|^{1/2}` for a `C`-Lipschitz, compactly supported
`φ`, with `K = Prod.snd '' tsupport φ`. -/
theorem eLpNorm_slice_sub_le {C : ℝ≥0} (hL : LipschitzWith C φ) (hφc : HasCompactSupport φ)
    (t s : ℝ) :
    eLpNorm (fun x : ℂ => φ (t, x) - φ (s, x)) 2 volume ≤
      ENNReal.ofReal ((C : ℝ) * |t - s|) *
        volume (Prod.snd '' tsupport φ) ^ (1 / (2 : ℝ≥0∞).toReal) := by
  have hK : MeasurableSet (Prod.snd '' tsupport φ) :=
    (isCompact_snd_tsupport hφc).isClosed.measurableSet
  refine (eLpNorm_mono_real (norm_slice_sub_le_indicator hL t s)).trans ?_
  rw [eLpNorm_indicator_const hK two_ne_zero ENNReal.ofNat_ne_top,
    Real.enorm_of_nonneg (by positivity)]

/-- The real form: `‖φ(t, ·) - φ(s, ·)‖_{L²} ≤ C |t - s| M`, where `M = |K|^{1/2}` (as a real
number). -/
theorem toReal_eLpNorm_slice_sub_le {C : ℝ≥0} (hL : LipschitzWith C φ)
    (hφc : HasCompactSupport φ) (t s : ℝ) :
    (eLpNorm (fun x : ℂ => φ (t, x) - φ (s, x)) 2 volume).toReal ≤
      (C : ℝ) * |t - s| *
        (volume (Prod.snd '' tsupport φ) ^ (1 / (2 : ℝ≥0∞).toReal)).toReal := by
  have hfin : volume (Prod.snd '' tsupport φ) ^ (1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (isCompact_snd_tsupport hφc).measure_lt_top.ne
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
    (eLpNorm_slice_sub_le hL hφc t s)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h

end NonUniqueEuler.Weak.WeakCont.Restart
