import NonUniqueEuler.Statement.WeakSolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Helper for `lem:lip-renorm`: approximating `Lip₀` by renormalizations

Proof helper for `P/Sec3/LipRenorm.lean` (`lem:lip-renorm`, `03_compactness.tex:92-118`).

The manuscript approximates `Υ ∈ Lip₀` by `Υ_j = Υ ⋆ ρ^t_{1/j} - (Υ ⋆ ρ^t_{1/j})(0)`. We use
instead the Steklov averages (the convolution with the normalized indicator of `[-h, 0]`)
`Υ_h(s) = h⁻¹ (∫_s^{s+h} Υ - ∫_0^h Υ)`, which are `C¹` by the fundamental theorem of calculus
(enough for `IsRenormalization`). For `h > 0`:
* `Υ_h' (s) = h⁻¹ (Υ(s+h) - Υ(s))`, so `|Υ_h'| ≤ L` and `Υ_h ∈ C¹`;
* `Υ_h(0) = 0`, hence `|Υ_h(s)| ≤ L|s|` (mean value theorem);
* `Υ_h(s) → Υ(s) - Υ(0) = Υ(s)` as `h → 0⁺` (the difference quotients of `∫_0^· Υ`).

Main result: `exists_seq_isRenormalization_tendsto`.
-/

noncomputable section

open Filter Set
open scoped Topology NNReal

namespace NonUniqueEuler.Weak.LipRenormAux

/-- The primitive `F(s) = ∫_0^s β`. -/
def prim (β : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..s, β r

/-- The Steklov average `β_h(s) = h⁻¹ (F(s + h) - F(s) - F(h))`, `F = ∫_0^· β`. -/
def steklov (β : ℝ → ℝ) (h s : ℝ) : ℝ :=
  h⁻¹ * (prim β (s + h) - prim β s - prim β h)

theorem prim_zero (β : ℝ → ℝ) : prim β 0 = 0 := by
  simp [prim]

theorem hasDerivAt_prim {β : ℝ → ℝ} (hβ : Continuous β) (s : ℝ) :
    HasDerivAt (prim β) (β s) s :=
  (hβ.integral_hasStrictDerivAt 0 s).hasDerivAt

theorem hasDerivAt_steklov {β : ℝ → ℝ} (hβ : Continuous β) (h s : ℝ) :
    HasDerivAt (steklov β h) (h⁻¹ * (β (s + h) - β s)) s := by
  have h1 : HasDerivAt (fun s => prim β (s + h)) (β (s + h)) s :=
    HasDerivAt.comp_add_const s h (hasDerivAt_prim hβ (s + h))
  exact ((h1.sub (hasDerivAt_prim hβ s)).sub_const (prim β h)).const_mul h⁻¹

theorem deriv_steklov {β : ℝ → ℝ} (hβ : Continuous β) (h : ℝ) :
    deriv (steklov β h) = fun s => h⁻¹ * (β (s + h) - β s) :=
  funext fun s => (hasDerivAt_steklov hβ h s).deriv

theorem differentiable_steklov {β : ℝ → ℝ} (hβ : Continuous β) (h : ℝ) :
    Differentiable ℝ (steklov β h) :=
  fun s => (hasDerivAt_steklov hβ h s).differentiableAt

theorem contDiff_steklov {β : ℝ → ℝ} (hβ : Continuous β) (h : ℝ) :
    ContDiff ℝ 1 (steklov β h) := by
  refine contDiff_one_iff_deriv.2 ⟨differentiable_steklov hβ h, ?_⟩
  rw [deriv_steklov hβ h]
  exact continuous_const.mul ((hβ.comp (continuous_id.add continuous_const)).sub hβ)

theorem steklov_zero (β : ℝ → ℝ) (h : ℝ) : steklov β h 0 = 0 := by
  simp [steklov, prim_zero]

/-- `|β_h'| ≤ K` for `h > 0` and `K`-Lipschitz `β`. -/
theorem abs_deriv_steklov_le {β : ℝ → ℝ} {K : ℝ≥0} (hK : LipschitzWith K β) {h : ℝ}
    (hh : 0 < h) (s : ℝ) : |deriv (steklov β h) s| ≤ K := by
  rw [deriv_steklov hK.continuous h]
  have hd := hK.dist_le_mul (s + h) s
  rw [Real.dist_eq, Real.dist_eq, add_sub_cancel_left, abs_of_pos hh] at hd
  rw [abs_mul, abs_inv, abs_of_pos hh, inv_mul_le_iff₀ hh]
  linarith

/-- `|β_h(s)| ≤ K |s|` for `h > 0` and `K`-Lipschitz `β`. -/
theorem abs_steklov_le {β : ℝ → ℝ} {K : ℝ≥0} (hK : LipschitzWith K β) {h : ℝ}
    (hh : 0 < h) (s : ℝ) : |steklov β h s| ≤ K * |s| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := steklov β h) (s := univ) (x := 0) (y := s)
    (C := K) (fun x _ => differentiable_steklov hK.continuous h x)
    (fun x _ => abs_deriv_steklov_le hK hh x) convex_univ (mem_univ _) (mem_univ _)
  simpa [steklov_zero] using this

/-- `β_h(s) → β(s) - β(0)` as `h → 0⁺`. -/
theorem tendsto_steklov {β : ℝ → ℝ} (hβ : Continuous β) (s : ℝ) :
    Tendsto (fun h => steklov β h s) (𝓝[>] 0) (𝓝 (β s - β 0)) := by
  have h1 := (hasDerivAt_prim hβ s).tendsto_slope_zero_right
  have h2 := (hasDerivAt_prim hβ 0).tendsto_slope_zero_right
  refine (h1.sub h2).congr fun h => ?_
  simp only [smul_eq_mul, zero_add, prim_zero, sub_zero, steklov]
  ring

/-- `lem:lip-renorm`, approximation step: every `K`-Lipschitz `β` with `β 0 = 0` is the
pointwise limit of renormalizations `Υ_n` (`C¹`, bounded derivative, `Υ_n(0) = 0`) with
`|Υ_n(s)| ≤ K |s|`. -/
theorem exists_seq_isRenormalization_tendsto {β : ℝ → ℝ} {K : ℝ≥0} (hK : LipschitzWith K β)
    (h0 : β 0 = 0) :
    ∃ Υ : ℕ → ℝ → ℝ, (∀ n, IsRenormalization (Υ n)) ∧ (∀ n s, |Υ n s| ≤ K * |s|) ∧
      ∀ s, Tendsto (fun n => Υ n s) atTop (𝓝 (β s)) := by
  set hn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hn_def
  have hpos : ∀ n, 0 < hn n := fun n => by
    simp only [hn_def]
    positivity
  have hlim : Tendsto hn atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hpos⟩
  refine ⟨fun n => steklov β (hn n), fun n => ?_, fun n s => abs_steklov_le hK (hpos n) s,
    fun s => ?_⟩
  · exact ⟨contDiff_steklov hK.continuous _, ⟨K, abs_deriv_steklov_le hK (hpos n)⟩,
      steklov_zero β _⟩
  · have := (tendsto_steklov hK.continuous s).comp hlim
    rw [h0, sub_zero] at this
    exact this

end NonUniqueEuler.Weak.LipRenormAux
