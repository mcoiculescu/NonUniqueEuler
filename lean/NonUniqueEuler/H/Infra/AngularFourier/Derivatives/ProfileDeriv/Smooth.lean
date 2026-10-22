import NonUniqueEuler.Defs.Infra.AngularFourier
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Helpers for `P/Infra/AngularFourier/Derivatives/ProfileDeriv`: the auxiliary test functions

For a profile `ζ : ℝ → ℂ` that is a test function on `(0, ∞)` we use the functions on `ℂ`
* `pW ℓ x = e^{-iℓθ} / |x|` (`angPhase (-ℓ) x / |x|`), smooth on `ℂ \ {0}`;
* `W ℓ ζ x = e^{-iℓθ} ζ(|x|) / |x|` (`pW ℓ x * ζ |x|`);
* `fW ℓ ζ x = e^{-iℓθ} ζ(|x|) / |x|²` (`pW ℓ x / |x| * ζ |x|`).

Both `W ℓ ζ` and `fW ℓ ζ` are test functions on the plane (`isTestFn_W`, `isTestFn_fW`): they
vanish near `0` because `ζ` vanishes near `0`, and off `0` all factors are smooth.
Values on circles: `W_circleMap`. Homogeneity: `fW_smul`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Ang.ProfileDerivAux

/-- `e^{-iℓθ}/|x|` at `x = |x| e^{iθ}`. -/
def pW (ℓ : ℤ) (x : ℂ) : ℂ :=
  angPhase (-ℓ) x / (‖x‖ : ℂ)

/-- `W ℓ ζ x = e^{-iℓθ} ζ(|x|)/|x|`. -/
def W (ℓ : ℤ) (ζ : ℝ → ℂ) (x : ℂ) : ℂ :=
  pW ℓ x * ζ ‖x‖

/-- `fW ℓ ζ x = e^{-iℓθ} ζ(|x|)/|x|²`. -/
def fW (ℓ : ℤ) (ζ : ℝ → ℂ) (x : ℂ) : ℂ :=
  pW ℓ x / (‖x‖ : ℂ) * ζ ‖x‖

/-! ### Smoothness off the origin -/

theorem contDiffAt_ofReal_norm {x : ℂ} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : ℂ => ((‖y‖ : ℝ) : ℂ)) x :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_norm ℝ hx)

theorem ofReal_norm_ne_zero {x : ℂ} (hx : x ≠ 0) : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by
  simpa using hx

theorem contDiffAt_inv_ofReal_norm {x : ℂ} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : ℂ => ((‖y‖ : ℝ) : ℂ)⁻¹) x :=
  (contDiffAt_ofReal_norm hx).fun_inv (ofReal_norm_ne_zero hx)

theorem contDiffAt_unit {x : ℂ} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : ℂ => y / (‖y‖ : ℂ)) x := by
  have h := (contDiffAt_id (𝕜 := ℝ) (x := x)).mul (contDiffAt_inv_ofReal_norm hx)
  simpa [div_eq_mul_inv] using h

theorem contDiffAt_zpow_comp {u : ℂ → ℂ} {x : ℂ} (hu : ContDiffAt ℝ ∞ u x) (hx : u x ≠ 0)
    (m : ℤ) : ContDiffAt ℝ ∞ (fun y => u y ^ m) x := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simpa [zpow_natCast] using hu.pow n
  · simp only [zpow_neg, zpow_natCast]
    exact (hu.pow n).fun_inv (pow_ne_zero n hx)

theorem contDiffAt_angPhase (m : ℤ) {x : ℂ} (hx : x ≠ 0) : ContDiffAt ℝ ∞ (angPhase m) x := by
  have hne : x / (‖x‖ : ℂ) ≠ 0 := div_ne_zero hx (ofReal_norm_ne_zero hx)
  exact contDiffAt_zpow_comp (contDiffAt_unit hx) hne m

theorem contDiffAt_pW (ℓ : ℤ) {x : ℂ} (hx : x ≠ 0) : ContDiffAt ℝ ∞ (pW ℓ) x := by
  have h := (contDiffAt_angPhase (-ℓ) hx).mul (contDiffAt_inv_ofReal_norm hx)
  have e : pW ℓ = fun y => angPhase (-ℓ) y * ((‖y‖ : ℝ) : ℂ)⁻¹ := by
    funext y; simp [pW, div_eq_mul_inv]
  rw [e]
  exact h

theorem contDiffAt_pW_div (ℓ : ℤ) {x : ℂ} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => pW ℓ y / (‖y‖ : ℂ)) x := by
  have h := (contDiffAt_pW ℓ hx).mul (contDiffAt_inv_ofReal_norm hx)
  simpa [div_eq_mul_inv] using h

/-! ### Profiles that are test functions on `(0, ∞)` -/

theorem eq_zero_of_nonpos {ζ : ℝ → ℂ} (hζ : Sob.IsTestFn (Ioi 0) ζ) {r : ℝ} (hr : r ≤ 0) :
    ζ r = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => (not_lt.2 hr) (hζ.subset h)

theorem eventually_comp_norm_eq_zero {ζ : ℝ → ℂ} (hζ : Sob.IsTestFn (Ioi 0) ζ) :
    ∀ᶠ y in 𝓝 (0 : ℂ), ζ ‖y‖ = 0 := by
  have h0 : (0 : ℝ) ∉ tsupport ζ := fun h => lt_irrefl (0 : ℝ) (hζ.subset h)
  have h1 : ζ =ᶠ[𝓝 0] 0 := notMem_tsupport_iff_eventuallyEq.1 h0
  have hc : Tendsto (fun y : ℂ => ‖y‖) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_norm.tendsto (0 : ℂ))
  filter_upwards [hc.eventually h1] with y hy
  simpa using hy

theorem hasCompactSupport_comp_norm {ζ : ℝ → ℂ} (hζ : HasCompactSupport ζ) :
    HasCompactSupport (fun x : ℂ => ζ ‖x‖) := by
  obtain ⟨R, hR⟩ := hζ.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) fun x hx => ?_
  apply image_eq_zero_of_notMem_tsupport
  intro h
  apply hx
  have := hR h
  simpa [Real.norm_eq_abs] using this

theorem contDiff_mul_comp_norm {u : ℂ → ℂ} (hu : ∀ x ≠ 0, ContDiffAt ℝ ∞ u x) {ζ : ℝ → ℂ}
    (hζ : Sob.IsTestFn (Ioi 0) ζ) : ContDiff ℝ ∞ (fun x => u x * ζ ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [eventually_comp_norm_eq_zero hζ] with y hy
    simp [hy]
  · exact (hu x hx).mul (hζ.smooth.contDiffAt.comp x (contDiffAt_norm ℝ hx))

theorem isTestFn_mul_comp_norm {u : ℂ → ℂ} (hu : ∀ x ≠ 0, ContDiffAt ℝ ∞ u x) {ζ : ℝ → ℂ}
    (hζ : Sob.IsTestFn (Ioi 0) ζ) : Sob.IsTestFn univ (fun x => u x * ζ ‖x‖) :=
  ⟨contDiff_mul_comp_norm hu hζ, (hasCompactSupport_comp_norm hζ.compact).mul_left,
    subset_univ _⟩

theorem isTestFn_W (ℓ : ℤ) {ζ : ℝ → ℂ} (hζ : Sob.IsTestFn (Ioi 0) ζ) :
    Sob.IsTestFn univ (W ℓ ζ) :=
  isTestFn_mul_comp_norm (fun _ hx => contDiffAt_pW ℓ hx) hζ

theorem isTestFn_fW (ℓ : ℤ) {ζ : ℝ → ℂ} (hζ : Sob.IsTestFn (Ioi 0) ζ) :
    Sob.IsTestFn univ (fW ℓ ζ) :=
  isTestFn_mul_comp_norm (fun _ hx => contDiffAt_pW_div ℓ hx) hζ

/-! ### Values on circles and homogeneity -/

theorem angPhase_circleMap (m : ℤ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    angPhase m (circleMap 0 r θ) = Complex.exp ((m : ℂ) * (θ * Complex.I)) := by
  have hn : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [angPhase, hn, circleMap_zero, Complex.exp_int_mul]
  congr 1
  field_simp

theorem W_circleMap (ℓ : ℤ) (ζ : ℝ → ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    W ℓ ζ (circleMap 0 r θ) =
      Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) * (ζ r / (r : ℂ)) := by
  have hn : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr]
  rw [W, pW, angPhase_circleMap (-ℓ) hr θ, hn]
  push_cast
  ring_nf

theorem angPhase_smul (m : ℤ) {t : ℝ} (ht : 0 < t) (x : ℂ) :
    angPhase m (t • x) = angPhase m x := by
  rw [angPhase, angPhase, norm_smul, Real.norm_eq_abs, abs_of_pos ht, Complex.real_smul]
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  by_cases hx : x = 0
  · simp [hx]
  have hx' : ((‖x‖ : ℝ) : ℂ) ≠ 0 := ofReal_norm_ne_zero hx
  congr 1
  push_cast
  field_simp

theorem fW_smul (ℓ : ℤ) (ζ : ℝ → ℂ) {t : ℝ} (ht : 0 < t) (x : ℂ) :
    fW ℓ ζ (t • x) =
      angPhase (-ℓ) x / ((t * ‖x‖ : ℝ) : ℂ) / ((t * ‖x‖ : ℝ) : ℂ) * ζ (t * ‖x‖) := by
  have hn : ‖t • x‖ = t * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  rw [fW, pW, angPhase_smul (-ℓ) ht x, hn]

end NonUniqueEuler.Ang.ProfileDerivAux
