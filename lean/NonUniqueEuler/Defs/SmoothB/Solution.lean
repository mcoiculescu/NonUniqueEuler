import NonUniqueEuler.Statement.WeakSolution
import NonUniqueEuler.Defs.Sec2.Conventions
import NonUniqueEuler.Defs.SmoothB.Flow

/-!
# Global smooth solutions (`thm:smooth`): the solution class and `Smooth.sol`

Definitions for Theorem `thm:smooth` (`02_prelim.tex:553-595`, proved in
Appendix B, `B_global_smooth.tex:493-566`).

* `Amax ω₀ = ‖ω₀‖_{L^∞}`, `l1 ω₀ = ‖ω₀‖_{L¹}`, `Ustar ω₀ = (2‖ω₀‖_{L^∞}‖ω₀‖_{L¹}/π)^{1/2}`, and
  `suppRadius ω₀ R₀ t = R(t) = R₀ + U_* |t|` (thm:smooth(1));
* `IsSmoothDatum ω₀ R₀`: `ω₀ ∈ C_c^∞(ℝ²)` real with `supp ω₀ ⊂ B_{R₀}`;
* `SolCore ω₀ ω`: `ω ∈ C^∞(ℝ × ℝ²)` with properties (2)–(3) (velocity smooth, bounded with all
  derivatives on `[-T,T] × ℝ²`, divergence free; transport equation; datum);
* `IsSmoothSol ω₀ R₀ ω`: properties (1)–(3) for the radius `R₀` — the manuscript's
  characterization ("there is a unique `ω ∈ C^∞(ℝ × ℝ²)` such that (1)–(3)");
* `IsSmoothSolAll ω₀ ω`: `SolCore` and (1) for **every** admissible `R₀`; this `R₀`-free form
  selects the same function and makes `sol` independent of `R₀`;
* `sol ω₀`: the solution, chosen by `Classical.choose` among the `ω` with `IsSmoothSolAll ω₀ ω`
  (junk `0` if none; for `IsSmoothDatum ω₀ R₀` existence and uniqueness are `thm:smooth`);
* `vel ω₀ = K_BS ∗ sol ω₀`, `flow ω₀ t = Φ_t = Φ_v(t, 0, ·)` and `flowInv ω₀ t = Φ_t⁻¹ =
  Φ_v(0, t, ·)` (thm:smooth(4); `B_global_smooth.tex:522-526`);
* `IsC1SolOn I ω₀ ω̃`: the class of thm:smooth(5) (`C¹(I × ℝ²)` solutions with locally bounded
  support).

Conventions: `∂_t ω` is `deriv (fun s => ω s x) t`, `v · ∇ω` is `fderiv ℝ (ω t) x (v t x)`
(D2, D3); smoothness is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)` (= `C^∞`, D15; the scope
`ContDiff` is not opened because its notation makes `ω` a token); `supp` is the closed support
`tsupport`; "every derivative of `v`" is `iteratedFDeriv ℝ n` of the space–time map
`(t, x) ↦ v(t, x)`; `div v` is the classical `Prelim.divergence`. All lemmas in this file are
fully proved.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Smooth

/-- `A = ‖ω₀‖_{L^∞}` (`B_global_smooth.tex:186`; `‖ω₀‖_{L^∞}` in thm:smooth(1)). -/
def Amax (ω₀ : ℂ → ℝ) : ℝ :=
  (eLpNorm ω₀ ⊤ volume).toReal

/-- `‖ω₀‖_{L¹}`. -/
def l1 (ω₀ : ℂ → ℝ) : ℝ :=
  (eLpNorm ω₀ 1 volume).toReal

/-- `U_* = (2A‖ω₀‖_{L¹}/π)^{1/2}` (`B_global_smooth.tex:187`), the speed bound
`|v| ≤ U_*` (`lem:iterates`(iii)). -/
def Ustar (ω₀ : ℂ → ℝ) : ℝ :=
  Real.sqrt (2 * Amax ω₀ * l1 ω₀ / Real.pi)

/-- The support radius `R(t) = R₀ + (2‖ω₀‖_{L^∞}‖ω₀‖_{L¹}/π)^{1/2} |t| = R₀ + U_* |t|` of
thm:smooth(1) (`02_prelim.tex:566-567`, `B_global_smooth.tex:193`). -/
def suppRadius (ω₀ : ℂ → ℝ) (R₀ t : ℝ) : ℝ :=
  R₀ + Ustar ω₀ * |t|

/-- The hypotheses on the datum in thm:smooth (`02_prelim.tex:563`): `ω₀ ∈ C_c^∞(ℝ²)` is real
(by its type) with `supp ω₀ ⊂ B_{R₀}`. Compactness of the support follows
(`IsSmoothDatum.hasCompactSupport`). -/
structure IsSmoothDatum (ω₀ : ℂ → ℝ) (R₀ : ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω₀
  tsupport_subset : tsupport ω₀ ⊆ ball 0 R₀

/-- Properties (2)–(3) of thm:smooth (`02_prelim.tex:568-570`) together with `ω ∈ C^∞(ℝ × ℝ²)`:
`v = K_BS ∗ ω ∈ C^∞(ℝ × ℝ²)`; `v` and every derivative of `v` are bounded on `[-T, T] × ℝ²` for
every `T > 0`; `div v = 0`; `∂_t ω + v · ∇ω = 0` on `ℝ × ℝ²`; `ω(0) = ω₀`. -/
structure SolCore (ω₀ : ℂ → ℝ) (ω : ℝ → ℂ → ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry ω)
  velocity_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (velocityField ω))
  velocity_bounded : ∀ T : ℝ, 0 < T → ∀ n : ℕ, ∃ C : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ,
    ‖iteratedFDeriv ℝ n (Function.uncurry (velocityField ω)) (t, x)‖ ≤ C
  divergence_eq_zero : ∀ t x, Prelim.divergence (velocityField ω t) x = 0
  transport : ∀ t x, deriv (fun s => ω s x) t + fderiv ℝ (ω t) x (velocityField ω t x) = 0
  init : ω 0 = ω₀

/-- Properties (1)–(3) of thm:smooth for the radius `R₀` (`02_prelim.tex:564-570`): `SolCore`
and `supp ω(t) ⊂ B_{R(t)}` for every `t ∈ ℝ`. thm:smooth asserts that exactly one `ω` has them
when `IsSmoothDatum ω₀ R₀`. -/
structure IsSmoothSol (ω₀ : ℂ → ℝ) (R₀ : ℝ) (ω : ℝ → ℂ → ℝ) : Prop extends SolCore ω₀ ω where
  tsupport_subset : ∀ t : ℝ, tsupport (ω t) ⊆ ball 0 (suppRadius ω₀ R₀ t)

/-- `SolCore` and property (1) of thm:smooth for every radius `R₀` with `supp ω₀ ⊂ B_{R₀}`. By
uniqueness this is the solution of thm:smooth for each such `R₀`; the form does not depend on
a choice of `R₀`. -/
structure IsSmoothSolAll (ω₀ : ℂ → ℝ) (ω : ℝ → ℂ → ℝ) : Prop extends SolCore ω₀ ω where
  tsupport_subset : ∀ R₀ : ℝ, tsupport ω₀ ⊆ ball 0 R₀ →
    ∀ t : ℝ, tsupport (ω t) ⊆ ball 0 (suppRadius ω₀ R₀ t)

/-- **The global smooth solution** `ω` of thm:smooth with datum `ω₀` (`02_prelim.tex:563-570`),
chosen among the functions with `IsSmoothSolAll ω₀`; the junk value `0` if there is none.
For `IsSmoothDatum ω₀ R₀` the choice is the unique solution (thm:smooth, `I/SmoothB/…`). -/
@[irreducible] def sol (ω₀ : ℂ → ℝ) : ℝ → ℂ → ℝ :=
  open scoped Classical in
  if h : ∃ ω : ℝ → ℂ → ℝ, IsSmoothSolAll ω₀ ω then h.choose else fun _ _ => 0

/-- The velocity `v = K_BS ∗ ω` of the smooth solution (thm:smooth(2)). -/
def vel (ω₀ : ℂ → ℝ) : ℝ → ℂ → ℂ :=
  velocityField (sol ω₀)

/-- The flow `Φ_t = Φ(t, ·)` of `v`: `∂_t Φ(t,y) = v(t, Φ(t,y))`, `Φ(0,y) = y`
(thm:smooth(4), `02_prelim.tex:573-576`; `Φ(t,y) = Φ_v(t,0,y)`, `B_global_smooth.tex:522`). -/
def flow (ω₀ : ℂ → ℝ) (t : ℝ) (y : ℂ) : ℂ :=
  flowOf (vel ω₀) t 0 y

/-- The inverse `Φ_t⁻¹ = Φ_v(0, t, ·)` of the flow map (thm:smooth(4),
`B_global_smooth.tex:523-524`). -/
def flowInv (ω₀ : ℂ → ℝ) (t : ℝ) (x : ℂ) : ℂ :=
  flowOf (vel ω₀) 0 t x

/-- The class of thm:smooth(5) (`02_prelim.tex:580-585`) on an interval `I ∋ 0`:
`ω̃ ∈ C¹(I × ℝ²)`, `ω̃(0) = ω₀`, `∂_t ω̃ + (K_BS ∗ ω̃) · ∇ω̃ = 0` on `I × ℝ²`, and for each compact
subinterval `[a, b] ⊆ I` the supports of `ω̃(t)`, `t ∈ [a, b]`, lie in one disk `B_R̃`.
The left side of the equation is the derivative of `(t, x) ↦ ω̃(t, x)` within `I × ℝ²` in the
direction `(1, v(t, x))`, which is one-sided in `t` at the end points of `I`. -/
structure IsC1SolOn (I : Set ℝ) (ω₀ : ℂ → ℝ) (ω : ℝ → ℂ → ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ 1 (Function.uncurry ω) (I ×ˢ univ)
  init : ω 0 = ω₀
  transport : ∀ t ∈ I, ∀ x : ℂ,
    fderivWithin ℝ (Function.uncurry ω) (I ×ˢ univ) (t, x) (1, velocity (ω t) x) = 0
  tsupport_bounded : ∀ a b : ℝ, Icc a b ⊆ I →
    ∃ R : ℝ, ∀ t ∈ Icc a b, tsupport (ω t) ⊆ ball 0 R

/-! ### Basic lemmas (fully proved) -/

theorem Amax_nonneg (ω₀ : ℂ → ℝ) : 0 ≤ Amax ω₀ := ENNReal.toReal_nonneg

theorem l1_nonneg (ω₀ : ℂ → ℝ) : 0 ≤ l1 ω₀ := ENNReal.toReal_nonneg

theorem Ustar_nonneg (ω₀ : ℂ → ℝ) : 0 ≤ Ustar ω₀ := Real.sqrt_nonneg _

@[simp] theorem suppRadius_zero (ω₀ : ℂ → ℝ) (R₀ : ℝ) : suppRadius ω₀ R₀ 0 = R₀ := by
  simp [suppRadius]

theorem le_suppRadius (ω₀ : ℂ → ℝ) (R₀ t : ℝ) : R₀ ≤ suppRadius ω₀ R₀ t :=
  le_add_of_nonneg_right (mul_nonneg (Ustar_nonneg ω₀) (abs_nonneg t))

theorem suppRadius_mono_abs (ω₀ : ℂ → ℝ) (R₀ : ℝ) {t t' : ℝ} (h : |t| ≤ |t'|) :
    suppRadius ω₀ R₀ t ≤ suppRadius ω₀ R₀ t' :=
  add_le_add_right (mul_le_mul_of_nonneg_left h (Ustar_nonneg ω₀)) R₀

theorem IsSmoothDatum.hasCompactSupport {ω₀ : ℂ → ℝ} {R₀ : ℝ} (h : IsSmoothDatum ω₀ R₀) :
    HasCompactSupport ω₀ :=
  (isCompact_closedBall (0 : ℂ) R₀).of_isClosed_subset (isClosed_tsupport ω₀)
    (h.tsupport_subset.trans ball_subset_closedBall)

theorem IsSmoothSolAll.isSmoothSol {ω₀ : ℂ → ℝ} {ω : ℝ → ℂ → ℝ} {R₀ : ℝ}
    (h : IsSmoothSolAll ω₀ ω) (hR : tsupport ω₀ ⊆ ball 0 R₀) : IsSmoothSol ω₀ R₀ ω :=
  ⟨h.toSolCore, h.tsupport_subset R₀ hR⟩

/-- If some function has the properties of thm:smooth for every admissible radius, `sol ω₀` has
them. -/
theorem sol_spec {ω₀ : ℂ → ℝ} (h : ∃ ω : ℝ → ℂ → ℝ, IsSmoothSolAll ω₀ ω) :
    IsSmoothSolAll ω₀ (sol ω₀) := by
  classical
  rw [sol, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

theorem vel_eq (ω₀ : ℂ → ℝ) (t : ℝ) (x : ℂ) : vel ω₀ t x = velocity (sol ω₀ t) x := rfl

theorem velocityField_zero : velocityField (fun _ _ => (0 : ℝ)) = fun _ _ => (0 : ℂ) := by
  funext t x
  simp [velocityField, velocity]

/-- Non-vacuity: the zero datum satisfies the hypotheses of thm:smooth. -/
theorem isSmoothDatum_zero (R₀ : ℝ) : IsSmoothDatum (fun _ => (0 : ℝ)) R₀ :=
  ⟨contDiff_const, by simp⟩

/-- Non-vacuity: `ω ≡ 0` is the smooth solution with datum `0` (`B_global_smooth.tex:517-518`),
so `IsSmoothSolAll` is satisfiable and `sol_spec` applies to the zero datum. -/
theorem isSmoothSolAll_zero : IsSmoothSolAll (fun _ => (0 : ℝ)) (fun _ _ => 0) := by
  have hv := velocityField_zero
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, rfl⟩, ?_⟩
  · exact contDiff_const
  · rw [hv]; exact contDiff_const
  · intro T _ n
    refine ⟨0, fun t _ x => ?_⟩
    rw [hv]
    have : Function.uncurry (fun (_ : ℝ) (_ : ℂ) => (0 : ℂ)) = fun _ => 0 := rfl
    rw [this]
    simp
  · intro t x
    rw [hv]
    simp [Prelim.divergence_eq]
  · intro t x
    rw [hv]
    simp
  · intro R₀ _ t
    simp

end NonUniqueEuler.Smooth
