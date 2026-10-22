import NonUniqueEuler.Defs.SmoothB.Solution
import NonUniqueEuler.Defs.Infra.Sobolev
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Appendix B: the iteration, its constants and its majorants

Definitions for `B_global_smooth.tex` §B.2–§B.4: `lem:grad-bound`,
`lem:comm-R2`, the constants of §B.3 (`B_global_smooth.tex:181-198`), `def:iterates`,
`lem:iterates`, `lem:iter-lip`, `lem:iter-Hs`, `lem:iter-cauchy`, `prop:iter-limit`, and
`lem:smooth-bounds`.

* `gradSup g = ‖∇g‖_{L^∞} = sup_x |∇g(x)|` (`lem:grad-bound`), `N0 ω₀ = sup_x |∇ω₀(x)|`;
  `|∇g(x)| = ‖Dg(x)‖` for a real scalar `g` (`Prelim.norm_fderiv_eq_norm_grad`);
* `gradSupC g = sup_x |∇g(x)|` for complex `g` (`lem:comm-R2`);
* `gradEntryMax u = |∇u|_max = max_{i,l} sup_x |∂_l u_i(x)|` (`lem:comm-R2`);
* `cstar`, `calL` (`𝓛`), `Psi` (`Ψ`), `Vbd` (`V`) of `B_global_smooth.tex:186-193`, with
  `A = Amax ω₀`, `U_* = Ustar ω₀`, `R(t) = suppRadius ω₀ R₀ t` (`Defs/SmoothB/Solution.lean`);
* `iter ω₀ j = ω^{[j]}`, `iterVel ω₀ j = v^{[j]}`, `iterFlow ω₀ j = Φ^{[j]}` (`def:iterates`);
* `iterErr ω₀ j t = e_j(t) = ‖ω^{[j]}(t) - ω^{[j-1]}(t)‖_{L²}` (`lem:iter-cauchy`);
* `calM ω₀ R₀ s T = 𝓜_s(T)` and `calB ω₀ R₀ s T = 𝓑_s(T)` (`lem:iter-Hs`);
* `spaceD γ f t = ∂_x^γ f(t, ·)` (classical, `Sob.partialD`), for the convergence statements of
  `prop:iter-limit`; `ofRealST ω` is `ω` viewed as complex valued.

`def:iterates` defines `ω^{[j+1]}` only when `v^{[j]}` satisfies the hypotheses of `lem:flow`;
here `iter` is defined for every `j` (through the junk-valued `flowOf`), and `lem:iterates` shows
that the hypotheses hold, so the two definitions agree. Norms are those of the manuscript:
`‖·‖_{L^p}` is `eLpNorm`, `‖·‖_{H^s}` of a real function `g` is `Sob.normH s (fun x => (g x : ℂ))`.
Suprema over `x` are real `iSup`s (junk `0` when unbounded); statements carry boundedness
hypotheses or use the explicit bounds. All lemmas in this file are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Smooth

/-- `‖∇g‖_{L^∞} = sup_x |∇g(x)|` (`lem:grad-bound`, `B_global_smooth.tex:119-120`), with
`|∇g(x)| = ‖Dg(x)‖` the Euclidean norm of the gradient. A real `iSup`: meaningful when the set
of values is bounded above (e.g. `g ∈ C¹_c`). -/
def gradSup (g : ℂ → ℝ) : ℝ :=
  ⨆ x : ℂ, ‖fderiv ℝ g x‖

/-- `‖∇g‖_{L^∞} = sup_x |∇g(x)|` for a complex function `g` (`lem:comm-R2`,
`B_global_smooth.tex:157`), with `|∇g(x)| = Prelim.gradAbs g x` the Euclidean norm of
`(∂₁g(x), ∂₂g(x))`. A real `iSup`: meaningful when bounded (e.g. `g ∈ C_c^∞`). -/
def gradSupC (g : ℂ → ℂ) : ℝ :=
  ⨆ x : ℂ, Prelim.gradAbs g x

/-- `|∇u|_max = max_{i,l} sup_x |∂_l u_i(x)|` (`lem:comm-R2`, `B_global_smooth.tex:153-154`).
A real `iSup`: meaningful when the entries are bounded. -/
def gradEntryMax (u : ℂ → ℂ) : ℝ :=
  ⨆ x : ℂ, ⨆ i : Fin 2, ⨆ l : Fin 2, |Prelim.gradEntry u i l x|

/-- `N₀ = sup_x |∇ω₀(x)|` (`B_global_smooth.tex:186`). -/
def N0 (ω₀ : ℂ → ℝ) : ℝ :=
  gradSup ω₀

/-- `c_* = 2 + ‖ω₀‖_{L¹}/(2πA)` (`B_global_smooth.tex:188`). -/
def cstar (ω₀ : ℂ → ℝ) : ℝ :=
  2 + l1 ω₀ / (2 * Real.pi * Amax ω₀)

/-- `𝓛(t) = (log₊(N₀/A) + c_*) e^{2A|t|} - c_*` (`B_global_smooth.tex:190`). -/
def calL (ω₀ : ℂ → ℝ) (t : ℝ) : ℝ :=
  (Real.posLog (N0 ω₀ / Amax ω₀) + cstar ω₀) * Real.exp (2 * Amax ω₀ * |t|) - cstar ω₀

/-- `Ψ(t) = A e^{𝓛(t)}` (`B_global_smooth.tex:191`), the bound `|∇ω^{[j]}(t,x)| ≤ Ψ(t)`. -/
def Psi (ω₀ : ℂ → ℝ) (t : ℝ) : ℝ :=
  Amax ω₀ * Real.exp (calL ω₀ t)

/-- `V(t) = 2A(𝓛(t) + c_*)` (`B_global_smooth.tex:192`), the bound `‖∇v^{[j]}(t,x)‖_op ≤ V(t)`. -/
def Vbd (ω₀ : ℂ → ℝ) (t : ℝ) : ℝ :=
  2 * Amax ω₀ * (calL ω₀ t + cstar ω₀)

/-- The iterates of `def:iterates` (`B_global_smooth.tex:199-206`): `ω^{[0]}(t, x) = ω₀(x)` and
`ω^{[j+1]}(t, x) = ω₀(Φ^{[j]}(0, t, x))`, where `Φ^{[j]} = Φ_{v^{[j]}}` is the flow of
`v^{[j]} = K_BS ∗ ω^{[j]}`. -/
def iter (ω₀ : ℂ → ℝ) : ℕ → ℝ → ℂ → ℝ
  | 0 => fun _ x => ω₀ x
  | j + 1 => fun t x => ω₀ (flowOf (velocityField (iter ω₀ j)) 0 t x)

/-- `v^{[j]} = K_BS ∗ ω^{[j]}` (`def:iterates`). -/
def iterVel (ω₀ : ℂ → ℝ) (j : ℕ) : ℝ → ℂ → ℂ :=
  velocityField (iter ω₀ j)

/-- `Φ^{[j]} = Φ_{v^{[j]}}`, the two-time flow of `v^{[j]}` (`def:iterates`). -/
def iterFlow (ω₀ : ℂ → ℝ) (j : ℕ) : ℝ → ℝ → ℂ → ℂ :=
  flowOf (iterVel ω₀ j)

/-- `e_j(t) = ‖ω^{[j]}(t) - ω^{[j-1]}(t)‖_{L²}` (`lem:iter-cauchy`, `B_global_smooth.tex:356`;
used for `j ≥ 1`). -/
def iterErr (ω₀ : ℂ → ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  (eLpNorm (iter ω₀ j t - iter ω₀ (j - 1) t) 2 volume).toReal

/-- The expression `(s+1) 2^{s+2} (V + M + M Ψ)` of `𝓑_s(T)` (`B_global_smooth.tex:310`), as a
function of `V = V(T)`, `M = 𝓜_{s-1}(T)` and `Ψ = Ψ(T)`. -/
def calBof (s : ℕ) (V M Ψ : ℝ) : ℝ :=
  ((s : ℝ) + 1) * 2 ^ (s + 2) * (V + M + M * Ψ)

/-- The bounds `𝓜_s(T)` of `lem:iter-Hs` (`B_global_smooth.tex:305-311`):
`𝓜_1(T)² = ‖ω₀‖²_{L²} + π R(T)² Ψ(T)²` and, for `s ≥ 2`,
`𝓜_s(T)² = (‖ω₀‖²_{H^s} + 𝓜_{s-1}(T)² + 1) e^{𝓑_s(T) T} + 𝓜_{s-1}(T)²`, where
`R(T) = suppRadius ω₀ R₀ T`. The value at `s = 0` (`‖ω₀‖_{L²}`) is not used by the manuscript. -/
def calM (ω₀ : ℂ → ℝ) (R₀ : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => (eLpNorm ω₀ 2 volume).toReal
  | 1, T => Real.sqrt ((eLpNorm ω₀ 2 volume).toReal ^ 2 +
      Real.pi * suppRadius ω₀ R₀ T ^ 2 * Psi ω₀ T ^ 2)
  | s + 2, T => Real.sqrt
      ((Sob.normH (s + 2) (fun x => (ω₀ x : ℂ)) ^ 2 + calM ω₀ R₀ (s + 1) T ^ 2 + 1) *
          Real.exp (calBof (s + 2) (Vbd ω₀ T) (calM ω₀ R₀ (s + 1) T) (Psi ω₀ T) * T) +
        calM ω₀ R₀ (s + 1) T ^ 2)

/-- `𝓑_s(T) = (s+1) 2^{s+2} (V(T) + 𝓜_{s-1}(T) + 𝓜_{s-1}(T) Ψ(T))` (`B_global_smooth.tex:310`;
used for `s ≥ 2`). -/
def calB (ω₀ : ℂ → ℝ) (R₀ : ℝ) (s : ℕ) (T : ℝ) : ℝ :=
  calBof s (Vbd ω₀ T) (calM ω₀ R₀ (s - 1) T) (Psi ω₀ T)

/-- A real space–time function viewed as complex valued. -/
def ofRealST (ω : ℝ → ℂ → ℝ) : ℝ → ℂ → ℂ :=
  fun t x => (ω t x : ℂ)

/-- The spatial derivative `∂_x^γ f(t, x)` (classical, `Sob.partialD`) of a space–time function
(`prop:iter-limit`, `B_global_smooth.tex:384-387`). -/
def spaceD (γ : ℕ × ℕ) (f : ℝ → ℂ → ℂ) (t : ℝ) : ℂ → ℂ :=
  Sob.partialD γ (f t)

/-! ### Basic lemmas (fully proved) -/

@[simp] theorem iter_zero (ω₀ : ℂ → ℝ) (t : ℝ) (x : ℂ) : iter ω₀ 0 t x = ω₀ x := rfl

theorem iter_succ (ω₀ : ℂ → ℝ) (j : ℕ) (t : ℝ) (x : ℂ) :
    iter ω₀ (j + 1) t x = ω₀ (iterFlow ω₀ j 0 t x) := rfl

theorem calM_succ_succ (ω₀ : ℂ → ℝ) (R₀ : ℝ) (s : ℕ) (T : ℝ) :
    calM ω₀ R₀ (s + 2) T = Real.sqrt
      ((Sob.normH (s + 2) (fun x => (ω₀ x : ℂ)) ^ 2 + calM ω₀ R₀ (s + 1) T ^ 2 + 1) *
          Real.exp (calB ω₀ R₀ (s + 2) T * T) + calM ω₀ R₀ (s + 1) T ^ 2) := by
  simp only [calB]
  rfl

theorem calM_nonneg (ω₀ : ℂ → ℝ) (R₀ : ℝ) (s : ℕ) (T : ℝ) : 0 ≤ calM ω₀ R₀ s T := by
  match s with
  | 0 => exact ENNReal.toReal_nonneg
  | 1 => exact Real.sqrt_nonneg _
  | _ + 2 => exact Real.sqrt_nonneg _

theorem cstar_ge_two (ω₀ : ℂ → ℝ) : 2 ≤ cstar ω₀ := by
  have : 0 ≤ l1 ω₀ / (2 * Real.pi * Amax ω₀) :=
    div_nonneg (l1_nonneg ω₀) (mul_nonneg (by positivity) (Amax_nonneg ω₀))
  simp only [cstar]
  linarith

@[simp] theorem calL_neg (ω₀ : ℂ → ℝ) (t : ℝ) : calL ω₀ (-t) = calL ω₀ t := by
  simp [calL]

@[simp] theorem Psi_neg (ω₀ : ℂ → ℝ) (t : ℝ) : Psi ω₀ (-t) = Psi ω₀ t := by
  simp [Psi]

@[simp] theorem Vbd_neg (ω₀ : ℂ → ℝ) (t : ℝ) : Vbd ω₀ (-t) = Vbd ω₀ t := by
  simp [Vbd]

/-- `𝓛(0) = log₊(N₀/A)` (`B_global_smooth.tex:195`). -/
theorem calL_zero (ω₀ : ℂ → ℝ) : calL ω₀ 0 = Real.posLog (N0 ω₀ / Amax ω₀) := by
  simp [calL]

/-- `𝓛 ≥ 𝓛(0) = log₊(N₀/A) ≥ 0` (`B_global_smooth.tex:195`). -/
theorem posLog_le_calL (ω₀ : ℂ → ℝ) (t : ℝ) : Real.posLog (N0 ω₀ / Amax ω₀) ≤ calL ω₀ t := by
  have he : 1 ≤ Real.exp (2 * Amax ω₀ * |t|) :=
    Real.one_le_exp (mul_nonneg (mul_nonneg zero_le_two (Amax_nonneg ω₀)) (abs_nonneg t))
  have hP : 0 ≤ Real.posLog (N0 ω₀ / Amax ω₀) := Real.posLog_nonneg
  have hc : 0 ≤ cstar ω₀ := le_trans zero_le_two (cstar_ge_two ω₀)
  have := mul_le_mul_of_nonneg_left he (add_nonneg hP hc)
  simp only [calL]
  linarith

theorem calL_nonneg (ω₀ : ℂ → ℝ) (t : ℝ) : 0 ≤ calL ω₀ t :=
  le_trans Real.posLog_nonneg (posLog_le_calL ω₀ t)

theorem Psi_nonneg (ω₀ : ℂ → ℝ) (t : ℝ) : 0 ≤ Psi ω₀ t :=
  mul_nonneg (Amax_nonneg ω₀) (Real.exp_pos _).le

theorem Vbd_nonneg (ω₀ : ℂ → ℝ) (t : ℝ) : 0 ≤ Vbd ω₀ t :=
  mul_nonneg (mul_nonneg zero_le_two (Amax_nonneg ω₀))
    (add_nonneg (calL_nonneg ω₀ t) (le_trans zero_le_two (cstar_ge_two ω₀)))

end NonUniqueEuler.Smooth
