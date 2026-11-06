import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The integrals `I_p(x)` (definition; eq:Ip)

Manuscript Part I, Equation (3) (`eq:Ip`): for `x > 0` and an integer `p ≥ 0`,
`I_p(x) = ∫₀^∞ e^{-xu} (1+u)^p du = ∑_{j=0}^p p!/((p-j)! x^{j+1})`, a decreasing function of `x`.
Used in the proof of Part I, Proposition 4.15 (`prop:large-sectors`), the
polynomial-drive estimate in Part II, Proposition 5.2 (`prop:kick`), the relay
estimates in Part II, Section 6 (`sec:relay`) and Appendix C.5–C.13, and the
parameter lists in Part II, Appendix C.2 (`sec:param-lists`). The former
`lem:pinning` remains a separate utility in the Lean proof decomposition.

Definition.
* `Ip p x = ∫ u in Ioi 0, exp (-x u) (1+u)^p` (Bochner integral; it is the junk value `0` for
  `x ≤ 0`, where the integrand is not integrable). Every theorem assumes `0 < x`.

The theorems (closed form, recursion, monotonicity, the bounds used by the consumers) are in
`NonUniqueEuler/I/Infra/Ip/Ip.lean`.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

/-- `I_p(x) = ∫₀^∞ e^{-xu} (1+u)^p du` (Part I, Equation (3), `eq:Ip`). -/
def Ip (p : ℕ) (x : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.exp (-x * u) * (1 + u) ^ p

end NonUniqueEuler
