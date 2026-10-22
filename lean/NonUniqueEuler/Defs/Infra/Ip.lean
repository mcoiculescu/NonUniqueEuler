import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The integrals `I_p(x)` (definition; eq:Ip)

Manuscript `02_prelim.tex:84-92`, label `eq:Ip`: for `x > 0` and an integer `p ≥ 0`,
`I_p(x) = ∫₀^∞ e^{-xu} (1+u)^p du = ∑_{j=0}^p p!/((p-j)! x^{j+1})`, a decreasing function of `x`.
Used in `lem:semigroup-construct`-type bounds (`04_ring.tex:1019-1038`), `lem:pinning`,
`prop:kick` (`08_kick.tex:179-277`), Section 9 (`09_relay.tex`) and the parameter lists
(`10_parameters.tex`).

Definition.
* `Ip p x = ∫ u in Ioi 0, exp (-x u) (1+u)^p` (Bochner integral; it is the junk value `0` for
  `x ≤ 0`, where the integrand is not integrable). Every theorem assumes `0 < x`.

The theorems (closed form, recursion, monotonicity, the bounds used by the consumers) are in
`NonUniqueEuler/I/Infra/Ip/Ip.lean`.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

/-- `I_p(x) = ∫₀^∞ e^{-xu} (1+u)^p du` (eq:Ip, `02_prelim.tex:88`). -/
def Ip (p : ℕ) (x : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.exp (-x * u) * (1 + u) ^ p

end NonUniqueEuler
