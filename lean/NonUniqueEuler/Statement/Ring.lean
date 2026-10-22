import NonUniqueEuler.Statement.Plane
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Statement layer: the ring `Φ`

Statement layer: definitions and statements only, no proofs.

Manuscript sources: `04_ring.tex:24-54` (Definition `def:ring`), `04_ring.tex:61-99`
(Lemma `lem:ring-facts`, whose proof constructs one admissible cutoff), and
`A_verification.tex:26-28` ("every statement of this appendix holds for every function `χ`
with the properties listed in Definition `def:ring`").

The pinned dyadic data are written exactly as in `04_ring.tex:29-31`; the Python package uses
the names `a0, d, sL, sa, sb, sR` for the same numbers
(`euler-ring-certificate/certificates/*.json`).

The cutoff. Definition `def:ring` fixes "once and for all" a function `χ` with the properties
listed there. We do not choose one: `IsAdmissibleCutoff χ` lists exactly these properties, every
object below takes `χ` as an argument, and the main theorem is stated for every admissible `χ`
(which is stronger than the statement for one fixed `χ`). The explicit cutoff `chiStd` of the
proof of `lem:ring-facts` is given for non-vacuity; that it is admissible is the statement
`ChiStdAdmissible`, proved in `P/Ring/ChiStd.lean` (`chiStd_admissible`).
-/

noncomputable section

open Set
open scoped ContDiff

namespace NonUniqueEuler

namespace RingData

/-- `a₀ = -7304210039150669 · 2⁻⁵⁴` (`04_ring.tex:29`). -/
def a₀ : ℝ := -7304210039150669 / 2 ^ 54

/-- `d = 5764607523034235 · 2⁻⁵⁸` (`04_ring.tex:29`). -/
def d : ℝ := 5764607523034235 / 2 ^ 58

/-- `ξ_L = -4528212286209965 · 2⁻⁵²` (`04_ring.tex:30`). -/
def ξL : ℝ := -4528212286209965 / 2 ^ 52

/-- `ξ_a = -4077852323472915 · 2⁻⁵²` (`04_ring.tex:30`). -/
def ξa : ℝ := -4077852323472915 / 2 ^ 52

/-- `ξ_b = 1/2` (`04_ring.tex:31`). -/
def ξb : ℝ := 1 / 2

/-- `ξ_R = 5404319552844595 · 2⁻⁵³` (`04_ring.tex:31`). -/
def ξR : ℝ := 5404319552844595 / 2 ^ 53

/-- `H(x) = (1 + e^{-2x})⁻¹` (`04_ring.tex:34`). -/
def H (x : ℝ) : ℝ := (1 + Real.exp (-2 * x))⁻¹

/-- The admissible cutoffs of Definition `def:ring` (`04_ring.tex:34-37`): `χ ∈ C_c^∞(ℝ)` with
values in `[0, 1]`, nondecreasing on `(-∞, ξ_a]`, equal to `1` on `[ξ_a, ξ_b]`, nonincreasing on
`[ξ_b, ∞)`, and supported in `[ξ_L, ξ_R]`. (Compactness of the support follows from
`tsupport χ ⊆ [ξ_L, ξ_R]`.) -/
structure IsAdmissibleCutoff (χ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ χ
  mem_Icc : ∀ ξ : ℝ, χ ξ ∈ Icc (0 : ℝ) 1
  monotoneOn : MonotoneOn χ (Iic ξa)
  eq_one : ∀ ξ ∈ Icc ξa ξb, χ ξ = 1
  antitoneOn : AntitoneOn χ (Ici ξb)
  tsupport_subset : tsupport χ ⊆ Icc ξL ξR

/-- The cutoff constructed in the proof of `lem:ring-facts` (`04_ring.tex:71-76`):
`χ(ξ) = S((ξ - ξ_L)/(ξ_a - ξ_L)) · S((ξ_R - ξ)/(ξ_R - ξ_b))`, where
`S(x) = e(x)/(e(x) + e(1-x))`, `e(x) = e^{-1/x}` for `x > 0` and `0` otherwise. Mathlib's
`Real.smoothTransition` is exactly `S` (it is defined from `expNegInvGlue = e`). -/
def chiStd (ξ : ℝ) : ℝ :=
  Real.smoothTransition ((ξ - ξL) / (ξa - ξL)) * Real.smoothTransition ((ξR - ξ) / (ξR - ξb))

/-- Statement (proved as `chiStd_admissible`, `P/Ring/ChiStd.lean`): `chiStd` is admissible. This
shows that the universally quantified statements over admissible cutoffs are not vacuous. -/
def ChiStdAdmissible : Prop := IsAdmissibleCutoff chiStd

/-- The ring profile in the variable `ξ = log r`:
`ϖ(ξ) = χ(ξ) H((ξ - a₀)/d) H(-ξ/d)` (`04_ring.tex:41`). -/
def prof (χ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  χ ξ * H ((ξ - a₀) / d) * H (-ξ / d)

/-- The ring in reference units: `ω̄_c(x) = ϖ(log|x|)` for `x ≠ 0`, `ω̄_c(0) = 0`
(`04_ring.tex:42`). -/
def ringRef (χ : ℝ → ℝ) (x : ℂ) : ℝ :=
  if x = 0 then 0 else prof χ (Real.log ‖x‖)

/-- The dilation factor `R_c = e^{ξ_R}` (`04_ring.tex:46`). -/
def Rc : ℝ := Real.exp ξR

/-- **The ring** `Φ(y) = ω̄_c(R_c y)`, in ring units (`04_ring.tex:46-49`). -/
def ringPhi (χ : ℝ → ℝ) (y : ℂ) : ℝ :=
  ringRef χ ((Rc : ℂ) * y)

/-- `a = e^{ξ_L - ξ_R}` (`04_ring.tex:46`); `supp Φ ⊂ {a ≤ |y| ≤ 1}`. -/
def a : ℝ := Real.exp (ξL - ξR)

/-- `G_max = 1/50` (`04_ring.tex:47`). -/
def Gmax : ℝ := 1 / 50

/-- `Ḡ = G_max R_c⁻²`, the circulation range in ring units (`04_ring.tex:47`). -/
def Gbar : ℝ := (1 / 50) * (Rc ^ 2)⁻¹

/-- Statement of `lem:ring-facts` (`04_ring.tex:61-69`) for an admissible cutoff, in the part
used by the main theorem: `Φ ∈ C_c^∞(ℝ²)` (as a function on `ℂ ≅ ℝ²`), `Φ` is radial,
`0 ≤ Φ < 1`, `Φ ≢ 0`, `supp Φ ⊂ {a ≤ |y| ≤ 1}`, and `0 < a < 1`. Proved in
`P/Sec4/RingFacts.lean` (`ringFacts_of_admissible`); recorded here so that reviewers can check
that the ring is not degenerate. -/
def RingFacts (χ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ (ringPhi χ) ∧ HasCompactSupport (ringPhi χ) ∧
    IsRadialPointwise (ringPhi χ) ∧ (∀ y, 0 ≤ ringPhi χ y ∧ ringPhi χ y < 1) ∧
    (∃ y, ringPhi χ y ≠ 0) ∧ tsupport (ringPhi χ) ⊆ {y : ℂ | a ≤ ‖y‖ ∧ ‖y‖ ≤ 1} ∧
    0 < a ∧ a < 1

end RingData

end NonUniqueEuler
