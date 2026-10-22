import NonUniqueEuler.Statement.MainTheorem
import Mathlib.Data.Rat.Defs

/-!
# Statement layer: the certificate data and the final statement (part (2))

Statement layer: definitions and statements only, no proofs.

Manuscript sources: `A_verification.tex:507-649` (Definition `def:Nprime`, the two runs,
Proposition `prop:runs`), and the certificate files
`euler-ring-certificate/certificates/sector3_{count,gap}_cells.json`
(format `ringcert-certificate-1`: a list of cells `{"G": [lo, hi], "rect": [x0, x1, y0, y1]}`
with exact rational entries, and run parameters).

Part (2) provides, outside the statement layer,
* a computable checker `check : CertificateData → Bool` (ball arithmetic, Taylor enclosure of
  `E_3`, winding count, coverage checks, all on exact dyadic/rational data), and
* the certificate `cert : CertificateData` transcribed from the two JSON files,
and proves `CheckerSound check` (`Verify.check_sound`). The final theorem is
`main_theorem_of_certificate : MainTheoremOfCertificate check cert` (`NonUniqueEuler/Final.lean`).

Non-vacuity of the final theorem rests on two things outside the kernel-checked proof:
`check` is an honest, terminating program, and its compiled run (the executable `ncert`, see
`README.md`) returns `true` on a working machine. This is the trust model of the formalization (the algorithm is verified; its run is
not replayed in the kernel); see `README.md`.
-/

noncomputable section

namespace NonUniqueEuler

open RingData

/-- A closed interval `[lo, hi]` of circulation parameters with rational endpoints. -/
structure QInterval where
  lo : ℚ
  hi : ℚ
deriving Repr, DecidableEq

/-- A closed rectangle `[x₀, x₁] × [y₀, y₁] ⊂ ℂ` with rational vertices (JSON order
`[x0, x1, y0, y1]`). -/
structure QRect where
  x₀ : ℚ
  x₁ : ℚ
  y₀ : ℚ
  y₁ : ℚ
deriving Repr, DecidableEq

/-- One certified pair `(𝒞, ℛ')`: an interval of `G` and a rectangle in the `λ`-plane. -/
structure CertCell where
  G : QInterval
  rect : QRect
deriving Repr, DecidableEq

/-- Parameters of a run (`A_verification.tex:559-602`): the density `ν` (for the `(N2')` run,
the numerator of `ν = 3/(x_i - 211/2500)`), the maximal numbers of rounds, of segments and of
halvings. -/
structure RunParams where
  density : ℚ
  maxRounds : ℕ
  maxSegments : ℕ
  maxHalvings : ℕ
deriving Repr, DecidableEq

/-- The certificate data: the cells and parameters of the `(N1')` run (`sector3_count`) and of
the `(N2')` run (`sector3_gap`). -/
structure CertificateData where
  countCells : List CertCell
  countParams : RunParams
  gapCells : List CertCell
  gapParams : RunParams
deriving Repr

/-- Soundness of a checker: if it accepts some certificate data, then (N1) and (N2) hold for
every admissible cutoff. ((N3) has a written proof without machine computation,
`prop:N3`.) Part (2) proves `CheckerSound Verify.check` (`Verify.check_sound`). -/
def CheckerSound (check : CertificateData → Bool) : Prop :=
  ∀ cert : CertificateData, check cert = true →
    ∀ χ : ℝ → ℝ, IsAdmissibleCutoff χ → N1 χ ∧ N2 χ

/-- **Statement of the final theorem** `main_theorem_of_certificate`: if the checker accepts the
certificate, then the explicit cutoff `chiStd` is admissible and Theorem 1.1 holds for every
admissible cutoff. -/
def MainTheoremOfCertificate (check : CertificateData → Bool) (cert : CertificateData) : Prop :=
  check cert = true → IsAdmissibleCutoff chiStd ∧ ∀ χ : ℝ → ℝ, IsAdmissibleCutoff χ → MainTheorem χ

end NonUniqueEuler
