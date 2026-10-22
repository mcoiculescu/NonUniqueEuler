import NonUniqueEuler.Defs.Verify.NPrime
import NonUniqueEuler.Defs.Verify.RunsBasic
import NonUniqueEuler.Verify.Comp.Runs
import NonUniqueEuler.I.Verify.Sound.CertifyCell

/-!
# Proof: the runs: a successful check gives (N1′) and (N2′)

Proof of the interface `I/Verify/Sound/Runs.lean` (same declarations, statements verbatim).

**Manuscript.** Proposition A.7 (`prop:runs`, `A_verification.tex:621-649`), with
Definition A.5 (`def:Nprime`, `A_verification.tex:513-527`). **Code.** `Verify/Comp/RunCore.lean`
(`checkCore`), `Verify/Comp/Runs.lean` (`check`).

The proof is the assembly of `checkCore_sound` (`Defs/Verify/RunsBasic.lean`, proved), which
reduces the claim to the soundness of each certification performed on the grid
`Grid.build p gridHpow gridOrder` with `ℓ = 3`, and `certifyCell_sound`
(`I/Verify/Sound/CertifyCell`), applicable because `1 ≤ gridOrder` (`gridOrder = 16`).
`check c` unfolds to `checkCore defaultPrec (CertSpec.ofCertificateData c)`.
-/

noncomputable section

namespace NonUniqueEuler.Verify

open RingData

/-- **The runs, at any precision** (Proposition A.7 for `checkCore`): if the checker accepts,
then (N1′) and (N2′) hold for every admissible cutoff. -/
theorem checkCore_N1'_N2' {p : ℕ} {spec : CertSpec} (h : checkCore p spec = true) {χ : ℝ → ℝ}
    (hχ : IsAdmissibleCutoff χ) : N1' χ ∧ N2' χ := by
  have hN : 1 ≤ gridOrder := by decide
  exact checkCore_sound h fun _ _ _ _ _ _ _ hw => certifyCell_sound hN hχ hw

/-- **The runs** (Proposition A.7): if `check cert = true`, then (N1′) and (N2′) hold for every
admissible cutoff; these are the hypotheses of Lemma A.6. -/
theorem check_N1'_N2' {cert : CertificateData} (h : check cert = true) {χ : ℝ → ℝ}
    (hχ : IsAdmissibleCutoff χ) : N1' χ ∧ N2' χ := by
  exact checkCore_N1'_N2' h hχ

end NonUniqueEuler.Verify
