import NonUniqueEuler.I.Main.Reduction
import NonUniqueEuler.I.Verify.Final
import NonUniqueEuler.I.Verify.N3
import NonUniqueEuler.I.Ring.ChiStd
import NonUniqueEuler.Verify.Data.Cells

/-!
# The final theorems

* `main_theorem_of_certificate`: if the Lean certificate checker `Verify.check` accepts the
  certificate `Verify.cert` (the data of Part II, Appendix A, `app:verify`), then
  the explicit cutoff `chiStd` is admissible and Theorem 1.1 of Parts I and II
  (`thm:main`) holds for every admissible cutoff `χ`.
* `main_theorem_full`: the same, with the non-vacuity witness and the soundness of the checker
  stated unconditionally, and with Hypothesis (N) (Part II, Theorem 1.3, `thm:N-holds`) also in the
  conclusion.

Inputs:
* the conditional reduction `main_theorem_of_N : ConditionalTheorem`
  (Part II, Proposition 1.2, `prop:reduction`);
* the soundness of the checker `Verify.check_sound : CheckerSound Verify.check`
  (Part II, Propositions A.3, A.4 and A.7, and Lemma A.6: `prop:enclosure`,
  `prop:winding`, `prop:runs`, `lem:Nprime-N`);
* `n3_holds : N3` (Part II, Proposition A.8, `prop:N3`, a written proof without machine computation);
* `chiStd_admissible` (the cutoff of the proof of Part I, Lemma 4.2, `lem:ring-facts`).

The hypothesis `Verify.check Verify.cert = true` is a closed Boolean computation. Kernel
evaluation of it is infeasible (it takes many CPU-hours even as compiled code), so it is established
by running the compiled executable `ncert` (`NonUniqueEuler/Verify/Main.lean`), which evaluates
`checkCorePar defaultPrec certLits`, equal to `check cert` by `Verify.check_eq_checkCorePar`.
-/

namespace NonUniqueEuler

open RingData

/-- **Theorem 1.1 of Parts I and II (`thm:main`) from the certificate.** -/
theorem main_theorem_of_certificate : MainTheoremOfCertificate Verify.check Verify.cert := by
  intro h
  refine ⟨chiStd_admissible, fun χ hχ => main_theorem_of_N χ hχ ?_⟩
  exact ⟨(Verify.check_sound Verify.cert h χ hχ).1, (Verify.check_sound Verify.cert h χ hχ).2,
    n3_holds⟩

/-- **The full final statement.** The admissible class is nonempty and the checker is sound
(unconditionally); if the checker accepts the certificate, then for every admissible cutoff,
Hypothesis (N) and Theorem 1.1 of Parts I and II (`thm:main`) hold. -/
theorem main_theorem_full :
    IsAdmissibleCutoff chiStd ∧ CheckerSound Verify.check ∧
      (Verify.check Verify.cert = true →
        ∀ χ : ℝ → ℝ, IsAdmissibleCutoff χ → NumericalHypothesis χ ∧ MainTheorem χ) := by
  refine ⟨chiStd_admissible, Verify.check_sound, fun h χ hχ => ?_⟩
  have hN : NumericalHypothesis χ :=
    ⟨(Verify.check_sound Verify.cert h χ hχ).1, (Verify.check_sound Verify.cert h χ hχ).2,
      n3_holds⟩
  exact ⟨hN, main_theorem_of_N χ hχ hN⟩

end NonUniqueEuler
