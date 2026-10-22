import NonUniqueEuler.I.Verify.Sound.Runs
import NonUniqueEuler.I.Verify.NPrimeN

/-!
# Proof of `I/Verify/Final.lean`: the checker is sound

Statement copied verbatim from `I/Verify/Final.lean`.

The runs (`check_N1'_N2'`, `I/Verify/Sound/Runs`, Proposition A.7) give (N1′) and (N2′) from
`check cert = true`; Lemma A.6 (`N1_N2_of_N1'_N2'`, `I/Verify/NPrimeN`) turns them into (N1)
and (N2).
-/

namespace NonUniqueEuler.Verify

/-- **Part (2), the final theorem**: the certificate checker is sound. -/
theorem check_sound : CheckerSound Verify.check := fun _ h _ hχ =>
  N1_N2_of_N1'_N2' hχ (check_N1'_N2' h hχ).1 (check_N1'_N2' h hχ).2

end NonUniqueEuler.Verify
