import NonUniqueEuler
import NonUniqueEuler.Verify.Data.CellsPar

/-!
# Axioms of the final theorems

Run from the root of the repository, after `lake build`:

    lake env lean tools/PrintAxioms.lean

Each command should print only `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms NonUniqueEuler.main_theorem_of_N
#print axioms NonUniqueEuler.main_theorem_of_certificate
#print axioms NonUniqueEuler.main_theorem_full
#print axioms NonUniqueEuler.Verify.check_sound
#print axioms NonUniqueEuler.Verify.check_cert
#print axioms NonUniqueEuler.Verify.check_eq_checkCorePar
