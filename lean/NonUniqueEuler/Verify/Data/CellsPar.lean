import NonUniqueEuler.Verify.Data.Cells
import NonUniqueEuler.Verify.Comp.Par

/-!
# Part 2 data: the checker on the certificate is the multithreaded computation

`check_eq_checkCorePar : check cert = checkCorePar defaultPrec certLits`, from `check_cert`
(`Data/Cells.lean`) and `checkCorePar_eq` (`Comp/Par.lean`). Nothing is evaluated and
`certLits` is not unfolded. So the value printed by `ncert par` (`Verify/Main.lean`), which is
`checkCorePar defaultPrec certLits` (`checkCorePar_def`), is the hypothesis `check cert` of the
final theorem.
-/

namespace NonUniqueEuler.Verify

/-- The checker on the certificate is the multithreaded core computation of the executable. -/
theorem check_eq_checkCorePar : check cert = checkCorePar defaultPrec certLits := by
  rw [check_cert, checkCorePar_eq]

end NonUniqueEuler.Verify
