import NonUniqueEuler.Verify.Comp.Series

/-!
# Part 2 arithmetic layer: optional operator notation

Optional. The arithmetic functions take the midpoint precision as an explicit first argument
(`Ball.add p x y`). Code that prefers operators can take an instance argument `[Prec]` and
write `x + y`, `x * y`, `-x`, `x - y`, `x / y`, `x⁻¹` for `Ball` and `CBox`; each operator is
*definitionally* the explicit function at precision `Prec.prec` (the lemmas `*_def` in
`Defs/Verify/Sem.lean` state this by `rfl`). The global default instance has
`prec = defaultPrec = 128`; a local `[Prec]` binder takes priority over it.

Core only.
-/

namespace NonUniqueEuler.Verify

/-- The midpoint precision (bits), passed as an instance. -/
class Prec where
  prec : Nat

/-- The default precision `defaultPrec = 128` (low priority: local instances win). -/
instance (priority := low) instPrecDefault : Prec := ⟨defaultPrec⟩

namespace Ball
instance instNeg : Neg Ball := ⟨neg⟩
instance instAdd [Prec] : Add Ball := ⟨add Prec.prec⟩
instance instSub [Prec] : Sub Ball := ⟨sub Prec.prec⟩
instance instMul [Prec] : Mul Ball := ⟨mul Prec.prec⟩
instance instInv [Prec] : Inv Ball := ⟨inv Prec.prec⟩
instance instDiv [Prec] : Div Ball := ⟨div Prec.prec⟩
end Ball

namespace CBox
instance instNeg : Neg CBox := ⟨neg⟩
instance instAdd [Prec] : Add CBox := ⟨add Prec.prec⟩
instance instSub [Prec] : Sub CBox := ⟨sub Prec.prec⟩
instance instMul [Prec] : Mul CBox := ⟨mul Prec.prec⟩
instance instInv [Prec] : Inv CBox := ⟨inv Prec.prec⟩
instance instDiv [Prec] : Div CBox := ⟨div Prec.prec⟩
end CBox

end NonUniqueEuler.Verify
