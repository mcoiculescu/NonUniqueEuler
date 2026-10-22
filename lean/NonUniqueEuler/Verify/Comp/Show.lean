import NonUniqueEuler.Verify.Comp.CBox

/-!
# Part 2 arithmetic layer: decimal display (debugging and tests only)

Not used by any algorithm or proof. `Dy.toSci x sig` prints `x` in scientific notation with
`sig` significant digits (truncated towards zero; display only). Core only.
-/

namespace NonUniqueEuler.Verify

/-- Number of decimal digits of `n` (`1` for `n = 0`). -/
def decDigits (n : Nat) : Nat := (toString n).length

/-- `|x|` truncated to `sig` significant decimal digits, as `"d.ddd…e±k"` (exact integer
arithmetic; display only). -/
def sciOfNatExp (a : Nat) (e : Int) (sig : Nat) : String :=
  if a = 0 then "0" else
  let b2 : Int := e + (bitLen a : Int) - 1               -- 2^b2 ≤ a·2^e < 2^(b2+1)
  let k0 : Int := (b2 * 30103) / 100000                  -- ≈ ⌊log₁₀⌋, may be off by one
  let s : Int := (sig : Int) - 1 - k0 + 1                -- one extra digit of slack
  let num : Nat := a * (if 0 ≤ e then 2 ^ e.toNat else 1) * (if 0 ≤ s then 10 ^ s.toNat else 1)
  let den : Nat := (if e < 0 then 2 ^ (-e).toNat else 1) * (if s < 0 then 10 ^ (-s).toNat else 1)
  let n : Nat := num / den
  let ds := toString n
  let nd := ds.length
  let ex : Int := (nd : Int) - 1 - s
  let digs := (ds.toList.take sig)
  let head := String.ofList (digs.take 1)
  let tail := String.ofList (digs.drop 1)
  head ++ (if tail.isEmpty then "" else "." ++ tail) ++ "e" ++ toString ex

namespace Dy
/-- Scientific notation with `sig` significant digits (truncated; display only). -/
def toSci (x : Dy) (sig : Nat := 20) : String :=
  (if x.man < 0 then "-" else "") ++ sciOfNatExp x.man.natAbs x.exp sig
instance : ToString Dy := ⟨fun x => toSci x⟩
end Dy

namespace UB
/-- Display. -/
def toSci (u : UB) (sig : Nat := 6) : String :=
  match u with
  | .fin m e => sciOfNatExp m e sig
  | .inf => "inf"
instance : ToString UB := ⟨fun u => toSci u⟩
end UB

namespace Ball
/-- Display as `mid ± rad`. -/
def toSci (x : Ball) (sig : Nat := 20) : String := x.mid.toSci sig ++ " ± " ++ x.rad.toSci
instance : ToString Ball := ⟨fun x => toSci x⟩
end Ball

namespace CBox
/-- Display. -/
def toSci (z : CBox) (sig : Nat := 20) : String :=
  "(" ++ z.re.toSci sig ++ ") + i(" ++ z.im.toSci sig ++ ")"
instance : ToString CBox := ⟨fun z => toSci z⟩
end CBox

end NonUniqueEuler.Verify
