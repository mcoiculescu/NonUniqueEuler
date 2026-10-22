/-!
# Part 2 arithmetic layer: dyadic numbers `Dy`

Checker design decision D2 (see `FORMALIZATION_NOTES.md`).

A dyadic number `Dy` is a pair `(man, exp)` of integers with value `man · 2^exp`
(semantics `Dy.toReal` in `NonUniqueEuler/Defs/Verify/Sem.lean`). There is no normalization:
several pairs have the same value. The ring operations `neg`, `add`, `sub`, `mul`, `scale`
are exact. `floorP p` / `ceilP p` round to at most `p` significant bits, downwards / upwards.
`recipDown p` / `recipUp p` enclose `1/x` for `x ≠ 0`.

This file imports only Lean core (checker design decision D6): it is compiled code, with no
`partial`, `implemented_by`, `extern`, `unsafe` or `Float`.
-/

namespace NonUniqueEuler.Verify

/-- An upper bound on the number of binary digits: `n < 2 ^ bitLen n` for every `n`
(`Nat.lt_log2_self`); for `n > 0` it is the exact bit length, and `bitLen 0 = 1`. -/
@[inline] def bitLen (n : Nat) : Nat := n.log2 + 1

/-- `shl m k = m · 2^k` (`Nat.one_shiftLeft`). Implemented as a multiplication by the
`Nat` power of two, which is cheaper than `Int.shiftLeft` on large negative integers. -/
@[inline] def shl (m : Int) (k : Nat) : Int := if k = 0 then m else m * ((1 <<< k : Nat) : Int)

/-- `shr m k = ⌊m / 2^k⌋` (`Int.shiftRight_eq_div_pow`; floor division, also for `m < 0`). -/
@[inline] def shr (m : Int) (k : Nat) : Int := m >>> k

/-- A dyadic number `man · 2^exp`. -/
structure Dy where
  man : Int
  exp : Int
deriving Inhabited, Repr

namespace Dy

/-- `0`. -/
def zero : Dy := ⟨0, 0⟩
/-- `1`. -/
def one : Dy := ⟨1, 0⟩
/-- The integer `n`. -/
def ofInt (n : Int) : Dy := ⟨n, 0⟩
/-- The natural number `n`. -/
def ofNat (n : Nat) : Dy := ⟨n, 0⟩
/-- `2^e`. -/
def pow2 (e : Int) : Dy := ⟨1, e⟩

/-- `-x` (exact). -/
@[inline] def neg (x : Dy) : Dy := ⟨-x.man, x.exp⟩

/-- `x · 2^k` (exact). -/
@[inline] def scale (x : Dy) (k : Int) : Dy := ⟨x.man, x.exp + k⟩

/-- `|x|` (exact). -/
@[inline] def abs (x : Dy) : Dy := ⟨(x.man.natAbs : Int), x.exp⟩

/-- `x + y` (exact). The operands are aligned on the smaller exponent; a zero operand is
returned unchanged (so a zero with an unusual exponent never causes a large shift). -/
def add (x y : Dy) : Dy :=
  if x.man = 0 then y
  else if y.man = 0 then x
  else if x.exp ≤ y.exp then ⟨x.man + shl y.man (y.exp - x.exp).toNat, x.exp⟩
  else ⟨shl x.man (x.exp - y.exp).toNat + y.man, y.exp⟩

/-- `x - y` (exact). -/
@[inline] def sub (x y : Dy) : Dy := add x (neg y)

/-- `x · y` (exact). -/
@[inline] def mul (x y : Dy) : Dy := ⟨x.man * y.man, x.exp + y.exp⟩

instance : Neg Dy := ⟨neg⟩
instance : Add Dy := ⟨add⟩
instance : Sub Dy := ⟨sub⟩
instance : Mul Dy := ⟨mul⟩

/-- Certainly `0 < x` (exact: the sign of the value is the sign of the mantissa). -/
@[inline] def isPos (x : Dy) : Bool := decide (0 < x.man)
/-- Certainly `x < 0`. -/
@[inline] def isNeg (x : Dy) : Bool := decide (x.man < 0)
/-- `0 ≤ x`. -/
@[inline] def isNonneg (x : Dy) : Bool := decide (0 ≤ x.man)

/-- `x < y` (exact comparison, by the sign of `x - y`). -/
def blt (x y : Dy) : Bool := decide ((sub x y).man < 0)
/-- `x ≤ y` (exact comparison). -/
def ble (x y : Dy) : Bool := decide ((sub x y).man ≤ 0)
/-- `x = y` as values (exact). -/
def beqv (x y : Dy) : Bool := decide ((sub x y).man = 0)

/-- `min x y` (as values). -/
def min (x y : Dy) : Dy := if ble x y then x else y
/-- `max x y` (as values). -/
def max (x y : Dy) : Dy := if ble x y then y else x

/-- Round down to at most `p` significant bits: `floorP p x ≤ x`, and
`x - floorP p x < 2^(x.exp + s)` where `s = bitLen |x.man| - p` (or `0` if nothing is cut).
The mantissa of the result has at most `max p (bitLen |x.man|)` bits, and at most `p` bits when
`p ≥ 1` and something is cut. -/
def floorP (p : Nat) (x : Dy) : Dy :=
  let b := bitLen x.man.natAbs
  if b ≤ p then x else ⟨shr x.man (b - p), x.exp + ((b - p : Nat) : Int)⟩

/-- Round up to at most `p` significant bits: `x ≤ ceilP p x`. -/
def ceilP (p : Nat) (x : Dy) : Dy := neg (floorP p (neg x))

/-- A lower bound of `1/x` for `x ≠ 0` (about `p` significant bits); `0` for `x = 0`.
With `a = |x.man|`, `t = p + bitLen a` and `q = ⌊2^t / a⌋`:
`q · 2^(-x.exp - t) ≤ 2^(-x.exp)/a < (q+1) · 2^(-x.exp - t)`. -/
def recipDown (p : Nat) (x : Dy) : Dy :=
  let a := x.man.natAbs
  if a = 0 then zero
  else
    let t := p + bitLen a
    let q : Nat := (1 <<< t) / a
    if 0 < x.man then ⟨(q : Int), -x.exp - (t : Int)⟩
    else ⟨-((q + 1 : Nat) : Int), -x.exp - (t : Int)⟩

/-- An upper bound of `1/x` for `x ≠ 0` (about `p` significant bits); `0` for `x = 0`. -/
def recipUp (p : Nat) (x : Dy) : Dy :=
  let a := x.man.natAbs
  if a = 0 then zero
  else
    let t := p + bitLen a
    let q : Nat := (1 <<< t) / a
    if 0 < x.man then ⟨((q + 1 : Nat) : Int), -x.exp - (t : Int)⟩
    else ⟨-(q : Int), -x.exp - (t : Int)⟩

end Dy

end NonUniqueEuler.Verify
