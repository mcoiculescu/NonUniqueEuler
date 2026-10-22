import NonUniqueEuler.Verify.Comp.Dyadic

/-!
# Part 2 arithmetic layer: upper bounds `UB`

Checker design decision D5 (see `FORMALIZATION_NOTES.md`).

A `UB` is a nonnegative dyadic number `man · 2^exp` (`man : Nat`) or `+∞` (`UB.inf`), like
Arb's `mag_t`. It is used for ball radii and for the monotone upper bounds of the enclosure
algorithm (`eps`, `q_*`, `κ_*`, `M`, `W`, the radius of `box(ρ)`).

Semantics (`NonUniqueEuler/Defs/Verify/Sem.lean`): `UB.toReal (fin m e) = m · 2^e`, and
`U.Bounds x` (notation `x ≤ᵤ U`) means `U = inf ∨ x ≤ U.toReal`. Every operation returns an
upper bound of the exact result (rounded up to `radPrec = 30` bits, plus at most one bit);
`inf` is absorbing for `add` and `mul` (also `0 · inf = inf`, which is conservative).

Core only.
-/

namespace NonUniqueEuler.Verify

/-- A nonnegative dyadic upper bound `man · 2^exp`, or `+∞`. -/
inductive UB where
  | fin (man : Nat) (exp : Int)
  | inf
deriving Inhabited, Repr

namespace UB

/-- Precision (bits) of radii and upper bounds. -/
def radPrec : Nat := 30

/-- `0`. -/
def zero : UB := fin 0 0
/-- `2^e`. -/
def pow2 (e : Int) : UB := fin 1 e

/-- `m · 2^e` rounded up to at most `radPrec + 1` bits: `m · 2^e ≤ (mkUp m e).toReal`. -/
@[inline] def mkUp (m : Nat) (e : Int) : UB :=
  let b := bitLen m
  if b ≤ radPrec then fin m e
  else
    let s := b - radPrec
    fin ((m >>> s) + 1) (e + (s : Int))

/-- An upper bound of the natural number `n`. -/
def ofNat (n : Nat) : UB := mkUp n 0

/-- An upper bound of `max x 0` (rounded). -/
def ofDyUp (x : Dy) : UB := if x.man ≤ 0 then zero else mkUp x.man.toNat x.exp

/-- The exact value `max x 0` (no rounding; for divisors of `UB.div`). -/
def ofDyExact (x : Dy) : UB := if x.man ≤ 0 then zero else fin x.man.toNat x.exp

/-- An upper bound of `|x|` (rounded). -/
def absUp (x : Dy) : UB := mkUp x.man.natAbs x.exp

/-- Is the bound finite? -/
def isFin : UB → Bool
  | fin .. => true
  | inf => false

/-- The finite value as a dyadic. -/
def toDy? : UB → Option Dy
  | fin m e => some ⟨(m : Int), e⟩
  | inf => none

/-- `m · 2^e + m' · 2^e'` rounded up, for `e' ≤ e`. With `k = radPrec + 1 - bitLen m`, the
first operand is `(m · 2^k) · 2^(e-k)`; if the second one is below the unit `2^(e-k)`
(`m' · 2^e' < 2^(e' + bitLen m') ≤ 2^(e-k)`), it is replaced by that unit, which avoids long
shifts and costs a relative `2^-radPrec`. Otherwise the sum is exact before rounding. -/
@[inline] def addFin (m : Nat) (e : Int) (m' : Nat) (e' : Int) : UB :=
  let k : Nat := (radPrec + 1) - bitLen m
  if e' + (bitLen m' : Int) ≤ e - (k : Int) then mkUp ((m <<< k) + 1) (e - (k : Int))
  else mkUp ((m <<< (e - e').toNat) + m') e'

/-- `u + v`, rounded up (`inf` if either is `inf`). -/
def add : UB → UB → UB
  | fin m e, fin m' e' =>
    if m = 0 then fin m' e'
    else if m' = 0 then fin m e
    else if e' ≤ e then addFin m e m' e'
    else addFin m' e' m e
  | _, _ => inf

/-- `u · v`, rounded up (`inf` if either is `inf`). -/
def mul : UB → UB → UB
  | fin m e, fin m' e' => mkUp (m * m') (e + e')
  | _, _ => inf

/-- `u · 2^k` (exact). -/
def scale : UB → Int → UB
  | fin m e, k => fin m (e + k)
  | inf, _ => inf

/-- An upper bound of `u · |x|`; `0` without any work when `u = 0`. -/
def mulAbs (u : UB) (x : Dy) : UB :=
  match u with
  | fin 0 _ => zero
  | _ => mul u (absUp x)

/-- `u · k` for a natural number `k`, rounded up. -/
def mulNat (u : UB) (k : Nat) : UB := mul u (fin k 0)

/-- Exact comparison `m · 2^e ≤ m' · 2^e'`. -/
def leFin (m : Nat) (e : Int) (m' : Nat) (e' : Int) : Bool :=
  if e ≤ e' then decide (m ≤ m' <<< (e' - e).toNat)
  else decide (m <<< (e - e').toNat ≤ m')

/-- Exact comparison `u ≤ v` in `[0, ∞]`. -/
def le : UB → UB → Bool
  | fin m e, fin m' e' => leFin m e m' e'
  | _, inf => true
  | inf, fin .. => false

/-- `max u v` (exact selection). -/
def max (u v : UB) : UB := if le u v then v else u

/-- Certainly `u ≤ c` (exact; `false` for `inf`). -/
def leDy (u : UB) (c : Dy) : Bool :=
  match u with
  | fin m e => Dy.ble ⟨(m : Int), e⟩ c
  | inf => false

/-- Upper bound of `x / y` for `0 ≤ x ≤ u` and `y ≥ c.toReal > 0`: the divisor `c` is a
positive (exact) lower bound of `y`. Returns `inf` if `c` is `0` or `inf`. -/
def div : UB → UB → UB
  | fin m e, fin m' e' =>
    if m' = 0 then inf
    else if m = 0 then zero
    else
      let t := (radPrec + bitLen m' + 1) - bitLen m
      mkUp ((m <<< t) / m' + 1) (e - e' - (t : Int))
  | _, _ => inf

/-- Upper bound of `x / k` for `0 ≤ x ≤ u` and a natural number `k > 0` (`inf` if `k = 0`). -/
def divNat (u : UB) (k : Nat) : UB := div u (fin k 0)

/-- The heuristic candidate `(c, g)` with `c · 2^g ≈ √(m · 2^e)` (about `radPrec` bits;
computed with `Nat.sqrt`). Its correctness is not used: `sqrtUp` checks it. -/
def sqrtCand (m : Nat) (e : Int) : Nat × Int :=
  let f : Int := e / 2
  let m2 : Nat := if e - 2 * f = 0 then m else 2 * m
  let t : Nat := (2 * radPrec + 2 - bitLen m2) / 2
  (Nat.sqrt (m2 <<< (2 * t)) + 1, f - (t : Int))

/-- Upper bound of `√x` for `0 ≤ x ≤ u`. The candidate `c · 2^g = sqrtCand m e` is *checked*
exactly (`m · 2^e ≤ c² · 2^(2g)`), so its correctness does not depend on the candidate
computation; if the check fails, `1 + u ≥ √u` is returned. -/
def sqrtUp : UB → UB
  | fin m e =>
    if m = 0 then zero
    else
      let cg := sqrtCand m e
      if leFin m e (cg.1 * cg.1) (2 * cg.2) then mkUp cg.1 cg.2 else add (fin 1 0) (fin m e)
  | inf => inf

end UB

end NonUniqueEuler.Verify
