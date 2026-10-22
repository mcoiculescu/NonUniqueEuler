import NonUniqueEuler.Verify.Comp.UB

/-!
# Part 2 arithmetic layer: real balls `Ball`

Checker design decision D3 (see `FORMALIZATION_NOTES.md`).
Reference: Arb's `arb_t` as used by `euler-ring-certificate/src/ringcert/{balls,evans,winding}.py`.

A `Ball` is a dyadic midpoint `mid : Dy` and a radius `rad : UB`; it stands for the closed
interval `[mid - rad, mid + rad]`, and for the whole line when `rad = UB.inf` (Arb's convention:
"a ball with infinite radius is the whole line"). Semantics (`Defs/Verify/Sem.lean`):
`x ∈ b ↔ b.rad.Bounds |x - b.mid.toReal|`.

Every operation is total and has the containment property (CP): for all inputs in the input
balls, the output ball contains the exact result. Division by a ball that may contain `0`
returns `Ball.top` (and Lean's `0⁻¹ = 0` is then still contained).

Precision: every rounding operation takes the midpoint precision `p` (bits) as its first
explicit argument (default `defaultPrec = 128`). Midpoints are rounded to at most `p` bits
(plus at most two guard bits in `divNat`/`ofFrac`), the rounding error is added to the radius,
and radii are rounded up to `UB.radPrec = 30` bits. Exact operations (`neg`, `scale2`,
`ofDy`, `addErr`) take no precision.

Core only.
-/

namespace NonUniqueEuler.Verify

/-- The default midpoint precision (bits). -/
def defaultPrec : Nat := 128

/-- A real ball `[mid - rad, mid + rad]` (the whole line if `rad = inf`). -/
structure Ball where
  mid : Dy
  rad : UB
deriving Inhabited, Repr

namespace Ball

/-- The whole line. -/
def top : Ball := ⟨Dy.zero, .inf⟩
/-- The exact ball `{x}`. -/
def ofDy (x : Dy) : Ball := ⟨x, UB.zero⟩
/-- `{0}`. -/
def zero : Ball := ofDy Dy.zero
/-- `{1}`. -/
def one : Ball := ofDy Dy.one
/-- `{n}`. -/
def ofInt (n : Int) : Ball := ofDy (Dy.ofInt n)
/-- `{n}`. -/
def ofNat (n : Nat) : Ball := ofDy (Dy.ofNat n)

/-- Finite radius (Arb `is_finite`). -/
def isFinite (x : Ball) : Bool := x.rad.isFin

/-- The core normalization: the ball around the exact dyadic `m` with radius `r`, after
truncating the mantissa of `m` towards zero to `p` bits and adding the truncation error
(below one unit `2^e` in the last place: `|man - sgn(man)·(|man| >>> s)·2^s| = |man| % 2^s`)
to the radius. CP: if `|x - m| ≤ r` then `x ∈ roundMk p m r`. -/
@[inline] def roundMk (p : Nat) (m : Dy) (r : UB) : Ball :=
  let a := m.man.natAbs
  let b := bitLen a
  if b ≤ p then ⟨m, r⟩
  else
    let s := b - p
    let q : Int := ((a >>> s : Nat) : Int)
    let e := m.exp + (s : Int)
    ⟨⟨if m.man < 0 then -q else q, e⟩, UB.add r (UB.pow2 e)⟩

/-- Round the midpoint to `p` bits. -/
def round (p : Nat) (x : Ball) : Ball := roundMk p x.mid x.rad

/-- Enlarge the radius by `r` (exact midpoint): contains every `y` with `|y - x| ≤ r`,
`x ∈ X`. This is Python's `ball + box(ρ)` componentwise. -/
def addErr (x : Ball) (r : UB) : Ball := ⟨x.mid, UB.add x.rad r⟩

/-- `-x` (exact). -/
def neg (x : Ball) : Ball := ⟨x.mid.neg, x.rad⟩

/-- `x + y`. -/
def add (p : Nat) (x y : Ball) : Ball := roundMk p (x.mid.add y.mid) (UB.add x.rad y.rad)

/-- `x - y`. -/
def sub (p : Nat) (x y : Ball) : Ball := roundMk p (x.mid.sub y.mid) (UB.add x.rad y.rad)

/-- `x · y`. Radius `r₁|m₂| + (r₂|m₁| + r₁r₂)` (+ rounding), from
`|xy - m₁m₂| ≤ |m₂||x - m₁| + |m₁||y - m₂| + |x - m₁||y - m₂|`. -/
def mul (p : Nat) (x y : Ball) : Ball :=
  roundMk p (x.mid.mul y.mid)
    (UB.add (x.rad.mulAbs y.mid) (UB.add (y.rad.mulAbs x.mid) (UB.mul x.rad y.rad)))

/-- `x²`. Radius `2r|m| + r²` (+ rounding), from `x² - m² = 2m(x - m) + (x - m)²`. -/
def sqr (p : Nat) (x : Ball) : Ball :=
  roundMk p (x.mid.mul x.mid) (UB.add ((x.rad.mulAbs x.mid).scale 1) (UB.mul x.rad x.rad))

/-- `c · x` for an exact dyadic `c`. -/
def mulDy (p : Nat) (c : Dy) (x : Ball) : Ball := roundMk p (c.mul x.mid) (x.rad.mulAbs c)

/-- `x · k` for an exact natural number `k`. -/
def mulNat (p : Nat) (x : Ball) (k : Nat) : Ball := mulDy p (Dy.ofNat k) x

/-- `x · k` for an exact integer `k`. -/
def mulInt (p : Nat) (x : Ball) (k : Int) : Ball := mulDy p (Dy.ofInt k) x

/-- `x · 2^k` (exact). -/
def scale2 (x : Ball) (k : Int) : Ball := ⟨x.mid.scale k, x.rad.scale k⟩

/-- `x / k` for a natural number `k > 0` (`top` if `k = 0`). The midpoint is
`q · 2^(m.exp - t)` with `q = ⌊m.man · 2^t / k⌋` (about `p + 1` bits), error `< 2^(m.exp - t)`;
the radius is `rad / k` rounded up. -/
def divNat (p : Nat) (x : Ball) (k : Nat) : Ball :=
  if k = 0 then top
  else
    let m := x.mid
    let t : Nat := (p + bitLen k + 1) - bitLen m.man.natAbs
    let e : Int := m.exp - (t : Int)
    ⟨⟨shl m.man t / (k : Int), e⟩, UB.add (x.rad.divNat k) (UB.pow2 e)⟩

/-- The exact lower endpoint `mid - rad` (`none` if the radius is infinite). -/
def lower? (x : Ball) : Option Dy :=
  match x.rad with
  | .fin m e => some (x.mid.sub ⟨(m : Int), e⟩)
  | .inf => none

/-- The exact upper endpoint `mid + rad` (`none` if the radius is infinite). -/
def upper? (x : Ball) : Option Dy :=
  match x.rad with
  | .fin m e => some (x.mid.add ⟨(m : Int), e⟩)
  | .inf => none

/-- A ball containing the interval `[lo, hi]` (exact endpoints): midpoint `(lo + hi)/2`,
radius `(hi - lo)/2` rounded up, midpoint rounded to `p` bits. -/
def ofInterval (p : Nat) (lo hi : Dy) : Ball :=
  roundMk p ((lo.add hi).scale (-1)) (UB.ofDyUp ((hi.sub lo).scale (-1)))

/-- `[lower L, upper U]` (Python `balls.hull`): contains every `z` with `l ≤ z ≤ u` for some
`l ∈ L`, `u ∈ U`. `top` if `L` or `U` is infinite. -/
def hull (p : Nat) (L U : Ball) : Ball :=
  match L.lower?, U.upper? with
  | some l, some u => ofInterval p l u
  | _, _ => top

/-- The convex hull of `X ∪ Y` (Arb `union`): `[min lowers, max uppers]`. -/
def union (p : Nat) (X Y : Ball) : Ball :=
  match X.lower?, X.upper?, Y.lower?, Y.upper? with
  | some a, some b, some c, some d => ofInterval p (Dy.min a c) (Dy.max b d)
  | _, _, _, _ => top

/-- A ball containing `X ∩ [0, ∞)` (Arb `nonnegative_part`): CP for `x ∈ X` with `0 ≤ x`.
`X` itself if `X ⊆ [0, ∞)`; `{0}` if `X ⊆ (-∞, 0)` (vacuous); `top` if `X` is infinite. -/
def nonnegPart (p : Nat) (x : Ball) : Ball :=
  match x.rad with
  | .inf => top
  | .fin m e =>
    let r : Dy := ⟨(m : Int), e⟩
    let hi := x.mid.add r
    if hi.man < 0 then zero
    else if 0 ≤ (x.mid.sub r).man then x
    else ofInterval p Dy.zero hi

/-- `1 / x`. If `x ⊆ (0, ∞)` or `x ⊆ (-∞, 0)` then `1/x ∈ [1/hi, 1/lo]`, enclosed with
`Dy.recipDown`/`Dy.recipUp`; otherwise (or if `x` is infinite) `top`. -/
def inv (p : Nat) (x : Ball) : Ball :=
  match x.rad with
  | .inf => top
  | .fin m e =>
    let r : Dy := ⟨(m : Int), e⟩
    let lo := x.mid.sub r
    let hi := x.mid.add r
    if 0 < lo.man ∨ hi.man < 0 then ofInterval p (Dy.recipDown p hi) (Dy.recipUp p lo)
    else top

/-- `x / y = x · (1/y)` (deviation A4). -/
def div (p : Nat) (x y : Ball) : Ball := mul p x (inv p y)

/-- An upper bound of `|x|` on the ball: `|mid|ᵘ + rad`. -/
def absUB (x : Ball) : UB := UB.add (UB.absUp x.mid) x.rad

/-- An upper bound (nonnegative) of `x` on the ball: `max(mid, 0)ᵘ + rad`
(Python `x.upper()` used as a magnitude). -/
def upperUB (x : Ball) : UB := UB.add (UB.ofDyUp x.mid) x.rad

/-- A nonnegative lower bound of `|x|` on the ball (exact): `max(|mid| - rad, 0)`;
`0` if the radius is infinite. -/
def absLow (x : Ball) : Dy :=
  match x.rad with
  | .inf => Dy.zero
  | .fin m e =>
    let l := x.mid.abs.sub ⟨(m : Int), e⟩
    if 0 < l.man then l else Dy.zero

/-- Certainly `0 < x` on the ball (Arb `x > 0`). -/
def posC (x : Ball) : Bool :=
  match x.lower? with
  | some l => l.isPos
  | none => false

/-- Certainly `x < 0` on the ball. -/
def negC (x : Ball) : Bool :=
  match x.upper? with
  | some u => u.isNeg
  | none => false

/-- Certainly `0 ≤ x` on the ball. -/
def nonnegC (x : Ball) : Bool :=
  match x.lower? with
  | some l => l.isNonneg
  | none => false

/-- Certainly `x < c` on the ball. -/
def ltDy (x : Ball) (c : Dy) : Bool :=
  match x.upper? with
  | some u => Dy.blt u c
  | none => false

/-- Certainly `x ≤ c` on the ball. -/
def leDy (x : Ball) (c : Dy) : Bool :=
  match x.upper? with
  | some u => Dy.ble u c
  | none => false

/-- Certainly `c < x` on the ball. -/
def gtDy (x : Ball) (c : Dy) : Bool :=
  match x.lower? with
  | some l => Dy.blt c l
  | none => false

/-- Certainly `c ≤ x` on the ball. -/
def geDy (x : Ball) (c : Dy) : Bool :=
  match x.lower? with
  | some l => Dy.ble c l
  | none => false

/-- Certainly `x < y` for all `x ∈ X`, `y ∈ Y`. -/
def ltB (X Y : Ball) : Bool :=
  match X.upper?, Y.lower? with
  | some u, some l => Dy.blt u l
  | _, _ => false

/-- A ball containing the rational `n / d` (`top` if `d = 0`). Exact (up to rounding the
midpoint to `p` bits) when `d` is a power of two; otherwise the midpoint is
`⌊n · 2^t / d⌋ · 2^(-t)` (about `p + 1` bits) with error `< 2^(-t)`. -/
def ofFrac (p : Nat) (n : Int) (d : Nat) : Ball :=
  if d = 0 then top
  else if 1 <<< d.log2 = d then roundMk p ⟨n, -(d.log2 : Int)⟩ UB.zero
  else
    let t : Nat := (p + bitLen d + 1) - bitLen n.natAbs
    ⟨⟨shl n t / (d : Int), -(t : Int)⟩, UB.pow2 (-(t : Int))⟩

/-- A ball containing the rational `q` (Python `balls.qball`). -/
def ofRat (p : Nat) (q : Rat) : Ball := ofFrac p q.num q.den

end Ball

end NonUniqueEuler.Verify
