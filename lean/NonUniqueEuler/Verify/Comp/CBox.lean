import NonUniqueEuler.Verify.Comp.Elem

/-!
# Part 2 arithmetic layer: complex boxes `CBox`

Checker design decision D4 (see `FORMALIZATION_NOTES.md`).
Reference: Arb's `acb_t` (a real ball times a real ball) as used by `evans.py`/`winding.py`.

A `CBox` is a pair of real balls; `z ∈ B ↔ z.re ∈ B.re ∧ z.im ∈ B.im` (`Defs/Verify/Sem.lean`).
Every operation has the containment property (CP). Precision conventions as for `Ball`.

Core only.
-/

namespace NonUniqueEuler.Verify

/-- A complex box `re × i·im`. -/
structure CBox where
  re : Ball
  im : Ball
deriving Inhabited, Repr

namespace CBox

/-- The whole plane. -/
def top : CBox := ⟨Ball.top, Ball.top⟩
/-- The real box `b + 0i`. -/
def ofBall (b : Ball) : CBox := ⟨b, Ball.zero⟩
/-- The imaginary box `0 + i·b`. -/
def ofIm (b : Ball) : CBox := ⟨Ball.zero, b⟩
/-- The exact point `x + 0i`. -/
def ofDy (x : Dy) : CBox := ofBall (Ball.ofDy x)
/-- `{0}`. -/
def zero : CBox := ofBall Ball.zero
/-- `{1}`. -/
def one : CBox := ofBall Ball.one
/-- `{n}`. -/
def ofNat (n : Nat) : CBox := ofBall (Ball.ofNat n)
/-- A box containing the point `x + iy` with rational coordinates (Python `pt_box`). -/
def ofRat (p : Nat) (x y : Rat) : CBox := ⟨Ball.ofRat p x, Ball.ofRat p y⟩

/-- Both components finite (Arb `is_finite`). -/
def isFinite (z : CBox) : Bool := z.re.isFinite && z.im.isFinite

/-- Round both midpoints to `p` bits. -/
def round (p : Nat) (z : CBox) : CBox := ⟨z.re.round p, z.im.round p⟩

/-- `-z` (exact). -/
def neg (z : CBox) : CBox := ⟨z.re.neg, z.im.neg⟩
/-- The complex conjugate (exact). -/
def conj (z : CBox) : CBox := ⟨z.re, z.im.neg⟩
/-- `i · z = -im + i·re` (exact). -/
def mulI (z : CBox) : CBox := ⟨z.im.neg, z.re⟩

/-- `z + w`. -/
def add (p : Nat) (z w : CBox) : CBox := ⟨Ball.add p z.re w.re, Ball.add p z.im w.im⟩
/-- `z - w`. -/
def sub (p : Nat) (z w : CBox) : CBox := ⟨Ball.sub p z.re w.re, Ball.sub p z.im w.im⟩

/-- `z · w = (ac - bd) + i(ad + bc)` (four real products). -/
def mul (p : Nat) (z w : CBox) : CBox :=
  ⟨Ball.sub p (Ball.mul p z.re w.re) (Ball.mul p z.im w.im),
   Ball.add p (Ball.mul p z.re w.im) (Ball.mul p z.im w.re)⟩

/-- `z²`. -/
def sqr (p : Nat) (z : CBox) : CBox :=
  ⟨Ball.sub p (Ball.sqr p z.re) (Ball.sqr p z.im),
   (Ball.mul p z.re z.im).scale2 1⟩

/-- `z · b` for a real ball `b` (Python `arb * acb`). -/
def mulBall (p : Nat) (z : CBox) (b : Ball) : CBox := ⟨Ball.mul p z.re b, Ball.mul p z.im b⟩
/-- `z · c` for an exact dyadic `c`. -/
def mulDy (p : Nat) (c : Dy) (z : CBox) : CBox := ⟨Ball.mulDy p c z.re, Ball.mulDy p c z.im⟩
/-- `z · k` for an exact natural number `k`. -/
def mulNat (p : Nat) (z : CBox) (k : Nat) : CBox := ⟨Ball.mulNat p z.re k, Ball.mulNat p z.im k⟩
/-- `z · 2^k` (exact). -/
def scale2 (z : CBox) (k : Int) : CBox := ⟨z.re.scale2 k, z.im.scale2 k⟩
/-- `z / k` for a natural number `k > 0`. -/
def divNat (p : Nat) (z : CBox) (k : Nat) : CBox := ⟨Ball.divNat p z.re k, Ball.divNat p z.im k⟩
/-- `z / b` for a real ball `b`. -/
def divBall (p : Nat) (z : CBox) (b : Ball) : CBox :=
  let bi := Ball.inv p b
  ⟨Ball.mul p z.re bi, Ball.mul p z.im bi⟩

/-- `z + b` for a real ball `b`. -/
def addBall (p : Nat) (z : CBox) (b : Ball) : CBox := ⟨Ball.add p z.re b, z.im⟩

/-- `1 / z = conj z / |z|²`: with `t = a² + b²` and `u = 1/t`, the box `(a u, -(b u))`.
If `t` may vanish then `u = top` and the result is infinite. -/
def inv (p : Nat) (z : CBox) : CBox :=
  let u := Ball.inv p (Ball.add p (Ball.sqr p z.re) (Ball.sqr p z.im))
  ⟨Ball.mul p z.re u, (Ball.mul p z.im u).neg⟩

/-- `z / w = z · (1/w)`. -/
def div (p : Nat) (z w : CBox) : CBox := mul p z (inv p w)

/-- An upper bound of `|z|` on the box: `√(|a|ᵘ² + |b|ᵘ²)` rounded up
(Python `abs_upper`). -/
def absUB (z : CBox) : UB :=
  let a := z.re.absUB
  let b := z.im.absUB
  UB.sqrtUp (UB.add (UB.mul a a) (UB.mul b b))

/-- A nonnegative lower bound of `|z|` on the box: `max(|a|_low, |b|_low)` (exact). -/
def absLow (z : CBox) : Dy := Dy.max z.re.absLow z.im.absLow

/-- The box `[-r, r] × [-r, r]` (Python `balls.box`): it contains the closed disk of radius
`ρ` for any `ρ ≤ r`. -/
def diskBox (r : UB) : CBox := ⟨⟨Dy.zero, r⟩, ⟨Dy.zero, r⟩⟩

/-- `z + box(r)` with exact midpoints (Python `psi + box(ρ)`): contains every `w` with
`|w - z'| ≤ ρ ≤ r` for some `z' ∈ z`. -/
def addDisk (z : CBox) (r : UB) : CBox := ⟨z.re.addErr r, z.im.addErr r⟩

/-- The componentwise convex hull of two boxes (Arb `acb_union`). -/
def union (p : Nat) (z w : CBox) : CBox := ⟨Ball.union p z.re w.re, Ball.union p z.im w.im⟩

end CBox

end NonUniqueEuler.Verify
