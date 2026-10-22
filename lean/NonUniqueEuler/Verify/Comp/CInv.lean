import NonUniqueEuler.Verify.Comp.CBox

/-!
# Part 2 arithmetic: a tight inverse of a complex box (`CBox.invTight`)

Deviation A7 (see `FORMALIZATION_NOTES.md`). CP lemmas: `Defs/Verify/SemCInv.lean`
(`Ball.mem_meet`, `CBox.mem_invDisk`, `CBox.mem_invTight`), proved.

Python's `R[0] = 1 / Dk[0]` (`evans._step_coeffs`) is Arb's `acb_div(1, D)`, i.e. `acb_inv(D)`,
which for a box of positive radius inverts the *midpoint* and adds the disk error bound
`r / (|m| (|m| - r))`, `r` the complex radius. `CBox.inv` (`Comp/CBox.lean`) instead evaluates
`conj z / |z|²` in box arithmetic; when `D` is uncertain mainly in one direction (the `G`-cell
enters `D` as `iℓ G e^{-2ξ}`), its result is about three times wider. Measured on the first
(N2′) cell: 208 segments with `CBox.inv` against 47 for the package, 56 with the disk bound
alone, and 54 with `invTight`, the componentwise intersection of both enclosures (both contain
`1/z`, so the intersection does).

* `Ball.meet p X Y`: a ball containing `X ∩ Y` (for a point in both).
* `CBox.invDisk p Z`: `1/m` (exact midpoint `m`, box arithmetic) enlarged by
  `r / L`, with `r ≥ √(r_re² + r_im²)` and `L = |m|² - r·|m|ᵘ > 0` a lower bound of
  `|m|(|m| - r)`; `top` if `L ≤ 0` (the box may contain `0`) or a radius is infinite.
* `CBox.invTight p Z = meet (inv p Z) (invDisk p Z)` componentwise.

Core only.
-/

namespace NonUniqueEuler.Verify

namespace Ball

/-- A ball containing `X ∩ Y`: `[max lo, min hi]` when both balls are finite and the interval
is nonempty; otherwise `X` (or `Y` if `X` is infinite). CP: `x ∈ X → x ∈ Y → x ∈ meet p X Y`. -/
def meet (p : Nat) (X Y : Ball) : Ball :=
  match X.lower?, X.upper?, Y.lower?, Y.upper? with
  | some a, some b, some c, some d =>
    let lo := Dy.max a c
    let hi := Dy.min b d
    if Dy.ble lo hi then ofInterval p lo hi else X
  | some _, some _, _, _ => X
  | _, _, _, _ => Y

end Ball

namespace CBox

/-- Arb's inverse of a box (`acb_inv` for inexact input): the inverse of the exact midpoint `m`,
enlarged by the disk bound `r / (|m|(|m| - r))`, computed as `r / L` with
`L = |m|² - r·|m|ᵘ ≤ |m|(|m| - r)`. `top` if `L ≤ 0` or a radius is infinite. -/
def invDisk (p : Nat) (z : CBox) : CBox :=
  match z.re.rad, z.im.rad with
  | .fin ma ea, .fin mb eb =>
    let ra : UB := .fin ma ea
    let rb : UB := .fin mb eb
    let r := UB.sqrtUp (UB.add (UB.mul ra ra) (UB.mul rb rb))
    let a := z.re.mid
    let b := z.im.mid
    let m2 := Dy.add (Dy.mul a a) (Dy.mul b b)
    let mU := UB.sqrtUp (UB.ofDyUp m2)
    match (UB.mul r mU).toDy? with
    | some rm =>
      let L := Dy.sub m2 rm
      if 0 < L.man then
        addDisk (inv p ⟨Ball.ofDy a, Ball.ofDy b⟩) (UB.div r (UB.ofDyExact L))
      else top
    | none => top
  | _, _ => top

/-- The componentwise intersection of the two enclosures `inv p z` and `invDisk p z` of `1/z`
(used for `R_0 = 1/D_0` in `stepCoeffs`). -/
def invTight (p : Nat) (z : CBox) : CBox :=
  let A := inv p z
  let B := invDisk p z
  ⟨Ball.meet p A.re B.re, Ball.meet p A.im B.im⟩

end CBox

end NonUniqueEuler.Verify
