import NonUniqueEuler.Verify.Comp.Ball

/-!
# Part 2 arithmetic layer: elementary functions (`exp`, `H`)

* `Ball.expPoint p x`: a ball containing `exp x` for an exact dyadic `x`. Argument reduction
  `r = x · 2^(-j)` with `|r| < 2^(-10)`, the Taylor sum `Σ_{i<n} r^i/i!` in ball arithmetic at
  working precision `w = p + j + 10`, the remainder radius `2^(-10 n)` (which bounds
  `|r|^n (n+1)/(n! n)` for `n ≥ 2`: `Real.exp_bound`), and `j` squarings
  (`exp (2y) = (exp y)²`). Arguments with `|x| ≥ 2^30` give `top`.
* `Ball.exp p X`: `[lower (exp lo), upper (exp hi)]` by monotonicity (`expPoint` of the
  midpoint if `X` is exact).
* `Ball.H p X = 1 / (1 + exp(-2X))` (Python `evans._H`), `H x = (1 + e^{-2x})⁻¹`.
* `UB.expUp u`: an upper bound of `exp x` for `x ≤ u`.

Core only.
-/

namespace NonUniqueEuler.Verify

namespace Ball

/-- Taylor partial sums of `exp`: with `t ∋ r^m/m!` and `s ∋ Σ_{i≤m} r^i/i!`,
`expTaylorAux w r k m t s ∋ Σ_{i ≤ m+k} r^i/i!` (each step: `t ← t·r/(m+1)`, `s ← s + t`). -/
def expTaylorAux (w : Nat) (r : Dy) : Nat → Nat → Ball → Ball → Ball
  | 0, _, _, s => s
  | k + 1, m, t, s =>
    let t' := divNat w (mulDy w r t) (m + 1)
    expTaylorAux w r k (m + 1) t' (add w s t')

/-- A ball containing `Σ_{i<n} r^i/i!` (`{0}` for `n = 0`). -/
def expTaylor (w : Nat) (r : Dy) (n : Nat) : Ball :=
  match n with
  | 0 => zero
  | n + 1 => expTaylorAux w r n 0 one one

/-- `j`-fold squaring: `sqrIter w j b ∋ y^(2^j)` for `y ∈ b`. -/
def sqrIter (w : Nat) : Nat → Ball → Ball
  | 0, b => b
  | j + 1, b => sqrIter w j (sqr w b)

/-- A ball containing `exp x` for the exact dyadic `x` (see the module docstring). -/
def expPoint (p : Nat) (x : Dy) : Ball :=
  let top' : Int := x.exp + (bitLen x.man.natAbs : Int)   -- |x| < 2^top'
  let j : Nat := (top' + 10).toNat
  if 40 < j then top
  else
    let r : Dy := ⟨x.man, x.exp - (j : Int)⟩               -- x = r · 2^j, |r| < 2^(-10)
    let w : Nat := p + j + 10
    let n : Nat := w / 10 + 2
    let s := addErr (expTaylor w r n) (UB.pow2 (-10 * (n : Int)))
    round p (sqrIter w j s)

/-- A ball containing `exp x` for every `x ∈ X`. -/
def exp (p : Nat) (X : Ball) : Ball :=
  match X.rad with
  | .inf => top
  | .fin m e =>
    if m = 0 then expPoint p X.mid
    else
      let r : Dy := ⟨(m : Int), e⟩
      match (expPoint p (X.mid.sub r)).lower?, (expPoint p (X.mid.add r)).upper? with
      | some a, some b => ofInterval p a b
      | _, _ => top

/-- `H(x) = 1 / (1 + e^{-2x})` on the ball (Python `evans._H`). -/
def H (p : Nat) (X : Ball) : Ball :=
  inv p (add p one (exp p (neg (scale2 X 1))))

end Ball

namespace UB

/-- An upper bound of `exp x` for every real `x ≤ u` (`inf` for `inf`). Computed with
midpoint precision `radPrec + 10`. -/
def expUp (u : UB) : UB :=
  match u with
  | .fin m e => (Ball.expPoint (radPrec + 10) ⟨(m : Int), e⟩).upperUB
  | .inf => .inf

end UB

end NonUniqueEuler.Verify
