import NonUniqueEuler.Verify.Comp.CBox

/-!
# Part 2 arithmetic layer: series helpers

Checker design decision D12 (see `FORMALIZATION_NOTES.md`).

Coefficient sequences are passed as functions `Nat → Ball` / `Nat → CBox` (for example
`fun j => a.getD j Ball.zero` for an `Array` or a `List`), so that the containment lemmas
do not depend on the container. Sums are left folds in the order of the Python reference:

* `Ball.foldSum p f acc j n = (((acc + f j) + f (j+1)) + …) + f (j+n-1)`;
* `Ball.cauchy p a b k = a 0 · b k + Σ_{j=1}^{k} a j · b (k-j)` (Python `evans._cauchy`);
* the `CBox` versions, and the mixed `CBox.cauchyBC` (`Σ a_j b_{k-j}` with `a` real, as in
  `fs[j] * R[k-j]`) and `CBox.cauchyCB` (`b` real).
* `buildArray init n step`: pushes `step arr` `n` times (recurrences such as
  `R_k = -R_0 Σ_{j=1}^k D_j R_{k-j}` or `ψ_{k+2} = …`, which read the prefix built so far).

Core only.
-/

namespace NonUniqueEuler.Verify

namespace Ball

/-- `foldSum p f acc j n = acc + f j + f (j+1) + … + f (j+n-1)` (left fold). -/
@[specialize] def foldSum (p : Nat) (f : Nat → Ball) (acc : Ball) (j : Nat) : Nat → Ball
  | 0 => acc
  | n + 1 => foldSum p f (add p acc (f j)) (j + 1) n

/-- `Σ_{j ≤ k} a j · b (k - j)`, evaluated as `a 0 · b k + Σ_{j=1}^{k} a j · b (k-j)`. -/
@[specialize] def cauchy (p : Nat) (a b : Nat → Ball) (k : Nat) : Ball :=
  foldSum p (fun j => mul p (a j) (b (k - j))) (mul p (a 0) (b k)) 1 k

end Ball

namespace CBox

/-- `foldSum p f acc j n = acc + f j + … + f (j+n-1)` (left fold). -/
@[specialize] def foldSum (p : Nat) (f : Nat → CBox) (acc : CBox) (j : Nat) : Nat → CBox
  | 0 => acc
  | n + 1 => foldSum p f (add p acc (f j)) (j + 1) n

/-- `Σ_{j ≤ k} a j · b (k - j)` for complex boxes, in Python's order. -/
@[specialize] def cauchy (p : Nat) (a b : Nat → CBox) (k : Nat) : CBox :=
  foldSum p (fun j => mul p (a j) (b (k - j))) (mul p (a 0) (b k)) 1 k

/-- `Σ_{j ≤ k} a j · b (k - j)` with real `a` and complex `b`. -/
@[specialize] def cauchyBC (p : Nat) (a : Nat → Ball) (b : Nat → CBox) (k : Nat) : CBox :=
  foldSum p (fun j => mulBall p (b (k - j)) (a j)) (mulBall p (b k) (a 0)) 1 k

/-- `Σ_{j ≤ k} a j · b (k - j)` with complex `a` and real `b`. -/
@[specialize] def cauchyCB (p : Nat) (a : Nat → CBox) (b : Nat → Ball) (k : Nat) : CBox :=
  foldSum p (fun j => mulBall p (a j) (b (k - j))) (mulBall p (a 0) (b k)) 1 k

end CBox

/-- Push `step arr` onto `arr`, `n` times: the result has size `init.size + n`, its first
`init.size` entries are those of `init`, and entry `init.size + i` is `step` applied to the
prefix of length `init.size + i`. -/
@[specialize] def buildArray {α : Type} (step : Array α → α) : Array α → Nat → Array α
  | arr, 0 => arr
  | arr, n + 1 => buildArray step (arr.push (step arr)) n

end NonUniqueEuler.Verify
