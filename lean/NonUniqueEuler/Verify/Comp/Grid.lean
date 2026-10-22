import NonUniqueEuler.Verify.Comp.Series

/-!
# Part 2 algorithms: the grid and the `λ`-independent Taylor data

Manuscript: §A.3, step (i) (`A_verification.tex:239-300`).
Reference: `euler-ring-certificate/src/ringcert/evans.py` (`_H`, `_H_pair_iv`, `_coeffs`,
`_omega`, class `Grid`) and `data.py` (`rn_binary64`, the data).

Everything here is computed once per run; it does not depend on `λ` or `G`.

* `RD.a0 … RD.ξR`: the pinned data as exact dyadics (`data.py`, `04_ring.tex:29-31`).
* `rnBinary64`: exact port of `data.rn_binary64` (round to the nearest binary64, ties to even).
* `gridPts hpow`: the points `s_0 = ξa`, `s_j = RN(ξa + (ξb - ξa) j/n)`, `s_n = ξb`,
  `n = ⌈(ξb - ξa) 2^hpow⌉` (`n = 360` for `hpow = 8`).
* `coeffs p Slo Shi N`: `_coeffs` (the Taylor coefficients `w, f, E^±, q` valid on
  `[Slo, Shi]`); `omegaCoeffs`: `_omega`; `dgStep`: the increment of `g` over one step;
  `gamma0`: the ball `γ₀ ∋ g(ξa)`.
* `StepData`, `mkStep`, `buildSteps`, `Grid`, `Grid.build`: the class `Grid`.

**Fail closed (deviation G1).** Python *asserts* that the grid points increase and that the
steps are exact. Here the steps carry their exact dyadic end points, and `Grid.ok` checks that
the steps are consecutive, strictly increasing, and run from `ξa` to `ξb`; `evansEncl` fails if
`Grid.ok = false`. (The steps `h = s₁ - s₀` are exact by construction: `Dy.sub` is exact.)

Core only (checker design decision D6): no Mathlib, no `Float`, no `partial`, `implemented_by`,
`extern` or `unsafe`. Every recursion is structural.

## Python → Lean

| `evans.py` / `data.py` | Lean |
|---|---|
| `A0, DD, SL, SA, SB, SR = [dy(v) …]` | `RD.a0, RD.d, RD.ξL, RD.ξa, RD.ξb, RD.ξR` (exact `Dy`) |
| `rn_binary64(q)` | `rnBinary64 q` (`none` where Python's assertions fail) |
| `_H(x)` | `Ball.H p x` (`Comp/Elem.lean`) |
| `_H_pair_iv(xlo, xhi)` | `hPairIv p xlo xhi` |
| `_coeffs`: `S = hull(Slo, Shi)`, `x1 = 1/DD` | `coeffs` (first lines) |
| `_coeffs`: `A, Ab = _H_pair_iv((Slo-A0)/DD, (Shi-A0)/DD)`, `B, Bb = _H_pair_iv(-(Shi/DD), -(Slo/DD))` | `coeffs` (`hA`, `hB`) |
| `_coeffs`: loop `ak = (2*x1)*PA/(k+1)`, `bk = -((2*x1)*PB)/(k+1)` | `hRec` (`pos = true` for `A`, `false` for `B`) |
| `_coeffs`: `w`, `fs`, `e2_0`, `em2_0`, `c = arb(2**k)/arb(k!)`, `e2`, `em2`, `q` | `coeffs` (tail) |
| `_omega(dat, g0, N)` | `omegaCoeffs p dat g0 N` |
| `Grid.__init__`: `h`, `n`, `ptsQ` | `gridN`, `gridPts` |
| `Grid.__init__`: `self.h[i] = s[i+1] - s[i]` | `StepData.h` (`mkStep`) |
| `Grid.__init__`: `pt`, `iv` | `StepData.pt`, `StepData.iv` (`mkStep`) |
| `Grid.__init__`: `dg` loop, `nonnegative_part()` | `dgAux`, `dgStep` |
| `Grid.__init__`: `xa`, `gmax`, `g[0] = hull(0, gmax)` | `gamma0` |
| `Grid.__init__`: `g[i+1] = g[i] + dg[i]` | `StepData.g1` (`mkStep`), threaded by `buildSteps` |
| `Grid.__init__`: `Omg`, `OmgI` | `StepData.Omg`, `StepData.OmgI` |
| `Grid.__init__`: `hp`, `khp` | `powArr`, `StepData.hp`, `StepData.khp` (`khp[0] = khp[1] = 0`, unused, Python `None`) |
| the asserts on `ptsQ` and `h` | `Grid.ok` (`chainSteps`) |
-/

namespace NonUniqueEuler.Verify

/-! ### The pinned data -/

namespace RD

/-- `a₀ = -7304210039150669 · 2^-54` (`A0_Q`). -/
def a0 : Dy := ⟨-7304210039150669, -54⟩
/-- `d = 5764607523034235 · 2^-58` (`DD_Q`). -/
def d : Dy := ⟨5764607523034235, -58⟩
/-- `ξ_L = -4528212286209965 · 2^-52` (`SL_Q`). -/
def ξL : Dy := ⟨-4528212286209965, -52⟩
/-- `ξ_a = -4077852323472915 · 2^-52` (`SA_Q`). -/
def ξa : Dy := ⟨-4077852323472915, -52⟩
/-- `ξ_b = 1/2` (`SB_Q`). -/
def ξb : Dy := ⟨1, -1⟩
/-- `ξ_R = 5404319552844595 · 2^-53` (`SR_Q`). -/
def ξR : Dy := ⟨5404319552844595, -53⟩

end RD

/-- The exact rational value `man · 2^exp` of a dyadic. -/
def Dy.toRatExact (x : Dy) : Rat :=
  if 0 ≤ x.exp then (x.man : Rat) * ((2 ^ x.exp.toNat : Nat) : Rat)
  else (x.man : Rat) / ((2 ^ (-x.exp).toNat : Nat) : Rat)

/-- `k!` (core has no factorial). -/
def fact : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * fact k

/-! ### `rn_binary64` (exact port of `data.rn_binary64`) -/

/-- `2^e ≤ a/d` for `a, d > 0` (exact). -/
def pow2LeFrac (e : Int) (a d : Nat) : Bool :=
  if 0 ≤ e then decide (d <<< e.toNat ≤ a) else decide (d ≤ a <<< (-e).toNat)

/-- The binary64 number nearest to `q` (ties to even), as an exact dyadic: a port of
`data.rn_binary64`. Python asserts `2^e ≤ |q| < 2^(e+1)` and `-1022 ≤ e ≤ 1023` (normal
range); where an assertion would fail, the result is `none`. With `|q| = a/d`:
`e = bitlen a - bitlen d`, decreased by one if `2^e > |q|`; `t = |q| 2^(52-e) ∈ [2^52, 2^53)`;
`n = ⌊t⌋`, incremented if `t - n > 1/2`, or `= 1/2` and `n` odd; the result is
`sgn · n · 2^(e-52)`. -/
def rnBinary64 (q : Rat) : Option Dy :=
  if q.num = 0 then some Dy.zero
  else
    let a := q.num.natAbs
    let d := q.den
    let e0 : Int := (bitLen a : Int) - (bitLen d : Int)
    let e : Int := if pow2LeFrac e0 a d then e0 else e0 - 1
    if pow2LeFrac e a d && !pow2LeFrac (e + 1) a d && decide (-1022 ≤ e) && decide (e ≤ 1023) then
      let sh : Int := 52 - e
      let num : Nat := if 0 ≤ sh then a <<< sh.toNat else a
      let den : Nat := if 0 ≤ sh then d else d <<< (-sh).toNat
      let n := num / den
      let r := num % den
      let n' := if 2 * r > den || (2 * r == den && n % 2 == 1) then n + 1 else n
      some ⟨if q.num < 0 then -(n' : Int) else (n' : Int), e - 52⟩
    else none

/-! ### The grid points -/

/-- `n = ⌈(ξb - ξa) / h⌉`, `h = 2^-hpow` (`n = 360` for `hpow = 8`). -/
def gridN (hpow : Nat) : Nat :=
  (Rat.ceil ((RD.ξb.toRatExact - RD.ξa.toRatExact) * ((2 ^ hpow : Nat) : Rat))).toNat

/-- The grid points `[ξa] ++ [RN(ξa + (ξb - ξa) i/n) | 0 < i < n] ++ [ξb]` as exact dyadics
(`Grid.__init__`, `ptsQ` and `self.s`); `[]` if a rounding fails its assertion. -/
def gridPts (hpow : Nat) : List Dy :=
  let n := gridN hpow
  let sa := RD.ξa.toRatExact
  let sb := RD.ξb.toRatExact
  let mids := (List.range (n - 1)).mapM fun i =>
    rnBinary64 (sa + (sb - sa) * (((i + 1 : Nat) : Rat) / (n : Rat)))
  match mids with
  | some ms => RD.ξa :: (ms ++ [RD.ξb])
  | none => []

/-! ### The coefficient data `_coeffs` -/

/-- The Taylor coefficients valid on one interval `S` (a point or a step), as in Python's dict
`dict(fs, e2, em2, q, w)`: `w_k` (`k ≤ N+1`) of `w = AB = ϖ`; `fs_k = (k+1) w_{k+1}`
(`k ≤ N`) of `f_s = ϖ'`; `e2_k`, `em2_k` (`k ≤ N`) of `e^{±2ξ}`; `q_k` (`k ≤ N`) of
`q = ϖ e^{2ξ}`. -/
structure CoeffData where
  w : Array Ball
  fs : Array Ball
  e2 : Array Ball
  em2 : Array Ball
  q : Array Ball
deriving Inhabited

/-- `_H_pair_iv(xlo, xhi) = (hull(H(xlo), H(xhi)), hull(H(-xhi), H(-xlo)))`: balls containing
`H` and `1 - H = H(-·)` on `[xlo, xhi]` (`H` is increasing). -/
def hPairIv (p : Nat) (xlo xhi : Ball) : Ball × Ball :=
  (Ball.hull p (Ball.H p xlo) (Ball.H p xhi),
   Ball.hull p (Ball.H p (Ball.neg xhi)) (Ball.H p (Ball.neg xlo)))

/-- The loop of `_coeffs` for one pair, run `n` times on arrays `A`, `Ab` of equal size
`k + 1`: push `a = c·(Σ_{r≤k} A_r Ab_{k-r})/(k+1)` (if `pos`; this is `A_{k+1}` with
`c = 2·x1 = 2/d`) or `a = -(c·Σ)/(k+1)` (if `!pos`; this is `B_{k+1}`) to `A`, and `-a` to
`Ab`. -/
def hRec (p : Nat) (c : Ball) (pos : Bool) : Nat → Array Ball → Array Ball → Array Ball × Array Ball
  | 0, A, Ab => (A, Ab)
  | n + 1, A, Ab =>
    let k := A.size - 1
    let P := Ball.cauchy p (fun j => A.getD j Ball.zero) (fun j => Ab.getD j Ball.zero) k
    let a := if pos then Ball.divNat p (Ball.mul p c P) (k + 1)
      else Ball.divNat p (Ball.neg (Ball.mul p c P)) (k + 1)
    hRec p c pos n (A.push a) (Ab.push (Ball.neg a))

/-- `_coeffs(Slo, Shi, N)`: the Taylor coefficients of `w, f_s, e^{±2ξ}, q` (on `[ξa, ξb]`,
where `χ = 1`), valid at every point of `[Slo, Shi]`. -/
def coeffs (p : Nat) (Slo Shi : Dy) (N : Nat) : CoeffData :=
  let S := Ball.hull p (Ball.ofDy Slo) (Ball.ofDy Shi)
  let DD := Ball.ofDy RD.d
  let A0 := Ball.ofDy RD.a0
  let x1 := Ball.inv p DD
  let hA := hPairIv p (Ball.div p (Ball.sub p (Ball.ofDy Slo) A0) DD)
    (Ball.div p (Ball.sub p (Ball.ofDy Shi) A0) DD)
  let hB := hPairIv p (Ball.neg (Ball.div p (Ball.ofDy Shi) DD))
    (Ball.neg (Ball.div p (Ball.ofDy Slo) DD))
  let c := Ball.scale2 x1 1
  let A := (hRec p c true (N + 1) #[hA.1] #[hA.2]).1
  let B := (hRec p c false (N + 1) #[hB.1] #[hB.2]).1
  let w := Array.ofFn (n := N + 2) fun k =>
    Ball.cauchy p (fun j => A.getD j Ball.zero) (fun j => B.getD j Ball.zero) k.val
  let fs := Array.ofFn (n := N + 1) fun k => Ball.mulNat p (w.getD (k.val + 1) Ball.zero) (k.val + 1)
  let e20 := Ball.exp p (Ball.scale2 S 1)
  let em20 := Ball.exp p (Ball.neg (Ball.scale2 S 1))
  let cc := fun k : Nat => Ball.ofFrac p ((2 ^ k : Nat) : Int) (fact k)
  let e2 := Array.ofFn (n := N + 1) fun k => Ball.mul p e20 (cc k.val)
  let em2 := Array.ofFn (n := N + 1) fun k =>
    Ball.mul p em20 (if k.val % 2 = 0 then cc k.val else Ball.neg (cc k.val))
  let q := Array.ofFn (n := N + 1) fun k =>
    Ball.cauchy p (fun j => w.getD j Ball.zero) (fun j => e2.getD j Ball.zero) k.val
  { w, fs, e2, em2, q }

/-- `_omega(dat, g0, N)`: the coefficients `o_k` (`k < N`) of `g e^{-2ξ}`, from `g_0 = g0` and
`g_k = q_{k-1}/k`. -/
def omegaCoeffs (p : Nat) (dat : CoeffData) (g0 : Ball) (N : Nat) : Array Ball :=
  let g := Array.ofFn (n := N + 1) fun k =>
    if k.val = 0 then g0 else Ball.divNat p (dat.q.getD (k.val - 1) Ball.zero) k.val
  Array.ofFn (n := N) fun k =>
    Ball.cauchy p (fun j => g.getD j Ball.zero) (fun j => dat.em2.getD j Ball.zero) k.val

/-! ### The steps -/

/-- The loop of the `dg` computation: from `k`, `n` times,
`acc ← acc + q_k·hp/(k+1)`, `hp ← hp·hh`. Returns `(acc, hp)`. -/
def dgAux (p : Nat) (q : Nat → Ball) (hh : Ball) : Nat → Nat → Ball → Ball → Ball × Ball
  | _, 0, acc, hp => (acc, hp)
  | k, n + 1, acc, hp =>
    dgAux p q hh (k + 1) n (Ball.add p acc (Ball.divNat p (Ball.mul p (q k) hp) (k + 1)))
      (Ball.mul p hp hh)

/-- The increment of `g` over a step of length `h`:
`(Σ_{k<N} q^pt_k h^{k+1}/(k+1) + q^st_N h^{N+1}/(N+1)) ∩ [0, ∞)`. -/
def dgStep (p : Nat) (pt iv : CoeffData) (h : Dy) (N : Nat) : Ball :=
  let hh := Ball.ofDy h
  let r := dgAux p (fun k => pt.q.getD k Ball.zero) hh 0 N Ball.zero hh
  Ball.nonnegPart p (Ball.add p r.1 (Ball.divNat p (Ball.mul p (iv.q.getD N Ball.zero) r.2) (N + 1)))

/-- `γ₀ = hull(0, e^{2x_a + 2ξa}/(2/d + 2)) ∋ g(ξa)`, `x_a = (ξa - a₀)/d`. -/
def gamma0 (p : Nat) : Ball :=
  let DD := Ball.ofDy RD.d
  let SA := Ball.ofDy RD.ξa
  let xa := Ball.div p (Ball.sub p SA (Ball.ofDy RD.a0)) DD
  let gmax := Ball.div p (Ball.exp p (Ball.add p (Ball.scale2 xa 1) (Ball.scale2 SA 1)))
    (Ball.add p (Ball.div p (Ball.ofNat 2) DD) (Ball.ofNat 2))
  Ball.hull p Ball.zero gmax

/-- `hp_k = h^k` for `k ≤ N + 1` (`hp[0] = 1`, `hp[k+1] = hp[k]·h`). -/
def powArr (p : Nat) (hh : Ball) (N : Nat) : Array Ball :=
  buildArray (fun arr => Ball.mul p (arr.getD (arr.size - 1) Ball.zero) hh) #[Ball.one] (N + 1)

/-- The data of one step `[s₀, s₁]` of the middle region. -/
structure StepData where
  /-- The left end point `s_j`. -/
  s0 : Dy
  /-- The right end point `s_{j+1}`. -/
  s1 : Dy
  /-- `h_j = s₁ - s₀` (exact). -/
  h : Dy
  /-- Coefficient data at the point `s₀`. -/
  pt : CoeffData
  /-- Coefficient data over `[s₀, s₁]`. -/
  iv : CoeffData
  /-- `γ_j ∋ g(s₀)`. -/
  g0 : Ball
  /-- `γ_{j+1} ∋ g(s₁)`. -/
  g1 : Ball
  /-- `o_k` (`k < N`) at `s₀`. -/
  Omg : Array Ball
  /-- `o_k` (`k < N`) over the step. -/
  OmgI : Array Ball
  /-- `h^k`, `k ≤ N+1`. -/
  hp : Array Ball
  /-- `k h^{k-1}` for `2 ≤ k ≤ N` (entries `0, 1` are `0`, unused). -/
  khp : Array Ball
deriving Inhabited

/-- The data of the step `[s₀, s₁]`, given `g0 ∋ g(s₀)`. -/
def mkStep (p N : Nat) (s0 s1 : Dy) (g0 : Ball) : StepData :=
  let h := Dy.sub s1 s0
  let pt := coeffs p s0 s0 N
  let iv := coeffs p s0 s1 N
  let g1 := Ball.add p g0 (dgStep p pt iv h N)
  let hp := powArr p (Ball.ofDy h) N
  let khp := Array.ofFn (n := N + 1) fun k =>
    if k.val < 2 then Ball.zero else Ball.mulNat p (hp.getD (k.val - 1) Ball.zero) k.val
  { s0, s1, h, pt, iv, g0, g1
    Omg := omegaCoeffs p pt g0 N
    OmgI := omegaCoeffs p iv (Ball.hull p g0 g1) N
    hp, khp }

/-- The steps between consecutive points of the list, with `γ` threaded from `g`. -/
def buildSteps (p N : Nat) : List Dy → Ball → List StepData
  | [], _ => []
  | s0 :: rest, g =>
    match rest with
    | [] => []
    | s1 :: _ =>
      let sd := mkStep p N s0 s1 g
      sd :: buildSteps p N rest sd.g1

/-- The steps are consecutive and strictly increasing, from `a` to `ξb`. -/
def chainSteps : Dy → List StepData → Bool
  | a, [] => Dy.beqv a RD.ξb
  | a, sd :: rest => Dy.beqv sd.s0 a && Dy.blt sd.s0 sd.s1 && chainSteps sd.s1 rest

/-- The `λ`-independent data of the middle region `[ξa, ξb]` (Python class `Grid`). -/
structure Grid where
  /-- The Taylor order `N`. -/
  N : Nat
  /-- The steps, in order. -/
  steps : List StepData
  /-- The steps run from `ξa` to `ξb`, consecutive and strictly increasing. -/
  ok : Bool

/-- `Grid(hpow, N)`: the grid with steps of about `2^-hpow` and Taylor order `N`. -/
def Grid.build (p hpow N : Nat) : Grid :=
  let steps := buildSteps p N (gridPts hpow) (gamma0 p)
  { N, steps, ok := chainSteps RD.ξa steps }

end NonUniqueEuler.Verify
