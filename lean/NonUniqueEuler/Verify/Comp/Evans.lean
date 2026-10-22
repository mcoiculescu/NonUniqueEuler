import NonUniqueEuler.Verify.Comp.Grid
import NonUniqueEuler.Verify.Comp.CInv

/-!
# Part 2 algorithms: the enclosure of the Evans function (`evansEncl`)

Manuscript: §A.3, the procedure (ii)–(iv) and Proposition A.3 (`A_verification.tex:239-460`).
Reference: `euler-ring-certificate/src/ringcert/evans.py` (`_step_coeffs`, `_psi_coeffs`,
`evans`), a line-by-line port.

`evansEncl p gr ℓ lam G` returns `some B` with a finite box `B`, or `none` (Python's NaN box:
fail closed). Proposition A.3 (`evansEncl_sound`, `P/Verify/Sound/EvansEncl.lean`): if
`gr = Grid.build p' 8 16` (any precisions), `lam ⊆ {Re > 0}` and `evansEncl p gr ℓ lam G = some B`,
then `evans χ ℓ z G' ∈ B` for every `z ∈ lam`, real `G' ∈ G` and admissible `χ`.

The precision `p` is the midpoint precision of every ball operation (Python: 128 bits).

Core only. No `partial`; the only recursion is `midLoop`, structural on the list of steps.

## Line-by-line table

| manuscript §A.3 | Python `evans.py` | Lean |
|---|---|---|
| (i) `A₀, Ā₀, B₀, B̄₀` hulls | `_H_pair_iv` (l. 61-70) | `hPairIv`, `coeffs` (first lines), `Comp/Grid.lean` |
| (i) recurrences `A_{k+1}`, `B_{k+1}` | `_coeffs` loop (l. 90-96) | `hRec` |
| (i) `w_k, f_k, E^±_k, q_k` | `_coeffs` tail (l. 97-107) | `coeffs` (tail) |
| (i) `γ₀`, `γ_{j+1}` with `∩[0,∞)` | `Grid.__init__` (`dg`, `gmax`, `g`; l. 150-166) | `dgAux`, `dgStep`, `gamma0`, `mkStep`, `buildSteps` |
| (i) `g_r`, `o_k` | `_omega` (l. 110-115), `Grid.__init__` (l. 167-168) | `omegaCoeffs` |
| (i) powers `h^k`, `k h^{k-1}` | `Grid.__init__` (l. 170-177) | `powArr`, `StepData.khp` |
| — | `TVEND = (arb(3)*arb(-50).exp()).upper()` (l. 44) | `tvendUp` |
| (ii) `lo(X) > 0` | `relo = lam.real.lower()`, `if not (relo > 0)` (l. 243-245) | `evansEncl`: `relo`, `isPos` |
| (ii) `ε`, `ε ≤ 1` | `eps = (TVEND/relo).upper()`, `if not (eps <= 1)` (l. 248-250) | `evansEncl`: `eps`, `UB.leDy` |
| (ii) `2ε` | `eg = (2*eps).upper()` (l. 251) | `evansEncl`: `eg` |
| (ii) `P = e^{ℓL₁} + box(2ε up(e^{ℓL₁}))`, `P' = ℓP` | `emL1`, `rad`, `psi`, `dpsi` (l. 252-255) | `evansEncl`: `emL1`, `rad`, `psi0`, `dpsi0` |
| (iii) `D_k` | `_step_coeffs`: `Dk` (l. 188-189) | `stepCoeffs`: `D` |
| (iii) `R_0`, `R_k` | `_step_coeffs`: `R` (l. 190-195) | `stepCoeffs`: `R0` (`CBox.invTight`), `R` |
| (iii) `V_k` | `_step_coeffs`: `Q` (l. 196-203) | `stepCoeffs` (result) |
| (iii) point data and step data | `Q`, `QI` (l. 259-260) | `midStep`: `Q`, `QI` |
| (iii) `q_* = |V^st_0|^up`, finite | `qsup`, `is_finite` (l. 263-265) | `midStep`: `qsup`, `UB.isFin` |
| (iii) `κ_*` | `kap = qsup.max(msq).sqrt().upper()` (l. 266) | `midStep`: `kap` (`UB.sqrtUp`, deviation A3) |
| (iii) `M ≥ max(κ|P|, |P'|) e^{κh}`, `κh ≤ 700` | `Mw`, `arg`, `M` (l. 267-271) | `midStep`: `Mw`, `arg`, `M` |
| (iii) `P^st`, `P'^st` | `psiI`, `dpsiI` (l. 272-273) | `midStep`: `psiI`, `dpsiI` |
| (iii) `Ψ_k`, `Ψ^st_k` | `_psi_coeffs` (l. 206-215), `pc`, `pI` (l. 274-275) | `psiCoeffs`; `midStep`: `pc`, `pI` |
| (iii) `P_new`, `P'_new` | `new_psi`, `new_dpsi`, `psi`, `dpsi` (l. 277-284) | `midStep`: `newPsi`, `newDpsi`, `psi'`, `dpsi'` |
| (iii) finiteness | `if not (psi.is_finite() and dpsi.is_finite())` (l. 285-286) | `midStep` (last line) |
| (iii) the loop `j = 0 … n-1` | `for i in range(grid.n)` (l. 258) | `midLoop` |
| (iv) `L₂`, `e^{ℓL₂}`, `P' + ℓP`, `W` | `L2`, `emL2`, `Wv`, `Wn` (l. 288-291) | `evansEncl`: `emL2`, `Wv`, `Wn` |
| (iv) `+ box(4εW up(e^{ℓL₂}))` | `Eend = Wv*emL2 + box(2*emL2.upper()*Wn*eg)` (l. 292) | `evansEncl`: `Eend` |
| (iv) `e^{-ℓ(ξR-ξL)}`, output | `norm`, `out`, `is_finite` (l. 293-297) | `evansEncl`: `nrm`, `out` |

Arithmetic correspondences: `acb(0, x)` is `CBox.ofIm`,
`acb(0, m) * s` is `CBox.mulI (CBox.mulNat p s m)`, `arb * acb` is `CBox.mulBall`,
`z + box(r)` is `CBox.addDisk z r`, `.upper()` of a magnitude is `UB`, and `1 / Dk[0]` is
`CBox.invTight` (`Comp/CInv.lean`): Arb's `acb_inv` inverts the midpoint and adds the disk error
`r/(|m|(|m|-r))`; `invTight` intersects that enclosure with the box formula `CBox.inv`
(deviation A7; with `CBox.inv` alone the first (N2′) cell needs 208 segments instead of 54,
the package 47).
-/

namespace NonUniqueEuler.Verify

/-- `TVEND`: an exact upper bound of `3e^{-50}` (`none` if the ball is infinite, which does not
happen). -/
def tvendUp (p : Nat) : Option Dy :=
  Ball.upper? (Ball.mulNat p (Ball.expPoint p ⟨-50, 0⟩) 3)

/-- `_step_coeffs(lam, G, m, Omg, em2, fs, N)`: the coefficients `V_k` (`k < N`) of
`V = ℓ² + iℓ f_s R`, `R = 1/D`, `D = λ + iℓ(g e^{-2ξ} + G e^{-2ξ})`, from the coefficient data
`Omg = o`, `em2 = E^-`, `fs = f`. -/
def stepCoeffs (p : Nat) (lam : CBox) (G : Ball) (ℓ : Nat) (Omg em2 fs : Nat → Ball) (N : Nat) :
    Array CBox :=
  -- Dk = [acb(0, m * (Omg[k] + G * em2[k])) for k in range(N)];  Dk[0] = Dk[0] + lam
  let D : Array CBox := Array.ofFn (n := N) fun k =>
    let dk := CBox.ofIm (Ball.mulNat p (Ball.add p (Omg k.val) (Ball.mul p G (em2 k.val))) ℓ)
    if k.val = 0 then CBox.add p dk lam else dk
  let Dk := fun j => D.getD j CBox.zero
  -- R = [1 / Dk[0]]  (Arb's acb_inv: midpoint inverse plus disk error; deviation A7)
  let R0 := CBox.invTight p (Dk 0)
  -- for k in range(1, N): s = Dk[1]*R[k-1] + Σ_{j=2}^{k} Dk[j]*R[k-j];  R.append(-(R[0]*s))
  let R := buildArray (fun arr =>
      let k := arr.size
      CBox.neg (CBox.mul p R0
        (CBox.foldSum p (fun j => CBox.mul p (Dk j) (arr.getD (k - j) CBox.zero))
          (CBox.mul p (Dk 1) (arr.getD (k - 1) CBox.zero)) 2 (k - 1))))
    #[R0] (N - 1)
  -- Q[k] = acb(0, m) * (fs[0]*R[k] + Σ_{j=1}^{k} fs[j]*R[k-j]);  Q[0] = Q[0] + m*m
  Array.ofFn (n := N) fun k =>
    let s := CBox.mulI (CBox.mulNat p (CBox.cauchyBC p fs (fun j => R.getD j CBox.zero) k.val) ℓ)
    if k.val = 0 then CBox.addBall p s (Ball.ofNat (ℓ * ℓ)) else s

/-- `_psi_coeffs(Q, p0, p1, N)`: `ψ_0 = p0`, `ψ_1 = p1` and
`ψ_{k+2} = (Σ_{j≤k} Q_j ψ_{k-j}) / ((k+1)(k+2))` for `k < N` (so `ψ_0, …, ψ_{N+1}`). -/
def psiCoeffs (p : Nat) (Q : Array CBox) (p0 p1 : CBox) (N : Nat) : Array CBox :=
  buildArray (fun arr =>
      let k := arr.size - 2
      CBox.divNat p
        (CBox.cauchy p (fun j => Q.getD j CBox.zero) (fun j => arr.getD j CBox.zero) k)
        ((k + 1) * (k + 2)))
    #[p0, p1] N

/-- One middle step (the body of the loop of `evans`, l. 259-286): from enclosures
`psi ∋ ψ(s₀)`, `dpsi ∋ ψ'(s₀)` to enclosures of `ψ(s₁)`, `ψ'(s₁)`; `none` if a required
comparison fails or a result is infinite. -/
def midStep (p ℓ : Nat) (lam : CBox) (G : Ball) (N : Nat) (sd : StepData) (psi dpsi : CBox) :
    Option (CBox × CBox) :=
  let Q := stepCoeffs p lam G ℓ (fun k => sd.Omg.getD k Ball.zero)
    (fun k => sd.pt.em2.getD k Ball.zero) (fun k => sd.pt.fs.getD k Ball.zero) N
  let QI := stepCoeffs p lam G ℓ (fun k => sd.OmgI.getD k Ball.zero)
    (fun k => sd.iv.em2.getD k Ball.zero) (fun k => sd.iv.fs.getD k Ball.zero) N
  -- a priori enclosure over the step (Gronwall in the norm max(κ|ψ|, |ψ'|))
  let qsup := CBox.absUB (QI.getD 0 CBox.zero)
  if !qsup.isFin then none
  else
    let kap := UB.sqrtUp (UB.max qsup (UB.ofNat (ℓ * ℓ)))
    let Mw := UB.max (UB.mul kap (CBox.absUB psi)) (CBox.absUB dpsi)
    let hU := UB.ofDyUp sd.h
    let arg := UB.mul kap hU
    if !(UB.leDy arg ⟨700, 0⟩) then none
    else
      let M := UB.mul Mw (UB.expUp arg)
      let psiI := CBox.addDisk psi (UB.mul hU M)
      let dpsiI := CBox.addDisk dpsi (UB.div (UB.mul (UB.mul hU qsup) M) kap)
      let pc := psiCoeffs p Q psi dpsi N
      let pI := psiCoeffs p QI psiI dpsiI N
      let pcf := fun k => pc.getD k CBox.zero
      let pIf := fun k => pI.getD k CBox.zero
      let hp := fun k => sd.hp.getD k Ball.zero
      let khp := fun k => sd.khp.getD k Ball.zero
      -- new_psi = pc[0] + Σ_{k=1}^{N-1} pc[k]*hp[k];  new_dpsi = pc[1] + Σ_{k=2}^{N} pc[k]*khp[k]
      let newPsi := CBox.foldSum p (fun k => CBox.mulBall p (pcf k) (hp k)) (pcf 0) 1 (N - 1)
      let newDpsi := CBox.foldSum p (fun k => CBox.mulBall p (pcf k) (khp k)) (pcf 1) 2 (N - 1)
      -- integral-form remainders (convex boxes)
      let psi' := CBox.add p newPsi (CBox.mulBall p (pIf N) (hp N))
      let dpsi' := CBox.add p newDpsi (CBox.mulBall p (pIf (N + 1)) (Ball.mulNat p (hp N) (N + 1)))
      if psi'.isFinite && dpsi'.isFinite then some (psi', dpsi') else none

/-- The middle region: `midStep` over the steps in order. -/
def midLoop (p ℓ : Nat) (lam : CBox) (G : Ball) (N : Nat) :
    List StepData → CBox → CBox → Option (CBox × CBox)
  | [], psi, dpsi => some (psi, dpsi)
  | sd :: rest, psi, dpsi =>
    match midStep p ℓ lam G N sd psi dpsi with
    | some r => midLoop p ℓ lam G N rest r.1 r.2
    | none => none

/-- **The enclosure procedure** (`evans.evans`): a finite box containing `E_ℓ(λ; G')` for all
`λ ∈ lam` and real `G' ∈ G`, for every admissible cutoff; `none` if the procedure fails. -/
def evansEncl (p : Nat) (gr : Grid) (ℓ : Nat) (lam : CBox) (G : Ball) : Option CBox :=
  if !gr.ok then none
  else
    match lam.re.lower?, tvendUp p with
    | some relo, some tv =>
      if !relo.isPos then none
      else
        -- left end [ξL, ξa] (Lemma A.1)
        let eps := UB.div (UB.ofDyUp tv) (UB.ofDyExact relo)
        if !(UB.leDy eps Dy.one) then none
        else
          let eg := UB.scale eps 1
          let emL1 := Ball.expPoint p (Dy.mul (Dy.ofNat ℓ) (Dy.sub RD.ξa RD.ξL))
          let rad := UB.mul (Ball.upperUB emL1) eg
          let psi0 := CBox.addDisk (CBox.ofBall emL1) rad
          let dpsi0 := CBox.mulNat p psi0 ℓ
          -- middle [ξa, ξb]
          match midLoop p ℓ lam G gr.N gr.steps psi0 dpsi0 with
          | none => none
          | some (psi, dpsi) =>
            -- right end [ξb, ξR] (Lemma A.1 again)
            let emL2 := Ball.expPoint p (Dy.mul (Dy.ofNat ℓ) (Dy.sub RD.ξR RD.ξb))
            let Wv := CBox.add p dpsi (CBox.mulNat p psi ℓ)
            let Wn := UB.max (UB.mulNat (CBox.absUB psi) ℓ) (CBox.absUB dpsi)
            let Eend := CBox.addDisk (CBox.mulBall p Wv emL2)
              (UB.mul (UB.mul (UB.scale (Ball.upperUB emL2) 1) Wn) eg)
            let nrm := Ball.expPoint p (Dy.neg (Dy.mul (Dy.ofNat ℓ) (Dy.sub RD.ξR RD.ξL)))
            let out := CBox.mulBall p Eend nrm
            if out.isFinite then some out else none
    | _, _ => none

end NonUniqueEuler.Verify
