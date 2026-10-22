import NonUniqueEuler.I.Verify.Sound.StepCoeffs
import NonUniqueEuler.I.Verify.StepGronwall
import NonUniqueEuler.I.Verify.TaylorRemainder
import NonUniqueEuler.I.Evans.ODE

/-!
# Proof: Proposition A.3, step (iii): one middle step and the middle region

Proof of `I/Verify/Sound/MidStep.lean` (same declarations, same statements).

**Manuscript.** Proof of Proposition A.3 (`prop:enclosure`), step (iii)
(`A_verification.tex:404-437`). **Code.** `Verify/Comp/Evans.lean`: `midStep`,
`midLoop`.

Structure of the proof of `midStep_sound` (helpers in the namespace `MidStepAux`):
* `MidStepAux.apriori_mem`: the a priori enclosure (Grönwall, `apriori_step`) turned into the
  boxes `psiI = psi + box(h M)`, `dpsiI = dpsi + box(h q_* M / κ_*)` of the code, for any
  enclosures of `ψ(s₀)`, `ψ'(s₀)` and any finite `q_*` bounding `|V|` on the step. The real
  bound `M` passed to `apriori_step` is the exact `max(κ|ψ(s₀)|, |ψ'(s₀)|) e^{κh}`, so no case
  split on the finiteness of the code's `M` is needed.
* `MidStepAux.psi_step_mem`, `MidStepAux.dpsi_step_mem`: the Taylor step in box form
  (`taylor_mem_reProdIm`, `taylor_deriv_mem_reProdIm`) for the code's sums `newPsi + Ψ^st_N h^N`
  and `newDpsi + Ψ^st_{N+1} (N+1) h^N`, including the reindexing of the sums (`N ≥ 1`).
* `midStep_sound`: unfold `midStep`, split its three guards, and combine the above with
  `stepCoeffs_sound` (point data and step data) and `psiCoeffs_sound` (at `s₀` and on the
  step).
`midLoop_sound`: induction on the list of steps.
-/

noncomputable section

open Set
open scoped ContDiff

namespace NonUniqueEuler.Verify

open AppA RingData

namespace MidStepAux

/-- A box as a product of its real and imaginary parts. -/
theorem mem_iff_reProdIm {B : CBox} {z : ℂ} :
    z ∈ B ↔ z ∈ {x : ℝ | x ∈ B.re} ×ℂ {y : ℝ | y ∈ B.im} := by
  rw [Complex.mem_reProdIm]; rfl

/-- The negated guards of `midStep`. -/
theorem of_not_not {b : Bool} (h : ¬(!b) = true) : b = true := by
  cases b <;> simp_all

/-- `UB.leDy` is `false` on `inf`. -/
theorem isFin_of_leDy {U : UB} {c : Dy} (h : U.leDy c = true) : U.isFin = true := by
  cases U with
  | fin m e => rfl
  | inf => simp [UB.leDy] at h

/-- An upper bound of two reals bounds their maximum. -/
theorem bounds_max_of {U : UB} {a b : ℝ} (ha : a ≤ᵤ U) (hb : b ≤ᵤ U) : max a b ≤ᵤ U := by
  cases U with
  | fin m e => exact max_le ha hb
  | inf => trivial

/-- **The a priori enclosure of one step** (code: `qsup`, `kap`, `Mw`, `hU`, `arg`, `M`,
`psiI`, `dpsiI`). If `|V| ≤ q_*` on `[s₀, s₀ + h]` (`q_*` finite), the step passed the test
`κ_* h ≤ 700`, `ψ(s₀) ∈ psi` and `ψ'(s₀) ∈ dpsi`, then `ψ ∈ psiI` and `ψ' ∈ dpsiI` on the
step. -/
theorem apriori_mem {ψ V : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hode : ∀ ξ, deriv (deriv ψ) ξ = V ξ * ψ ξ) {s : ℝ} {hd : Dy} (hh : 0 ≤ hd.toReal)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {qsup kap hU Mw M : UB} (hq : qsup.isFin = true)
    (hV : ∀ ξ ∈ Icc s (s + hd.toReal), ‖V ξ‖ ≤ᵤ qsup)
    {psi dpsi : CBox} (h0 : ψ s ∈ psi) (h1 : deriv ψ s ∈ dpsi)
    (hkap : kap = (qsup.max (UB.ofNat (ℓ * ℓ))).sqrtUp) (hhU : hU = UB.ofDyUp hd)
    (hMw : Mw = (kap.mul psi.absUB).max dpsi.absUB) (hM : M = Mw.mul (kap.mul hU).expUp)
    (harg : (kap.mul hU).leDy ⟨700, 0⟩ = true) :
    ∀ ξ ∈ Icc s (s + hd.toReal),
      ψ ξ ∈ psi.addDisk (hU.mul M) ∧ deriv ψ ξ ∈ dpsi.addDisk (((hU.mul qsup).mul M).div kap) := by
  have hfin := UB.isFin_of_mul (isFin_of_leDy harg)
  have hks := kappa_sound hq ℓ (hkap ▸ hfin.1)
  rw [← hkap] at hks
  set κ := kap.toReal with hκ
  set q := qsup.toReal with hqdef
  set h := hd.toReal with hhd
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hκpos : 0 < κ := by linarith [hks.2]
  have hq0 : 0 ≤ q := UB.toReal_nonneg qsup
  -- derivatives of the global smooth solution
  have hd1 := contDiff_infty_iff_deriv.mp hψ
  have hd2 := contDiff_infty_iff_deriv.mp hd1.2
  have hψd : ∀ ξ ∈ Icc s (s + h), HasDerivWithinAt ψ (deriv ψ ξ) (Icc s (s + h)) ξ :=
    fun ξ _ => (hd1.1 ξ).hasDerivAt.hasDerivWithinAt
  have hψ'd : ∀ ξ ∈ Icc s (s + h),
      HasDerivWithinAt (deriv ψ) (V ξ * ψ ξ) (Icc s (s + h)) ξ := by
    intro ξ _
    have := (hd2.1 ξ).hasDerivAt
    rw [hode] at this
    exact this.hasDerivWithinAt
  have hVr : ∀ ξ ∈ Icc s (s + h), ‖V ξ‖ ≤ q := fun ξ hξ => (hV ξ hξ).le_toReal hq
  -- the real bound `Mr` and its upper bound `M`
  set Mr := max (κ * ‖ψ s‖) ‖deriv ψ s‖ * Real.exp (κ * h) with hMr
  have hap := apriori_step (ψ := ψ) (ψ' := deriv ψ) (V := V) (M := Mr) hh hκpos hψd hψ'd hVr
    hks.1 le_rfl
  have hκb : κ ≤ᵤ kap := UB.bounds_of_isFin hfin.1 le_rfl
  have hhb : h ≤ᵤ hU := hhU ▸ UB.bounds_ofDyUp le_rfl
  have hqb : q ≤ᵤ qsup := UB.bounds_of_isFin hq le_rfl
  have hMwb : max (κ * ‖ψ s‖) ‖deriv ψ s‖ ≤ᵤ Mw := hMw ▸ bounds_max_of
    (UB.bounds_max_left (UB.bounds_mul hκpos.le (norm_nonneg _) hκb (CBox.norm_le_absUB h0)))
    (UB.bounds_max_right (CBox.norm_le_absUB h1))
  have hexpb : Real.exp (κ * h) ≤ᵤ (kap.mul hU).expUp :=
    UB.bounds_expUp (UB.bounds_mul hκpos.le hh hκb hhb)
  have hMr0 : 0 ≤ Mr := mul_nonneg ((mul_nonneg hκpos.le (norm_nonneg _)).trans (le_max_left _ _))
    (Real.exp_pos _).le
  have hMrb : Mr ≤ᵤ M := hM ▸ UB.bounds_mul ((mul_nonneg hκpos.le (norm_nonneg _)).trans
    (le_max_left _ _)) (Real.exp_pos _).le hMwb hexpb
  intro ξ hξ
  obtain ⟨hξ1, hξ2⟩ := hap ξ hξ
  refine ⟨CBox.mem_addDisk h0 (UB.Bounds.mono hξ1 (UB.bounds_mul hh hMr0 hhb hMrb)),
    CBox.mem_addDisk h1 (UB.Bounds.mono hξ2 ?_)⟩
  exact UB.bounds_div' (mul_nonneg (mul_nonneg hh hq0) hMr0)
    (UB.bounds_mul (mul_nonneg hh hq0) hMr0 (UB.bounds_mul hh hq0 hhb hqb) hMrb) hfin.1 hκpos
    le_rfl

/-- **The Taylor step for `ψ`** (code: `newPsi`, `psi'`): `ψ(s+h) ∈ newPsi + Ψ^st_N · h^N`,
where `newPsi = Ψ_0 + Σ_{k=1}^{N-1} Ψ_k h^k`. -/
theorem psi_step_mem {p : ℕ} {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) {s h : ℝ} (hh : 0 ≤ h) {N : ℕ}
    (hN : 1 ≤ N) {pc pI : Array CBox} {hp : Array Ball}
    (hpc : ∀ k < N + 2, taylorCoeff ψ k s ∈ pc.getD k CBox.zero)
    (hpI : ∀ η ∈ Icc s (s + h), ∀ k < N + 2, taylorCoeff ψ k η ∈ pI.getD k CBox.zero)
    (hhp : ∀ k ≤ N + 1, h ^ k ∈ hp.getD k Ball.zero) :
    ψ (s + h) ∈ CBox.add p
      (CBox.foldSum p (fun k => CBox.mulBall p (pc.getD k CBox.zero) (hp.getD k Ball.zero))
        (pc.getD 0 CBox.zero) 1 (N - 1))
      (CBox.mulBall p (pI.getD N CBox.zero) (hp.getD N Ball.zero)) := by
  rw [mem_iff_reProdIm]
  apply taylor_mem_reProdIm hψ hh N
  intro η hη
  rw [← mem_iff_reProdIm]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hsum := CBox.mem_foldSum (p := p)
    (f := fun k => CBox.mulBall p (pc.getD k CBox.zero) (hp.getD k Ball.zero))
    (y := fun k => taylorCoeff ψ k s * ((h ^ k : ℝ) : ℂ)) (acc := pc.getD 0 CBox.zero)
    (a := taylorCoeff ψ 0 s) (j := 1) (n := n) (hpc 0 (by omega))
    (fun i hi => CBox.mem_mulBall (hpc _ (by omega)) (hhp _ (by omega)))
  have hrem := CBox.mem_mulBall (p := p) (hpI η hη (n + 1) (by omega)) (hhp (n + 1) (by omega))
  have hall := CBox.mem_add (p := p) hsum hrem
  rw [Nat.add_sub_cancel]
  convert hall using 1
  rw [taylorPoly, Finset.sum_range_succ']
  simp only [Complex.real_smul, pow_zero, Complex.ofReal_one, one_mul]
  have e : ∑ i ∈ Finset.range n, ((h ^ (i + 1) : ℝ) : ℂ) * taylorCoeff ψ (i + 1) s =
      ∑ i ∈ Finset.range n, taylorCoeff ψ (1 + i) s * ((h ^ (1 + i) : ℝ) : ℂ) :=
    Finset.sum_congr rfl fun i _ => by rw [add_comm 1 i, mul_comm]
  rw [e]
  ring

/-- **The Taylor step for `ψ'`** (code: `newDpsi`, `dpsi'`):
`ψ'(s+h) ∈ newDpsi + Ψ^st_{N+1} · (N+1) h^N`, where
`newDpsi = Ψ_1 + Σ_{k=2}^{N} Ψ_k · k h^{k-1}`. -/
theorem dpsi_step_mem {p : ℕ} {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) {s h : ℝ} (hh : 0 ≤ h) {N : ℕ}
    (hN : 1 ≤ N) {pc pI : Array CBox} {hp khp : Array Ball}
    (hpc : ∀ k < N + 2, taylorCoeff ψ k s ∈ pc.getD k CBox.zero)
    (hpI : ∀ η ∈ Icc s (s + h), ∀ k < N + 2, taylorCoeff ψ k η ∈ pI.getD k CBox.zero)
    (hhp : ∀ k ≤ N + 1, h ^ k ∈ hp.getD k Ball.zero)
    (hkhp : ∀ k, 2 ≤ k → k ≤ N → (k : ℝ) * h ^ (k - 1) ∈ khp.getD k Ball.zero) :
    deriv ψ (s + h) ∈ CBox.add p
      (CBox.foldSum p (fun k => CBox.mulBall p (pc.getD k CBox.zero) (khp.getD k Ball.zero))
        (pc.getD 1 CBox.zero) 2 (N - 1))
      (CBox.mulBall p (pI.getD (N + 1) CBox.zero) (Ball.mulNat p (hp.getD N Ball.zero) (N + 1))) := by
  rw [mem_iff_reProdIm]
  apply taylor_deriv_mem_reProdIm hψ hh N
  intro η hη
  rw [← mem_iff_reProdIm]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hsum := CBox.mem_foldSum (p := p)
    (f := fun k => CBox.mulBall p (pc.getD k CBox.zero) (khp.getD k Ball.zero))
    (y := fun k => taylorCoeff ψ k s * (((k : ℝ) * h ^ (k - 1) : ℝ) : ℂ))
    (acc := pc.getD 1 CBox.zero) (a := taylorCoeff ψ 1 s) (j := 2) (n := n) (hpc 1 (by omega))
    (fun i hi => CBox.mem_mulBall (hpc _ (by omega)) (hkhp _ (by omega) (by omega)))
  have hrem := CBox.mem_mulBall (p := p) (hpI η hη (n + 1 + 1) (by omega))
    (Ball.mem_mulNat (p := p) (hhp (n + 1) (by omega)) (n + 1 + 1))
  have hall := CBox.mem_add (p := p) hsum hrem
  rw [Nat.add_sub_cancel]
  convert hall using 1
  rw [Finset.sum_range_succ']
  simp only [Complex.real_smul]
  have e : ∑ i ∈ Finset.range n,
      ((((i + 1 : ℕ) : ℝ) + 1) * h ^ (i + 1) : ℝ) * taylorCoeff ψ (i + 1 + 1) s =
      ∑ i ∈ Finset.range n,
        taylorCoeff ψ (2 + i) s * ((((2 + i : ℕ) : ℝ) * h ^ (2 + i - 1) : ℝ) : ℂ) :=
    Finset.sum_congr rfl fun i _ => by
      rw [show 2 + i - 1 = i + 1 by omega, show i + 1 + 1 = 2 + i by omega, mul_comm]
      push_cast; ring_nf
  push_cast at e ⊢
  rw [e]
  ring

end MidStepAux

open MidStepAux

/-- **One middle step** (`midStep`): if `ψ(s₀) ∈ psi`, `ψ'(s₀) ∈ dpsi`, the step data are sound
and the step succeeds with `(psi', dpsi')`, then `ψ(s₁) ∈ psi'` and `ψ'(s₁) ∈ dpsi'`. -/
theorem midStep_sound {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {p ℓ N : ℕ} (hℓ : 1 ≤ ℓ)
    (hN : 1 ≤ N) {lam : CBox} {Gb : Ball} {z : ℂ} (hz : z ∈ lam) (hz0 : 0 < z.re) {G : ℝ}
    (hG : G ∈ Gb) {sd : StepData} (hsd : StepSound χ N sd) {ψ : ℝ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hode : ∀ ξ, deriv (deriv ψ) ξ = riccatiCoeff χ ℓ z G ξ * ψ ξ)
    {psi dpsi : CBox} (h0 : ψ sd.s0.toReal ∈ psi) (h1 : deriv ψ sd.s0.toReal ∈ dpsi)
    {r : CBox × CBox} (h : midStep p ℓ lam Gb N sd psi dpsi = some r) :
    ψ sd.s1.toReal ∈ r.1 ∧ deriv ψ sd.s1.toReal ∈ r.2 := by
  have hlt := hsd.lt
  have hheq := hsd.h_eq
  have hh : 0 ≤ sd.h.toReal := by rw [hheq]; linarith
  have e1 : sd.s1.toReal = sd.s0.toReal + sd.h.toReal := by rw [hheq]; ring
  have hVc := contDiff_riccatiCoeff χ hχ ℓ z hz0 G
  -- the coefficients `V_k` at `s₀` and over the step
  have hS0 : ({sd.s0.toReal} : Set ℝ) ⊆ Icc ξa ξb :=
    singleton_subset_iff.2 ⟨hsd.left, hlt.le.trans hsd.right⟩
  have hSI : Icc sd.s0.toReal sd.s1.toReal ⊆ Icc ξa ξb := Icc_subset_Icc hsd.left hsd.right
  have hQ := stepCoeffs_sound (p := p) (ℓ := ℓ) hχ hz hz0 hG hS0 hsd.Omg
    (fun ξ hξ k hk => hsd.pt.em2 ξ hξ k (by omega)) (fun ξ hξ k hk => hsd.pt.fs ξ hξ k (by omega))
  have hQI := stepCoeffs_sound (p := p) (ℓ := ℓ) hχ hz hz0 hG hSI hsd.OmgI
    (fun ξ hξ k hk => hsd.iv.em2 ξ hξ k (by omega)) (fun ξ hξ k hk => hsd.iv.fs ξ hξ k (by omega))
  have hIcc : ∀ η ∈ Icc sd.s0.toReal (sd.s0.toReal + sd.h.toReal),
      η ∈ Icc sd.s0.toReal sd.s1.toReal := fun η hη => by rwa [e1]
  -- the coefficients `Ψ_k` at `s₀`
  have hpc := psiCoeffs_sound (p := p) hψ hVc hode (fun k hk => hQ _ rfl k hk) h0 h1
  -- `|V| ≤ q_*` on the step
  have hVb : ∀ ξ ∈ Icc sd.s0.toReal (sd.s0.toReal + sd.h.toReal),
      ‖riccatiCoeff χ ℓ z G ξ‖ ≤ᵤ (CBox.absUB ((stepCoeffs p lam Gb ℓ
        (fun k => sd.OmgI.getD k Ball.zero) (fun k => sd.iv.em2.getD k Ball.zero)
        (fun k => sd.iv.fs.getD k Ball.zero) N).getD 0 CBox.zero)) := by
    intro ξ hξ
    have := hQI ξ (hIcc ξ hξ) 0 (by omega)
    rw [taylorCoeff_zero] at this
    exact CBox.norm_le_absUB this
  unfold midStep at h
  dsimp only at h
  split at h
  · simp at h
  rename_i hq
  split at h
  · simp at h
  rename_i harg
  split at h
  swap
  · simp at h
  cases h
  have hap := apriori_mem hψ hode hh hℓ (of_not_not hq) hVb h0 h1 rfl rfl rfl rfl
    (of_not_not harg)
  have hpI : ∀ η ∈ Icc sd.s0.toReal (sd.s0.toReal + sd.h.toReal), ∀ k < N + 2,
      taylorCoeff ψ k η ∈ (psiCoeffs p (stepCoeffs p lam Gb ℓ
        (fun k => sd.OmgI.getD k Ball.zero) (fun k => sd.iv.em2.getD k Ball.zero)
        (fun k => sd.iv.fs.getD k Ball.zero) N) _ _ N).getD k CBox.zero :=
    fun η hη => psiCoeffs_sound (p := p) hψ hVc hode (fun k hk => hQI η (hIcc η hη) k hk)
      (hap η hη).1 (hap η hη).2
  rw [e1]
  exact ⟨psi_step_mem hψ hh hN hpc hpI hsd.hp, dpsi_step_mem hψ hh hN hpc hpI hsd.hp hsd.khp⟩

/-- **The middle region** (`midLoop`): along a chain of sound steps from `a` to `ξb`, the
enclosures of `(ψ, ψ')` at `a` become enclosures at `ξb`. -/
theorem midLoop_sound {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {p ℓ N : ℕ} (hℓ : 1 ≤ ℓ)
    (hN : 1 ≤ N) {lam : CBox} {Gb : Ball} {z : ℂ} (hz : z ∈ lam) (hz0 : 0 < z.re) {G : ℝ}
    (hG : G ∈ Gb) {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hode : ∀ ξ, deriv (deriv ψ) ξ = riccatiCoeff χ ℓ z G ξ * ψ ξ) :
    ∀ (steps : List StepData) (a : ℝ) (psi dpsi : CBox) (r : CBox × CBox),
      StepChain a steps → (∀ sd ∈ steps, StepSound χ N sd) →
      ψ a ∈ psi → deriv ψ a ∈ dpsi → midLoop p ℓ lam Gb N steps psi dpsi = some r →
      ψ ξb ∈ r.1 ∧ deriv ψ ξb ∈ r.2 := by
  intro steps
  induction steps with
  | nil =>
    intro a psi dpsi r hc _ h0 h1 h
    simp only [midLoop, Option.some.injEq] at h
    subst h
    have ha : a = ξb := hc
    subst ha
    exact ⟨h0, h1⟩
  | cons sd rest ih =>
    intro a psi dpsi r hc hs h0 h1 h
    obtain ⟨ha, hc'⟩ := hc
    have hsd : StepSound χ N sd := hs sd (by simp)
    simp only [midLoop] at h
    split at h
    · rename_i r' hr'
      have hstep := midStep_sound hχ hℓ hN hz hz0 hG hsd hψ hode (ha ▸ h0) (ha ▸ h1) hr'
      exact ih sd.s1.toReal r'.1 r'.2 r hc' (fun x hx => hs x (by simp [hx])) hstep.1 hstep.2 h
    · simp at h

end NonUniqueEuler.Verify
