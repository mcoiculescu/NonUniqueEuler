import NonUniqueEuler.Verify.Comp.Evans
import NonUniqueEuler.Defs.Verify.SemElem
import NonUniqueEuler.Defs.Verify.SemCInv
import NonUniqueEuler.Defs.Verify.CertifyBasic
import NonUniqueEuler.Defs.Verify.Taylor
import NonUniqueEuler.Defs.Verify.Profile

/-!
# Soundness predicates of the enclosure procedure (definitions and basic facts, all proved)

Manuscript: Proposition A.3 (`prop:enclosure`, `A_verification.tex:301-460`), step (i): the
`λ`-independent data are valid enclosures of the Taylor coefficients of the profile objects.
Code: `Verify/Comp/{Grid,Evans,Contour,Certify}.lean`.

These are the invariants that the stage lemmas of Proposition A.3 (`I/Verify/Sound/*`) are
stated with. They mention the code's arrays exactly as the code reads them
(`fun k => arr.getD k Ball.zero`), so that a stage lemma applies to the code term without
rewriting.

* `CoeffEncl f S n c`, `CoeffEnclC f S n c`: for every `ξ ∈ S` and `k < n`, the Taylor
  coefficient `f_k(ξ) = f^{(k)}(ξ)/k!` lies in the ball (box) `c k`.
* `CoeffDataSound N cd S`: the coefficient data `cd` of `coeffs` (Python `_coeffs`) enclose the
  coefficients of `w = AB`, `f = (AB)'`, `e^{±2ξ}`, `q = AB e^{2ξ}` on `S` (to order `N+1`,
  resp. `N`).
* `omegaFn χ = g e^{-2ξ}`, so `Ω_G = omegaFn χ + G e^{-2ξ}` (`OmegaG_eq`).
* `StepSound χ N sd`: the data of one step `[s₀, s₁] ⊆ [ξa, ξb]` are valid (the conclusion of
  step (i) of Proposition A.3 for this step): coefficient data at `s₀` and over the step,
  `γ_j ∋ g(s₀)`, `γ_{j+1} ∋ g(s₁)`, the coefficients `o_k` of `g e^{-2ξ}` at `s₀` and over the
  step, and the powers `h^k`, `k h^{k-1}`.
* `StepChain a steps`: the steps are consecutive, from `a` to `ξb`.
* `GridSound χ gr`: the steps of `gr` form a chain from `ξa` to `ξb` and each is sound.

Proved basic facts:
* the pinned data: `RD.a0_toReal`, `RD.d_toReal`, `RD.ξL_toReal`, `RD.ξa_toReal`,
  `RD.ξb_toReal`, `RD.ξR_toReal`; `fact_eq_factorial`;
* `chainSteps_spec` (what `Grid.ok` checks), `StepChain.bounds`, `mem_buildSteps`
  (every step of `buildSteps` is `mkStep` of its own end points and `g`-ball),
  `Grid.build_N`, `Grid.build_steps`, `Grid.build_ok`;
* `evansEncl_re_pos`: a successful enclosure certifies `Re λ > 0` on the `λ`-box;
  `evansEncl_grid_ok`: it has passed the grid check;
* `mem_gBall`, `mem_ptBox`: the `G`-ball and the point boxes of the certification;
* derived containment (CP) facts of the composite arithmetic of `evansEncl` and `Grid.build`:
  `mem_expPoint_endL`, `mem_expPoint_endR`, `mem_expPoint_nrm` (`e^{ℓL₁}`, `e^{ℓL₂}`,
  `e^{-ℓ(ξR-ξL)}`), `tvendUp_sound` (`TVEND ≥ 3e^{-50}`), `eps_sound` (`ε ≥ ε_end`),
  `kappa_sound` (`q_* ≤ κ_*²`, `ℓ ≤ κ_*`), `mem_ofFrac_two_pow` (`2^k/k!`), `mem_powArr`
  (`h^k`). The CP of every single ball, box and upper-bound operation is in
  `Defs/Verify/{Sem,SemOps,SemElem,SemCInv}.lean`.
-/

noncomputable section

open Set

namespace NonUniqueEuler.Verify

open AppA RingData

/-! ### Taylor-coefficient enclosures -/

/-- `c k` encloses the Taylor coefficient `f_k(ξ)` for every `ξ ∈ S` and `k < n`. -/
def CoeffEncl (f : ℝ → ℝ) (S : Set ℝ) (n : ℕ) (c : ℕ → Ball) : Prop :=
  ∀ ξ ∈ S, ∀ k < n, taylorCoeff f k ξ ∈ c k

/-- `c k` encloses the Taylor coefficient `f_k(ξ)` for every `ξ ∈ S` and `k < n` (complex
version). -/
def CoeffEnclC (f : ℝ → ℂ) (S : Set ℝ) (n : ℕ) (c : ℕ → CBox) : Prop :=
  ∀ ξ ∈ S, ∀ k < n, taylorCoeff f k ξ ∈ c k

/-- The coefficient data `cd` (`coeffs p Slo Shi N`, Python `_coeffs`) are valid on `S`:
`w_k` (`k ≤ N+1`) of `w = AB`, `fs_k` (`k ≤ N`) of `(AB)'`, `e2_k`, `em2_k` (`k ≤ N`) of
`e^{±2ξ}`, and `q_k` (`k ≤ N`) of `q = AB e^{2ξ}`. On `[ξa, ξb]` these are the coefficients of
`ϖ`, `ϖ'` and `ϖ e^{2ξ}` (`taylorCoeff_prof_eq` etc. of `I/Verify/ProfileBasic.lean`). -/
structure CoeffDataSound (N : ℕ) (cd : CoeffData) (S : Set ℝ) : Prop where
  w : CoeffEncl profW S (N + 2) fun k => cd.w.getD k Ball.zero
  fs : CoeffEncl (deriv profW) S (N + 1) fun k => cd.fs.getD k Ball.zero
  e2 : CoeffEncl (fun x => Real.exp (2 * x)) S (N + 1) fun k => cd.e2.getD k Ball.zero
  em2 : CoeffEncl (fun x => Real.exp (-2 * x)) S (N + 1) fun k => cd.em2.getD k Ball.zero
  q : CoeffEncl profQ S (N + 1) fun k => cd.q.getD k Ball.zero

/-- `g e^{-2ξ}`, the `G`-independent part of `Ω_G = e^{-2ξ}(G + g)`. -/
def omegaFn (χ : ℝ → ℝ) (x : ℝ) : ℝ := gInt χ x * Real.exp (-2 * x)

theorem OmegaG_eq_omegaFn (χ : ℝ → ℝ) (G x : ℝ) :
    OmegaG χ G x = omegaFn χ x + G * Real.exp (-2 * x) := by
  rw [OmegaG_eq, omegaFn]; ring

/-! ### The steps and the grid -/

/-- The data `sd` of one step of the middle region are valid for the cutoff `χ` (step (i) of
Proposition A.3 for the step `[s₀, s₁]`, `h = s₁ - s₀`). -/
structure StepSound (χ : ℝ → ℝ) (N : ℕ) (sd : StepData) : Prop where
  /-- `s₀ < s₁`. -/
  lt : sd.s0.toReal < sd.s1.toReal
  /-- `ξa ≤ s₀`. -/
  left : ξa ≤ sd.s0.toReal
  /-- `s₁ ≤ ξb`. -/
  right : sd.s1.toReal ≤ ξb
  /-- `h = s₁ - s₀` (exact). -/
  h_eq : sd.h.toReal = sd.s1.toReal - sd.s0.toReal
  /-- The coefficient data at the point `s₀`. -/
  pt : CoeffDataSound N sd.pt {sd.s0.toReal}
  /-- The coefficient data over the step. -/
  iv : CoeffDataSound N sd.iv (Icc sd.s0.toReal sd.s1.toReal)
  /-- `γ_j ∋ g(s₀)`. -/
  g0 : gInt χ sd.s0.toReal ∈ sd.g0
  /-- `γ_{j+1} ∋ g(s₁)`. -/
  g1 : gInt χ sd.s1.toReal ∈ sd.g1
  /-- `o_k` (`k < N`) of `g e^{-2ξ}` at `s₀`. -/
  Omg : CoeffEncl (omegaFn χ) {sd.s0.toReal} N fun k => sd.Omg.getD k Ball.zero
  /-- `o_k` (`k < N`) of `g e^{-2ξ}` over the step. -/
  OmgI : CoeffEncl (omegaFn χ) (Icc sd.s0.toReal sd.s1.toReal) N
    fun k => sd.OmgI.getD k Ball.zero
  /-- `hp[k] ∋ h^k` for `k ≤ N + 1`. -/
  hp : ∀ k ≤ N + 1, sd.h.toReal ^ k ∈ sd.hp.getD k Ball.zero
  /-- `khp[k] ∋ k h^{k-1}` for `2 ≤ k ≤ N`. -/
  khp : ∀ k, 2 ≤ k → k ≤ N → (k : ℝ) * sd.h.toReal ^ (k - 1) ∈ sd.khp.getD k Ball.zero

/-- The steps are consecutive, starting at `a` and ending at `ξb`. -/
def StepChain : ℝ → List StepData → Prop
  | a, [] => a = ξb
  | a, sd :: rest => sd.s0.toReal = a ∧ StepChain sd.s1.toReal rest

/-- The grid is valid for the cutoff `χ`: its steps run consecutively from `ξa` to `ξb`, and
each step is sound (the conclusion of step (i) of Proposition A.3). -/
structure GridSound (χ : ℝ → ℝ) (gr : Grid) : Prop where
  chain : StepChain ξa gr.steps
  steps : ∀ sd ∈ gr.steps, StepSound χ gr.N sd

/-! ### The pinned data (proved) -/

theorem RD.a0_toReal : RD.a0.toReal = RingData.a₀ := by
  simp only [RD.a0, Dy.toReal_mk, RingData.a₀]; norm_num

theorem RD.d_toReal : RD.d.toReal = RingData.d := by
  simp only [RD.d, Dy.toReal_mk, RingData.d]; norm_num

theorem RD.ξL_toReal : RD.ξL.toReal = RingData.ξL := by
  simp only [RD.ξL, Dy.toReal_mk, RingData.ξL]; norm_num

theorem RD.ξa_toReal : RD.ξa.toReal = RingData.ξa := by
  simp only [RD.ξa, Dy.toReal_mk, RingData.ξa]; norm_num

theorem RD.ξb_toReal : RD.ξb.toReal = RingData.ξb := by
  simp only [RD.ξb, Dy.toReal_mk, RingData.ξb]; norm_num

theorem RD.ξR_toReal : RD.ξR.toReal = RingData.ξR := by
  simp only [RD.ξR, Dy.toReal_mk, RingData.ξR]; norm_num

theorem fact_eq_factorial : ∀ k : ℕ, fact k = Nat.factorial k
  | 0 => rfl
  | k + 1 => by rw [fact, fact_eq_factorial k, Nat.factorial_succ]

/-! ### The grid (proved) -/

@[simp] theorem Grid.build_N (p hpow N : ℕ) : (Grid.build p hpow N).N = N := rfl

theorem Grid.build_steps (p hpow N : ℕ) :
    (Grid.build p hpow N).steps = buildSteps p N (gridPts hpow) (gamma0 p) := rfl

theorem Grid.build_ok (p hpow N : ℕ) :
    (Grid.build p hpow N).ok = chainSteps RD.ξa (buildSteps p N (gridPts hpow) (gamma0 p)) :=
  rfl

/-- What `Grid.ok` checks: the steps are consecutive and strictly increasing, from `a` to
`ξb`. -/
theorem chainSteps_spec : ∀ (a : Dy) (steps : List StepData), chainSteps a steps = true →
    StepChain a.toReal steps ∧ ∀ sd ∈ steps, sd.s0.toReal < sd.s1.toReal
  | a, [], h => by
    simp only [chainSteps, Dy.beqv_iff, RD.ξb_toReal] at h
    exact ⟨(h : a.toReal = ξb), by simp⟩
  | a, sd :: rest, h => by
    simp only [chainSteps, Bool.and_eq_true, Dy.beqv_iff, Dy.blt_iff] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨hc, hl⟩ := chainSteps_spec sd.s1 rest h3
    refine ⟨⟨h1, hc⟩, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h2
    · exact hl x hx

/-- The steps of a chain lie between its start and `ξb`. -/
theorem StepChain.bounds : ∀ {a : ℝ} {steps : List StepData}, StepChain a steps →
    (∀ sd ∈ steps, sd.s0.toReal < sd.s1.toReal) →
    a ≤ ξb ∧ ∀ sd ∈ steps, a ≤ sd.s0.toReal ∧ sd.s1.toReal ≤ ξb
  | a, [], h, _ => ⟨le_of_eq h, by simp⟩
  | a, sd :: rest, h, hlt => by
    obtain ⟨h1, h2⟩ := h
    have hlt' : ∀ x ∈ rest, x.s0.toReal < x.s1.toReal := fun x hx => hlt x (by simp [hx])
    obtain ⟨hb, hr⟩ := StepChain.bounds h2 hlt'
    have hsd := hlt sd (by simp)
    refine ⟨by linarith, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨le_of_eq h1.symm, hb⟩
    · obtain ⟨hx1, hx2⟩ := hr x hx
      exact ⟨by linarith, hx2⟩

/-- Every step built by `buildSteps` is `mkStep` of its own end points and `g`-ball. -/
theorem mem_buildSteps {p N : ℕ} : ∀ (pts : List Dy) (g : Ball) (sd : StepData),
    sd ∈ buildSteps p N pts g → sd = mkStep p N sd.s0 sd.s1 sd.g0
  | [], _, _, h => by simp [buildSteps] at h
  | [_], _, _, h => by simp [buildSteps] at h
  | s0 :: s1 :: rest, g, sd, h => by
    simp only [buildSteps, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact mem_buildSteps (s1 :: rest) _ sd h

/-! ### The enclosure certifies `Re λ > 0` (proved) -/

/-- A successful enclosure on the `λ`-box `lam` certifies `Re λ > 0` on `lam` (the test
`lo(Re lam) > 0` of step (ii)). -/
theorem evansEncl_re_pos {p ℓ : ℕ} {gr : Grid} {lam B : CBox} {Gb : Ball}
    (h : evansEncl p gr ℓ lam Gb = some B) {z : ℂ} (hz : z ∈ lam) : 0 < z.re := by
  unfold evansEncl at h
  split at h
  · simp at h
  · split at h
    · rename_i relo tv hrelo _
      split at h
      · simp at h
      · rename_i hpos
        have hp : relo.isPos = true := by simpa using hpos
        exact lt_of_lt_of_le ((Dy.isPos_iff relo).1 hp) (Ball.lower?_le hrelo hz.1)
    · simp at h

/-- A successful enclosure has passed the grid check `Grid.ok`. -/
theorem evansEncl_grid_ok {p ℓ : ℕ} {gr : Grid} {lam B : CBox} {Gb : Ball}
    (h : evansEncl p gr ℓ lam Gb = some B) : gr.ok = true := by
  unfold evansEncl at h
  split at h
  · simp at h
  · rename_i hok
    simpa using hok

/-! ### The boxes of the certification (proved) -/

/-- `G ∈ [lo, hi]` lies in the `G`-ball `gBall p lo hi` (Python `G_ball`). -/
theorem mem_gBall (p : ℕ) {lo hi : ℚ} {G : ℝ} (h1 : (lo : ℝ) ≤ G) (h2 : G ≤ hi) :
    G ∈ gBall p lo hi :=
  Ball.mem_union_of_between (Ball.mem_ofRat p lo) (Ball.mem_ofRat p hi)
    ((min_le_left _ _).trans h1) (h2.trans (le_max_right _ _))

/-- The contour point with rational parameter `t` lies in its point box (Python `pt_box`). -/
theorem mem_ptBox (p : ℕ) (R : Rect) (t : ℚ) : R.toQRect.bdryPath (t : ℝ) ∈ ptBox p R t := by
  rw [QRect.bdryPath_ratCast]
  exact CBox.mem_ofRat p _ _

/-! ### Derived containment facts of the enclosure code (proved) -/

/-- `e^{ℓL₁} ∈ emL1` (step (ii)). -/
theorem mem_expPoint_endL (p ℓ : ℕ) :
    Real.exp (ℓ * endL) ∈ Ball.expPoint p (Dy.mul (Dy.ofNat ℓ) (Dy.sub RD.ξa RD.ξL)) := by
  have h := Ball.mem_expPoint p (Dy.mul (Dy.ofNat ℓ) (Dy.sub RD.ξa RD.ξL))
  rwa [Dy.toReal_mul, Dy.toReal_ofNat, Dy.toReal_sub, RD.ξa_toReal, RD.ξL_toReal] at h

/-- `e^{ℓL₂} ∈ emL2` (step (iv)). -/
theorem mem_expPoint_endR (p ℓ : ℕ) :
    Real.exp (ℓ * endR) ∈ Ball.expPoint p (Dy.mul (Dy.ofNat ℓ) (Dy.sub RD.ξR RD.ξb)) := by
  have h := Ball.mem_expPoint p (Dy.mul (Dy.ofNat ℓ) (Dy.sub RD.ξR RD.ξb))
  rwa [Dy.toReal_mul, Dy.toReal_ofNat, Dy.toReal_sub, RD.ξR_toReal, RD.ξb_toReal] at h

/-- `e^{-ℓ(ξR-ξL)} ∈ nrm` (step (iv), normalization). -/
theorem mem_expPoint_nrm (p ℓ : ℕ) :
    Real.exp (-(ℓ : ℝ) * (ξR - ξL)) ∈
      Ball.expPoint p (Dy.neg (Dy.mul (Dy.ofNat ℓ) (Dy.sub RD.ξR RD.ξL))) := by
  have h := Ball.mem_expPoint p (Dy.neg (Dy.mul (Dy.ofNat ℓ) (Dy.sub RD.ξR RD.ξL)))
  rwa [Dy.toReal_neg, Dy.toReal_mul, Dy.toReal_ofNat, Dy.toReal_sub, RD.ξR_toReal,
    RD.ξL_toReal, ← neg_mul] at h

/-- `TVEND ≥ 3e^{-50}` (Python `TVEND = (3·exp(-50)).upper()`). -/
theorem tvendUp_sound {p : ℕ} {tv : Dy} (h : tvendUp p = some tv) :
    3 * Real.exp (-50) ≤ tv.toReal := by
  unfold tvendUp at h
  have h3 := Ball.le_upper? h (Ball.mem_mulNat (p := p) (Ball.mem_expPoint p ⟨-50, 0⟩) 3)
  simp only [Dy.toReal_mk] at h3
  norm_num at h3
  linarith

/-- `ε = (TVEND/lo(Re Λ))^up ≥ ε_end = 3e^{-50}/Re λ` (step (ii)). -/
theorem eps_sound {p : ℕ} {tv relo : Dy} (htv : tvendUp p = some tv) (hrelo : relo.isPos = true)
    {z : ℂ} (hz : relo.toReal ≤ z.re)
    (hfin : (UB.div (UB.ofDyUp tv) (UB.ofDyExact relo)).isFin = true) :
    epsEnd z ≤ (UB.div (UB.ofDyUp tv) (UB.ofDyExact relo)).toReal := by
  have hr : 0 < relo.toReal := (Dy.isPos_iff relo).1 hrelo
  have hC0 : 0 < (UB.ofDyExact relo).toReal := by
    rw [UB.toReal_ofDyExact]; exact lt_max_of_lt_left hr
  have hy : (UB.ofDyExact relo).toReal ≤ z.re := by
    rw [UB.toReal_ofDyExact]; exact max_le hz (by linarith)
  have hb := UB.bounds_div' (x := 3 * Real.exp (-50)) (y := z.re) (by positivity)
    (UB.bounds_ofDyUp (tvendUp_sound htv)) (UB.isFin_ofDyExact relo) hC0 hy
  exact UB.Bounds.le_toReal hfin hb

/-- `κ_* = (max(q_*, ℓ²))^{1/2, up}`: `q_* ≤ κ_*²` and `ℓ ≤ κ_*` (step (iii), deviation A3). -/
theorem kappa_sound {qsup : UB} (hq : qsup.isFin = true) (ℓ : ℕ)
    (hk : (UB.sqrtUp (UB.max qsup (UB.ofNat (ℓ * ℓ)))).isFin = true) :
    qsup.toReal ≤ (UB.sqrtUp (UB.max qsup (UB.ofNat (ℓ * ℓ)))).toReal ^ 2 ∧
      (ℓ : ℝ) ≤ (UB.sqrtUp (UB.max qsup (UB.ofNat (ℓ * ℓ)))).toReal := by
  have hκ0 := UB.toReal_nonneg (UB.sqrtUp (UB.max qsup (UB.ofNat (ℓ * ℓ))))
  have h1 := UB.Bounds.le_toReal hk (UB.bounds_sqrtUp (UB.toReal_nonneg qsup)
    (UB.bounds_max_left (V := UB.ofNat (ℓ * ℓ)) (UB.bounds_of_isFin hq le_rfl)))
  have h2 := UB.Bounds.le_toReal hk (UB.bounds_sqrtUp (Nat.cast_nonneg _)
    (UB.bounds_max_right (U := qsup) (UB.bounds_ofNat (ℓ * ℓ))))
  refine ⟨(Real.sqrt_le_left hκ0).1 h1, ?_⟩
  rw [Nat.cast_mul, Real.sqrt_mul_self (Nat.cast_nonneg _)] at h2
  exact h2

/-- The ball `cc k` of `coeffs` contains `2^k/k!`. -/
theorem mem_ofFrac_two_pow (p k : ℕ) :
    (2 : ℝ) ^ k / (Nat.factorial k : ℝ) ∈ Ball.ofFrac p ((2 ^ k : ℕ) : ℤ) (fact k) := by
  have h := Ball.mem_ofFrac p ((2 ^ k : ℕ) : ℤ) (Nat.factorial k)
  rw [fact_eq_factorial]
  simpa using h

/-- `powArr` contains the powers `h^k`, `k ≤ N + 1`. -/
theorem mem_powArr (p : ℕ) {hh : Ball} {h : ℝ} (hmem : h ∈ hh) (N : ℕ) :
    ∀ k ≤ N + 1, h ^ k ∈ (powArr p hh N).getD k Ball.zero := by
  let step : Array Ball → Ball := fun arr => Ball.mul p (arr.getD (arr.size - 1) Ball.zero) hh
  have key : ∀ n k, k ≤ n → h ^ k ∈ (buildArray step #[Ball.one] n).getD k Ball.zero := by
    intro n k
    induction k generalizing n with
    | zero =>
      intro _
      have hs : 0 < (buildArray step #[Ball.one] n).size := by
        rw [size_buildArray]; simp
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs, Option.getD_some,
        buildArray_getElem_of_lt step #[Ball.one] n (by simp)]
      simp
    | succ k ih =>
      intro hk
      have hs : k + 1 < (buildArray step #[Ball.one] n).size := by
        rw [size_buildArray]; simp; omega
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs, Option.getD_some]
      have e : (buildArray step #[Ball.one] n)[k + 1]'hs = step (buildArray step #[Ball.one] k) := by
        have e0 := buildArray_getElem step #[Ball.one] n (i := k) (by omega)
        simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add] at e0
        rw [← e0]
        congr 1
        omega
      rw [e]
      have hsz : (buildArray step #[Ball.one] k).size - 1 = k := by
        rw [size_buildArray]; simp
      simp only [step, hsz]
      rw [pow_succ]
      exact Ball.mem_mul (ih k le_rfl) hmem
  intro k hk
  exact key (N + 1) k hk

end NonUniqueEuler.Verify
