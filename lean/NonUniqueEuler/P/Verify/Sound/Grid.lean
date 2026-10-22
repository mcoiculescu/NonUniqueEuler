import NonUniqueEuler.Defs.Verify.Encl
import NonUniqueEuler.I.Verify.Sound.Coeffs
import NonUniqueEuler.I.Verify.TaylorRemainder
import NonUniqueEuler.I.Verify.ProfileBasic
import NonUniqueEuler.I.Verify.ProfileOmega

/-!
# Proof: Proposition A.3, step (i): the grid (`γ_j`, the steps, `Grid.build`)

Proof of the interface `I/Verify/Sound/Grid.lean` (same declarations, statements verbatim).

**Manuscript.** Proof of Proposition A.3 (`prop:enclosure`), step (i), second paragraph
(`A_verification.tex:376-393`). **Code.** `Verify/Comp/Grid.lean`.

Helper lemmas (proved here):
* `dgAux_mem`: the loop invariant of `dgAux` (the accumulator contains the partial Taylor sum
  `a + Σ_{i<n} c_{k+i} h^{k+i+1}/(k+i+1)`, the power ball contains `h^{k+n+1}`);
* `buildSteps_sound`: induction over `buildSteps` with the invariant `g(s₀) ∈ γ`.

The certificate data and the grid points are never unfolded: every statement is generic in the
precision, the grid parameters and the Taylor order.
-/

noncomputable section

open Set

namespace NonUniqueEuler.Verify

open AppA RingData

/-- `γ₀ = hull(0, e^{2x_a + 2ξa}/(2/d + 2)) ∋ g(ξa)`. -/
theorem gamma0_sound {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (p : ℕ) : gInt χ ξa ∈ gamma0 p := by
  have hxa : xa ∈ Ball.div p (Ball.sub p (Ball.ofDy RD.ξa) (Ball.ofDy RD.a0)) (Ball.ofDy RD.d) := by
    have h := Ball.mem_div (p := p)
      (Ball.mem_sub (p := p) (Ball.mem_ofDy RD.ξa) (Ball.mem_ofDy RD.a0)) (Ball.mem_ofDy RD.d)
    rwa [RD.ξa_toReal, RD.a0_toReal, RD.d_toReal] at h
  have hnum := Ball.mem_exp p
    (Ball.mem_add (p := p) (Ball.mem_scale2 hxa 1) (Ball.mem_scale2 (Ball.mem_ofDy RD.ξa) 1))
  have hden := Ball.mem_add (p := p)
    (Ball.mem_div (p := p) (Ball.mem_ofNat 2) (Ball.mem_ofDy RD.d)) (Ball.mem_ofNat 2)
  have hg := Ball.mem_div (p := p) hnum hden
  rw [RD.ξa_toReal, RD.d_toReal] at hg
  have e : Real.exp (xa * 2 ^ (1 : ℤ) + ξa * 2 ^ (1 : ℤ)) / (((2 : ℕ) : ℝ) / d + ((2 : ℕ) : ℝ)) =
      Real.exp (2 * xa + 2 * ξa) / (2 / d + 2) := by
    rw [zpow_one]; push_cast; ring_nf
  rw [e] at hg
  exact Ball.mem_hull Ball.mem_zero hg (gInt_nonneg hχ ξa) (gInt_ξa_bound hχ)

/-- The loop invariant of `dgAux`: starting from `k` with `a ∈ acc` and `h^{k+1} ∈ hp`, after
`n` iterations the accumulator contains `a + Σ_{i<n} c_{k+i} h^{k+i+1}/(k+i+1)` and the power
ball contains `h^{k+n+1}`. -/
theorem dgAux_mem {p : ℕ} {q : ℕ → Ball} {hh : Ball} {h : ℝ} (hmem : h ∈ hh) {c : ℕ → ℝ} :
    ∀ (n k : ℕ) (acc hp : Ball) (a : ℝ), a ∈ acc → h ^ (k + 1) ∈ hp →
      (∀ j, k ≤ j → j < k + n → c j ∈ q j) →
      a + ∑ i ∈ Finset.range n, c (k + i) * (h ^ (k + i + 1) / (((k + i : ℕ) : ℝ) + 1)) ∈
          (dgAux p q hh k n acc hp).1 ∧
        h ^ (k + n + 1) ∈ (dgAux p q hh k n acc hp).2
  | 0, k, acc, hp, a, ha, hhp, _ => by
    simp only [dgAux, Finset.range_zero, Finset.sum_empty, add_zero]
    exact ⟨ha, hhp⟩
  | n + 1, k, acc, hp, a, ha, hhp, hc => by
    simp only [dgAux]
    have hck := hc k le_rfl (by omega)
    have h1 : a + c k * (h ^ (k + 1) / ((k : ℝ) + 1)) ∈
        Ball.add p acc (Ball.divNat p (Ball.mul p (q k) hp) (k + 1)) := by
      have := Ball.mem_add (p := p) ha
        (Ball.mem_divNat (p := p) (Ball.mem_mul (p := p) hck hhp) (k + 1))
      convert this using 2
      push_cast; ring
    have h2 : h ^ (k + 1 + 1) ∈ Ball.mul p hp hh := by
      rw [pow_succ]; exact Ball.mem_mul hhp hmem
    obtain ⟨r1, r2⟩ := dgAux_mem (p := p) hmem n (k + 1) _ _ _ h1 h2
      (fun j hj1 hj2 => hc j (by omega) (by omega))
    refine ⟨?_, ?_⟩
    · have e : ∑ i ∈ Finset.range (n + 1),
            c (k + i) * (h ^ (k + i + 1) / (((k + i : ℕ) : ℝ) + 1)) =
          c k * (h ^ (k + 1) / ((k : ℝ) + 1)) + ∑ i ∈ Finset.range n,
            c (k + 1 + i) * (h ^ (k + 1 + i + 1) / (((k + 1 + i : ℕ) : ℝ) + 1)) := by
        have e2 : ∀ i, c (k + (i + 1)) * (h ^ (k + (i + 1) + 1) / (((k + (i + 1) : ℕ) : ℝ) + 1)) =
            c (k + 1 + i) * (h ^ (k + 1 + i + 1) / (((k + 1 + i : ℕ) : ℝ) + 1)) := fun i => by
          rw [show k + (i + 1) = k + 1 + i by omega]
        rw [Finset.sum_range_succ', Finset.sum_congr rfl (fun i _ => e2 i)]
        simp only [add_zero]
        ring
      rw [e, ← add_assoc]
      exact r1
    · rw [show k + (n + 1) + 1 = k + 1 + n + 1 by omega]
      exact r2

/-- The increment of `g` over a step `[s₀, s₁] ⊆ [ξa, ξb]` lies in `dgStep` (the ball in
parentheses of the definition of `γ_{j+1}`, intersected with `[0, ∞)`). -/
theorem dgStep_sound {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {p N : ℕ} {pt iv : CoeffData}
    {s0 s1 : Dy} (hle : s0.toReal ≤ s1.toReal) (ha : ξa ≤ s0.toReal) (hb : s1.toReal ≤ ξb)
    (hpt : CoeffDataSound N pt {s0.toReal})
    (hiv : CoeffDataSound N iv (Icc s0.toReal s1.toReal)) :
    gInt χ s1.toReal - gInt χ s0.toReal ∈ dgStep p pt iv (Dy.sub s1 s0) N := by
  have hh : (Dy.sub s1 s0).toReal = s1.toReal - s0.toReal := Dy.toReal_sub _ _
  have hh0 : 0 ≤ (Dy.sub s1 s0).toReal := by rw [hh]; linarith
  have hq : ∀ x, deriv (gInt χ) x = prof χ x * Real.exp (2 * x) :=
    fun x => (hasDerivAt_gInt hχ x).deriv
  obtain ⟨η, hη, heq⟩ := taylor_increment_real (s := s0.toReal) (contDiff_gInt hχ) hq hh0 N
  have hs1 : s0.toReal + (Dy.sub s1 s0).toReal = s1.toReal := by rw [hh]; ring
  rw [hs1] at heq hη
  have hs0mem : s0.toReal ∈ Icc ξa ξb := ⟨ha, hle.trans hb⟩
  have hηmem : η ∈ Icc ξa ξb := ⟨ha.trans hη.1, hη.2.trans hb⟩
  have hcpt : ∀ k, k < N → taylorCoeff (fun t => prof χ t * Real.exp (2 * t)) k s0.toReal ∈
      pt.q.getD k Ball.zero := by
    intro k hk
    rw [taylorCoeff_prof_exp_eq hχ hs0mem]
    exact hpt.q _ (mem_singleton _) k (by omega)
  have hciv : taylorCoeff (fun t => prof χ t * Real.exp (2 * t)) N η ∈ iv.q.getD N Ball.zero := by
    rw [taylorCoeff_prof_exp_eq hχ hηmem]
    exact hiv.q η hη N (by omega)
  have hmemh : (Dy.sub s1 s0).toReal ∈ Ball.ofDy (Dy.sub s1 s0) := Ball.mem_ofDy _
  obtain ⟨r1, r2⟩ := dgAux_mem (p := p) (q := fun k => pt.q.getD k Ball.zero)
    (c := fun k => taylorCoeff (fun t => prof χ t * Real.exp (2 * t)) k s0.toReal) hmemh
    N 0 Ball.zero (Ball.ofDy (Dy.sub s1 s0)) 0 Ball.mem_zero (by simpa using hmemh)
    (fun j _ hj => hcpt j (by omega))
  have hfin := Ball.mem_add (p := p) r1
    (Ball.mem_divNat (p := p) (Ball.mem_mul (p := p) hciv r2) (N + 1))
  unfold dgStep
  refine Ball.mem_nonnegPart ?_ (sub_nonneg.2 (monotone_gInt hχ hle))
  rw [heq]
  convert hfin using 1
  simp only [zero_add, Nat.cast_add, Nat.cast_one]
  ring

/-- **One step of step (i)**: the data `mkStep p N s₀ s₁ γ` of a step `[s₀, s₁] ⊆ [ξa, ξb]` with
`γ ∋ g(s₀)` are sound. -/
theorem mkStep_sound {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {p N : ℕ} {s0 s1 : Dy}
    {g0 : Ball} (hlt : s0.toReal < s1.toReal) (ha : ξa ≤ s0.toReal) (hb : s1.toReal ≤ ξb)
    (hg : gInt χ s0.toReal ∈ g0) :
    StepSound χ N (mkStep p N s0 s1 g0) := by
  have hpt : CoeffDataSound N (coeffs p s0 s0 N) {s0.toReal} := by
    have := coeffs_sound p N s0 s0
    rwa [Icc_self] at this
  have hiv := coeffs_sound p N s0 s1
  have hdg := dgStep_sound hχ (p := p) hlt.le ha hb hpt hiv
  have hg1 : gInt χ s1.toReal ∈
      Ball.add p g0 (dgStep p (coeffs p s0 s0 N) (coeffs p s0 s1 N) (Dy.sub s1 s0) N) := by
    have := Ball.mem_add (p := p) hg hdg
    rwa [show gInt χ s0.toReal + (gInt χ s1.toReal - gInt χ s0.toReal) = gInt χ s1.toReal by
      ring] at this
  have hS1 : Icc s0.toReal s1.toReal ⊆ Icc ξa ξb := Icc_subset_Icc ha hb
  have hS0 : ({s0.toReal} : Set ℝ) ⊆ Icc ξa ξb := by
    rw [singleton_subset_iff]; exact ⟨ha, hlt.le.trans hb⟩
  have hmemh : (Dy.sub s1 s0).toReal ∈ Ball.ofDy (Dy.sub s1 s0) := Ball.mem_ofDy _
  have hpow := mem_powArr p hmemh N
  refine
    { lt := hlt
      left := ha
      right := hb
      h_eq := Dy.toReal_sub _ _
      pt := hpt
      iv := hiv
      g0 := hg
      g1 := hg1
      Omg := omegaCoeffs_sound hχ hS0 hpt (fun ξ hξ => by rw [mem_singleton_iff.1 hξ]; exact hg)
      OmgI := omegaCoeffs_sound hχ hS1 hiv (fun ξ hξ =>
        Ball.mem_hull hg hg1 (monotone_gInt hχ hξ.1) (monotone_gInt hχ hξ.2))
      hp := hpow
      khp := ?_ }
  intro k hk2 hkN
  have hk : k < N + 1 := by omega
  show _ ∈ (Array.ofFn (n := N + 1) fun k : Fin (N + 1) => if k.val < 2 then Ball.zero else
    Ball.mulNat p ((powArr p (Ball.ofDy (Dy.sub s1 s0)) N).getD (k.val - 1) Ball.zero)
      k.val).getD k Ball.zero
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hk, dite_true, Option.getD_some, show ¬ k < 2 by omega, ite_false]
  have := Ball.mem_mulNat (p := p) (hpow (k - 1) (by omega)) k
  rwa [mul_comm] at this

/-- Induction over `buildSteps`, with the invariant `g(s₀) ∈ γ`: if the steps built from `pts`
and `g` form a chain from `a` with `g(a) ∈ g`, and every step lies in `[ξa, ξb]` with
`s₀ < s₁`, then every step is sound. -/
theorem buildSteps_sound {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {p N : ℕ} :
    ∀ (pts : List Dy) (g : Ball) (a : ℝ), StepChain a (buildSteps p N pts g) → gInt χ a ∈ g →
      (∀ sd ∈ buildSteps p N pts g,
        sd.s0.toReal < sd.s1.toReal ∧ ξa ≤ sd.s0.toReal ∧ sd.s1.toReal ≤ ξb) →
      ∀ sd ∈ buildSteps p N pts g, StepSound χ N sd
  | [], _, _, _, _, _ => by simp [buildSteps]
  | [_], _, _, _, _, _ => by simp [buildSteps]
  | s0 :: s1 :: rest, g, a, hc, hg, hb => by
    simp only [buildSteps] at hc hb ⊢
    obtain ⟨hc1, hc2⟩ := hc
    have hb0 := hb _ List.mem_cons_self
    have hg' : gInt χ s0.toReal ∈ g := by
      have e : s0.toReal = a := hc1
      rw [e]; exact hg
    have hst : StepSound χ N (mkStep p N s0 s1 g) := mkStep_sound hχ hb0.1 hb0.2.1 hb0.2.2 hg'
    intro sd hsd
    rcases List.mem_cons.1 hsd with rfl | hsd
    · exact hst
    · exact buildSteps_sound hχ (s1 :: rest) _ _ hc2 hst.g1
        (fun x hx => hb x (List.mem_cons_of_mem _ hx)) sd hsd

/-- **Step (i) of Proposition A.3**: if the grid passes its check `Grid.ok`, its data are
sound for every admissible cutoff. -/
theorem grid_sound {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {p hpow N : ℕ}
    (hok : (Grid.build p hpow N).ok = true) : GridSound χ (Grid.build p hpow N) := by
  rw [Grid.build_ok] at hok
  obtain ⟨hchain, hlt⟩ := chainSteps_spec _ _ hok
  rw [RD.ξa_toReal] at hchain
  obtain ⟨_, hbd⟩ := StepChain.bounds hchain hlt
  refine ⟨?_, ?_⟩
  · rw [Grid.build_steps]; exact hchain
  · rw [Grid.build_steps, Grid.build_N]
    exact buildSteps_sound hχ _ _ _ hchain (gamma0_sound hχ p)
      (fun sd hsd => ⟨hlt sd hsd, hbd sd hsd⟩)

end NonUniqueEuler.Verify
