import NonUniqueEuler.Defs.Verify.Encl
import NonUniqueEuler.I.Verify.TaylorCoef
import NonUniqueEuler.I.Verify.TaylorRecurrence
import NonUniqueEuler.I.Verify.ProfileBasic
import NonUniqueEuler.I.Verify.ProfileOmega

/-!
# Proof: Proposition A.3, step (i): the coefficient data `coeffs` and `omegaCoeffs`

Proof of `NonUniqueEuler/I/Verify/Sound/Coeffs.lean`. Manuscript: proof of Proposition A.3
(`prop:enclosure`), step (i) (`A_verification.tex:360-393`). Code: `Verify/Comp/Grid.lean`
(`hPairIv`, `hRec`, `coeffs`, `omegaCoeffs`).

We follow the manuscript (and the interface's proof sketch):
* `hPairIv_sound`: `H` is increasing, so `H` on `[a, b]` lies between `H a` and `H b`.
* `hRec_sound`: induction on the number of iterations; the new entry is the logistic
  recurrence `taylorCoeff_riccati`, the conjugate entry is its negative
  (`taylorCoeff_succ_eq_neg_of_add_eq_const`).
* `coeffs_sound`: one field lemma per array of `coeffs` (`w`, `fs`, `e2`, `em2`, `q`), stated
  for arbitrary input arrays; the code term `coeffs p Slo Shi N` matches them by definitional
  unfolding.
* `omegaCoeffs_sound`: `g_0 ∋ g(ξ)`, `g_k = q_{k-1}/k` (`g' = ϖ e^{2ξ}` and
  `taylorCoeff_prof_exp_eq` on `[ξa, ξb]`), and the Leibniz rule for `g · e^{-2ξ}`.

Helper lemmas are in the namespace `NonUniqueEuler.Verify.CoeffsProof`.
-/

noncomputable section

open Set
open scoped ContDiff

namespace NonUniqueEuler.Verify

open AppA RingData

namespace CoeffsProof

/-! ### Array access -/

theorem getD_push_lt {α : Type} (a : Array α) (x d : α) {i : ℕ} (hi : i < a.size) :
    (a.push x).getD i d = a.getD i d := by
  simp [Array.getElem?_push, hi, Nat.ne_of_lt hi]

theorem getD_push_size {α : Type} (a : Array α) (x d : α) :
    (a.push x).getD a.size d = x := by
  simp

theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (d : α) {k : ℕ} (hk : k < n) :
    (Array.ofFn f).getD k d = f ⟨k, hk⟩ := by
  simp [hk]

end CoeffsProof

open CoeffsProof

/-- `_H_pair_iv(xlo, xhi)`: for `x` between points of the two balls, the pair contains
`H(x)` and `H(-x) = 1 - H(x)` (`H` is increasing). -/
theorem hPairIv_sound {p : ℕ} {xlo xhi : Ball} {a b x : ℝ} (ha : a ∈ xlo) (hb : b ∈ xhi)
    (hax : a ≤ x) (hxb : x ≤ b) :
    RingData.H x ∈ (hPairIv p xlo xhi).1 ∧ RingData.H (-x) ∈ (hPairIv p xlo xhi).2 := by
  refine ⟨?_, ?_⟩
  · exact Ball.mem_hull (Ball.mem_H p ha) (Ball.mem_H p hb) (strictMono_H.monotone hax)
      (strictMono_H.monotone hxb)
  · exact Ball.mem_hull (Ball.mem_H p (Ball.mem_neg hb)) (Ball.mem_H p (Ball.mem_neg ha))
      (strictMono_H.monotone (neg_le_neg hxb)) (strictMono_H.monotone (neg_le_neg hax))

/-- The loop of `_coeffs` (`hRec`): if `A' = (±c)·A Ā` and `A + Ā = 1`, and the arrays enclose
the first `size` Taylor coefficients of `A`, `Ā` on `S`, then after `n` iterations they
enclose the first `size + n`. -/
theorem hRec_sound {p : ℕ} {cB : Ball} {c : ℝ} (hc : c ∈ cB) (pos : Bool) {A Ā : ℝ → ℝ}
    (hA : ContDiff ℝ ∞ A) (hĀ : ContDiff ℝ ∞ Ā)
    (hder : ∀ x, deriv A x = (if pos then c else -c) * (A x * Ā x))
    (hsum : ∀ x, A x + Ā x = 1) {S : Set ℝ} :
    ∀ (n : ℕ) (arrA arrĀ : Array Ball), arrA.size = arrĀ.size → 0 < arrA.size →
      CoeffEncl A S arrA.size (fun k => arrA.getD k Ball.zero) →
      CoeffEncl Ā S arrA.size (fun k => arrĀ.getD k Ball.zero) →
      CoeffEncl A S (arrA.size + n) (fun k => (hRec p cB pos n arrA arrĀ).1.getD k Ball.zero) ∧
        CoeffEncl Ā S (arrA.size + n)
          (fun k => (hRec p cB pos n arrA arrĀ).2.getD k Ball.zero) := by
  intro n
  induction n with
  | zero =>
    intro arrA arrĀ _ _ h1 h2
    exact ⟨h1, h2⟩
  | succ n ih =>
    intro arrA arrĀ hsz hpos h1 h2
    -- the new entry
    set k := arrA.size - 1 with hkdef
    have hk : arrA.size = k + 1 := by omega
    set P := Ball.cauchy p (fun j => arrA.getD j Ball.zero) (fun j => arrĀ.getD j Ball.zero) k
      with hP
    set a := (if pos then Ball.divNat p (Ball.mul p cB P) (k + 1)
      else Ball.divNat p (Ball.neg (Ball.mul p cB P)) (k + 1)) with ha
    have hnew : ∀ ξ ∈ S, taylorCoeff A (k + 1) ξ ∈ a := by
      intro ξ hξ
      have hsumP : ∑ r ∈ Finset.range (k + 1), taylorCoeff A r ξ * taylorCoeff Ā (k - r) ξ ∈ P :=
        Ball.mem_cauchy (fun i hi => h1 ξ hξ i (by omega)) (fun i hi => h2 ξ hξ i (by omega))
      rw [taylorCoeff_riccati hA hĀ hder k ξ]
      have hcP := Ball.mem_mul (p := p) hc hsumP
      cases pos
      · have h := Ball.mem_divNat (p := p) (Ball.mem_neg hcP) (k + 1)
        simp only [Bool.false_eq_true, ↓reduceIte, ha]
        convert h using 1
        push_cast
        ring
      · have h := Ball.mem_divNat (p := p) hcP (k + 1)
        simp only [↓reduceIte, ha]
        convert h using 1
        push_cast
        ring
    have hstep : hRec p cB pos (n + 1) arrA arrĀ =
        hRec p cB pos n (arrA.push a) (arrĀ.push (Ball.neg a)) := by
      rw [hRec]
    have hIH := ih (arrA.push a) (arrĀ.push (Ball.neg a)) (by simp [hsz]) (by simp)
      (by
        intro ξ hξ i hi
        beta_reduce
        rw [Array.size_push] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · rw [getD_push_lt _ _ _ hi]; exact h1 ξ hξ i hi
        · subst hi
          rw [getD_push_size, hk]
          exact hnew ξ hξ)
      (by
        intro ξ hξ i hi
        beta_reduce
        rw [Array.size_push] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · rw [getD_push_lt _ _ _ (hsz ▸ hi)]; exact h2 ξ hξ i hi
        · subst hi
          rw [hsz, getD_push_size, ← hsz, hk,
            taylorCoeff_succ_eq_neg_of_add_eq_const hA hĀ hsum k ξ]
          exact Ball.mem_neg (hnew ξ hξ))
    rw [Array.size_push, show arrA.size + 1 + n = arrA.size + (n + 1) by omega] at hIH
    rw [hstep]
    exact hIH

namespace CoeffsProof

/-! ### The arrays of `coeffs`, one lemma per array (stated for arbitrary inputs) -/

theorem d_pos : 0 < RingData.d := by norm_num [RingData.d]

/-- The `A` array of `coeffs`: the logistic loop started at `A_0`, `Ā_0`, with `c ∋ 2/d`. -/
theorem hRecA_sound {p N : ℕ} {T : Set ℝ} {cB : Ball} {hA : Ball × Ball} (hc : 2 / d ∈ cB)
    (hA0 : ∀ ξ ∈ T, profA ξ ∈ hA.1 ∧ profAbar ξ ∈ hA.2) :
    CoeffEncl profA T (N + 2) fun k =>
      (hRec p cB true (N + 1) #[hA.1] #[hA.2]).1.getD k Ball.zero := by
  have hs : (#[hA.1] : Array Ball).size = 1 := rfl
  have h := (hRec_sound (p := p) hc true contDiff_profA contDiff_profAbar
    (fun x => by simp only [↓reduceIte]; exact (hasDerivAt_profA x).deriv) profA_add_profAbar
    (N + 1) #[hA.1] #[hA.2] rfl (by rw [hs]; omega)
    (by
      intro ξ hξ k hk
      rw [hs] at hk
      obtain rfl : k = 0 := by omega
      rw [taylorCoeff_zero]
      exact (hA0 ξ hξ).1)
    (by
      intro ξ hξ k hk
      rw [hs] at hk
      obtain rfl : k = 0 := by omega
      rw [taylorCoeff_zero]
      exact (hA0 ξ hξ).2)).1
  rw [hs, show 1 + (N + 1) = N + 2 by omega] at h
  exact h

/-- The `B` array of `coeffs`: the logistic loop started at `B_0`, `B̄_0`, with `-c`. -/
theorem hRecB_sound {p N : ℕ} {T : Set ℝ} {cB : Ball} {hB : Ball × Ball} (hc : 2 / d ∈ cB)
    (hB0 : ∀ ξ ∈ T, profB ξ ∈ hB.1 ∧ profBbar ξ ∈ hB.2) :
    CoeffEncl profB T (N + 2) fun k =>
      (hRec p cB false (N + 1) #[hB.1] #[hB.2]).1.getD k Ball.zero := by
  have hs : (#[hB.1] : Array Ball).size = 1 := rfl
  have h := (hRec_sound (p := p) hc false contDiff_profB contDiff_profBbar
    (fun x => by
      simp only [Bool.false_eq_true, ↓reduceIte]; exact (hasDerivAt_profB x).deriv)
    profB_add_profBbar
    (N + 1) #[hB.1] #[hB.2] rfl (by rw [hs]; omega)
    (by
      intro ξ hξ k hk
      rw [hs] at hk
      obtain rfl : k = 0 := by omega
      rw [taylorCoeff_zero]
      exact (hB0 ξ hξ).1)
    (by
      intro ξ hξ k hk
      rw [hs] at hk
      obtain rfl : k = 0 := by omega
      rw [taylorCoeff_zero]
      exact (hB0 ξ hξ).2)).1
  rw [hs, show 1 + (N + 1) = N + 2 by omega] at h
  exact h

/-- `w = A ⋆ B` (Cauchy product): the coefficients of `AB`. -/
theorem w_sound {p N : ℕ} {T : Set ℝ} {A B : Array Ball}
    (hA : CoeffEncl profA T (N + 2) fun k => A.getD k Ball.zero)
    (hB : CoeffEncl profB T (N + 2) fun k => B.getD k Ball.zero) :
    CoeffEncl profW T (N + 2) fun k => (Array.ofFn (n := N + 2) fun k =>
      Ball.cauchy p (fun j => A.getD j Ball.zero) (fun j => B.getD j Ball.zero) k.val).getD k
        Ball.zero := by
  intro ξ hξ k hk
  beta_reduce
  rw [getD_ofFn _ _ hk]
  have e : profW = fun y => profA y * profB y := rfl
  rw [e, taylorCoeff_mul contDiff_profA contDiff_profB]
  exact Ball.mem_cauchy (x := fun i => taylorCoeff profA i ξ)
    (y := fun i => taylorCoeff profB i ξ)
    (fun i hi => hA ξ hξ i (by omega)) (fun i hi => hB ξ hξ i (by omega))

/-- `fs_k = (k+1) w_{k+1}`: the coefficients of `(AB)'`. -/
theorem fs_sound {p N : ℕ} {T : Set ℝ} {w : Array Ball}
    (hw : CoeffEncl profW T (N + 2) fun k => w.getD k Ball.zero) :
    CoeffEncl (deriv profW) T (N + 1) fun k => (Array.ofFn (n := N + 1) fun k =>
      Ball.mulNat p (w.getD (k.val + 1) Ball.zero) (k.val + 1)).getD k Ball.zero := by
  intro ξ hξ k hk
  beta_reduce
  rw [getD_ofFn _ _ hk, taylorCoeff_deriv, smul_eq_mul]
  have h := Ball.mem_mulNat (p := p) (hw ξ hξ (k + 1) (by omega)) (k + 1)
  convert h using 1
  push_cast
  ring

theorem contDiff_exp_mul (c : ℝ) : ContDiff ℝ ∞ (fun x => Real.exp (c * x)) :=
  Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)

/-- `e2_k = e^{2S} · 2^k/k!`: the coefficients of `e^{2ξ}`. -/
theorem e2_sound {p N : ℕ} {T : Set ℝ} {Sb : Ball} (hS : ∀ ξ ∈ T, ξ ∈ Sb) :
    CoeffEncl (fun x => Real.exp (2 * x)) T (N + 1) fun k => (Array.ofFn (n := N + 1) fun k =>
      Ball.mul p (Ball.exp p (Ball.scale2 Sb 1))
        (Ball.ofFrac p ((2 ^ k.val : Nat) : Int) (fact k.val))).getD k Ball.zero := by
  intro ξ hξ k hk
  beta_reduce
  rw [getD_ofFn _ _ hk, taylorCoeff_exp_mul]
  have h1 : Real.exp (2 * ξ) ∈ Ball.exp p (Ball.scale2 Sb 1) := by
    have := Ball.mem_exp p (Ball.mem_scale2 (hS ξ hξ) 1)
    rwa [zpow_one, mul_comm] at this
  have h := Ball.mem_mul (p := p) h1 (mem_ofFrac_two_pow p k)
  convert h using 1
  ring

/-- `em2_k = e^{-2S} · (-2)^k/k!`: the coefficients of `e^{-2ξ}`. -/
theorem em2_sound {p N : ℕ} {T : Set ℝ} {Sb : Ball} (hS : ∀ ξ ∈ T, ξ ∈ Sb) :
    CoeffEncl (fun x => Real.exp (-2 * x)) T (N + 1) fun k => (Array.ofFn (n := N + 1) fun k =>
      Ball.mul p (Ball.exp p (Ball.neg (Ball.scale2 Sb 1)))
        (if k.val % 2 = 0 then Ball.ofFrac p ((2 ^ k.val : Nat) : Int) (fact k.val)
          else Ball.neg (Ball.ofFrac p ((2 ^ k.val : Nat) : Int) (fact k.val)))).getD k
        Ball.zero := by
  intro ξ hξ k hk
  beta_reduce
  rw [getD_ofFn _ _ hk, taylorCoeff_exp_mul]
  have h1 : Real.exp (-2 * ξ) ∈ Ball.exp p (Ball.neg (Ball.scale2 Sb 1)) := by
    have := Ball.mem_exp p (Ball.mem_neg (Ball.mem_scale2 (hS ξ hξ) 1))
    rwa [zpow_one, show -(ξ * 2) = -2 * ξ by ring] at this
  dsimp only
  split_ifs with hev
  · have h := Ball.mem_mul (p := p) h1 (mem_ofFrac_two_pow p k)
    convert h using 1
    rw [Even.neg_pow (Nat.even_iff.2 hev)]
    ring
  · have h := Ball.mem_mul (p := p) h1 (Ball.mem_neg (mem_ofFrac_two_pow p k))
    convert h using 1
    rw [Odd.neg_pow (Nat.odd_iff.2 (by omega))]
    ring

/-- `q = w ⋆ e2`: the coefficients of `AB e^{2ξ}`. -/
theorem q_sound {p N : ℕ} {T : Set ℝ} {w e2 : Array Ball}
    (hw : CoeffEncl profW T (N + 2) fun k => w.getD k Ball.zero)
    (he2 : CoeffEncl (fun x => Real.exp (2 * x)) T (N + 1) fun k => e2.getD k Ball.zero) :
    CoeffEncl profQ T (N + 1) fun k => (Array.ofFn (n := N + 1) fun k =>
      Ball.cauchy p (fun j => w.getD j Ball.zero) (fun j => e2.getD j Ball.zero) k.val).getD k
        Ball.zero := by
  intro ξ hξ k hk
  beta_reduce
  rw [getD_ofFn _ _ hk]
  have e : profQ = fun y => profW y * Real.exp (2 * y) := rfl
  rw [e, taylorCoeff_mul contDiff_profW (contDiff_exp_mul 2)]
  exact Ball.mem_cauchy (x := fun i => taylorCoeff profW i ξ)
    (y := fun i => taylorCoeff (fun x => Real.exp (2 * x)) i ξ)
    (fun i hi => hw ξ hξ i (by omega)) (fun i hi => he2 ξ hξ i (by omega))

end CoeffsProof

/-- **Step (i), coefficient data** (`_coeffs`): `coeffs p Slo Shi N` encloses the Taylor
coefficients of `AB`, `(AB)'`, `e^{±2ξ}` and `AB e^{2ξ}` at every point of `[Slo, Shi]`. -/
theorem coeffs_sound (p N : ℕ) (Slo Shi : Dy) :
    CoeffDataSound N (coeffs p Slo Shi N) (Icc Slo.toReal Shi.toReal) := by
  have hd := d_pos
  -- `ξ ∈ S`
  have hS : ∀ ξ ∈ Icc Slo.toReal Shi.toReal,
      ξ ∈ Ball.hull p (Ball.ofDy Slo) (Ball.ofDy Shi) := fun ξ hξ =>
    Ball.mem_hull (Ball.mem_ofDy Slo) (Ball.mem_ofDy Shi) hξ.1 hξ.2
  -- `c = 2·x1 ∋ 2/d`
  have hc : 2 / d ∈ Ball.scale2 (Ball.inv p (Ball.ofDy RD.d)) 1 := by
    have h := Ball.mem_scale2 (Ball.mem_inv (p := p) (Ball.mem_ofDy RD.d)) 1
    rw [RD.d_toReal, zpow_one] at h
    convert h using 1
    ring
  -- `A_0, Ā_0`
  have hA0 : ∀ ξ ∈ Icc Slo.toReal Shi.toReal,
      profA ξ ∈ (hPairIv p
        (Ball.div p (Ball.sub p (Ball.ofDy Slo) (Ball.ofDy RD.a0)) (Ball.ofDy RD.d))
        (Ball.div p (Ball.sub p (Ball.ofDy Shi) (Ball.ofDy RD.a0)) (Ball.ofDy RD.d))).1 ∧
      profAbar ξ ∈ (hPairIv p
        (Ball.div p (Ball.sub p (Ball.ofDy Slo) (Ball.ofDy RD.a0)) (Ball.ofDy RD.d))
        (Ball.div p (Ball.sub p (Ball.ofDy Shi) (Ball.ofDy RD.a0)) (Ball.ofDy RD.d))).2 := by
    intro ξ hξ
    have hlo := Ball.mem_div (p := p)
      (Ball.mem_sub (p := p) (Ball.mem_ofDy Slo) (Ball.mem_ofDy RD.a0)) (Ball.mem_ofDy RD.d)
    have hhi := Ball.mem_div (p := p)
      (Ball.mem_sub (p := p) (Ball.mem_ofDy Shi) (Ball.mem_ofDy RD.a0)) (Ball.mem_ofDy RD.d)
    rw [RD.a0_toReal, RD.d_toReal] at hlo hhi
    have h := hPairIv_sound (p := p) (x := (ξ - a₀) / d) hlo hhi
      (div_le_div_of_nonneg_right (by linarith [hξ.1]) hd.le)
      (div_le_div_of_nonneg_right (by linarith [hξ.2]) hd.le)
    refine ⟨h.1, ?_⟩
    have e : profAbar ξ = RingData.H (-((ξ - a₀) / d)) := by
      rw [profAbar]; congr 1; ring
    rw [e]; exact h.2
  -- `B_0, B̄_0`
  have hB0 : ∀ ξ ∈ Icc Slo.toReal Shi.toReal,
      profB ξ ∈ (hPairIv p (Ball.neg (Ball.div p (Ball.ofDy Shi) (Ball.ofDy RD.d)))
        (Ball.neg (Ball.div p (Ball.ofDy Slo) (Ball.ofDy RD.d)))).1 ∧
      profBbar ξ ∈ (hPairIv p (Ball.neg (Ball.div p (Ball.ofDy Shi) (Ball.ofDy RD.d)))
        (Ball.neg (Ball.div p (Ball.ofDy Slo) (Ball.ofDy RD.d)))).2 := by
    intro ξ hξ
    have hlo := Ball.mem_neg (Ball.mem_div (p := p) (Ball.mem_ofDy Shi) (Ball.mem_ofDy RD.d))
    have hhi := Ball.mem_neg (Ball.mem_div (p := p) (Ball.mem_ofDy Slo) (Ball.mem_ofDy RD.d))
    rw [RD.d_toReal] at hlo hhi
    have h := hPairIv_sound (p := p) (x := -ξ / d) hlo hhi
      (by rw [neg_div]; exact neg_le_neg (div_le_div_of_nonneg_right hξ.2 hd.le))
      (by rw [neg_div]; exact neg_le_neg (div_le_div_of_nonneg_right hξ.1 hd.le))
    refine ⟨h.1, ?_⟩
    have e : profBbar ξ = RingData.H (-(-ξ / d)) := by
      rw [profBbar]; congr 1; ring
    rw [e]; exact h.2
  have hAr := hRecA_sound (p := p) (N := N) hc hA0
  have hBr := hRecB_sound (p := p) (N := N) hc hB0
  have hw := w_sound (p := p) hAr hBr
  have he2 := e2_sound (p := p) (N := N) hS
  exact ⟨hw, fs_sound hw, he2, em2_sound hS, q_sound hw he2⟩

/-- **Step (i), the coefficients `o_k` of `g e^{-2ξ}`** (`_omega`): from valid coefficient data
on `S ⊆ [ξa, ξb]` and a ball `g0` containing `g` on `S`. -/
theorem omegaCoeffs_sound {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {p N : ℕ} {dat : CoeffData}
    {S : Set ℝ} (hS : S ⊆ Icc ξa ξb) (hdat : CoeffDataSound N dat S) {g0 : Ball}
    (hg : ∀ ξ ∈ S, gInt χ ξ ∈ g0) :
    CoeffEncl (omegaFn χ) S N fun k => (omegaCoeffs p dat g0 N).getD k Ball.zero := by
  intro ξ hξ k hk
  -- the coefficients `g_i` of `g`
  have hgk : ∀ i, i < N + 1 → taylorCoeff (gInt χ) i ξ ∈
      (Array.ofFn (n := N + 1) fun k : Fin (N + 1) =>
        if k.val = 0 then g0 else Ball.divNat p (dat.q.getD (k.val - 1) Ball.zero) k.val).getD i
        Ball.zero := by
    intro i hi
    rw [getD_ofFn _ _ hi]
    dsimp only
    rcases i with _ | j
    · simp only [↓reduceIte, taylorCoeff_zero]
      exact hg ξ hξ
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      have hd := taylorCoeff_deriv (gInt χ) j ξ
      have hder : deriv (gInt χ) = fun t => prof χ t * Real.exp (2 * t) :=
        funext fun t => (hasDerivAt_gInt hχ t).deriv
      rw [hder, taylorCoeff_prof_exp_eq hχ (hS hξ), smul_eq_mul] at hd
      have hq := Ball.mem_divNat (p := p) (hdat.q ξ hξ j (by omega)) (j + 1)
      convert hq using 1
      rw [hd]
      push_cast
      field_simp
  beta_reduce
  unfold omegaCoeffs
  dsimp only
  rw [getD_ofFn _ _ hk]
  have e : omegaFn χ = fun x => gInt χ x * Real.exp (-2 * x) := rfl
  rw [e, taylorCoeff_mul (contDiff_gInt hχ) (CoeffsProof.contDiff_exp_mul (-2))]
  exact Ball.mem_cauchy (x := fun i => taylorCoeff (gInt χ) i ξ)
    (y := fun i => taylorCoeff (fun x => Real.exp (-2 * x)) i ξ)
    (fun i hi => hgk i (by omega)) (fun i hi => hdat.em2 ξ hξ i (by omega))

end NonUniqueEuler.Verify
