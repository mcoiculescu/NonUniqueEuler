import NonUniqueEuler.I.Sec5.Running
import NonUniqueEuler.I.Sec6.InnerCirc
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.H.Sec8.Coupling.PartOne
import NonUniqueEuler.H.Sec8.Coupling.KickFormula

/-!
# Helper for `lem:coupling`(2) and `eq:kick` (`08_kick.tex:111-138`)

Helper of `P/Sec8/Coupling.lean` (fully proved, modulo the interface files it imports).

* `G_mem`, `T_succ_pos`, `tsh_pos`, `tash_eq`: `G_k ∈ [0,G₁]`, `T_{k+1} > 0`, `t♯_k > 0`,
  `t̄♯_k = (T_pin - τ₀)/μ` (ring-`k` time of `t♯_k` in kick time);
* `hIn_ckPath`: `τ ↦ h^in_k(τ)` is continuous on `[0, t̄♯_k]` into every `C^M(N')`;
* `ellFn_zero`: `ℓ_*(G)(0) = 0`;
* `cin_eq_coef`: `c^in(τ_K) = Kick.coef ζ₀ β_k τ₀ q_{k+1} τ_K` on `[τ₀, T_pin]` (`lem:running`
  with `w₀ = 0`, part (1), and the substitution `v = (τ_K' - τ₀)/μ`);
* `coupling_two_aux`: the statement of `lem:coupling`(2).
-/

noncomputable section

open MeasureTheory Set Metric Filter

namespace NonUniqueEuler.CouplingAux

open RingData Datum OneRing

variable (P : Approx)

/-- `G_k ∈ [0,G₁]` for `1 ≤ k ≤ n` (`lem:inner-circ` and `GSmall`). -/
theorem G_mem (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ P.n) : P.G k ∈ Icc (0 : ℝ) Gbar := by
  have hmem : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨hk, hkn⟩
  exact ⟨((Approx.inner_circ P hP hN).2.2.1 k hmem).1, hG k hmem⟩

/-- `T_{k+1} > 0` (`lem:clock`(1) at level `k+1`: `0 ≤ t♯_{k+1} < T_{k+1}`). -/
theorem T_succ_pos (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall) {k : ℕ}
    (hkn : k < P.n) (hc : P.ClockUpTo (k + 1)) : 0 < P.T (k + 1) := by
  have hmem : k + 1 ∈ Finset.Icc (k + 1) P.n := Finset.mem_Icc.mpr ⟨le_rfl, hkn⟩
  have hord := Approx.clock_order P hP hN hG (Nat.le_add_left 1 k) hc
  exact lt_of_le_of_lt (hord.2.2.2 (k + 1) hmem) (hord.1 (k + 1) hmem)

/-- `t♯_k > 0`. -/
theorem tsh_pos (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall) {k : ℕ}
    (hkn : k < P.n) (hc : P.ClockUpTo (k + 1)) : 0 < P.tsh k := by
  rw [P.tsh_eq_T_add hkn]
  have := T_succ_pos P hP hN hG hkn hc
  have := hP.Tpin_pos
  have := hP.A_pos (k + 1)
  positivity

/-- `t̄♯_k = (T_pin - τ₀)/μ`. -/
theorem tash_eq (hP : P.Valid) {k : ℕ} (hk : 1 ≤ k) (hkn : k < P.n) :
    P.tash k = (P.Tpin - P.tau0 k) / P.μ := by
  have hA := hP.A_pos k
  have hμ : 0 < P.μ := by linarith [hP.datumParams.one_lt_μ]
  have hAs : P.A (k + 1) = P.μ * P.A k := amp_succ _ _ hk
  rw [Approx.tash_def, P.tsh_eq_T_add hkn, Approx.tau0, hAs]
  field_simp
  ring

/-- `τ ↦ h^in_k(τ)` is continuous on `[0, t̄♯_k]` into every `C^M(N')`. -/
theorem hIn_ckPath (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < P.n) (hin : ∀ t ∈ Icc (0 : ℝ) (P.tsh k), P.HInDefined k t) (M : ℕ) :
    CkPathOn M annN' (Icc 0 (P.tash k)) (P.hIn k) := by
  have h := Approx.hIn_continuous P hP hN hk hkn.le (le_refl 0) hin M
  rwa [mul_zero, ← Approx.tash_def] at h

/-- `ℓ_*(G)(0) = 0`. -/
theorem ellFn_zero (χ : ℝ → ℝ) (G : ℝ) : Eig.ellFn χ G (0 : ℂ → ℂ) = 0 := by
  simp [Eig.ellFn, SectorSetting.ellStar, Polar.angularSector]

/-- **`c^in` in kick time** (`08_kick.tex:121-135`): for `τ_K ∈ [τ₀, T_pin]`,
`c^in(τ_K) = Kick.coef ζ₀ β_k τ₀ q_{k+1} τ_K = e^{ζ₀τ_K} β_k ∫_{τ₀}^{τ_K} e^{-ζ₀s} q_{k+1}(s) ds`. -/
theorem cin_eq_coef (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k < P.n) (hc : P.ClockUpTo (k + 1))
    (hin : ∀ t ∈ Icc (0 : ℝ) (P.tsh k), P.HInDefined k t) :
    ∀ τK ∈ Icc (P.tau0 k) P.Tpin,
      P.cin k τK = Kick.coef (P.zeta0 k) (P.betaK k) (P.tau0 k) (P.qKick k) τK := by
  intro τK hτK
  have hχ := hP.admissible
  have hA := hP.A_pos k
  have hA1 := hP.A_pos (k + 1)
  have hμ : 0 < P.μ := by linarith [hP.datumParams.one_lt_μ]
  have hAs : P.A (k + 1) = P.μ * P.A k := amp_succ _ _ hk
  have htash := tash_eq P hP hk hkn
  have htpos : 0 < P.tash k := mul_pos hA (tsh_pos P hP hN hG hkn hc)
  set u : ℝ := (τK - P.tau0 k) / P.μ with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith [hτK.1]) hμ.le
  have hu1 : u ≤ P.tash k := by
    rw [htash, hu]
    exact div_le_div_of_nonneg_right (by linarith [hτK.2]) hμ.le
  have hsym : ∀ v ∈ Icc (0 : ℝ) (P.tash k), IsSymFieldOn annN' (P.hIn k v) :=
    fun v hv => isSymFieldOn_hIn P hP hN hk hkn hv.1 annN'
  have hrun := (running P.χ hχ hN (G_mem P hP hN hG hk hkn.le) htpos (memXFn_zero 0)
    (Eventually.of_forall fun x => by simp) (hIn_ckPath P hP hN hk hkn hin 0) hsym u
    ⟨hu0, hu1⟩).2.2.1
  have hcin : P.cin k τK = Eig.ellFn P.χ (P.G k) (wlin0 P.χ 0 (P.G k) 0 (P.hIn k) u).fn := rfl
  rw [hcin, hrun, runCoef, ellFn_zero, zero_add]
  -- the integrand: `ℓ_*(G_k)(F(v)) = μβ_kq_{k+1}(v/A_k)` on `[0,u]` (part (1))
  have hint : ∫ v in (0 : ℝ)..u, Complex.exp (-(Eig.lam P.χ (P.G k) * v)) *
        Eig.ellFn P.χ (P.G k) (forcing P.χ (P.hIn k) v) =
      ∫ v in (0 : ℝ)..u, Complex.exp (-(Eig.lam P.χ (P.G k) * v)) *
        ((P.μ : ℂ) * P.betaK k * P.q (k + 1) (v / P.A k)) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hu0] at hv
    have ht0 : 0 ≤ v / P.A k := div_nonneg hv.1 hA.le
    have ht1 : v / P.A k ≤ P.tsh k := by
      rw [div_le_iff₀ hA, mul_comm, ← Approx.tash_def]
      exact hv.2.trans hu1
    have h1 := (coupling_one_aux P hP hN hk hkn ht0 (hin _ ⟨ht0, ht1⟩)).2.1
    rw [mul_div_cancel₀ v hA.ne'] at h1
    simp only [h1]
  rw [hint, mul_comm]
  have hQ : ∀ v : ℝ, P.q (k + 1) (v / P.A k) = P.qKick k (P.μ * v + P.tau0 k) := by
    intro v
    simp only [Approx.qKick, Approx.tau0, hAs]
    congr 1
    field_simp
    ring
  have h := coef_eq_of_running (lam := Eig.lam P.χ (P.G k)) (τK := τK) hμ (P.betaK k) hQ
  exact h

/-- **`lem:coupling`(2) and `eq:kick`** (`08_kick.tex:34-53`), proved. -/
theorem coupling_two_aux (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k < P.n) (hc : P.ClockUpTo (k + 1))
    (hin : ∀ t ∈ Icc (0 : ℝ) (P.tsh k), P.HInDefined k t) :
    (∀ s : ℕ, OneRing.PathC s (P.tash k) (OneRing.forcing P.χ (P.hIn k))) ∧
    ContinuousOn (P.qKick k) (Icc (P.tau0 k) P.Tpin) ∧
    (∀ τK ∈ Icc (P.tau0 k) P.Tpin, HasDerivWithinAt (P.cin k)
      (P.zeta0 k * P.cin k τK + P.betaK k * P.qKick k τK) (Icc (P.tau0 k) P.Tpin) τK) ∧
    P.cin k (P.tau0 k) = 0 ∧
    P.cinK k = Complex.exp (P.zeta0 k * P.Tpin) * P.Ain k P.Tpin := by
  have hχ := hP.admissible
  have hA1 := hP.A_pos (k + 1)
  have hT := T_succ_pos P hP hN hG hkn hc
  have hsym : ∀ v ∈ Icc (0 : ℝ) (P.tash k), IsSymFieldOn annN' (P.hIn k v) :=
    fun v hv => isSymFieldOn_hIn P hP hN hk hkn hv.1 annN'
  have hform := cin_eq_coef P hP hN hG hk hkn hc hin
  -- continuity of `q_{k+1}` in kick time
  have hq : ContinuousOn (P.qKick k) (Icc (P.tau0 k) P.Tpin) := by
    have h0 := Approx.q_continuous P hP hN hk hkn
    have hmaps : MapsTo (fun τK : ℝ => P.T (k + 1) + τK / P.A (k + 1))
        (Icc (P.tau0 k) P.Tpin) (Ici 0) := by
      intro τK hτK
      have h1 : -(P.A (k + 1) * P.T (k + 1)) ≤ τK := hτK.1
      have h2 : -P.T (k + 1) ≤ τK / P.A (k + 1) := by
        rw [le_div_iff₀ hA1]; linarith
      show 0 ≤ P.T (k + 1) + τK / P.A (k + 1)
      linarith
    exact h0.comp (continuousOn_const.add (continuousOn_id.div_const _)) hmaps
  have hτ0 : P.tau0 k ≤ P.Tpin := by
    have : P.tau0 k < 0 := by
      simp only [Approx.tau0, neg_lt_zero]; exact mul_pos hA1 hT
    linarith [hP.Tpin_pos]
  refine ⟨fun s => forcing_pathC P.χ hχ hN (hIn_ckPath P hP hN hk hkn hin s) hsym, hq,
    fun τK hτK => ?_, ?_, ?_⟩
  · have h := (coef_hasDerivWithinAt_Icc (ζ := P.zeta0 k) (β := P.betaK k) hq hτK).congr
      (fun x hx => hform x hx) (hform τK hτK)
    rwa [← hform τK hτK] at h
  · rw [hform (P.tau0 k) ⟨le_rfl, hτ0⟩, Kick.coef_self]
  · have h1 : P.cinK k = P.cin k P.Tpin := by
      show Eig.ellFn P.χ (P.G k) (P.wlinIn 0 k (P.tash k)).fn =
        Eig.ellFn P.χ (P.G k) (P.wlinIn 0 k ((P.Tpin - P.tau0 k) / P.μ)).fn
      rw [tash_eq P hP hk hkn]
    rw [h1, Approx.Ain_def, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
      one_mul]

end NonUniqueEuler.CouplingAux
