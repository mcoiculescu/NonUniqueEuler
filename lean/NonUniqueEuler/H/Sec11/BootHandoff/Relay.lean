import NonUniqueEuler.H.Sec11.BootHandoff.Basic
import NonUniqueEuler.I.Sec9.QuietTime
import NonUniqueEuler.I.Sec10.ThetaQuiet

/-!
# Helper for `P/Sec11/BootHandoff.lean`: `eq:boot-theta` and the hypotheses of `prop:relay`

Step 3 of the proof of `prop:bootstrap` (`11_bootstrap.tex:341-374`):
* `etaOut_le_theta`: `η^out_k ≤ θ_k maj_k` on `[0, t̄♯_k]` (Step 2, `lem:O` for `j = k`);
* `theta`: `eq:boot-theta`, `θ_k t̄♯_k ≤ θ_k τ̄♯_k ≤ min{1/2, 1/(4C_lsK₁)}` (`lem:quiet-time` at the
  time `t♯_k`, `lem:theta-quiet`);
* `relayHyp`: the hypotheses (H1)–(H4) of `prop:relay` with `j = k`, `τ = t̄♯_k`, `C₀ = S.C0`,
  `K₁ = S.K1` (`11_bootstrap.tex:351-369`);
* `xiNext_le`: `Ξ_{k+1} ≤ δ₀/(σ_b(μ-1))` from `1 - γ_k ≥ γ'_μ` and (κ7) at `κ♯_{k+1}`
  (`11_bootstrap.tex:371-374`). All proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace BootHandoffH

open RingData Datum

variable {S : Standing}

/-- Step 2 at `t♯_k` for the ring `k`: the conclusions `QuietStep k t♯_k`. -/
theorem quietStep_self (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Ico 1 S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (hquiet : ∀ t' ∈ Icc (0 : ℝ) (S.P.tsh k), S.QuietStepAt t') :
    S.QuietStep k (S.P.tsh k) := by
  have hk1 := (Finset.mem_Ico.1 hk).1
  have hkn := (Finset.mem_Ico.1 hk).2
  exact hquiet (S.P.tsh k) ⟨tsh_nonneg hS hk1 hkn hc, le_rfl⟩ k hk (Or.inr le_rfl)

/-- `η^out_k ≤ θ_k maj_k` on `[0, t̄♯_k]` (Step 2: `lem:O` for `j = k`, `τ = t̄♯_k`). -/
theorem etaOut_le_theta (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Ico 1 S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (hquiet : ∀ t' ∈ Icc (0 : ℝ) (S.P.tsh k), S.QuietStepAt t') :
    ∀ τ ∈ Icc (0 : ℝ) (S.P.tash k), S.etaOut k τ ≤ S.theta k * S.maj k τ := by
  intro τ hτ
  have hO := ((quietStep_self hS hk hc hquiet).lemO hc).2
  have hA := A_pos hS k
  have hmem : τ / S.P.A k ∈ Icc (0 : ℝ) (S.P.A k * S.P.tsh k / S.P.A k) :=
    ⟨div_nonneg hτ.1 hA.le, div_le_div_of_nonneg_right hτ.2 hA.le⟩
  have := hO.etaOut_le (τ / S.P.A k) hmem
  rwa [A_mul_div hS] at this

/-- **`eq:boot-theta`** (`11_bootstrap.tex:341-348`): `θ_k t̄♯_k ≤ θ_k τ̄♯_k ≤ min{1/2, 1/(4C_lsK₁)}`,
by `lem:quiet-time` at the time `t♯_k` (levels `i ∈ (k, n)` by Step 3, `κ♯_n ≥ ½κ_seed` by Step 0)
and `lem:theta-quiet`. -/
theorem theta (hS : S.Holds) (hL : S.ParamLists) {k : ℕ} (hk : k ∈ Finset.Ico 1 S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (h0 : S.BootStartConcl)
    (hdeep : ∀ i ∈ Finset.Ioo k S.P.n, S.HandoffStep i) :
    S.theta k * S.P.tash k ≤ S.theta k * S.tauBarSh k ∧
      S.theta k * S.tauBarSh k ≤ min (1 / 2) (1 / (4 * Eig.Cls S.P.χ * S.K1)) := by
  have hk1 := (Finset.mem_Ico.1 hk).1
  have hkn := (Finset.mem_Ico.1 hk).2
  have hpos := constPos hS
  refine ⟨?_, (theta_quiet S hS hL.sbar.b7 hk1 hkn).2⟩
  have hcl : ∀ i ∈ Finset.Ioc k S.P.n, S.P.ClockUpTo (i + 1) → S.P.tsh i ≤ S.P.tsh k →
      S.P.ClockUpTo i ∧ (i < S.P.n → S.Klo * S.P.s i ^ (3 + 2) ≤ S.P.ksh i) := by
    intro i hi _ _
    have hi' := Finset.mem_Ioc.1 hi
    exact ⟨hc.mono (by omega), fun hin => (hdeep i (Finset.mem_Ioo.2 ⟨hi'.1, hin⟩)).amp_lo⟩
  have hqt := quiet_time S hS hL.det hL.sbar.b6 hk1 hkn (tsh_nonneg hS hk1 hkn hc) hcl
    (fun _ => le_rfl) h0.ksh_n.1
  exact mul_le_mul_of_nonneg_left hqt (theta_nonneg hpos hS k)

/-- The bound (BA3) for ring `k+1` on `Ph_{k+1}`, with `2C₂` (`11_bootstrap.tex:362-366`): by
(BA°)(t♯_k) off `t♯_{k+1}`, and at `t♯_{k+1}` by `eq:boot-switch` for ring `k+1` or by
`eq:boot-start`. -/
theorem ba3_next (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Ico 1 S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (h0 : S.BootStartConcl) (hBA : S.BAcirc (S.P.tsh k))
    (hdeep : ∀ i ∈ Finset.Ioo k S.P.n, S.HandoffStep i) {t : ℝ}
    (ht : t ∈ Icc (S.P.tsh (k + 1)) (S.P.T (k + 1))) :
    Sob.normH S.s (S.P.w (k + 1) t) ≤
      2 * S.C2 * S.ahatK (k + 1) (S.P.activeTime (k + 1) t) *
        (1 + S.rhoHatK S.C0 (k + 1) (S.P.activeTime (k + 1) t)) := by
  have hk1 := (Finset.mem_Ico.1 hk).1
  have hkn := (Finset.mem_Ico.1 hk).2
  obtain ⟨htsh1, htshT, hTtsh, -⟩ := clock_around hS hk1 hkn hc
  have hk1I : k + 1 ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  by_cases hts : t = S.P.tsh (k + 1)
  · subst hts
    have hat : S.P.activeTime (k + 1) (S.P.tsh (k + 1)) = 0 := by
      simp [Approx.activeTime]
    rw [hat]
    -- `‖w_{k+1}(t♯_{k+1})‖_{H^s} ≤ C₀κ♯_{k+1} < C₂ â_{k+1}(0)(1 + ρ̂_{k+1}(0))`
    have key : Sob.normH S.s (S.P.w (k + 1) (S.P.tsh (k + 1))) ≤ S.C0 * S.P.ksh (k + 1) ∧
        S.C0 * S.P.ksh (k + 1) < S.C2 * S.ahatK (k + 1) 0 * (1 + S.rhoHatK S.C0 (k + 1) 0) := by
      by_cases h : k + 1 < S.P.n
      · have hd := hdeep (k + 1) (Finset.mem_Ioo.2 ⟨by omega, h⟩)
        exact ⟨hd.switch_le.trans hd.switch_C0, hd.switch_lt⟩
      · have hn : k + 1 = S.P.n := by omega
        rw [hn, S.P.tsh_n]
        exact ⟨h0.start_le, h0.start_lt⟩
    have h1 : 0 ≤ S.C0 * S.P.ksh (k + 1) := mul_nonneg S.C0_pos.le (S.P.ksh_nonneg _)
    linarith [key.1, key.2]
  · exact hBA.ba3 t ⟨htsh1.trans ht.1, ht.2.trans hTtsh⟩ (k + 1) hk1I hts ⟨hc, ht.1, ht.2⟩

/-- **The hypotheses (H1)–(H4) of `prop:relay`** with `j = k`, `τ = t̄♯_k`, `C₀ = S.C0`,
`K₁ = S.K1` (`11_bootstrap.tex:351-369`), given `θ_k t̄♯_k ≤ 1/2` (`eq:boot-theta`). -/
theorem relayHyp (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Ico 1 S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (h0 : S.BootStartConcl) (hBA : S.BAcirc (S.P.tsh k))
    (hgeo : S.GeometryConcl (S.P.tsh k))
    (hquiet : ∀ t' ∈ Icc (0 : ℝ) (S.P.tsh k), S.QuietStepAt t')
    (hdeep : ∀ i ∈ Finset.Ioo k S.P.n, S.HandoffStep i)
    (hact : S.ActiveStep (k + 1) (S.P.That (k + 1)))
    (hθ : S.theta k * S.P.tash k ≤ 1 / 2) : S.RelayHyp S.C0 S.K1 k (S.P.tash k) := by
  have hk1 := (Finset.mem_Ico.1 hk).1
  have hkn := (Finset.mem_Ico.1 hk).2
  have hpos := constPos hS
  obtain ⟨htsh1, htshT, hTtsh, -⟩ := clock_around hS hk1 hkn hc
  have hk1I : k + 1 ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hdiv := tash_div hS k
  refine
    { one_le := hk1
      lt_n := hkn
      clock := hc
      τ_nonneg := mul_nonneg (A_pos hS k).le (tsh_nonneg hS hk1 hkn hc)
      τ_le := le_rfl
      h1 := fun t ht => hgeo.loc t (by rwa [hdiv] at ht)
      h2 := ⟨etaOut_le_theta hS hk hc hquiet, hθ⟩
      h3 := ?_
      h4 := ?_ }
  · -- (H3): `thm:quiet` for ring `k+1` on `[0, t̄♯_{k+1}]` (Step 2)
    intro h
    rw [hdiv, min_eq_right (htshT.trans hTtsh)]
    exact (hquiet (S.P.tsh (k + 1)) ⟨htsh1, htshT.trans hTtsh⟩ (k + 1)
      (Finset.mem_Ico.2 ⟨by omega, h⟩) (Or.inr le_rfl)).concl
  · -- (H4) on `Ph_{k+1}`
    intro _
    rw [hdiv, min_eq_right hTtsh]
    refine ⟨?_, fun t ht => ⟨?_, ba3_next hS hk hc h0 hBA hdeep ht, ?_⟩⟩
    · by_cases h : k + 1 < S.P.n
      · exact (hdeep (k + 1) (Finset.mem_Ioo.2 ⟨by omega, h⟩)).handoff.2.2.1
      · have hn : k + 1 = S.P.n := by omega
        have h00 : S.P.tash (k + 1) = 0 := by
          rw [Approx.tash_def, hn, S.P.tsh_n, mul_zero]
        rw [h00, S.maj_zero]
        exact mul_nonneg hpos.K1_pos.le (S.P.ksh_nonneg _)
    · exact (hgeo.ring t ⟨htsh1.trans ht.1, ht.2.trans hTtsh⟩ (k + 1) hk1I
        (not_debris_of_le_T ht.2)).2.1
    · -- the inner bound, by Step 4 for ring `k+1` with `C_F ≤ C₀`
      have hA := A_pos hS (k + 1)
      set u := S.P.activeTime (k + 1) t with hu
      have hu0 : 0 ≤ u := mul_nonneg hA.le (by linarith [ht.1])
      have huT : u ≤ S.P.That (k + 1) := by
        have hT := ht.2
        rw [T_eq (by omega)] at hT
        have h1 : t - S.P.tsh (k + 1) ≤ S.P.That (k + 1) / S.P.A (k + 1) := by linarith
        have h2 := mul_le_mul_of_nonneg_left h1 hA.le
        rwa [mul_div_cancel₀ _ hA.ne'] at h2
      have hin := (hact.inner u ⟨hu0, huT⟩).2
      have heq : S.P.A (k + 1) * t = S.P.tash (k + 1) + u := by
        rw [hu, Approx.tash_def, Approx.activeTime]
        ring
      rw [heq]
      refine hin.trans ?_
      have hj : 0 ≤ S.P.ksh (k + 1) * Prelim.jap u ^ 3 :=
        mul_nonneg (S.P.ksh_nonneg _) (pow_nonneg (le_trans zero_le_one
          (by rw [Prelim.jap]; exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg u]))) _)
      have := mul_le_mul_of_nonneg_right S.CF_le_C0 hj
      linarith [this]

/-- `C_Ξ(C₀, K₁) ≥ 0`. -/
theorem CXi_nonneg (hpos : S.ConstPos) : 0 ≤ S.CXi S.C0 S.K1 := by
  unfold Standing.CXi
  have hC0 : 0 ≤ S.C0 := S.C0_pos.le
  have hC2 : 0 ≤ S.C2 := le_trans zero_le_one hpos.one_le_C2
  have hCact : 0 ≤ S.Cact S.C0 := le_trans hC0 (OneRing.le_Cact _ _ _)
  have hsb := hpos.sigb_pos
  have hm : 0 < min 1 S.sigb := lt_min one_pos hsb
  have hK1 := hpos.K1_pos
  have hmax : 0 ≤ max 1 (2 * S.CQ) := le_trans zero_le_one (le_max_left _ _)
  positivity

/-- **`Ξ_{k+1} ≤ δ₀/(σ_b(μ-1))`** (`11_bootstrap.tex:371-374`): `κ♯_{k+1} < δ₀` and
`1 - γ_k ≥ γ'_μ` give `(κ♯_{k+1}/δ₀)^{1-γ_k} ≤ (κ♯_{k+1}/δ₀)^{γ'_μ}`; then (κ7) at `κ♯_{k+1}`. -/
theorem xiNext_le (hS : S.Holds) (hL : S.ParamLists) {k : ℕ} (hk : k ∈ Finset.Ico 1 S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (hκle : S.P.ksh (k + 1) ≤ 2 * S.P.κs)
    (hγ : S.gammaMu' ≤ 1 - S.gammaJ k) :
    S.XiNext S.C0 S.K1 k ≤ S.P.δ₀ / (S.sigb * (S.P.μ - 1)) := by
  have hkn := (Finset.mem_Ico.1 hk).2
  have hpos := constPos hS
  have hκ := hc.ksh_mem le_rfl (by omega : k + 1 ≤ S.P.n)
  have hδ := hS.δ₀_pos
  have h7 := (hL.kappa.cond hκ.1 hκle).k7
  set X := S.P.ksh (k + 1) / S.P.δ₀ with hX
  set J := Prelim.jap (Real.log (S.P.δ₀ / S.P.ksh (k + 1))) ^ (3 + 1) with hJ
  set c := S.CXi S.C0 S.K1 * (1 + 1 / (S.sigb * (S.P.μ - 1))) with hcdef
  have hsb := hpos.sigb_pos
  have hμ : 0 < S.P.μ - 1 := by linarith [hS.one_lt_μ]
  have hc0 : 0 ≤ c := by
    have := CXi_nonneg hpos
    have : 0 ≤ 1 / (S.sigb * (S.P.μ - 1)) := by positivity
    positivity
  have hJ0 : 0 ≤ J := by
    rw [hJ]
    exact pow_nonneg (le_trans zero_le_one (by
      rw [Prelim.jap]; exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (Real.log
        (S.P.δ₀ / S.P.ksh (k + 1)))]))) _
  have hX0 : 0 < X := div_pos hκ.1 hδ
  have hX1 : X ≤ 1 := by rw [hX, div_le_one hδ]; exact hκ.2.le
  have hpow : X ^ (1 - S.gammaJ k) ≤ X ^ S.gammaMu' :=
    Real.rpow_le_rpow_of_exponent_ge hX0 hX1 hγ
  have hXi : S.XiNext S.C0 S.K1 k = S.P.δ₀ * (c * X ^ (1 - S.gammaJ k) * J) := by
    simp only [Standing.XiNext, hcdef, hX, hJ]
    ring
  rw [hXi]
  have h7' : c * X ^ S.gammaMu' * J ≤ 1 / (S.sigb * (S.P.μ - 1)) := h7
  have hstep : c * X ^ (1 - S.gammaJ k) * J ≤ c * X ^ S.gammaMu' * J :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hc0) hJ0
  calc S.P.δ₀ * (c * X ^ (1 - S.gammaJ k) * J) ≤ S.P.δ₀ * (1 / (S.sigb * (S.P.μ - 1))) :=
        mul_le_mul_of_nonneg_left (hstep.trans h7') hδ.le
    _ = S.P.δ₀ / (S.sigb * (S.P.μ - 1)) := by ring

end BootHandoffH

end Relay

end NonUniqueEuler
