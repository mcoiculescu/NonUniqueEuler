import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec9.ActiveRing
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec5.Active.Moment
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec4.RingFacts

/-!
# Proof: `lem:readout` (reading the instability off ring `1` at `T₁`)

Proof of `I/Sec9/Readout.lean` (`09_relay.tex:1409-1463`). Same declaration, statement copied
verbatim.

Uses: `standing_levels` (`I/Sec9/Standing.lean`: `σ_1 ≥ σ_b > 0`, `G_1 ∈ [0,G₁]`),
`activeConfig_units` (`I/Sec9/ActiveRing.lean`: `t♯_1 ≥ 0`), `regions_basic_two` and
`regions_basic_four` (`I/Sec6/RegionsBasic.lean`: `supp ω(t) ⊂ ⋃ S_k(t)`, `w_1(T_1)` smooth,
compactly supported, in `X^s`), `active_moment_bound` (`I/Sec5/Active/Moment.lean`:
`|2πpout_3[f] - 2πpout_*(G)X| ≤ 2πC_p‖f - 2Re(Xφ_*)‖_{H^s}`), `uniform_constants`
(`I/Sec4/Uniform.lean`: `c_out > 0`, `c_out ≤ 2π|pout_*(G)|`), `ringFacts_of_admissible`
(`I/Sec4/RingFacts.lean`: `Φ` continuous with compact support).

`pout_3[Φ] = 0` is proved here from `Φ(-y) = Φ(y)` and the invariance of Lebesgue measure under
`y ↦ -y` (the manuscript: "`Φ` is radial").
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- `∫ Φ(y) ȳ³ dy = 0`: `Φ(-y) = Φ(y)` and `(-ȳ)³ = -ȳ³` (`09_relay.tex:1437`, "`Φ` is radial,
so `pout_m[Φ] = 0`"). -/
private theorem integral_ringPhi_mul_conj_pow_three (χ : ℝ → ℝ) :
    ∫ y, ((ringPhi χ y : ℝ) : ℂ) * conj y ^ 3 = 0 := by
  have hneg : ∀ y : ℂ, ringPhi χ (-y) = ringPhi χ y := by
    intro y
    simp only [ringPhi, ringRef, mul_neg, neg_eq_zero, norm_neg]
  have h := integral_neg_eq_self (fun y : ℂ => ((ringPhi χ y : ℝ) : ℂ) * conj y ^ 3) volume
  have h' : (fun y : ℂ => ((ringPhi χ (-y) : ℝ) : ℂ) * conj (-y) ^ 3) =
      fun y => -(((ringPhi χ y : ℝ) : ℂ) * conj y ^ 3) := by
    funext y
    rw [hneg, map_neg, Odd.neg_pow (by decide), mul_neg]
  simp only [h', integral_neg] at h
  have h2 : (2 : ℂ) * ∫ y, ((ringPhi χ y : ℝ) : ℂ) * conj y ^ 3 = 0 := by
    linear_combination -h
  simpa using h2

/-- The readout integrand on ring `1`: if `S_1(t) ⊂ 𝒩` (`r_1 = 1`), `D_2(t) ⊂ B_{a/8}` and
`supp ω(t) ⊂ S_1(t) ∪ D_2(t)`, then `ω(t)Ψ₁ = ω(t)1_{S_1(t)} ȳ³` pointwise. -/
private theorem om_mul_readoutTest_eq (P : Approx) {χo : ℝ → ℝ} (hχo : IsReadoutCutoff χo)
    {t : ℝ} (hr : P.r 1 = 1)
    (hsupp : P.St 1 t ⊆ P.Nnk 1) (hD : P.D 2 t ⊆ ball 0 (a / 8))
    (hom : tsupport (P.om t) ⊆ ⋃ k ∈ Finset.Icc 1 P.n, P.St k t) (x : ℂ) :
    (P.om t x : ℂ) * readoutTest χo x = (P.omegaRing 1 t x : ℂ) * conj x ^ 3 := by
  have ha := zero_lt_a
  by_cases hx : x ∈ P.St 1 t
  · have hxN := hsupp hx
    rw [Approx.Nnk, mem_scaleSet, hr] at hxN
    simp only [Complex.ofReal_one, inv_one, one_mul, annNn, Sect.closedAnnulus] at hxN
    have h1 : χo ‖x‖ = 1 :=
      hχo.eq_one _ ⟨by linarith [hxN.1], by linarith [hxN.2]⟩
    simp only [readoutTest, h1, Complex.ofReal_one, one_mul, Approx.omegaRing,
      indicator_of_mem hx]
  · rw [Approx.omegaRing, indicator_of_notMem hx, Complex.ofReal_zero, zero_mul]
    by_cases hx2 : x ∈ P.D 2 t
    · have hb := hD hx2
      rw [mem_ball, dist_zero_right] at hb
      have h0 : χo ‖x‖ = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have := (hχo.tsupport_subset hmem).1
        linarith
      simp only [readoutTest, h0, Complex.ofReal_zero, zero_mul, mul_zero]
    · have hnot : x ∉ tsupport (P.om t) := by
        intro hmem
        have := hom hmem
        simp only [mem_iUnion, Finset.mem_Icc] at this
        obtain ⟨k, ⟨hk1, hkn⟩, hxk⟩ := this
        rcases Nat.lt_or_ge k 2 with hk | hk
        · have : k = 1 := by omega
          subst this
          exact hx hxk
        · apply hx2
          simp only [Approx.D, mem_iUnion, Finset.mem_Icc]
          exact ⟨k, ⟨hk, hkn⟩, hxk⟩
      rw [image_eq_zero_of_notMem_tsupport hnot, Complex.ofReal_zero, zero_mul]

/-- `ω(t)1_{S_1(t)} = A_1(Φ + w_1(t))` pointwise (`def:regions`, `r_1 = 1`). -/
private theorem omegaRing_one_eq (P : Approx) (hA : P.A 1 ≠ 0) (hr : P.r 1 = 1) (t : ℝ)
    (x : ℂ) :
    (P.omegaRing 1 t x : ℂ) = (P.A 1 : ℂ) * (P.w 1 t x + ((ringPhi P.χ x : ℝ) : ℂ)) := by
  have hA' : (P.A 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hA
  simp only [Approx.w, Approx.wR, Approx.unitsVort, scaleVort, hr, Complex.ofReal_one, one_mul]
  push_cast
  field_simp
  ring

/-- **`lem:readout`** (`09_relay.tex:1409-1423`). Assume (SA), (Det), `C₀ ≥ 1`, a readout cutoff
`χ_out`, the clock defined up to level `1`, the conclusions (a)–(b) of `thm:active` for ring `1` on
`Ph_1` with `C₀` and `η_b = 0`, `|c_1(T̂_1)|e^{σ_1T̂_1} ≥ 15δ₀/16`, `D_2(T_1) ⊂ B_{a/8}`,
`C_pC₂δ₀ ≤ c_out/(16π)` and `C_pC₂(ρ̂_1(T̂_1) + κ♯_1^{1/2}) ≤ c_out/(16π)`. Then
`|∫ ω^{(n)}(T_1) Ψ₁| ≥ c₀ = ½A₁c_outδ₀`. -/
theorem readout (S : Standing) (hS : S.Holds) (hDet : S.Det) {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    {χo : ℝ → ℝ} (hχo : IsReadoutCutoff χo) (hc : S.P.ClockUpTo 1)
    (hact : S.ActiveConclABOn C₀ 0 1)
    (hcoef : 15 / 16 * S.P.δ₀ ≤ ‖S.P.runCoefK 1 (S.P.That 1)‖ * Real.exp (S.P.sigma 1 * S.P.That 1))
    (hD : S.P.D 2 (S.P.T 1) ⊆ ball 0 (a / 8))
    (h1 : Eig.Cp * S.C2 * S.P.δ₀ ≤ Eig.cout S.P.χ / (16 * Real.pi))
    (h2 : Eig.Cp * S.C2 * (S.rhoHatK C₀ 1 (S.P.That 1) + Real.sqrt (S.P.ksh 1)) ≤
      Eig.cout S.P.χ / (16 * Real.pi)) :
    S.c0 ≤ ‖∫ x, (S.P.om (S.P.T 1) x : ℂ) * readoutTest χo x‖ := by
  -- Step 0: the numbers of ring `1` at `u = T̂_1`.
  have hP := hS.valid
  have hN := hS.hN
  have hn : 2 ≤ S.P.n := hS.two_le_n
  have hδ : 0 < S.P.δ₀ := hS.δ₀_pos
  have hκ : S.P.ksh 1 ∈ Ioo (0 : ℝ) S.P.δ₀ := hc.ksh_mem le_rfl (by omega)
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  obtain ⟨hsigb, -, -, hlev⟩ := standing_levels S hS
  obtain ⟨-, hG1, hsig1⟩ := hlev 1 h1mem
  have hσ : 0 < S.P.sigma 1 := hsigb.trans_le hsig1
  have hlog : 0 < Real.log (S.P.δ₀ / S.P.ksh 1) :=
    Real.log_pos ((one_lt_div hκ.1).2 hκ.2)
  have hThat : 0 ≤ S.P.That 1 := mul_nonneg (inv_nonneg.2 hσ.le) hlog.le
  have hahat : S.ahatK 1 (S.P.That 1) = S.P.δ₀ := by
    rw [Standing.ahatK_def, Approx.That, ← mul_assoc, mul_inv_cancel₀ hσ.ne', one_mul,
      Real.exp_log (div_pos hδ hκ.1)]
    field_simp [hκ.1.ne']
  have hA : 0 < S.P.A 1 := hP.A_pos 1
  have hA1 : S.P.A 1 = S.P.A₁ := by simp [Approx.A]
  have hr : S.P.r 1 = 1 := by simp [Approx.r]
  have hT : S.P.tsh 1 + S.P.That 1 / S.P.A 1 = S.P.T 1 := (S.P.T_of_ne (by omega)).symm
  have htsh : 0 ≤ S.P.tsh 1 := (activeConfig_units S hS le_rfl (by omega) hc).1
  have hT0 : 0 ≤ S.P.T 1 := by
    rw [← hT]
    exact add_nonneg htsh (div_nonneg hThat hA.le)
  -- Step 1: the conclusions (a)–(b) of `thm:active` at `u = T̂_1`, i.e. at `t = T_1`.
  have hab := hact (S.P.That 1) ⟨hThat, le_rfl⟩
  have hsupp : S.P.St 1 (S.P.T 1) ⊆ S.P.Nnk 1 := hT ▸ hab.supp
  have hmode := hab.mode
  rw [hT, hahat] at hmode
  have hpert : S.P.PertDefined 1 (S.P.T 1) := by
    intro x hx
    have hxN := hsupp hx
    rw [Approx.Nnk, mem_scaleSet] at hxN
    rw [Approx.Nk, mem_scaleSet]
    have ha := zero_lt_a
    simp only [annNn, annN, Sect.closedAnnulus, mem_ofPred_eq] at hxN ⊢
    exact ⟨by linarith [hxN.1], by linarith [hxN.2]⟩
  obtain ⟨hwc, hwcpt, -, -, hwX, -⟩ := Approx.regions_basic_four S.P hP hN h1mem hT0 hpert
  obtain ⟨-, -, -, -, hom, -⟩ := Approx.regions_basic_two S.P hP hN hT0
  -- Step 2: `∫ ω(T_1)Ψ₁ = A_1 ∫ w_1(T_1) ȳ³ = 2πA_1 pout_3[w_1(T_1)]`.
  obtain ⟨hΦc, hΦs, -⟩ := ringFacts_of_admissible hS.admissible
  have hcont3 : Continuous fun y : ℂ => conj y ^ 3 := Complex.continuous_conj.pow 3
  have hintw : Integrable (fun y => S.P.w 1 (S.P.T 1) y * conj y ^ 3) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((Complex.continuous_ofReal.comp hwc.continuous).mul hcont3) ?_
    exact (hwcpt.comp_left Complex.ofReal_zero).mul_right
  have hintΦ : Integrable (fun y => ((ringPhi S.P.χ y : ℝ) : ℂ) * conj y ^ 3) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((Complex.continuous_ofReal.comp hΦc.continuous).mul hcont3) ?_
    exact (hΦs.comp_left Complex.ofReal_zero).mul_right
  have hpt : ∀ x, (S.P.om (S.P.T 1) x : ℂ) * readoutTest χo x =
      (S.P.A 1 : ℂ) * (S.P.w 1 (S.P.T 1) x * conj x ^ 3) +
        (S.P.A 1 : ℂ) * (((ringPhi S.P.χ x : ℝ) : ℂ) * conj x ^ 3) := by
    intro x
    rw [om_mul_readoutTest_eq S.P hχo hr hsupp hD hom x,
      omegaRing_one_eq S.P hA.ne' hr (S.P.T 1) x]
    ring
  have hint : ∫ x, (S.P.om (S.P.T 1) x : ℂ) * readoutTest χo x =
      (S.P.A 1 : ℂ) * (2 * Real.pi * BS.pout 3 (S.P.w 1 (S.P.T 1))) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add (hintw.const_mul _) (hintΦ.const_mul _), integral_const_mul,
      integral_const_mul, integral_ringPhi_mul_conj_pow_three, mul_zero, add_zero, BS.pout]
    have h2π : (2 * Real.pi : ℂ) ≠ 0 := by
      have := Real.pi_pos
      exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    rw [mul_inv_cancel_left₀ h2π]
  -- Step 3: the moment bound `|2πpout_3[w_1(T_1)] - 2πpout_*(G_1)ce^{λT̂}| ≤ c_outδ₀/4`.
  set X : ℂ := S.P.runCoefK 1 (S.P.That 1) * Complex.exp (S.P.lam 1 * (S.P.That 1 : ℂ)) with hX
  obtain ⟨-, -, -, -, -, -, -, hcout, hGb⟩ := Eig.uniform_constants S.P.χ hS.admissible hN
  obtain ⟨-, -, hcoutG, -⟩ := hGb _ hG1
  have hCp : 0 ≤ Eig.Cp := by
    unfold Eig.Cp
    positivity
  have hmom := OneRing.active_moment_bound S.P.χ hS.admissible hN hG1 (hwX S.s).1
    (hwX S.s).2.1 X
  have hpi := Real.pi_pos
  have hB : ‖2 * Real.pi * BS.pout 3 (S.P.w 1 (S.P.T 1)) -
      2 * Real.pi * Eig.pout S.P.χ (S.P.G 1) * X‖ ≤ Eig.cout S.P.χ * S.P.δ₀ / 4 := by
    calc _ ≤ 2 * Real.pi * Eig.Cp *
          Sob.normH S.s (S.P.w 1 (S.P.T 1) - OneRing.modeFn S.P.χ (S.P.G 1) X) := hmom
      _ ≤ 2 * Real.pi * Eig.Cp * (S.C2 * S.P.δ₀ *
          (S.rhoHatK C₀ 1 (S.P.That 1) + S.P.δ₀ + Real.sqrt (S.P.ksh 1) + 0)) := by
          gcongr
      _ = 2 * Real.pi * S.P.δ₀ * (Eig.Cp * S.C2 * (S.rhoHatK C₀ 1 (S.P.That 1) +
          Real.sqrt (S.P.ksh 1)) + Eig.Cp * S.C2 * S.P.δ₀) := by ring
      _ ≤ 2 * Real.pi * S.P.δ₀ * (Eig.cout S.P.χ / (16 * Real.pi) +
          Eig.cout S.P.χ / (16 * Real.pi)) := by gcongr
      _ = Eig.cout S.P.χ * S.P.δ₀ / 4 := by
          field_simp
          ring
  -- Step 4: `|2πpout_*(G_1)ce^{λT̂}| ≥ (15/16)c_outδ₀`.
  have hXn : ‖X‖ = ‖S.P.runCoefK 1 (S.P.That 1)‖ * Real.exp (S.P.sigma 1 * S.P.That 1) := by
    rw [hX, norm_mul, Complex.norm_exp]
    congr 2
    simp [Approx.sigma, Eig.sigma, Approx.lam]
  have hY : 15 / 16 * (Eig.cout S.P.χ * S.P.δ₀) ≤
      ‖2 * Real.pi * Eig.pout S.P.χ (S.P.G 1) * X‖ := by
    have e : ‖2 * Real.pi * Eig.pout S.P.χ (S.P.G 1) * X‖ =
        (2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G 1)‖) * ‖X‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
      norm_num
    rw [e, hXn]
    calc 15 / 16 * (Eig.cout S.P.χ * S.P.δ₀) = Eig.cout S.P.χ * (15 / 16 * S.P.δ₀) := by ring
      _ ≤ (2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G 1)‖) *
          (‖S.P.runCoefK 1 (S.P.That 1)‖ * Real.exp (S.P.sigma 1 * S.P.That 1)) := by
          apply mul_le_mul hcoutG hcoef (by positivity) (by positivity)
  -- Step 5: conclusion.
  have hZ : 11 / 16 * (Eig.cout S.P.χ * S.P.δ₀) ≤
      ‖2 * Real.pi * BS.pout 3 (S.P.w 1 (S.P.T 1))‖ := by
    have := norm_sub_norm_le (2 * Real.pi * Eig.pout S.P.χ (S.P.G 1) * X)
      (2 * Real.pi * BS.pout 3 (S.P.w 1 (S.P.T 1)))
    rw [norm_sub_rev] at this
    linarith
  rw [hint, norm_mul, Complex.norm_real, Real.norm_of_nonneg hA.le, Standing.c0_def, ← hA1]
  have hcd : 0 ≤ Eig.cout S.P.χ * S.P.δ₀ := by positivity
  calc 1 / 2 * S.P.A 1 * Eig.cout S.P.χ * S.P.δ₀ ≤ S.P.A 1 * (11 / 16 * (Eig.cout S.P.χ * S.P.δ₀)) := by
        nlinarith
    _ ≤ S.P.A 1 * ‖2 * Real.pi * BS.pout 3 (S.P.w 1 (S.P.T 1))‖ :=
        mul_le_mul_of_nonneg_left hZ hA.le

end Relay

end NonUniqueEuler
