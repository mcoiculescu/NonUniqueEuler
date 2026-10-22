import NonUniqueEuler.H.Sec11.BootActive.Outer
import NonUniqueEuler.I.Sec9.Drift
import NonUniqueEuler.I.Sec8.Coupling
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec10.P0P4Uses
import NonUniqueEuler.I.Sec9.Standing

/-!
# Helper for `P/Sec11/BootActive.lean`: (Coef), the hypotheses of `lem:drift`

Step 4 of the proof of `prop:bootstrap`, "(Coef)" (`11_bootstrap.tex:461-480`):
* `boot_driftHyp`: the hypotheses (i)–(iv) of `lem:drift` for ring `k`, `ū = A_k(t' - t♯_k)` and
  `η = η_{b,k}`: (i) `lem:geometry`(a) on `W_k` (the kick time of `t` is `T_pin + μ A_k(t - t♯_k)`);
  (ii) `lem:geometry`(b) on `[0, t♯_k]`, `lem:coupling`(2) with `eq:handoff`
  (`κ♯_k ≥ ½|c^in_k| = ½e^{x_kT_pin}|A^in(T_pin)|`), `q' = q_s` of Step 3, `lem:uniform` and (P2);
  (iii) the outer bound (`lem:Oprime`), as `‖·‖_{C^0} ≤ ‖·‖_{C^{M_h}}`; (iv) `lem:geometry`(b);
* `boot_cls`: `C_ls η_{b,k} T̂_k ≤ 1/32` (`η_{b,1} = 0`; (B8) with `σ_k ≥ σ'` and
  `κ♯_k ≥ K_lo s_k^{m+2}` for `2 ≤ k < n`; (B8) with `κ♯_n ≥ κ_seed/2` and `η_{b,n} ≤ η_b` for `k = n`).
All proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace BootActiveH

open RingData Datum

/-- **The hypotheses (i)–(iv) of `lem:drift`** for ring `k`, `ū = A_k(t' - t♯_k)` and
`η = η_{b,k}` (`11_bootstrap.tex:461-474`). -/
theorem boot_driftHyp (S : Standing) (hS : S.Holds) (hL : S.ParamLists) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 S.P.n) (hc : S.P.ClockUpTo k) {t' : ℝ} (ht' : t' ∈ S.P.Phase k)
    (htsh : S.P.tsh k < t') (h0 : S.BootStartConcl)
    (hBA : S.BAcirc t') (hgeo : S.GeometryConcl t')
    (hquiet : ∀ t'' ∈ Icc (0 : ℝ) t', S.QuietStepAt t'')
    (hlev : ∀ i ∈ Finset.Ico k S.P.n, S.HandoffStep i) :
    S.DriftHyp k (S.P.activeTime k t') (S.etabK S.C0 S.K1 k) := by
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hk
  have hP := hS.valid
  have hN := hS.hN
  have hpos := constPos hS
  have htsh0 : 0 ≤ S.P.tsh k := (activeConfig_units S hS hk1 hkn hc).1
  have hnd : ∀ t'' ≤ t', ¬ S.P.DebrisAt k t'' := fun t'' ht'' h =>
    absurd h.2 (not_lt.2 (ht''.trans ht'.2))
  have hlevels := standing_levels S hS
  refine
    { moment := ?_
      kick := ?_
      outer := ?_
      geom := ?_ }
  · -- (i): `lem:geometry`(a) on the window `W_k`
    intro hkn' τK hτK
    have hc1 : S.P.ClockUpTo (k + 1) := hc.mono (Nat.le_succ k)
    have hA1 := A_pos hS (k + 1)
    have hTk1 : S.P.T (k + 1) ≤ S.P.tsh k := by
      rw [S.P.tsh_eq_T_add hkn']
      have := div_nonneg hS.Tpin_pos.le hA1.le
      linarith
    have hwin := hgeo.window k (Finset.mem_Ico.2 ⟨hk1, hkn'⟩) hc1 (hTk1.trans htsh.le)
    have hendW : S.P.endW k = S.P.T k := by simp [Approx.endW, hc]
    set t'' := S.P.T (k + 1) + τK / S.P.A (k + 1) with ht''
    have hkick'' : S.P.kickTime k t'' = τK := by
      simp only [Approx.kickTime, ht'']
      field_simp
      ring
    have hkick' : S.P.kickTime k t' = S.P.Tpin + S.P.μ * S.P.activeTime k t' :=
      (S.P.kickTime_eq hP hk1 hkn').1 t'
    have hle : t'' ≤ t' := by
      have h1 : S.P.A (k + 1) * (t'' - S.P.T (k + 1)) ≤ S.P.A (k + 1) * (t' - S.P.T (k + 1)) := by
        have e1 : S.P.A (k + 1) * (t'' - S.P.T (k + 1)) = S.P.kickTime k t'' := rfl
        have e2 : S.P.A (k + 1) * (t' - S.P.T (k + 1)) = S.P.kickTime k t' := rfl
        rw [e1, e2, hkick'', hkick']
        exact hτK.2
      have := le_of_mul_le_mul_left h1 hA1
      linarith
    have hge : S.P.T (k + 1) ≤ t'' := by
      have := div_nonneg (hS.Tpin_pos.le.trans hτK.1) hA1.le
      linarith
    have ht''W : t'' ∈ Icc (S.P.T (k + 1)) (min t' (S.P.endW k)) :=
      ⟨hge, le_min hle (by rw [hendW]; exact hle.trans ht'.2)⟩
    have h := (hwin.2 t'' ht''W).2.2
    rw [hkick''] at h
    exact h
  · -- (ii): `lem:coupling`(2), `eq:handoff`, Step 3, `lem:uniform`, (P2)
    intro hkn'
    have hc1 : S.P.ClockUpTo (k + 1) := hc.mono (Nat.le_succ k)
    have hin0 : ∀ t ∈ Icc (0 : ℝ) (S.P.tsh k), S.P.HInDefined k t := fun t ht =>
      (hgeo.ring t ⟨ht.1, ht.2.trans htsh.le⟩ k hk (hnd t (ht.2.trans htsh.le))).2.1
    have hcin := (Kick.coupling_two S.P hP hN hlevels.2.2.1 hk1 hkn' hc1 hin0).2.2.2.2
    have hlk := hlev k (Finset.mem_Ico.2 ⟨le_rfl, hkn'⟩)
    have hnorm : ‖S.P.cinK k‖ = Real.exp (S.P.xk k * S.P.Tpin) * ‖S.P.Ain k S.P.Tpin‖ := by
      rw [hcin, norm_mul, Complex.norm_exp]
      congr 2
      simp only [Approx.zeta0, Approx.xk, Approx.sigma, Approx.lam]
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.div_ofReal_re]
      rfl
    refine ⟨hin0, ?_, ?_⟩
    · have := hlk.handoff.1
      rw [hnorm] at this
      linarith
    · -- `q' = q_s`
      have hqs := hlk.qs_mem.1
      have hG1 : S.P.G (k + 1) ∈ Icc (0 : ℝ) Gbar :=
        (hlevels.2.2.2 (k + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)).2.1
      have hunif := (Eig.uniform_constants S.P.χ hS.admissible hN).2.2.2.2.2.2.2.2
        (S.P.G (k + 1)) hG1
      have hcout : Eig.cout S.P.χ ≤ 2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ :=
        hunif.2.2.1
      have hcpos := hpos.cout_pos
      have hδ := hS.δ₀_pos
      have hq15 : 15 / 16 * Eig.cout S.P.χ * S.P.δ₀ ≤ ‖S.P.kickQs k‖ := by
        have : 15 / 16 * Eig.cout S.P.χ * S.P.δ₀ ≤
            15 / 16 * (2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ * S.P.δ₀) := by
          have := mul_le_mul_of_nonneg_right hcout hδ.le
          linarith
        linarith
      refine ⟨S.P.kickQs k, ?_, (hlk.kick S.P.Tpin ⟨hS.Tpin_pos.le, le_rfl⟩).1,
        p2_drift S hS.admissible hN hL.structural hq15⟩
      intro h0q
      rw [h0q, norm_zero] at hq15
      have : 0 < 15 / 16 * Eig.cout S.P.χ * S.P.δ₀ := by positivity
      linarith
  · -- (iii): the outer bound in `C^0`
    intro u hu
    have h := (boot_outer S hS hL hk hc ht' htsh h0 hBA hgeo hquiet hlev).1 u hu
    exact (normCk_mono_order h.1 (Nat.zero_le _)).trans h.2
  · -- (iv): `lem:geometry`(b)
    intro t'' ht''
    rw [eq_tsh_add hS k t'] at ht''
    exact (hgeo.ring t'' ⟨htsh0.trans ht''.1, ht''.2⟩ k hk (hnd t'' ht''.2)).2.2.1

/-- `T̂_k ≤ σ'⁻¹ log(δ₀/κ)` for `0 < κ ≤ κ♯_k < δ₀` and `σ_k ≥ σ' > 0`. -/
theorem That_le_of {S : Standing} (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n)
    (hc : S.P.ClockUpTo k) {κ : ℝ} (hκ : 0 < κ) (hκk : κ ≤ S.P.ksh k) :
    0 ≤ S.P.That k ∧ S.P.That k ≤ S.σ'⁻¹ * Real.log (S.P.δ₀ / κ) := by
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hk
  have hmem := hc.ksh_mem le_rfl hkn
  have hσk := ((standing_levels S hS).2.2.2 k hk).2.2
  have hσ' : 0 < S.σ' := by linarith [hS.σ'_gt]
  have hσ'k : S.σ' ≤ S.P.sigma k := le_trans hS.σ'_lt_sigb.le hσk
  have hσkpos : 0 < S.P.sigma k := lt_of_lt_of_le hσ' hσ'k
  have hδ := hS.δ₀_pos
  have hlog0 : 0 ≤ Real.log (S.P.δ₀ / S.P.ksh k) :=
    Real.log_nonneg ((one_le_div hmem.1).2 hmem.2.le)
  have hlog : Real.log (S.P.δ₀ / S.P.ksh k) ≤ Real.log (S.P.δ₀ / κ) :=
    Real.log_le_log (div_pos hδ hmem.1) (div_le_div_of_nonneg_left hδ.le hκ hκk)
  have hinv : (S.P.sigma k)⁻¹ ≤ S.σ'⁻¹ := inv_anti₀ hσ' hσ'k
  refine ⟨mul_nonneg (inv_nonneg.2 hσkpos.le) hlog0, ?_⟩
  calc S.P.That k = (S.P.sigma k)⁻¹ * Real.log (S.P.δ₀ / S.P.ksh k) := rfl
    _ ≤ S.σ'⁻¹ * Real.log (S.P.δ₀ / S.P.ksh k) := mul_le_mul_of_nonneg_right hinv hlog0
    _ ≤ S.σ'⁻¹ * Real.log (S.P.δ₀ / κ) := mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hσ'.le)

/-- **`C_ls η_{b,k} T̂_k ≤ 1/32`** (`11_bootstrap.tex:474-479`). -/
theorem boot_cls (S : Standing) (hS : S.Holds) (hL : S.ParamLists) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 S.P.n) (hc : S.P.ClockUpTo k) (h0 : S.BootStartConcl)
    (hlev : ∀ i ∈ Finset.Ico k S.P.n, S.HandoffStep i)
    (hetab : S.etabK S.C0 S.K1 k ≤ S.etab S.C0 S.K1) :
    Eig.Cls S.P.χ * S.etabK S.C0 S.K1 k * S.P.That k ≤ 1 / 32 := by
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hk
  have hpos := constPos hS
  have hCls := hpos.Cls_pos
  have hη := etabK_nonneg hpos hS k
  have hσ' : 0 < S.σ' := by linarith [hS.σ'_gt]
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · rw [S.etabK_of_le_one S.C0 S.K1 (by omega), mul_zero, zero_mul]
    norm_num
  rcases eq_or_lt_of_le hkn with hkn' | hkn'
  · -- `k = n`: (B8) with `log(2δ₀/κ_seed)`
    have hks := h0.ksh_n.1
    have hκs := hS.kseed_pos
    have hks' : 1 / 2 * S.P.κs ≤ S.P.ksh k := by rw [hkn']; exact hks
    have hT := That_le_of hS hk hc (by positivity) hks'
    have he : S.P.δ₀ / (1 / 2 * S.P.κs) = 2 * S.P.δ₀ / S.P.κs := by field_simp
    rw [he] at hT
    have hb := hL.sbar.b8_seed
    have hηb := etab_nonneg hpos hS
    calc Eig.Cls S.P.χ * S.etabK S.C0 S.K1 k * S.P.That k
        ≤ Eig.Cls S.P.χ * S.etab S.C0 S.K1 * S.P.That k := by gcongr; exact hT.1
      _ ≤ Eig.Cls S.P.χ * S.etab S.C0 S.K1 * (S.σ'⁻¹ * Real.log (2 * S.P.δ₀ / S.P.κs)) := by
          gcongr
          exact hT.2
      _ = Eig.Cls S.P.χ * S.etab S.C0 S.K1 * S.σ'⁻¹ * Real.log (2 * S.P.δ₀ / S.P.κs) := by ring
      _ ≤ 1 / 32 := hb
  · -- `2 ≤ k < n`: (B8) at the level `k`
    have hamp := (hlev k (Finset.mem_Ico.2 ⟨le_rfl, hkn'⟩)).amp_lo
    have hs := hS.valid.s_pos k
    have hKlo := hpos.Klo_pos
    have hκ : 0 < S.Klo * S.P.s k ^ (3 + 2) := by positivity
    have hT := That_le_of hS hk hc hκ hamp
    have hδ := hS.δ₀_pos
    have hlog : Real.log (S.P.δ₀ / (S.Klo * S.P.s k ^ (3 + 2))) ≤
        (3 + 2) * Real.log (1 / S.P.s k) + Real.posLog (S.P.δ₀ / S.Klo) := by
      have he : S.P.δ₀ / (S.Klo * S.P.s k ^ (3 + 2)) = (S.P.δ₀ / S.Klo) * (1 / S.P.s k) ^ (3 + 2) := by
        rw [one_div_pow, mul_one_div, div_div]
      rw [he, Real.log_mul (div_pos hδ hKlo).ne' (pow_pos (one_div_pos.2 hs) _).ne',
        Real.log_pow]
      have hpl : Real.log (S.P.δ₀ / S.Klo) ≤ Real.posLog (S.P.δ₀ / S.Klo) := le_max_right _ _
      push_cast
      linarith
    have hb := hL.sbar.b8_level k hk2
    calc Eig.Cls S.P.χ * S.etabK S.C0 S.K1 k * S.P.That k
        ≤ Eig.Cls S.P.χ * S.etabK S.C0 S.K1 k *
            (S.σ'⁻¹ * ((3 + 2) * Real.log (1 / S.P.s k) + Real.posLog (S.P.δ₀ / S.Klo))) := by
          gcongr
          exact hT.2.trans (mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hσ'.le))
      _ = Eig.Cls S.P.χ * S.etabK S.C0 S.K1 k / S.σ' *
            ((3 + 2) * Real.log (1 / S.P.s k) + Real.posLog (S.P.δ₀ / S.Klo)) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ 1 / 32 := hb

end BootActiveH

end Relay

end NonUniqueEuler
