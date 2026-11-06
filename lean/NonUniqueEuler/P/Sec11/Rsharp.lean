import NonUniqueEuler.Defs.Sec11.All
import NonUniqueEuler.I.Sec11.Bootstrap
import NonUniqueEuler.I.Sec9.Readout
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec10.P0P4Uses
import NonUniqueEuler.I.Sec6.Clock

/-!
# Uniform moment bound in the proof of the reduction proposition

Current source: Part II §8, the readout calculation in the proof of Proposition 1.2
(`prop:reduction`), in `manuscript/part2/sections/11_bootstrap.tex`. The old labels
`thm:Rsharp` and `eq:Rsharp` are retired. Lean `Rsharp` retains the separate intermediate
statement that bounds the defect uniformly in the depth `n`.

For `n ≥ 2`, put `S = p.standing A₁ n` and choose `T^{(n)} = T₁`.
* `bootstrap_params` gives the stronger Lean bundle `S.BootConcl`: its `clock` and `amp`
  fields supply current Proposition 8.1(1), `active` and `coef` supply (2), `confine` gives
  (3) at `T₁`, and `time` gives (4). For ring 1, `η_{b,1} = 0` (`etabK_one`).
* Lemma 3.10(1) (`lem:clock`) gives `0 ≤ t♯_1 < T₁` and `T₂ < t♯_1`, so `T₁ ∈ W₁`.
  The confinement field gives `D₂(T₁) ⊂ B_{a/8}`, since `r₁ = 1`.
* (P1) gives `C_pC₂δ₀ ≤ c_out/(16π)` (`p1_readout`). Condition (κ5) applies at
  `G = G₁` and `κ = κ♯_1`: the clock gives positivity, and `BootConcl.amp` with (B6)
  gives `κ♯_1 ≤ K_up s_1⁵ ≤ K_up s̄⁵ ≤ κ_seed`.
* Lean `readout` isolates the moment estimate now written directly in the proof of
  `prop:reduction`. The identities `S.c0 = p.c0 A₁`, `S.Tstar = p.Tstar A₁` and
  `S.P.om = p.approxVort A₁ n` hold by `rfl`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- **The historical `thm:Rsharp` decomposition** (Part II §8, proof of Proposition 1.2
(`prop:reduction`), the uniform moment bound in that proof). Assume (N1)–(N3), (P0)–(P6) for the
parameters `p`, and `A₁ > 0`. For every readout cutoff `χ_out` and every `n ≥ 2` there is
`T^{(n)} ∈ [0, T_*]` with `|∫ ω^{(n)}(T^{(n)}) Ψ₁| ≥ c₀ = ½A₁c_outδ₀`; `c₀ = p.c0 A₁` and
`T_* = p.Tstar A₁` do not depend on `n`. -/
theorem Rsharp (p : Params) (hχ : IsAdmissibleCutoff p.χ) (hN : NumericalHypothesis p.χ)
    (hL : p.Lists) {A₁ : ℝ} (hA₁ : 0 < A₁) {χo : ℝ → ℝ} (hχo : IsReadoutCutoff χo) :
    ∀ n : ℕ, 2 ≤ n → ∃ T ∈ Icc (0 : ℝ) (p.Tstar A₁),
      p.c0 A₁ ≤ ‖∫ x, (p.approxVort A₁ n T x : ℂ) * readoutTest χo x‖ := by
  intro n hn
  have hS : (p.standing A₁ n).Holds := hL.holds hχ hN hA₁ hn
  have hPL : (p.standing A₁ n).ParamLists := hL.standing A₁ n
  have hDet : (p.standing A₁ n).Det := hL.det A₁ n
  have hB : (p.standing A₁ n).BootConcl := bootstrap_params p hχ hN hL hA₁ hn
  set S := p.standing A₁ n with hSdef
  have hnS : S.P.n = n := rfl
  have h1Icc : 1 ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have h1Ico : 1 ∈ Finset.Ico 1 S.P.n := Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
  obtain ⟨-, -, hG, hlev⟩ := standing_levels S hS
  obtain ⟨hord1, -, hord3, hord4⟩ :=
    Datum.Approx.clock_order S.P hS.valid hS.hN hG le_rfl hB.clock
  -- `t♯_1 < T_1`, `0 ≤ t♯_1`, `T_2 < t♯_1`
  have htsh : S.P.tsh 1 < S.P.T 1 := hord1 1 h1Icc
  have htsh0 : 0 ≤ S.P.tsh 1 := hord4 1 h1Icc
  have hT2 : S.P.T 2 < S.P.tsh 1 := hord3 1 2 le_rfl (by norm_num) (by omega)
  have hT0 : 0 ≤ S.P.T 1 := htsh0.trans htsh.le
  -- `D_2(T_1) ⊂ B_{a/8}`
  have hD : S.P.D 2 (S.P.T 1) ⊆ ball 0 (a / 8) := by
    have hW : S.P.T 1 ∈ S.P.W 1 := ⟨(hT2.trans htsh).le, le_rfl⟩
    have hin : S.P.HInDefined 1 (S.P.T 1) := ((hB.confine 1 h1Ico).2 (S.P.T 1) hW).2
    have hr : S.P.r 1 = 1 := radius_one _ _
    have h := hin
    unfold Datum.Approx.HInDefined at h
    rw [hr, mul_one] at h
    exact h
  -- the active conclusions for ring `1` with `η_{b,1} = 0`
  have hact : S.ActiveConclABOn S.C0 0 1 := by
    have h := (hB.active 1 h1Icc).ab
    rwa [Standing.etabK_one] at h
  -- the coefficient bound
  have hcoef : 15 / 16 * S.P.δ₀ ≤
      ‖S.P.runCoefK 1 (S.P.That 1)‖ * Real.exp (S.P.sigma 1 * S.P.That 1) :=
    (hB.coef 1 h1Icc).1
  -- (P1)
  have h1 : Eig.Cp * S.C2 * S.P.δ₀ ≤ Eig.cout S.P.χ / (16 * Real.pi) :=
    p1_readout S hS.valid.admissible hS.hN hPL.structural
  -- (κ5) at `κ = κ♯_1`, `G = G_1`
  have hk1 : S.P.ksh 1 ∈ Ioo (0 : ℝ) S.P.δ₀ := (hB.clock 1 h1Icc).2
  have hkpos : 0 < S.P.ksh 1 := hk1.1
  have hamp : S.P.ksh 1 ≤ S.Kup * S.P.s 1 ^ (3 + 2) := (hB.amp 1 h1Ico).2
  have hsbar : 0 < S.P.sbar := hPL.sbar.sbar_pos
  have hμ : 1 < S.P.μ := hPL.structural.p2.one_lt_μ
  have hs1pos : 0 < S.P.s 1 := ratio_pos hsbar (by linarith) 1
  have hs1le : S.P.s 1 ≤ S.P.sbar := by
    show S.P.sbar / (2 * S.P.μ) ^ 1 ≤ S.P.sbar
    rw [pow_one]
    exact div_le_self hsbar.le (by linarith)
  have hKup : 0 < S.Kup := by
    have h5 : 0 < S.P.s 1 ^ (3 + 2) := pow_pos hs1pos _
    rcases le_or_gt S.Kup 0 with hK | hK
    · have : S.Kup * S.P.s 1 ^ (3 + 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hK h5.le
      linarith
    · exact hK
  have hkle : S.P.ksh 1 ≤ S.P.κs := by
    calc S.P.ksh 1 ≤ S.Kup * S.P.s 1 ^ (3 + 2) := hamp
      _ ≤ S.Kup * S.P.sbar ^ (3 + 2) := by
        gcongr
      _ ≤ S.P.κs := hPL.sbar.b6
  have hκs : 0 < S.P.κs := hPL.kappa.pos
  have hcond : S.CondKappa (S.P.ksh 1) := hPL.kappa.cond hkpos (by linarith)
  have hG1 : S.P.G 1 ∈ Icc (0 : ℝ) Gbar := (hlev 1 h1Icc).2.1
  have h2 : Eig.Cp * S.C2 * (S.rhoHatK S.C0 1 (S.P.That 1) + Real.sqrt (S.P.ksh 1)) ≤
      Eig.cout S.P.χ / (16 * Real.pi) :=
    hcond.k5 (S.P.G 1) hG1
  -- the readout estimate in the proof of `prop:reduction`
  have hread := readout S hS hDet S.one_le_C0 hχo hB.clock hact hcoef hD h1 h2
  exact ⟨S.P.T 1, ⟨hT0, hB.time⟩, hread⟩

end Relay

end NonUniqueEuler
