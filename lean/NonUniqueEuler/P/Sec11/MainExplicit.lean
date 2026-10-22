import NonUniqueEuler.Defs.Sec11.All
import NonUniqueEuler.I.Sec11.Rsharp
import NonUniqueEuler.I.Sec11.ApproxWeakCont
import NonUniqueEuler.I.Sec3.Defect
import NonUniqueEuler.I.Sec3.RadialStationary
import NonUniqueEuler.I.Sec6.Integrability
import NonUniqueEuler.I.Sec6.Adm
import NonUniqueEuler.I.Sec4.Uniform

/-!
# Proof: `thm:main-explicit` (the main theorem in explicit form)

Proof of `I/Sec11/MainExplicit.lean` (`11_bootstrap.tex:665-683`, proof `:685-721`).

1. `T_* ≥ 1/A₁` (`Tstar_ge`): the bracket of `T_*` is `1` plus nonnegative terms
   (`T_pin > 0`, `σ' > 9/200`, `μ > 1`, `0 < s̄ ≤ a/16 < 1`, `2κ_seed < δ₀`).
2. `c₀ = ½A₁c_outδ₀ > 0` (`c0_pos`, `c_out > 0` by `Eig.uniform_constants`).
3. `prop:defect` (`Compact.defect`) with `T̄ = T_*`, `χ = χ_out = Relay.chiOut`, `m = 3`,
   `fs n = f^{(n+2)}`, `ωs n = ω^{(n+2)}`: hypotheses from `prop:integrability`
   (`Datum.integrability`), `lem:adm` (`Datum.adm`, `q = 2`), `approx_weakCont`, `thm:Rsharp`.
4. (ii) from `lem:radial-stationary` (`Compact.radial_stationary`) and the conclusions of step 3.
-/

noncomputable section

open MeasureTheory Set Metric Filter

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace MainExplicitProof

/-- The bracket of `T_*` is at least `1` (`11_bootstrap.tex:687-689`). -/
theorem one_le_bracket (p : Params) (hL : p.Lists) (A₁ : ℝ) :
    1 ≤ p.μ / (p.μ - 1) * ((p.standing A₁ 2).Tz + (3 + 2) / p.σ' * Real.log (1 / p.sbar)) +
      (3 + 2) * Real.log (2 * p.μ) / p.σ' * (p.μ ^ 2 / (p.μ - 1) ^ 2) + 1 +
      1 / p.σ' * Real.log (2 * p.δ₀ / p.κs) := by
  have hμ : 1 < p.μ := hL.one_lt_μ
  have hσ : 0 < p.σ' := lt_trans (by norm_num) hL.structural.p0.σ'_gt
  have hsb : 0 < p.sbar := hL.sbar_pos
  have hsb1 : p.sbar < 1 := by
    have := hL.sbar_le
    have := a_lt_one
    linarith
  have hκ : 0 < p.κs := hL.kseed_pos
  have hδκ : 2 * p.κs < p.δ₀ := hL.two_kseed_lt_δ₀
  have hTpin : 0 < p.Tpin := hL.Tpin_pos
  -- `T_z ≥ 0`
  have hTz : 0 ≤ (p.standing A₁ 2).Tz := by
    rw [Standing.Tz_def]
    have h1 : 0 ≤ (p.standing A₁ 2).σ'⁻¹ := inv_nonneg.mpr hσ.le
    have h2 : 0 ≤ Real.posLog ((p.standing A₁ 2).P.δ₀ / (p.standing A₁ 2).Klo) :=
      Real.posLog_nonneg
    have h3 : (p.standing A₁ 2).P.Tpin = p.Tpin := rfl
    rw [h3]
    have := mul_nonneg h1 h2
    linarith
  have hlogsb : 0 ≤ Real.log (1 / p.sbar) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hsb]
    linarith
  have hlogμ : 0 ≤ Real.log (2 * p.μ) := Real.log_nonneg (by linarith)
  have hlogδ : 0 ≤ Real.log (2 * p.δ₀ / p.κs) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hκ]
    linarith
  have hμ1 : 0 < p.μ - 1 := by linarith
  have t1 : 0 ≤ p.μ / (p.μ - 1) * ((p.standing A₁ 2).Tz + (3 + 2) / p.σ' * Real.log (1 / p.sbar)) := by
    apply mul_nonneg (div_nonneg (by linarith) hμ1.le)
    exact add_nonneg hTz (mul_nonneg (div_nonneg (by norm_num) hσ.le) hlogsb)
  have t2 : 0 ≤ (3 + 2) * Real.log (2 * p.μ) / p.σ' * (p.μ ^ 2 / (p.μ - 1) ^ 2) := by
    apply mul_nonneg
    · exact div_nonneg (mul_nonneg (by norm_num) hlogμ) hσ.le
    · positivity
  have t3 : 0 ≤ 1 / p.σ' * Real.log (2 * p.δ₀ / p.κs) :=
    mul_nonneg (div_nonneg zero_le_one hσ.le) hlogδ
  linarith

/-- `T_* ≥ 1/A₁` (`11_bootstrap.tex:687-689`). -/
theorem Tstar_ge (p : Params) (hL : p.Lists) {A₁ : ℝ} (hA₁ : 0 < A₁) :
    1 / A₁ ≤ p.Tstar A₁ := by
  have hb := one_le_bracket p hL A₁
  show 1 / A₁ ≤ A₁⁻¹ * _
  rw [one_div]
  calc A₁⁻¹ = A₁⁻¹ * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hA₁.le)

/-- `c₀ = ½A₁c_outδ₀ > 0` (`11_bootstrap.tex:696-698`). -/
theorem c0_pos (p : Params) (hχ : IsAdmissibleCutoff p.χ) (hN : NumericalHypothesis p.χ)
    (hL : p.Lists) {A₁ : ℝ} (hA₁ : 0 < A₁) : 0 < p.c0 A₁ := by
  rw [Params.c0_def]
  have hc : 0 < Eig.cout p.χ := (Eig.uniform_constants p.χ hχ hN).2.2.2.2.2.2.2.1
  have hδ : 0 < p.δ₀ := hL.δ₀_pos
  positivity

end MainExplicitProof

open MainExplicitProof in
/-- **`thm:main-explicit`** (`11_bootstrap.tex:665-683`). Assume (N1)–(N3), an admissible cutoff,
parameters `p` with (P0)–(P6), and `A₁ > 0`. Then `T_* ∈ [1/A₁, ∞)`, and there are a renormalized
weak solution `ω_∞` on `[0, ∞)` with datum `f` (`q = 2`) and `t₀ ∈ [0, T_*)` with the properties
(i), (ii) (`p.MainExplicit A₁`). -/
theorem main_explicit (p : Params) (hχ : IsAdmissibleCutoff p.χ) (hN : NumericalHypothesis p.χ)
    (hL : p.Lists) {A₁ : ℝ} (hA₁ : 0 < A₁) : p.MainExplicit A₁ := by
  have hT := Tstar_ge p hL hA₁
  have hTpos : 0 < p.Tstar A₁ := lt_of_lt_of_le (one_div_pos.mpr hA₁) hT
  have hc₀ := c0_pos p hχ hN hL hA₁
  have hdp : DatumParams A₁ p.μ p.sbar := hL.datumParams hA₁
  have hκ : p.κs ∈ Ioc 0 (OneRing.kL p.χ) := ⟨hL.kseed_pos, hL.kseed_le⟩
  -- `prop:integrability`: `f` radial, in every `L^q`
  obtain ⟨⟨_, hradP, _, hLq, _⟩, _⟩ := integrability p.χ hχ hdp
  have hf : ∀ q : ℝ, 1 ≤ q → MemLp (p.datum A₁) (ENNReal.ofReal q) volume := hLq
  have hrad : IsRadial (p.datum A₁) := fun θ => Filter.Eventually.of_forall (hradP θ)
  have hf1 : MemLp (p.datum A₁) 1 volume := by
    simpa using hf 1 le_rfl
  -- `lem:adm`: `2`-admissible, symmetric
  obtain ⟨hadm1, _, hadm3⟩ := adm p.χ hχ hN hdp hκ
  have hadm : Compact.IsAdmissibleSeq 2 ⊤ (p.datum A₁)
      (fun n => approxDatum p.χ A₁ p.μ p.sbar p.κs (n + 2))
      (fun n => p.approxVort A₁ (n + 2)) := hadm3 2 (by norm_num)
  have hcont : ∀ n, Weak.IsWeakContL2On (Ici 0) (p.approxVort A₁ (n + 2)) := fun n =>
    approx_weakCont p.χ hχ hN hdp hκ (by omega : 2 ≤ n + 2)
  have hsym : ∀ n, ∀ t : ℝ, 0 ≤ t → IsMFoldSymmetric 3 (p.approxVort A₁ (n + 2) t) :=
    fun n t _ => ((hadm1 (n + 2) (by omega)).2.2.2.2) t
  -- `thm:Rsharp` with `χ_out = chiOut`
  have hR := Rsharp p hχ hN hL hA₁ isReadoutCutoff_chiOut
  choose! Tn hTn hlowR using hR
  have hlow : ∀ᶠ n in atTop, Tn (n + 2) ∈ Icc 0 (p.Tstar A₁) ∧
      p.c0 A₁ ≤ ‖∫ x, (p.approxVort A₁ (n + 2) (Tn (n + 2)) x : ℂ) *
        Compact.defectTest chiOut 3 x‖ :=
    Filter.Eventually.of_forall fun n =>
      ⟨hTn (n + 2) (by omega), hlowR (n + 2) (by omega)⟩
  -- `prop:defect` with `T̄ = T_*`, `c₀ = p.c0 A₁`
  obtain ⟨ωinf, hhalf, heq, hcLp, ⟨t₀, ht₀, ht₀T, hdist⟩, hren⟩ :=
    Compact.defect (f := p.datum A₁) (m := 3) (χ := chiOut)
      (fs := fun n => approxDatum p.χ A₁ p.μ p.sbar p.κs (n + 2))
      (ωs := fun n => p.approxVort A₁ (n + 2)) (Tn := fun n => Tn (n + 2))
      hf hrad (by norm_num) isReadoutCutoff_chiOut.isRadialTestProfile hadm hcont hsym hc₀ hTpos
      hlow
  refine ⟨hT, ωinf, t₀, ht₀, ht₀T, hhalf, hcLp, heq, ?_⟩
  -- (ii)
  intro T hT' q hq
  have hTp : 0 < T := lt_of_le_of_lt ht₀ hT'
  exact ⟨Compact.radial_stationary hq hTp hf1 (hf q (by linarith)) hrad, hren T hTp q hq,
    hdist T hT'⟩

end Relay

end NonUniqueEuler
