import Mathlib.MeasureTheory.Function.LocallyIntegrable
import NonUniqueEuler.Defs.Sec7.All
import NonUniqueEuler.I.Sec6.Speed
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec6.Adm
import NonUniqueEuler.I.SmoothB.SmoothFlow
import NonUniqueEuler.I.Infra.Multipole.Moments
import NonUniqueEuler.H.Sec7.Confine.Speed
import NonUniqueEuler.H.Sec7.Confine.Trajectory

/-!
# Proof: `prop:confine` (confinement on a window)

Proof of `I/Sec7/Confine.lean` (`07_several_rings.tex:285-314`, proof `:316-380`).

* (b) is `ConfineH.confine_speed` (`H/Sec7/Confine/Speed.lean`): the velocity splits into the
  inner part (`lem:speed`) and the outer rings `j ≤ k` (`lem:hollow` under (Cl), `eq:sk-small`,
  (iii), (iv)).
* (a): every trajectory `τ ↦ Φ_τ(y)`, `y ∈ S_i`, `i ≥ k+1`, starts in `\bar B_{2r_{k+1}}` at `t₀` (i),
  and moves with speed `≤ 2C_*A_{k+1}r_{k+1}` while it stays in `\bar B_{Λr_{k+1}}` (b); the
  trajectory lemma `ConfineH.norm_le_of_cond_deriv_bound` (`H/Sec7/Confine/Trajectory.lean`) gives
  `|Φ_t(y)| ≤ ϱ(t)`. **Deviation (restructuring):** the manuscript's continuity argument is run
  for the whole set `D_{k+1}(0)` with uniform continuity of `(t,y) ↦ |Φ_t(y)|`; here it is run for
  one trajectory at a time, which suffices because (b) holds on the whole ball at every time of
  the window, independently of the other trajectories.
* (c): `ω_{≥k+1}(t) ≥ 0` is `3`-fold symmetric (`lem:regions-basic`(3)), so its moments vanish off
  `3ℕ` (`moment_eq_zero_of_isMFoldSymmetric`); it is supported in `\bar B_{ϱ(t)}` by (a), and
  `‖ω_{≥k+1}(t)‖_{L¹} ≤ M_vort A_{k+1}r_{k+1}²` (`lem:speed`), so `norm_moment_le` gives the bound;
  `l = 3` gives `|q_{k+1}(t)| ≤ M_vort(2 + 2C_*τ_K)³ ≤ C_mom(1 + τ_K)³`.
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate

namespace NonUniqueEuler

namespace Rings

namespace ConfineP

open RingData Datum Datum.Approx ConfineH

variable (P : Approx)

/-- The flow of a valid approximation solves `∂_τ Φ_τ(y) = v(τ, Φ_τ(y))` for every `τ`
(`thm:smooth`(4)). -/
theorem hasDerivAt_flow (hP : P.Valid) (hN : NumericalHypothesis P.χ) (y : ℂ) (τ : ℝ) :
    HasDerivAt (fun s => P.flow s y) (P.vel τ (P.flow τ y)) τ := by
  have hadm := (Datum.adm P.χ hP.admissible hN hP.datumParams
    ⟨hP.kseed_pos, hP.kseed_le⟩).1 P.n hP.two_le_n
  obtain ⟨hcd, hcs, -, -, -⟩ := hadm
  obtain ⟨R₀, hR₀⟩ := hcs.isCompact.isBounded.subset_ball (0 : ℂ)
  have hsd : Smooth.IsSmoothDatum P.f R₀ := ⟨hcd, hR₀⟩
  have hsol := (Smooth.flow_global hsd y).2.hasDerivAt τ (mem_univ τ)
  have hflow : (fun s => P.flow s y) = fun s => Smooth.flow P.f s y := by
    funext s
    rw [hP.flow_eq s]
  have hvel : P.vel = Smooth.vel P.f := by
    funext s x
    simp only [Approx.vel, Smooth.vel, hP.om_eq]
  rw [hflow, hvel, hP.flow_eq τ]
  exact hsol

/-- `τ_K = A_{k+1}(t - T_{k+1}) ≥ 0` for `t ≥ T_{k+1}`. -/
theorem kickTime_nonneg (hP : P.Valid) {k : ℕ} {t : ℝ} (ht : P.T (k + 1) ≤ t) :
    0 ≤ P.kickTime k t := by
  unfold kickTime
  exact mul_nonneg (hP.A_pos (k + 1)).le (by linarith)

/-- `ϱ(t) ≥ 0` for `t ≥ T_{k+1}`. -/
theorem confRadius_nonneg (hP : P.Valid) {k : ℕ} {t : ℝ} (ht : P.T (k + 1) ≤ t) :
    0 ≤ P.confRadius k t := by
  unfold confRadius
  have := kickTime_nonneg P hP ht
  have := Cstar_pos
  have := hP.r_pos (k + 1)
  positivity

/-- **`prop:confine`(a), support** (`07_several_rings.tex:351-368`):
`D_{k+1}(t) ⊂ \bar B_{ϱ(t)}` for `t ∈ [T_{k+1}, t₁]`. -/
theorem confine_supp (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall) {k : ℕ}
    {t₁ : ℝ} (h : P.ConfineHyp k t₁) {t : ℝ} (ht : t ∈ Icc (P.T (k + 1)) t₁) :
    P.D (k + 1) t ⊆ closedBall 0 (P.confRadius k t) := by
  intro z hz
  simp only [Approx.D, mem_iUnion] at hz
  obtain ⟨i, hi, hzi⟩ := hz
  obtain ⟨y, hy, rfl⟩ := hzi
  have hC := Cstar_pos
  have hA := hP.A_pos (k + 1)
  have hr := hP.r_pos (k + 1)
  have hV : 0 < 2 * Cstar * P.A (k + 1) * P.r (k + 1) := by positivity
  -- the trajectory starts in `\bar B_{2 r_{k+1}}` (i)
  have h0 : ‖P.flow (P.T (k + 1)) y‖ ≤ 2 * P.r (k + 1) := by
    have hmem : P.flow (P.T (k + 1)) y ∈ P.D (k + 1) (P.T (k + 1)) := by
      simp only [Approx.D, mem_iUnion]
      exact ⟨i, hi, mem_image_of_mem _ hy⟩
    have := h.init hmem
    simpa [mem_closedBall, dist_zero_right] using this
  have hL : 2 * P.r (k + 1) + 2 * Cstar * P.A (k + 1) * P.r (k + 1) * (t₁ - P.T (k + 1)) ≤
      P.confLambda k t₁ * P.r (k + 1) := by
    rw [confLambda_def]
    nlinarith
  have hbound : ∀ τ ∈ Icc (P.T (k + 1)) t₁,
      ‖P.flow τ y‖ ≤ P.confLambda k t₁ * P.r (k + 1) →
        ‖P.vel τ (P.flow τ y)‖ ≤ 2 * Cstar * P.A (k + 1) * P.r (k + 1) := by
    intro τ hτ hle
    refine confine_speed P hP hN hG h τ hτ _ ?_
    simpa [mem_closedBall, dist_zero_right] using hle
  have hmain := norm_le_of_cond_deriv_bound (γ := fun s => P.flow s y)
    (γ' := fun s => P.vel s (P.flow s y)) (hasDerivAt_flow P hP hN y) hV h0 hL hbound t ht
  simp only [mem_closedBall, dist_zero_right]
  refine hmain.trans (le_of_eq ?_)
  rw [confRadius_def]
  ring

/-- **`prop:confine`(a), radius** (`07_several_rings.tex:367-368`): `ϱ(t) ≤ ϱ(t₁) = Λ s_k r_k ≤ a r_k/8`. -/
theorem confRadius_le (hP : P.Valid) {k : ℕ} {t₁ : ℝ} (h : P.ConfineHyp k t₁) {t : ℝ}
    (ht : t ∈ Icc (P.T (k + 1)) t₁) : P.confRadius k t ≤ a / 8 * P.r k := by
  have hC := Cstar_pos
  have hA := hP.A_pos (k + 1)
  have hr := hP.r_pos (k + 1)
  have hrk := hP.r_pos k
  have h1 : P.confRadius k t ≤ P.confRadius k t₁ := by
    rw [confRadius_def, confRadius_def]
    have : 2 * Cstar * P.A (k + 1) * (t - P.T (k + 1)) ≤
        2 * Cstar * P.A (k + 1) * (t₁ - P.T (k + 1)) := by
      have : 0 ≤ 2 * Cstar * P.A (k + 1) := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) this
    exact mul_le_mul_of_nonneg_right (by linarith) hr.le
  have hrs : P.r (k + 1) = P.s k * P.r k := by
    rw [r_def, r_def, s_def]
    exact radius_succ _ _ h.one_le
  calc P.confRadius k t ≤ P.confRadius k t₁ := h1
    _ = P.confLambda k t₁ * P.s k * P.r k := by
        rw [confRadius_eq_confLambda, hrs, mul_assoc]
    _ ≤ a / 8 * P.r k := mul_le_mul_of_nonneg_right h.lambda_le hrk.le

/-- `∫ x^l g = moment g l` (the form of `I-MULT`). -/
theorem integral_pow_mul_eq_moment (g : ℂ → ℝ) (l : ℕ) :
    ∫ x, x ^ l * ((g x : ℝ) : ℂ) = Multipole.moment (fun w => ((g w : ℝ) : ℂ)) l := by
  unfold Multipole.moment
  congr 1
  funext w
  rw [zpow_natCast, mul_comm]

/-- The facts on `g = ω_{≥k+1}(t)` used in (c): integrable, `3`-fold symmetric, supported in
`\bar B_{ϱ(t)}`, and `∫ |g| ≤ M_vort A_{k+1} r_{k+1}²`. -/
theorem omegaGe_facts (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall) {k : ℕ}
    {t₁ : ℝ} (h : P.ConfineHyp k t₁) {t : ℝ} (ht : t ∈ Icc (P.T (k + 1)) t₁) :
    Integrable (fun w => ((P.omegaGe (k + 1) t w : ℝ) : ℂ)) ∧
    IsMFoldSymmetric 3 (P.omegaGe (k + 1) t) ∧
    (∀ᵐ w ∂volume, P.confRadius k t < ‖w‖ → ((P.omegaGe (k + 1) t w : ℝ) : ℂ) = 0) ∧
    ∫ w, ‖((P.omegaGe (k + 1) t w : ℝ) : ℂ)‖ ≤ Mvort * P.A (k + 1) * P.r (k + 1) ^ 2 := by
  have hT0 := T_succ_nonneg P hP hN hG h
  have ht0 : 0 ≤ t := hT0.trans ht.1
  have hk1 : k + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨by omega, h.lt_n⟩
  obtain ⟨-, -, -, -, -, -, -, ⟨hcd, hcs, -, hsym⟩⟩ := P.regions_basic_three hP hN hk1 ht0
  have hint : Integrable (P.omegaGe (k + 1) t) := hcd.continuous.integrable_of_hasCompactSupport hcs
  refine ⟨hint.ofReal, isMFoldSymmetric_three_of_forall hsym, ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun w hw => ?_
    have hw' : w ∉ P.D (k + 1) t := fun hwD => by
      have := confine_supp P hP hN hG h ht hwD
      simp only [mem_closedBall, dist_zero_right] at this
      linarith
    simp only [Approx.omegaGe, indicator_of_notMem hw', Complex.ofReal_zero]
  · have hL1 := (P.speed hP hN hk1 ht0).1 1 (by simp)
    simp only [ENNReal.ofReal_one, div_one, Real.rpow_one, Real.rpow_two] at hL1
    have hnorm : ∫ w, ‖((P.omegaGe (k + 1) t w : ℝ) : ℂ)‖ =
        (eLpNorm (P.omegaGe (k + 1) t) 1 volume).toReal := by
      rw [toReal_eLpNorm_one_eq hcd.continuous.aestronglyMeasurable]
      simp only [Complex.norm_real]
    rw [hnorm]
    have hA := hP.A_pos (k + 1)
    exact ENNReal.toReal_le_of_le_ofReal (by have := Mvort_pos; positivity) hL1

/-- **`prop:confine`** (`07_several_rings.tex:285-314`). Assume (N1)–(N3) and `G_k ≤ G₁` for all
levels. Under the hypotheses (i)–(iv) of the proposition for the level `k` (`1 ≤ k < n`, clock
defined up to level `k+1`, `t₀ = T_{k+1}`) and the end time `t₁ ≥ t₀` (`P.ConfineHyp k t₁`), the
conclusions (a)–(c) hold at every `t ∈ [t₀,t₁]` (`P.ConfineConcl k t₁ t`): `D_{k+1}(t) ⊂ \bar B_{ϱ(t)}`
with `ϱ(t) ≤ (a/8)r_k`; the speed bound `2C_*A_{k+1}r_{k+1}` on `\bar B_{Λr_{k+1}}`; the moments of
`ω_{≥k+1}(t)` vanish off `mℕ` and are `≤ M_vort A_{k+1}r_{k+1}²ϱ(t)^l`; `|q_{k+1}(t)| ≤ C_mom(1+τ_K)^m`. -/
theorem confine_aux (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall)
    {k : ℕ} {t₁ : ℝ} (h : P.ConfineHyp k t₁) :
    ∀ t ∈ Icc (P.T (k + 1)) t₁, P.ConfineConcl k t₁ t := by
  intro t ht
  obtain ⟨hint, hsym, hsupp, hL1⟩ := omegaGe_facts P hP hN hG h ht
  have hϱ0 := confRadius_nonneg P hP ht.1
  have hmom : ∀ l : ℕ, ‖∫ x, x ^ l * ((P.omegaGe (k + 1) t x : ℝ) : ℂ)‖ ≤
      Mvort * P.A (k + 1) * P.r (k + 1) ^ 2 * P.confRadius k t ^ l := by
    intro l
    rw [integral_pow_mul_eq_moment]
    refine (Multipole.norm_moment_le hint hϱ0 hsupp l).trans ?_
    exact mul_le_mul_of_nonneg_right hL1 (pow_nonneg hϱ0 _)
  refine ⟨confine_supp P hP hN hG h ht, confRadius_le P hP h ht, confine_speed P hP hN hG h t ht,
    ?_, hmom, ?_⟩
  · intro l hl
    rw [integral_pow_mul_eq_moment]
    refine Multipole.moment_eq_zero_of_isMFoldSymmetric (m := 3) (by norm_num) hsym ?_
    exact_mod_cast hl
  · -- `|q_{k+1}(t)| ≤ M_vort (ϱ/r_{k+1})³ ≤ C_mom (1 + τ_K)³`
    have hA := hP.A_pos (k + 1)
    have hr := hP.r_pos (k + 1)
    have hden : 0 < P.A (k + 1) * P.r (k + 1) ^ (3 + 2) := by positivity
    have hQ : ‖BS.Qm 3 (fun x => ((P.omegaGe (k + 1) t x : ℝ) : ℂ))‖ ≤
        Mvort * P.A (k + 1) * P.r (k + 1) ^ 2 * P.confRadius k t ^ 3 := by
      rw [BS.Qm_eq_moment, ← integral_pow_mul_eq_moment]
      exact hmom 3
    have hτ := kickTime_nonneg P hP ht.1
    have hcm := Mvort_mul_le_Cmom hτ
    rw [Approx.q, norm_div, Complex.norm_conj, Complex.norm_of_nonneg hden.le,
      div_le_iff₀ hden]
    calc ‖BS.Qm 3 (fun x => ((P.omegaGe (k + 1) t x : ℝ) : ℂ))‖
        ≤ Mvort * P.A (k + 1) * P.r (k + 1) ^ 2 * P.confRadius k t ^ 3 := hQ
      _ = Mvort * (2 + 2 * Cstar * P.kickTime k t) ^ 3 *
            (P.A (k + 1) * P.r (k + 1) ^ (3 + 2)) := by
          rw [confRadius]
          ring
      _ ≤ Cmom * (1 + P.kickTime k t) ^ 3 * (P.A (k + 1) * P.r (k + 1) ^ (3 + 2)) :=
          mul_le_mul_of_nonneg_right hcm hden.le

end ConfineP

open RingData Datum

/-- **`prop:confine`** (`07_several_rings.tex:285-314`). Assume (N1)–(N3) and `G_k ≤ G₁` for all
levels. Under the hypotheses (i)–(iv) of the proposition for the level `k` (`1 ≤ k < n`, clock
defined up to level `k+1`, `t₀ = T_{k+1}`) and the end time `t₁ ≥ t₀` (`P.ConfineHyp k t₁`), the
conclusions (a)–(c) hold at every `t ∈ [t₀,t₁]` (`P.ConfineConcl k t₁ t`): `D_{k+1}(t) ⊂ \bar B_{ϱ(t)}`
with `ϱ(t) ≤ (a/8)r_k`; the speed bound `2C_*A_{k+1}r_{k+1}` on `\bar B_{Λr_{k+1}}`; the moments of
`ω_{≥k+1}(t)` vanish off `mℕ` and are `≤ M_vort A_{k+1}r_{k+1}²ϱ(t)^l`; `|q_{k+1}(t)| ≤ C_mom(1+τ_K)^m`. -/
theorem confine (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall)
    {k : ℕ} {t₁ : ℝ} (h : P.ConfineHyp k t₁) :
    ∀ t ∈ Icc (P.T (k + 1)) t₁, P.ConfineConcl k t₁ t :=
  ConfineP.confine_aux P hP hN hG h

end Rings

end NonUniqueEuler
