import NonUniqueEuler.Defs.Verify.Profile
import NonUniqueEuler.I.Verify.ProfileBasic
import NonUniqueEuler.I.Verify.ProfileOmega
import NonUniqueEuler.I.Verify.EndRegions
import NonUniqueEuler.I.Verify.Comparison
import NonUniqueEuler.I.Evans.ODE
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Compact

/-!
# Proof: Lemma A.2 (`lem:apriori`), the a priori location of the zeros

Proof of `NonUniqueEuler/I/Verify/APriori.lean` (same declarations, statements copied
verbatim). Manuscript: `A_verification.tex:193-247`.

Used black boxes:
* `integrable_deriv_prof`, `endRegion_left_TV_interval`, `endRegion_right_TV_interval`
  (`I/Verify/EndRegions.lean`);
* `comparison_estimate`, `cmpSol_one_ell` (`I/Verify/Comparison.lean`);
* `contDiff_evansDenom`, `contDiff_evansDelta`, `norm_evansDelta_div`, `OmegaG_nonneg`,
  `OmegaG_le_OmegaMax`, `re_add_I_mul_ofReal`, `re_le_norm_add_I_mul_ofReal`
  (`I/Verify/ProfileOmega.lean`);
* `hasDerivAt_profA`, `hasDerivAt_profB`, `contDiff_profA` (and `Abar`, `B`, `Bbar`),
  `H_pos`, `H_le_one`, `deriv_prof_eq_zero_of_not_mem`, `taylorCoeff_deriv_prof_eq`
  (`I/Verify/ProfileBasic.lean`), with `taylorCoeff_zero` (`Defs/Verify/Taylor.lean`);
* `evansSolution_spec` (`I/Evans/ODE.lean`).

The proof follows the manuscript.
* `TV` is split as `∫_{ξL}^{ξa} + ∫_{ξa}^{ξb} + ∫_{ξb}^{ξR}` (the integrand vanishes off
  `[ξL, ξR]`); on the closed interval `[ξa, ξb]`, `ϖ' = (AB)'` (Taylor coefficient of order
  `0` of `ϖ'`), and `|(AB)'| ≤ A' - B'`, which integrates to `A(ξb) - A(ξa) + B(ξa) - B(ξb)`.
* Numerics: `e^{-50} < 1/676` (from `e^{25} > 26`, weaker than the manuscript's
  `e^{50} > 10^{21}` but sufficient), `log 2 > 0.6931471803`; `e^{-2ξL} = e² e^{x}` with
  `x = -2ξL - 2 < 0.011` and `e^x < 1/(1 - x)` (instead of `e^x ≤ 1 + x + x²`).
* `apriori_exists_xi`: `E_ℓ(λ; G)` is evaluated directly from its definition with the chosen
  solution `evansSolution` (no uniqueness needed); the comparison estimate at `ξR` with
  `ε = TV/μ` gives `2ℓe^{ℓL} = |ψ'(ξR) + ℓψ(ξR) - 2ℓe^{ℓL}| ≤ 2ℓe^{ℓL}(e^ε - 1)` when
  `E_ℓ = 0`, so `ε ≥ log 2`.
-/

noncomputable section

open Set MeasureTheory

namespace NonUniqueEuler

namespace AppA

open RingData

/-! ### Numerical facts -/

/-- `e^{-50} < 1/676` (from `e^{25} ≥ 26`). -/
private theorem apriori_exp_neg_fifty_lt : Real.exp (-50) < 1 / 676 := by
  have h25 : (26 : ℝ) < Real.exp 25 := by
    have := Real.add_one_lt_exp (show (25 : ℝ) ≠ 0 by norm_num); linarith
  have h50 : Real.exp 50 = Real.exp 25 * Real.exp 25 := by
    rw [← Real.exp_add]; norm_num
  have h676 : (676 : ℝ) < Real.exp 50 := by
    rw [h50]; nlinarith
  rw [Real.exp_neg, ← one_div]
  exact one_div_lt_one_div_of_lt (by norm_num) h676

/-- `Ω_max < 0.6495`. -/
theorem OmegaMax_lt : OmegaMax < 6495 / 10000 := by
  -- `e^{-2ξL} = e · e · e^{x}` with `x = -2ξL - 2 ∈ (0, 1)`.
  set x : ℝ := -2 * ξL - 2 with hx
  have hx0 : 0 < x := by rw [hx]; norm_num [ξL]
  have hx1 : x < 11 / 1000 := by rw [hx]; norm_num [ξL]
  have hex : Real.exp x < 1 / (1 - x) := Real.exp_bound_div_one_sub_of_interval' hx0 (by linarith)
  have hsplit : Real.exp (-2 * ξL) = Real.exp 1 * Real.exp 1 * Real.exp x := by
    rw [← Real.exp_add, ← Real.exp_add, hx]; ring_nf
  have he := Real.exp_one_lt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hexp0 : 0 < Real.exp x := Real.exp_pos x
  have h1x : 1 / (1 - x) < 1000 / 989 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hE : Real.exp (-2 * ξL) < 7.4715 := by
    rw [hsplit]
    have hee : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 := by
      nlinarith
    calc Real.exp 1 * Real.exp 1 * Real.exp x
        ≤ 2.7182818286 * 2.7182818286 * Real.exp x := by gcongr
      _ < 2.7182818286 * 2.7182818286 * (1000 / 989) := by gcongr; linarith
      _ < 7.4715 := by norm_num
  have hd : d < 0.0200001 := by norm_num [d]
  have hd0 : 0 < d := by norm_num [d]
  unfold OmegaMax
  nlinarith [Real.exp_pos (-2 * ξL)]

/-! ### `TV` -/

private theorem apriori_ξL_lt_ξR : ξL < ξR := by norm_num [ξL, ξR]

private theorem apriori_ξL_le_ξa : ξL ≤ ξa := by norm_num [ξL, ξa]

private theorem apriori_ξa_le_ξb : ξa ≤ ξb := by norm_num [ξa, ξb]

private theorem apriori_ξb_le_ξR : ξb ≤ ξR := by norm_num [ξb, ξR]

/-- The integrand of `TV` vanishes off `[ξL, ξR]`, so `TV = ∫_{ξL}^{ξR} |ϖ'|`. -/
private theorem apriori_TV_eq_intervalIntegral {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    TV χ = ∫ ξ in ξL..ξR, |deriv (prof χ) ξ| := by
  rw [intervalIntegral.integral_of_le apriori_ξL_lt_ξR.le, ← integral_Icc_eq_integral_Ioc, TV]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  rw [deriv_prof_eq_zero_of_not_mem hχ hx, abs_zero]

/-- On `[ξa, ξb]`: `∫_{ξa}^{ξb} |ϖ'| ≤ ∫_{ξa}^{ξb} (A' - B') = A(ξb) - A(ξa) + B(ξa) - B(ξb) ≤ 2`. -/
private theorem apriori_TV_middle_le {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    ∫ ξ in ξa..ξb, |deriv (prof χ) ξ| ≤ 2 := by
  -- the derivative of `A - B`
  set f' : ℝ → ℝ := fun ξ =>
    (2 / d) * (profA ξ * profAbar ξ) - -(2 / d) * (profB ξ * profBbar ξ) with hf'
  have hd0 : 0 < d := by norm_num [d]
  have hfd : ∀ ξ, HasDerivAt (fun x => profA x - profB x) (f' ξ) ξ := fun ξ =>
    (hasDerivAt_profA ξ).sub (hasDerivAt_profB ξ)
  have hf'c : Continuous f' := by
    simp only [hf']
    have hA := contDiff_profA.continuous
    have hAb := contDiff_profAbar.continuous
    have hB := contDiff_profB.continuous
    have hBb := contDiff_profBbar.continuous
    fun_prop
  have hFTC : ∫ ξ in ξa..ξb, f' ξ = (profA ξb - profB ξb) - (profA ξa - profB ξa) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ξ _ => hfd ξ)
      (hf'c.intervalIntegrable _ _)
  have hpt : ∀ ξ ∈ Icc ξa ξb, |deriv (prof χ) ξ| ≤ f' ξ := by
    intro ξ hξ
    have h1 := taylorCoeff_deriv_prof_eq hχ hξ 0
    rw [taylorCoeff_zero, taylorCoeff_zero] at h1
    have hW : HasDerivAt profW
        ((2 / d) * (profA ξ * profAbar ξ) * profB ξ +
          profA ξ * (-(2 / d) * (profB ξ * profBbar ξ))) ξ :=
      (hasDerivAt_profA ξ).mul (hasDerivAt_profB ξ)
    rw [h1, hW.deriv]
    have hA0 := H_pos ((ξ - a₀) / d)
    have hA1 := H_le_one ((ξ - a₀) / d)
    have hAb0 := H_pos ((a₀ - ξ) / d)
    have hAb1 := H_le_one ((a₀ - ξ) / d)
    have hB0 := H_pos (-ξ / d)
    have hB1 := H_le_one (-ξ / d)
    have hBb0 := H_pos (ξ / d)
    have hBb1 := H_le_one (ξ / d)
    simp only [hf', profA, profAbar, profB, profBbar]
    set A := H ((ξ - a₀) / d)
    set Ab := H ((a₀ - ξ) / d)
    set B := H (-ξ / d)
    set Bb := H (ξ / d)
    have hc : 0 < 2 / d := by positivity
    have e1 : 0 ≤ 2 / d * (A * Ab) * B := by positivity
    have e2 : 0 ≤ A * (2 / d * (B * Bb)) := by positivity
    have e3 : 2 / d * (A * Ab) * B ≤ 2 / d * (A * Ab) := by
      have : 0 ≤ 2 / d * (A * Ab) := by positivity
      nlinarith
    have e4 : A * (2 / d * (B * Bb)) ≤ 2 / d * (B * Bb) := by
      have : 0 ≤ 2 / d * (B * Bb) := by positivity
      nlinarith
    rw [abs_le]
    constructor <;> nlinarith
  calc ∫ ξ in ξa..ξb, |deriv (prof χ) ξ| ≤ ∫ ξ in ξa..ξb, f' ξ :=
        intervalIntegral.integral_mono_on apriori_ξa_le_ξb
          ((integrable_deriv_prof hχ).intervalIntegrable) (hf'c.intervalIntegrable _ _) hpt
    _ = (profA ξb - profB ξb) - (profA ξa - profB ξa) := hFTC
    _ ≤ 2 := by
      simp only [profA, profB]
      linarith [H_le_one ((ξb - a₀) / d), H_pos (-ξb / d), H_pos ((ξa - a₀) / d),
        H_le_one (-ξa / d)]

/-- `TV = ∫_ℝ |ϖ'| ≤ 2 + 6e^{-50}`. -/
theorem TV_le {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) : TV χ ≤ 2 + 6 * Real.exp (-50) := by
  have hint := integrable_deriv_prof hχ
  rw [apriori_TV_eq_intervalIntegral hχ,
    ← intervalIntegral.integral_add_adjacent_intervals (b := ξa) hint.intervalIntegrable
      hint.intervalIntegrable,
    ← intervalIntegral.integral_add_adjacent_intervals (a := ξa) (b := ξb)
      hint.intervalIntegrable hint.intervalIntegrable]
  linarith [endRegion_left_TV_interval hχ, endRegion_right_TV_interval hχ,
    apriori_TV_middle_le hχ]

/-- `TV / log 2 < 2.9`. -/
theorem TV_div_log_two_lt {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    TV χ / Real.log 2 < 29 / 10 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [div_lt_iff₀ hlog]
  linarith [TV_le hχ, apriori_exp_neg_fifty_lt, Real.log_two_gt_d9]

/-! ### Location of the zeros -/

-- The hypothesis `hG` of the interface statement is not needed in this proof.
set_option linter.unusedVariables false in
/-- A zero of `E_ℓ(·; G)` with `Re λ > 0` satisfies `|λ + iℓΩ_G(ξ)| ≤ TV/log 2` for some
`ξ ∈ [ξL, ξR]`. -/
theorem apriori_exists_xi {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) d) {z : ℂ} (hz : 0 < z.re) (h0 : evans χ ℓ z G = 0) :
    ∃ ξ ∈ Icc ξL ξR,
      ‖z + Complex.I * (ℓ : ℂ) * ((OmegaG χ G ξ : ℝ) : ℂ)‖ ≤ TV χ / Real.log 2 := by
  set D : ℝ → ℂ := fun ξ => z + Complex.I * (ℓ : ℂ) * ((OmegaG χ G ξ : ℝ) : ℂ) with hD
  have hDc : Continuous D := (contDiff_evansDenom hχ z ℓ G).continuous
  -- `μ = min_{[ξL, ξR]} |λ + iℓΩ_G|` is attained at `ξ₀`
  obtain ⟨ξ₀, hξ₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr apriori_ξL_lt_ξR.le) hDc.norm.continuousOn
  refine ⟨ξ₀, hξ₀, ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  set μ : ℝ := ‖D ξ₀‖ with hμ
  have hμpos : 0 < μ := lt_of_lt_of_le hz (re_le_norm_add_I_mul_ofReal z ℓ _)
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  set ε : ℝ := TV χ / μ with hε
  have hεlt : ε < Real.log 2 := by
    rw [hε, div_lt_iff₀ hμpos]
    rw [div_lt_iff₀ hlog] at hcon
    linarith
  -- the comparison estimate on `[ξL, ξR]` with the data `(1, ℓ)`
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hsol := evansSolution_spec χ hχ ℓ z hz G
  set ψ := (evansSolution χ ℓ z G).1 with hψ
  set ψ' := (evansSolution χ ℓ z G).2 with hψ'
  have hcast : ((ℓ : ℝ) : ℂ) = (ℓ : ℂ) := Complex.ofReal_natCast ℓ
  have hδint : ∫ t in ξL..ξR, ‖evansDelta χ ℓ z G t‖ / (ℓ : ℝ) ≤ ε := by
    have hint := integrable_deriv_prof hχ
    calc ∫ t in ξL..ξR, ‖evansDelta χ ℓ z G t‖ / (ℓ : ℝ)
        ≤ ∫ t in ξL..ξR, |deriv (prof χ) t| / μ := by
          refine intervalIntegral.integral_mono_on apriori_ξL_lt_ξR.le
            (((contDiff_evansDelta hχ ℓ hz G).continuous.norm.div_const _).intervalIntegrable
              _ _)
            ((hint.div_const μ).intervalIntegrable) fun t ht => ?_
          rw [norm_evansDelta_div hℓ]
          exact div_le_div_of_nonneg_left (abs_nonneg _) hμpos (isMinOn_iff.mp hmin t ht)
      _ = (∫ t in ξL..ξR, |deriv (prof χ) t|) / μ := intervalIntegral.integral_div _ _
      _ = ε := by rw [← apriori_TV_eq_intervalIntegral hχ]
  have hcmp := comparison_estimate hℓpos (α := ξL) (β := ξR) (ψ := ψ) (ψ' := ψ')
    (δ := evansDelta χ ℓ z G) hsol.hasDerivWithinAt
    (fun ξ hξ => by rw [hcast]; exact hsol.hasDerivWithinAt' ξ hξ)
    (contDiff_evansDelta hχ ℓ hz G).continuous.continuousOn hδint ξR
    ⟨apriori_ξL_lt_ξR.le, le_rfl⟩
  have h1 := cmpSol_one_ell hℓpos.ne' ξL ξR
  rw [hcast] at h1
  rw [hsol.init, hsol.init', h1.1, h1.2] at hcmp
  set E : ℝ := Real.exp (ℓ * (ξR - ξL)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hw0 : wnorm ℓ 1 (ℓ : ℂ) = ℓ := by simp [wnorm]
  rw [hw0] at hcmp
  -- `E_ℓ(λ; G) = 0` gives `ψ'(ξR) + ℓψ(ξR) = 0`
  have hsum : ψ' ξR + (ℓ : ℂ) * ψ ξR = 0 := by
    have h0' := h0
    unfold evans at h0'
    rcases mul_eq_zero.mp h0' with h | h
    · exact absurd h (by exact_mod_cast (Real.exp_pos _).ne')
    · exact h
  set u : ℂ := ψ ξR - ((E : ℝ) : ℂ) with hu
  set v : ℂ := ψ' ξR - (ℓ : ℂ) * ((E : ℝ) : ℂ) with hv
  have hkey : v + (ℓ : ℂ) * u = -(((2 * ℓ * E : ℝ)) : ℂ) := by
    rw [hu, hv]; push_cast; linear_combination hsum
  have hnorm : ‖v + (ℓ : ℂ) * u‖ = 2 * ℓ * E := by
    rw [hkey, norm_neg, Complex.norm_of_nonneg (by positivity)]
  have htri : ‖v + (ℓ : ℂ) * u‖ ≤ ‖v‖ + ℓ * ‖u‖ := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_natCast]
  have hm1 : (ℓ : ℝ) * ‖u‖ ≤ wnorm ℓ u v := le_max_left _ _
  have hm2 : ‖v‖ ≤ wnorm ℓ u v := le_max_right _ _
  have hineq : 2 * ℓ * E * 1 ≤ 2 * ℓ * E * (Real.exp ε - 1) := by nlinarith
  have hexp : 2 ≤ Real.exp ε := by
    have := le_of_mul_le_mul_left hineq (by positivity)
    linarith
  have := (Real.log_le_iff_le_exp two_pos).mpr hexp
  linarith

/-- **Lemma A.2**: `Re λ < 2.9` and `-ℓΩ_max - 2.9 < Im λ < 2.9` for every zero with
`Re λ > 0`. -/
theorem apriori_zero_bounds {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) d) {z : ℂ} (hz : 0 < z.re) (h0 : evans χ ℓ z G = 0) :
    z.re < 29 / 10 ∧ -(ℓ * OmegaMax) - 29 / 10 < z.im ∧ z.im < 29 / 10 := by
  obtain ⟨ξ, hξ, hnorm⟩ := apriori_exists_xi hχ hℓ hG hz h0
  have hTV := TV_div_log_two_lt hχ
  set Ω := OmegaG χ G ξ with hΩ
  have hre : (z + Complex.I * (ℓ : ℂ) * ((Ω : ℝ) : ℂ)).re = z.re :=
    re_add_I_mul_ofReal z ℓ Ω
  have him : (z + Complex.I * (ℓ : ℂ) * ((Ω : ℝ) : ℂ)).im = z.im + ℓ * Ω := by
    simp
  have h1 := Complex.abs_re_le_norm (z + Complex.I * (ℓ : ℂ) * ((Ω : ℝ) : ℂ))
  have h2 := Complex.abs_im_le_norm (z + Complex.I * (ℓ : ℂ) * ((Ω : ℝ) : ℂ))
  rw [hre] at h1
  rw [him] at h2
  have hΩ0 : 0 ≤ Ω := OmegaG_nonneg hχ hG.1 ξ
  have hΩmax : Ω ≤ OmegaMax := OmegaG_le_OmegaMax hχ hG hξ.1
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have hlΩ : (ℓ : ℝ) * Ω ≤ ℓ * OmegaMax := mul_le_mul_of_nonneg_left hΩmax hℓ0
  have hlΩ0 : 0 ≤ (ℓ : ℝ) * Ω := mul_nonneg hℓ0 hΩ0
  have hb1 := abs_le.mp (h1.trans hnorm)
  have hb2 := abs_le.mp (h2.trans hnorm)
  refine ⟨by linarith [hb1.2], by linarith [hb2.1], by linarith [hb2.2]⟩

/-- **Lemma A.2**, last assertion: every zero of `E_3(·; G)` with `Re λ ≥ 9/200` lies in
`[9/200, 2.9) × (-4.85, 2.9)`. -/
theorem apriori_zero_mem_RA {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) d) {z : ℂ} (hre : 9 / 200 ≤ z.re) (h0 : evans χ 3 z G = 0) :
    z.re < 29 / 10 ∧ -485 / 100 < z.im ∧ z.im < 29 / 10 := by
  have hz : 0 < z.re := by linarith
  obtain ⟨h1, h2, h3⟩ := apriori_zero_bounds hχ (by norm_num) hG hz h0
  have hΩ := OmegaMax_lt
  refine ⟨h1, ?_, h3⟩
  push_cast at h2
  linarith

end AppA

end NonUniqueEuler
