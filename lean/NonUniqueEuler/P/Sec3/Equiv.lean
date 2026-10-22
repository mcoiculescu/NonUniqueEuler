import NonUniqueEuler.Defs.Sec3.Extra2Criterion
import NonUniqueEuler.I.Sec3.Criterion
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Order.Filter.ENNReal

/-!
# Proof of `I/Sec3/Equiv.lean`: `prop:equiv`, (d) ⇒ (a) and (a) ⇒ (e)

Manuscript: `prop:equiv`, `03_compactness.tex:1079-1097`, proof `03_compactness.tex:1099-1128`.

* (d) ⇒ (a) (`03_compactness.tex:1111-1112`): `|∫ g ψ| ≤ ‖ψ‖_{L^∞} ‖g‖_{L¹}` for every `n`, `t`
  (`pairing_le`), hence `defectPairing T ωs f ψ ≤ C · defectLp 1 T ωs f`
  (`defectPairing_le_mul_defectLp`) with `C = sup |ψ| < ∞`.
* (a) ⇒ (e) (`03_compactness.tex:1101-1103`): `thm:criterion` (`I/Sec3/Criterion.lean`), fields
  (i), the weak continuity, (iv) and (v) (`𝒪 ∩ (0, T] ≠ ∅`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact

open Weak

/-- `‖∫ g ψ‖ₑ ≤ C ‖g‖_{L¹}` for `|ψ| ≤ C` (also when `g ψ` is not integrable: then the
integral is `0`). -/
private theorem pairing_le {g ψ : ℂ → ℝ} {C : ℝ} (hC : ∀ x, ‖ψ x‖ ≤ C) :
    ‖∫ x, g x * ψ x‖ₑ ≤ ENNReal.ofReal C * eLpNorm g 1 volume := by
  calc ‖∫ x, g x * ψ x‖ₑ ≤ ∫⁻ x, ‖g x * ψ x‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, ENNReal.ofReal C * ‖g x‖ₑ := by
        refine lintegral_mono fun x => ?_
        rw [enorm_mul, mul_comm]
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hC x)
    _ = ENNReal.ofReal C * eLpNorm g 1 volume := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, eLpNorm_one_eq_lintegral_enorm]

/-- `defectPairing T ωs f ψ ≤ C · defectLp 1 T ωs f` for `|ψ| ≤ C`. -/
private theorem defectPairing_le_mul_defectLp {T : ℝ} {ωs : ℕ → ℝ → ℂ → ℝ} {f ψ : ℂ → ℝ} {C : ℝ}
    (hC : ∀ x, ‖ψ x‖ ≤ C) :
    defectPairing T ωs f ψ ≤ ENNReal.ofReal C * defectLp 1 T ωs f := by
  unfold defectPairing defectLp
  rw [← ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
  refine iSup₂_le fun t ht => ?_
  calc ‖∫ x, (ωs n t x - f x) * ψ x‖ₑ
      ≤ ENNReal.ofReal C * eLpNorm (fun x => ωs n t x - f x) 1 volume := pairing_le hC
    _ ≤ ENNReal.ofReal C * supDist 1 (Icc 0 T) (ωs n) (stationary f) := by
        gcongr
        exact eLpNorm_le_supDist (ω₁ := ωs n) (ω₂ := stationary f) ht

-- The hypotheses of `prop:equiv` other than (d) are not needed for this implication.
set_option linter.unusedVariables false in
/-- **`prop:equiv`, (d) ⇒ (a)** (`03_compactness.tex:1111-1112`): if some real `ψ ∈ C_c^∞(ℝ²)` has
`limsup_n sup_{t≤T} |∫ (ω⁽ⁿ⁾(t) - f) ψ| > 0`, then
`limsup_n sup_{t≤T} ‖ω⁽ⁿ⁾(t) - f‖_{L¹} > 0`. -/
theorem equiv_d_imp_a {T₀ : ℝ≥0∞} {T : ℝ} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ}
    {ωs : ℕ → ℝ → ℂ → ℝ} (hrad : IsRadial f) (hadm : IsAdmissibleSeq 2 T₀ f fs ωs)
    (hcont : ∀ n, IsWeakContL2On (timeInterval T₀) (ωs n))
    (hT : 0 < T) (hTT₀ : ENNReal.ofReal T < T₀) (hd : HasPairingDefect T ωs f) :
    0 < defectLp 1 T ωs f := by
  obtain ⟨ψ, hψ, hψc, hpos⟩ := hd
  obtain ⟨C, hC⟩ := hψc.exists_bound_of_continuous hψ.continuous
  have hle := defectPairing_le_mul_defectLp (T := T) (ωs := ωs) (f := f) hC
  refine pos_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero] at hle
  exact (lt_of_lt_of_le hpos hle).false

/-- **`prop:equiv`, (a) ⇒ (e)** (`03_compactness.tex:1101-1103`, from `thm:criterion`): if
`limsup_n sup_{t≤T} ‖ω⁽ⁿ⁾(t) - f‖_{L¹} > 0`, then some subsequence converges in the sense of
`thm:criterion`(iv) to a renormalized weak solution `ω_∞` on `[0, T₀)` with datum `f` such that
`ω_∞(t) ≠ f` for some `t ∈ (0, T]`. -/
theorem equiv_a_imp_e {T₀ : ℝ≥0∞} {T : ℝ} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ}
    {ωs : ℕ → ℝ → ℂ → ℝ} (hrad : IsRadial f) (hadm : IsAdmissibleSeq 2 T₀ f fs ωs)
    (hcont : ∀ n, IsWeakContL2On (timeInterval T₀) (ωs n))
    (hT : 0 < T) (hTT₀ : ENNReal.ofReal T < T₀) (ha : 0 < defectLp 1 T ωs f) :
    HasNonstationaryLimit T₀ T ωs f := by
  obtain ⟨φ, ωinf, h⟩ := criterion hrad hadm hcont hT hTT₀ ha
  obtain ⟨t, ⟨-, hne⟩, ht⟩ := h.departureSet_inter_nonempty
  exact ⟨φ, h.strictMono, ωinf, h.renormalized, h.weakCont, h.tendstoUnif, t, ht, hne⟩

end NonUniqueEuler.Compact
