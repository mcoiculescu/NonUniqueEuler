import NonUniqueEuler.Defs.Sec4.Operators
import Mathlib.Analysis.Normed.Algebra.Spectrum
import NonUniqueEuler.I.Sec4.LargeSectors
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition
import NonUniqueEuler.H.Sec4.SectorSum.Laplace

/-!
# Proof: `lem:sector-sum`(2) (the resolvent of the large sectors)

Proof of `I/Sec4/SectorSum.lean` (`04_ring.tex:1057-1060`, proof `:1087-1093`).

* `largeSectors_opNorm` (`prop:large-sectors` in the operator norm of `Y^s_ℓ`) gives `M ≥ 1`,
  `C₀ > 0` with `‖exp(tL_ℓ(G))‖ ≤ C₀ e^{γt}` for `|ℓ| ≥ M`, `|G| ≤ G₊`, `t ≥ 0`.
* The generic Laplace-transform lemma `SectorSumH.mem_resolventSet_and_norm_resolvent_le`
  (`H/Sec4/SectorSum/Laplace.lean`) gives `z ∈ resolventSet` and `‖(z - L_ℓ)⁻¹‖ ≤ C₀/(Re z - γ)`
  in the operator norm.
* The profile norm `‖·‖_{s,ℓ}` (`S.secNormY`) is equivalent to the norm of `Y^s_ℓ` uniformly in
  `ℓ` (`Sect.exists_norm_Ysec_equiv`), which converts the bound.

Deviation from the manuscript: none in substance. The manuscript bounds the Laplace integral
directly in `‖·‖_{s,ℓ}`; here it is bounded in the (equivalent, uniformly in `ℓ`) operator norm and
converted at the end, so the constant is `C₀ √C_eq/√c_eq` instead of `2C_s c_s(γ)`; the statement
has an existential constant (D11).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace SectorSetting

open Sect

/-- The profile norm `‖·‖_{s,ℓ}` and the norm of `Y^s_ℓ` are equivalent, uniformly in `ℓ`
(square roots of the constants of `Sect.exists_norm_Ysec_equiv`). -/
theorem exists_secNormY_equiv_norm (S : SectorSetting) (hS : S.Valid) (s : ℕ) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ (ℓ : ℤ) (g : Ysec s S.Nstar ℓ),
      a * S.secNormY s g ≤ ‖g‖ ∧ ‖g‖ ≤ b * S.secNormY s g := by
  obtain ⟨c, C, hc, hC, h⟩ := exists_norm_Ysec_equiv s hS.ρm_pos hS.ρm_lt_ρp
  refine ⟨Real.sqrt c, Real.sqrt C, Real.sqrt_pos.mpr hc, Real.sqrt_pos.mpr hC, fun ℓ g => ?_⟩
  obtain ⟨h1, h2⟩ := h ℓ g
  have hn : Real.sqrt (‖g‖ ^ 2) = ‖g‖ := Real.sqrt_sq (norm_nonneg g)
  constructor
  · calc Real.sqrt c * S.secNormY s g
        = Real.sqrt (c * Sob.secNormSq s ℓ (Icc S.ρm S.ρp) (Polar.angularSector g.fn ℓ)) := by
          rw [Real.sqrt_mul hc.le]; rfl
      _ ≤ Real.sqrt (‖g‖ ^ 2) := Real.sqrt_le_sqrt h1
      _ = ‖g‖ := hn
  · calc ‖g‖ = Real.sqrt (‖g‖ ^ 2) := hn.symm
      _ ≤ Real.sqrt (C * Sob.secNormSq s ℓ (Icc S.ρm S.ρp) (Polar.angularSector g.fn ℓ)) :=
          Real.sqrt_le_sqrt h2
      _ = Real.sqrt C * S.secNormY s g := by
          rw [Real.sqrt_mul hC.le]; rfl

/-- **`lem:sector-sum`(2)** (`04_ring.tex:1057-1060`): for `γ > 0`, `G₊ ≥ 0` there are `M_γ ≥ 1`
and `C` such that for `|ℓ| ≥ M_γ`, `|G| ≤ G₊` and `Re z > γ`, `z` lies in the resolvent set of
`L_ℓ(G)` on `Y^s_ℓ` and `‖(z - L_ℓ(G))⁻¹‖_{s,ℓ → s,ℓ} ≤ C/(Re z - γ)`. -/
theorem sectorSum2_resolvent (S : SectorSetting) (hS : S.Valid) (s : ℕ) {γ Gp : ℝ}
    (hγ : 0 < γ) (hGp : 0 ≤ Gp) :
    ∃ M C : ℝ, 1 ≤ M ∧ 0 < C ∧ ∀ ℓ : ℤ, M ≤ |(ℓ : ℝ)| → ∀ G : ℝ, |G| ≤ Gp →
      ∀ z : ℂ, γ < z.re →
        z ∈ resolventSet ℂ (S.Lsec s ℓ G) ∧
          ∀ g : Ysec s S.Nstar ℓ,
            S.secNormY s (resolvent (S.Lsec s ℓ G) z g) ≤ C / (z.re - γ) * S.secNormY s g := by
  obtain ⟨M, C₀, hM, hC₀, hexp⟩ := largeSectors_opNorm S hS s hγ hGp
  obtain ⟨a, b, ha, hb, hab⟩ := exists_secNormY_equiv_norm S hS s
  refine ⟨M, C₀ * b / a, hM, by positivity, fun ℓ hℓ G hG z hz => ?_⟩
  obtain ⟨hmem, hnorm⟩ :=
    SectorSumH.mem_resolventSet_and_norm_resolvent_le (S.Lsec s ℓ G) (hexp ℓ hℓ G hG) hz
  refine ⟨hmem, fun g => ?_⟩
  have hlam : 0 < z.re - γ := sub_pos.mpr hz
  set R := resolvent (S.Lsec s ℓ G) z with hR
  have h1 : a * S.secNormY s (R g) ≤ ‖R g‖ := (hab ℓ (R g)).1
  have h2 : ‖R g‖ ≤ ‖R‖ * ‖g‖ := R.le_opNorm g
  have h3 : ‖g‖ ≤ b * S.secNormY s g := (hab ℓ g).2
  have h4 : ‖R‖ * ‖g‖ ≤ C₀ / (z.re - γ) * (b * S.secNormY s g) :=
    mul_le_mul hnorm h3 (norm_nonneg g) (div_nonneg hC₀.le hlam.le)
  have h5 : a * (C₀ * b / a / (z.re - γ) * S.secNormY s g) =
      C₀ / (z.re - γ) * (b * S.secNormY s g) := by
    field_simp
  refine le_of_mul_le_mul_left ?_ ha
  rw [h5]
  exact h1.trans (h2.trans h4)

end SectorSetting

end NonUniqueEuler
