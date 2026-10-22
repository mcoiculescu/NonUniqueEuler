import NonUniqueEuler.Defs.Sec4.Eigendata
import NonUniqueEuler.H.Sec4.PropSemigroup.Basic
import NonUniqueEuler.H.Sec4.PropSemigroup.Sectors
import NonUniqueEuler.H.Sec4.PropSemigroup.Formulas
import NonUniqueEuler.I.Sec4.PropSU
import NonUniqueEuler.I.Sec4.PropU
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.SemigroupLaw
import NonUniqueEuler.I.Sec4.RingFacts

/-!
# Proof: `prop:semigroup` (uniform bounds for `e^{tL(G)}` on `X^s`)

Proof of `I/Sec4/PropSemigroup.lean` (same declarations, statements copied verbatim).
Manuscript `04_ring.tex:1430-1500`.

Structure (restructuring R2 of the I file):
* sector-wise bound `‖P_ℓ e^{tL}(1 - R)w‖ ≤ C e^{σ't}‖P_ℓ w‖` uniformly in `ℓ`, `G`, `t`, `w ∈ X^s`
  (`H/Sec4/PropSemigroup/Sectors.lean`: `exists_secProj_one_sub_bound`; large sectors by
  `prop:large-sectors`, `ℓ = ±3` by deflation and the uniform Dunford bound, using the continuity
  of the projections `I/Sec4/PropSemigroup/RieszCont.lean`), then the norm equivalence
  (`H/Sec4/PropSemigroup/Basic.lean`: `exists_norm_le_of_secProj_le`);
* `‖R(G)‖ ≤ C`: sector-wise, `R` acts by the rank-one projections `R_{±3}(G)`, bounded on
  `[0,G₁]` (continuity and compactness, `exists_rieszSec_bound`);
* `‖e^{tL}‖ ≤ C e^{σ(G)t}`: `e^{tL} = e^{tL}(1-R) + e^{tL}R`, `‖P_ℓ e^{tL}Rw‖ ≤ Ke^{σ(G)t}‖P_ℓ w‖`
  (`exp_mul_proj`), and `σ' < σ_b ≤ σ(G)` (`propU_a`);
* formulas: `ℓ_*(G)(e^{tL}w) = e^{λ_*t}ℓ_*(G)(w)` (`H/Sec4/PropSemigroup/Formulas.lean`: `ell_S`),
  and for real `w`, `e^{tL}Rw = R e^{tL}w` (`R_sector`) with `e^{tL}w` real (`semigroup_isReal`),
  so `R_of_isReal` gives `2Re(ℓ_*(G)(e^{tL}w)φ_*) = 2Re(ℓ_*(G)(w)e^{λ_*t}φ_*)`.
-/

noncomputable section

open MeasureTheory Set ComplexConjugate

namespace NonUniqueEuler

namespace Eig

open RingData Sect

/-- **`prop:semigroup`, the bounds** (`04_ring.tex:1433-1441`): for `s ≥ 0` and
`σ' ∈ (9/200, σ_b)` there is `C_S` such that for all `G ∈ [0,G₁]` and `t ≥ 0`, on `X^s`:
`‖e^{tL(G)}(1 - R(G))‖ ≤ C_S e^{σ't}`, `‖R(G)‖ ≤ C_S`, `‖e^{tL(G)}‖ ≤ C_S e^{σ(G)t}`. -/
theorem propSemigroup_bounds (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) (s : ℕ) {σ' : ℝ} (hσ' : σ' ∈ Ioo (9 / 200 : ℝ) (sigb χ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ G ∈ Icc (0 : ℝ) Gbar, ∀ t : ℝ, 0 ≤ t →
      (∀ w : Y s annN, Lin.MemX w →
        ‖Lin.S χ s G t (w - R χ s G w)‖ ≤ C * Real.exp (σ' * t) * ‖w‖) ∧
      (∀ w : Y s annN, Lin.MemX w → ‖R χ s G w‖ ≤ C * ‖w‖) ∧
      (∀ w : Y s annN, Lin.MemX w →
        ‖Lin.S χ s G t w‖ ≤ C * Real.exp (sigma χ G * t) * ‖w‖) := by
  have hS := ringPhiSetting_valid hχ
  obtain ⟨B, hB, hBnd⟩ := PropSemigroupH.exists_norm_le_of_secProj_le s hS.ρm_pos hS.ρm_lt_ρp
  obtain ⟨C₁, hC₁, h1⟩ := PropSemigroupH.exists_secProj_one_sub_bound hχ hN s hσ'.1
  obtain ⟨K, hK, hKG⟩ := PropSemigroupH.exists_rieszSec_bound hχ hN s
  obtain ⟨G₀, -, hsigb, hmin⟩ := (propU_a χ hχ hN).2.2.1
  refine ⟨B * C₁ + B * K + 1, by positivity, fun G hG t ht => ?_⟩
  have hfirst : ∀ w : Y s annN, Lin.MemX w →
      ‖Lin.S χ s G t (w - R χ s G w)‖ ≤ B * C₁ * Real.exp (σ' * t) * ‖w‖ := by
    intro w hw
    have h := hBnd (Lin.S χ s G t (w - R χ s G w)) w (C₁ * Real.exp (σ' * t)) (by positivity)
      (fun ℓ => h1 ℓ G hG t ht w hw)
    calc ‖Lin.S χ s G t (w - R χ s G w)‖ ≤ B * (C₁ * Real.exp (σ' * t)) * ‖w‖ := h
      _ = B * C₁ * Real.exp (σ' * t) * ‖w‖ := by ring
  have hRb : ∀ w : Y s annN, ‖R χ s G w‖ ≤ B * K * ‖w‖ := fun w =>
    hBnd _ w K hK fun ℓ => (PropSemigroupH.secProj_R_bounds hχ hN s hK hG (hKG G hG) ht w ℓ).1
  have hSR : ∀ w : Y s annN,
      ‖Lin.S χ s G t (R χ s G w)‖ ≤ B * K * Real.exp (sigma χ G * t) * ‖w‖ := by
    intro w
    have h := hBnd (Lin.S χ s G t (R χ s G w)) w (K * Real.exp (sigma χ G * t)) (by positivity)
      fun ℓ => (PropSemigroupH.secProj_R_bounds hχ hN s hK hG (hKG G hG) ht w ℓ).2
    calc ‖Lin.S χ s G t (R χ s G w)‖ ≤ B * (K * Real.exp (sigma χ G * t)) * ‖w‖ := h
      _ = B * K * Real.exp (sigma χ G * t) * ‖w‖ := by ring
  have hσle : σ' ≤ sigma χ G := by
    have := hmin G hG
    rw [← hsigb] at this
    linarith [hσ'.2]
  have hexp : Real.exp (σ' * t) ≤ Real.exp (sigma χ G * t) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hσle ht)
  have hBC : 0 ≤ B * C₁ := by positivity
  have hBK : 0 ≤ B * K := by positivity
  refine ⟨fun w hw => ?_, fun w _ => ?_, fun w hw => ?_⟩
  · refine (hfirst w hw).trans ?_
    have h0 : 0 ≤ Real.exp (σ' * t) * ‖w‖ := by positivity
    nlinarith
  · refine (hRb w).trans ?_
    have h0 : 0 ≤ ‖w‖ := norm_nonneg _
    nlinarith
  · have hsplit : Lin.S χ s G t w = Lin.S χ s G t (w - R χ s G w) + Lin.S χ s G t (R χ s G w) := by
      rw [← map_add, sub_add_cancel]
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have hA := hfirst w hw
    have hB2 := hSR w
    have hE : B * C₁ * Real.exp (σ' * t) * ‖w‖ ≤ B * C₁ * Real.exp (sigma χ G * t) * ‖w‖ := by
      have := mul_le_mul_of_nonneg_left hexp hBC
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have h0 : 0 ≤ Real.exp (sigma χ G * t) * ‖w‖ := by positivity
    nlinarith

/-- **`prop:semigroup`, the formulas** (`04_ring.tex:1442-1447`): for `G ∈ [0,G₁]` and `t ≥ 0`,
`e^{tL(G)}R(G)w = 2Re(ℓ_*(G)(w) e^{λ_*(G)t} φ_*(G))` for real `w ∈ X^s`, and
`ℓ_*(G)(e^{tL(G)}w) = e^{λ_*(G)t} ℓ_*(G)(w)` for `w ∈ X^s` (in particular `w ∈ X^0`). -/
theorem propSemigroup_formulas (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) (s : ℕ) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {t : ℝ}
    (ht : 0 ≤ t) :
    (∀ w : Y s annN, Lin.MemX w → w.IsReal →
      (Lin.S χ s G t (R χ s G w)).fn =ᵐ[volume]
        fun x => ((2 * (ell χ s G w * Complex.exp (lam χ G * (t : ℂ)) * phi χ G x).re : ℝ) : ℂ)) ∧
      ∀ w : Y s annN, Lin.MemX w →
        ell χ s G (Lin.S χ s G t w) = Complex.exp (lam χ G * (t : ℂ)) * ell χ s G w := by
  have hS := ringPhiSetting_valid hχ
  refine ⟨fun w _ hreal => ?_, fun w _ => PropSemigroupH.ell_S χ hχ hN hG s ht w⟩
  obtain ⟨-, -, -, -, hcomm⟩ := R_sector χ hχ hN hG s
  have hc : Lin.S χ s G t (R χ s G w) = R χ s G (Lin.S χ s G t w) :=
    congrArg (fun T : Y s annN →L[ℂ] Y s annN => T w) (hcomm t ht)
  have hr : (Lin.S χ s G t w).IsReal := SectorSetting.semigroup_isReal _ hS s G ht hreal
  rw [hc]
  filter_upwards [R_of_isReal χ hχ hN hG s hr] with x hx
  rw [hx, PropSemigroupH.ell_S χ hχ hN hG s ht w,
    mul_comm (Complex.exp (lam χ G * (t : ℂ))) (ell χ s G w)]

end Eig

end NonUniqueEuler
