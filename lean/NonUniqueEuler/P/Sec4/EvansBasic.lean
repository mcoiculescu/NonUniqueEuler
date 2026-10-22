import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.Defs.Sec4.RingSetting
import NonUniqueEuler.I.Sec4.Sector
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Evans.ODE
import NonUniqueEuler.I.Infra.ODE.Existence
import NonUniqueEuler.I.Infra.ODE.Uniqueness
import NonUniqueEuler.I.Infra.ODE.Smooth
import NonUniqueEuler.I.Infra.ODE.Wronskian
import NonUniqueEuler.I.Infra.ODE.Param
import NonUniqueEuler.I.Infra.ODE.Holo
import NonUniqueEuler.H.Sec4.EvansBasic.HalfLine
import NonUniqueEuler.H.Sec4.EvansBasic.RefUnits

/-!
# Proof: `def:evans` (the solution `ψ_ℓ`) and `lem:evans-basic`

Proof of `NonUniqueEuler/I/Sec4/EvansBasic.lean` (`04_ring.tex:187-198`, `:285-352`). Same
declarations, statements copied verbatim.

Method (following the manuscript).
* `V_ℓ` is smooth in `ξ` and equal to `ℓ²` outside `[ξ₁, ξ₂]` (`sector_riccati`), hence, by
  continuity, on `(-∞, ξ₁]` and `[ξ₂, ∞)` (`EvansBasicH.vric_facts`). The global solution
  `LinODE.sol` exists (`sol_spec`) and is smooth (`IsSolOn.contDiff`); on `(-∞, ξ₁]` it is
  `e^{ℓ(ξ-ξ₁)}` by uniqueness (`EvansBasicH.sol_left`).
* (1) Holomorphy and joint continuity come from I-ODE `differentiableOn_sol`, `continuousOn_sol`
  (the manuscript's Picard-iterate argument is the content of those interface lemmas).
* (2) `eq:evans-coef` from `exists_eq_exp_add_exp` on `[ξ₂, ∞)` (`EvansBasicH.right_coef`).
  Independence of `(ξ₁, ξ₂)`: `EvansBasicH.evans_val_indep`. Instead of the smallest interval
  `[α, β₀]` containing `supp f_ξ` used in the manuscript, we compare the solutions `ψ_L` of the
  two normalizations at `min ξ₁ ξ₁'` and the quantity `e^{-ℓξ}(ψ_L' + ℓψ_L) = 2ℓA₊` on
  `[min ξ₂ ξ₂', ∞)` (same argument, no need to define the minimal interval; the case
  `ω̄' ≡ 0` needs no separate treatment).
* (3) `W' = 0` (`wronskian_eq`), evaluated at `ξ₂`.
* Last assertion: `f_ξ = ϖ'` (chain rule), `Ω(e^ξ;G) = Ω_G(ξ)` (`circ_comp_norm` and the
  substitution `ρ = e^{ξ'}`), so `V_ℓ = riccatiCoeff`; conclude with
  `evans_eq_of_isEvansSolution`.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace NonUniqueEuler

namespace SectorSetting

/-- The Riccati coefficient of a valid sector setting for `Re λ > 0`: smooth, and equal to `ℓ²`
on `(-∞, ξ₁]` and on `[ξ₂, ∞)` (`lem:sector`(3) plus continuity at `ξ₁`, `ξ₂`). -/
theorem EvansBasicH.vric_facts (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (z : ℂ) (hz : 0 < z.re) (G : ℝ) :
    ContDiff ℝ ∞ (S.Vric ℓ z G) ∧ Continuous (S.Vric ℓ z G) ∧
      (∀ ξ, ξ ≤ S.ξ₁ → S.Vric ℓ z G ξ = (ℓ : ℂ) ^ 2) ∧
      (∀ ξ, S.ξ₂ ≤ ξ → S.Vric ℓ z G ξ = (ℓ : ℂ) ^ 2) := by
  obtain ⟨-, hsm, -, -, hout⟩ := sector_riccati S hS ℓ hℓ G
  have hsm' : ContDiff ℝ ∞ (S.Vric ℓ z G) := hsm z hz
  have hc : Continuous (S.Vric ℓ z G) := hsm'.continuous
  refine ⟨hsm', hc, ?_, ?_⟩
  · exact NonUniqueEuler.EvansBasicH.eq_of_le_of_lt hc
      (fun ξ hξ => hout z ξ (fun h => (not_le.2 hξ) h.1))
  · exact NonUniqueEuler.EvansBasicH.eq_of_ge_of_gt hc
      (fun ξ hξ => hout z ξ (fun h => (not_le.2 hξ) h.2))

/-! ### `def:evans`: the solution `ψ_ℓ` -/

/-- `def:evans` (`04_ring.tex:189-191`): `(ψ_ℓ, ψ_ℓ')` is a smooth solution on `ℝ` of
`ψ'' = V_ℓ(·;λ,G) ψ` with `ψ(ξ₁) = 1`, `ψ'(ξ₁) = ℓ`; and `ψ_ℓ = e^{ℓ(ξ-ξ₁)}` on `(-∞, ξ₁]`
(`04_ring.tex:305-306`). -/
theorem psi_spec (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) :
    LinODE.IsSolOn (S.Vric ℓ z G) univ (S.psi ℓ z G) (S.dpsi ℓ z G) ∧
      S.psi ℓ z G S.ξ₁ = 1 ∧ S.dpsi ℓ z G S.ξ₁ = (ℓ : ℂ) ∧
      ContDiff ℝ ∞ (S.psi ℓ z G) ∧ deriv (S.psi ℓ z G) = S.dpsi ℓ z G ∧
      ∀ ξ : ℝ, ξ ≤ S.ξ₁ →
        S.psi ℓ z G ξ = ((Real.exp (ℓ * (ξ - S.ξ₁)) : ℝ) : ℂ) ∧
          S.dpsi ℓ z G ξ = (ℓ : ℂ) * ((Real.exp (ℓ * (ξ - S.ξ₁)) : ℝ) : ℂ) := by
  obtain ⟨hsm, hc, hL, -⟩ := EvansBasicH.vric_facts S hS ℓ hℓ z hz G
  obtain ⟨hsol, h0⟩ := LinODE.sol_spec hc S.ξ₁ (1, (ℓ : ℂ))
  have hsol' : LinODE.IsSolOn (S.Vric ℓ z G) univ (S.psi ℓ z G) (S.dpsi ℓ z G) := hsol
  obtain ⟨hcd, -, hder, -⟩ := LinODE.IsSolOn.contDiff hsm hsol'
  refine ⟨hsol', ?_, ?_, hcd, hder, ?_⟩
  · show (LinODE.sol (S.Vric ℓ z G) S.ξ₁ (1, (ℓ : ℂ)) S.ξ₁).1 = 1
    rw [h0]
  · show (LinODE.sol (S.Vric ℓ z G) S.ξ₁ (1, (ℓ : ℂ)) S.ξ₁).2 = (ℓ : ℂ)
    rw [h0]
  · intro ξ hξ
    exact NonUniqueEuler.EvansBasicH.sol_left hc ℓ le_rfl hL ξ hξ

/-! ### `lem:evans-basic`(1): holomorphy -/

/-- `lem:evans-basic`(1): `ψ_ℓ(ξ;λ,G)` and its `ξ`-derivative are holomorphic in
`λ ∈ {Re λ > 0}`, locally uniformly in `ξ` (holomorphic for each `ξ`, jointly continuous in
`(ξ, λ)`); the same holds for `ψ_R` (`04_ring.tex:319-320`); and `E_ℓ(·;G)` is holomorphic on
`{Re λ > 0}`. -/
theorem evans_basic_holo (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (G : ℝ) :
    (∀ ξ : ℝ,
        DifferentiableOn ℂ (fun z => S.psi ℓ z G ξ) {z : ℂ | 0 < z.re} ∧
          DifferentiableOn ℂ (fun z => S.dpsi ℓ z G ξ) {z : ℂ | 0 < z.re} ∧
          DifferentiableOn ℂ (fun z => S.psiR ℓ z G ξ) {z : ℂ | 0 < z.re} ∧
          DifferentiableOn ℂ (fun z => S.dpsiR ℓ z G ξ) {z : ℂ | 0 < z.re}) ∧
      ContinuousOn (fun p : ℝ × ℂ => S.psi ℓ p.2 G p.1) (univ ×ˢ {z : ℂ | 0 < z.re}) ∧
      ContinuousOn (fun p : ℝ × ℂ => S.dpsi ℓ p.2 G p.1) (univ ×ˢ {z : ℂ | 0 < z.re}) ∧
      ContinuousOn (fun p : ℝ × ℂ => S.psiR ℓ p.2 G p.1) (univ ×ˢ {z : ℂ | 0 < z.re}) ∧
      ContinuousOn (fun p : ℝ × ℂ => S.dpsiR ℓ p.2 G p.1) (univ ×ˢ {z : ℂ | 0 < z.re}) ∧
      DifferentiableOn ℂ (fun z => S.evans ℓ z G) {z : ℂ | 0 < z.re} := by
  obtain ⟨-, -, hd, hcont, -⟩ := sector_riccati S hS ℓ hℓ G
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hV : ContinuousOn (Function.uncurry fun ξ z => S.Vric ℓ z G ξ)
      (univ ×ˢ {z : ℂ | 0 < z.re}) := hcont
  set yR : ℂ × ℂ := (((Real.exp (-(ℓ : ℝ) * S.ξ₂) : ℝ) : ℂ),
    -(ℓ : ℂ) * ((Real.exp (-(ℓ : ℝ) * S.ξ₂) : ℝ) : ℂ)) with hyR
  have hpsi : ∀ ξ : ℝ, DifferentiableOn ℂ
      (fun z => LinODE.sol (S.Vric ℓ z G) S.ξ₁ (1, (ℓ : ℂ)) ξ) {z : ℂ | 0 < z.re} :=
    fun ξ => LinODE.differentiableOn_sol (V := fun ξ z => S.Vric ℓ z G ξ) hU hV hd S.ξ₁
      (1, (ℓ : ℂ)) ξ
  have hpsiR : ∀ ξ : ℝ, DifferentiableOn ℂ
      (fun z => LinODE.sol (S.Vric ℓ z G) S.ξ₂ yR ξ) {z : ℂ | 0 < z.re} :=
    fun ξ => LinODE.differentiableOn_sol (V := fun ξ z => S.Vric ℓ z G ξ) hU hV hd S.ξ₂ yR ξ
  have cpsi := LinODE.continuousOn_sol (V := fun ξ z => S.Vric ℓ z G ξ) hV S.ξ₁
    (y₀ := fun _ => (1, (ℓ : ℂ))) continuousOn_const
  have cpsiR := LinODE.continuousOn_sol (V := fun ξ z => S.Vric ℓ z G ξ) hV S.ξ₂
    (y₀ := fun _ => yR) continuousOn_const
  refine ⟨fun ξ => ⟨(hpsi ξ).fst, (hpsi ξ).snd, (hpsiR ξ).fst, (hpsiR ξ).snd⟩,
    continuous_fst.comp_continuousOn cpsi, continuous_snd.comp_continuousOn cpsi,
    continuous_fst.comp_continuousOn cpsiR, continuous_snd.comp_continuousOn cpsiR, ?_⟩
  show DifferentiableOn ℂ (fun z => ((Real.exp (-(ℓ : ℝ) * (S.ξ₂ - S.ξ₁)) : ℝ) : ℂ) *
    (S.dpsi ℓ z G S.ξ₂ + (ℓ : ℂ) * S.psi ℓ z G S.ξ₂)) {z : ℂ | 0 < z.re}
  exact ((hpsi S.ξ₂).snd.add ((hpsi S.ξ₂).fst.const_mul _)).const_mul _

/-! ### `lem:evans-basic`(2) and `eq:evans-coef` -/

/-- `eq:evans-coef` (`04_ring.tex:325-333`): on `[ξ₂, ∞)`, `ψ_ℓ = A₊e^{ℓξ} + A₋e^{-ℓξ}`, and
`E_ℓ(λ;G) = 2ℓ e^{ℓξ₁} A₊`. -/
theorem evans_coef (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) :
    ∃ Ap Am : ℂ,
      (∀ ξ : ℝ, S.ξ₂ ≤ ξ →
        S.psi ℓ z G ξ = Ap * ((Real.exp (ℓ * ξ) : ℝ) : ℂ) + Am * ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ)) ∧
        S.evans ℓ z G = 2 * (ℓ : ℂ) * ((Real.exp (ℓ * S.ξ₁) : ℝ) : ℂ) * Ap := by
  obtain ⟨-, -, -, hR⟩ := EvansBasicH.vric_facts S hS ℓ hℓ z hz G
  obtain ⟨hsol, -⟩ := psi_spec S hS ℓ hℓ z hz G
  have hℓ0 : ℓ ≠ 0 := by omega
  obtain ⟨A, B, hAB⟩ := NonUniqueEuler.EvansBasicH.right_coef hℓ0 hR (hsol.mono (subset_univ _))
  refine ⟨A, B, fun ξ hξ => (hAB ξ hξ).1, ?_⟩
  have k := (hAB S.ξ₂ le_rfl).2.2
  have e : ((Real.exp (-(ℓ : ℝ) * (S.ξ₂ - S.ξ₁)) : ℝ) : ℂ) =
      ((Real.exp (ℓ * S.ξ₁) : ℝ) : ℂ) * ((Real.exp (-(ℓ * S.ξ₂)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [evans_def, e]
  linear_combination ((Real.exp (ℓ * S.ξ₁) : ℝ) : ℂ) * k

/-- `lem:evans-basic`(2): `E_ℓ(λ;G)` does not change if `(ξ₁, ξ₂)` is replaced by any pair
`(log r₁', log r₂')` with `supp ω̄' ⊆ [r₁', r₂']` (the radii `ρ₋, ρ₊` do not enter `E_ℓ`). -/
theorem evans_indep (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) {r₁' r₂' : ℝ} (h₁ : 0 < r₁') (h₁₂ : r₁' ≤ r₂')
    (hsupp : ∀ r : ℝ, 0 < r → r ∉ Icc r₁' r₂' → S.dom r = 0) :
    ({ S with r₁ := r₁', r₂ := r₂' } : SectorSetting).evans ℓ z G = S.evans ℓ z G := by
  obtain ⟨-, hc, hL, hR⟩ := EvansBasicH.vric_facts S hS ℓ hℓ z hz G
  have hℓ0 : ℓ ≠ 0 := by omega
  have h₂ : 0 < r₂' := h₁.trans_le h₁₂
  have hfx : ∀ ξ, S.dom (Real.exp ξ) = 0 → S.Vric ℓ z G ξ = (ℓ : ℂ) ^ 2 := by
    intro ξ h
    simp [Vric, fxi, h]
  have hL' : ∀ ξ, ξ ≤ Real.log r₁' → S.Vric ℓ z G ξ = (ℓ : ℂ) ^ 2 :=
    NonUniqueEuler.EvansBasicH.eq_of_le_of_lt hc (fun ξ hξ => hfx ξ
      (hsupp _ (Real.exp_pos ξ) (fun h => (not_le.2 ((Real.lt_log_iff_exp_lt h₁).1 hξ)) h.1)))
  have hR' : ∀ ξ, Real.log r₂' ≤ ξ → S.Vric ℓ z G ξ = (ℓ : ℂ) ^ 2 :=
    NonUniqueEuler.EvansBasicH.eq_of_ge_of_gt hc (fun ξ hξ => hfx ξ
      (hsupp _ (Real.exp_pos ξ) (fun h => (not_le.2 ((Real.log_lt_iff_lt_exp h₂).1 hξ)) h.2)))
  exact NonUniqueEuler.EvansBasicH.evans_val_indep hc hℓ0 hL' hL hR' hR

/-! ### `lem:evans-basic`(3): `ψ_L`, `ψ_R` and the Wronskian -/

/-- `lem:evans-basic`(3): `ψ_R` is a smooth solution on `ℝ` of `ψ'' = V_ℓ ψ` with
`ψ_R(ξ) = e^{-ℓξ}` for `ξ ≥ ξ₂`. -/
theorem psiR_spec (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) :
    LinODE.IsSolOn (S.Vric ℓ z G) univ (S.psiR ℓ z G) (S.dpsiR ℓ z G) ∧
      ContDiff ℝ ∞ (S.psiR ℓ z G) ∧ deriv (S.psiR ℓ z G) = S.dpsiR ℓ z G ∧
      ∀ ξ : ℝ, S.ξ₂ ≤ ξ →
        S.psiR ℓ z G ξ = ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ) ∧
          S.dpsiR ℓ z G ξ = -(ℓ : ℂ) * ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ) := by
  obtain ⟨hsm, hc, -, hR⟩ := EvansBasicH.vric_facts S hS ℓ hℓ z hz G
  obtain ⟨hsol, h0⟩ := LinODE.sol_spec hc S.ξ₂
    (((Real.exp (-(ℓ : ℝ) * S.ξ₂) : ℝ) : ℂ), -(ℓ : ℂ) * ((Real.exp (-(ℓ : ℝ) * S.ξ₂) : ℝ) : ℂ))
  have hsol' : LinODE.IsSolOn (S.Vric ℓ z G) univ (S.psiR ℓ z G) (S.dpsiR ℓ z G) := hsol
  obtain ⟨hcd, -, hder, -⟩ := LinODE.IsSolOn.contDiff hsm hsol'
  refine ⟨hsol', hcd, hder, ?_⟩
  have hexp := NonUniqueEuler.EvansBasicH.isSolOn_ofReal_exp (V := S.Vric ℓ z G)
    (s := Ici S.ξ₂) (NonUniqueEuler.EvansBasicH.hasDerivAt_neg_mul (ℓ : ℝ))
    (fun ξ hξ => by rw [hR ξ hξ]; push_cast; ring)
  have h0₁ : S.psiR ℓ z G S.ξ₂ = ((Real.exp (-(ℓ : ℝ) * S.ξ₂) : ℝ) : ℂ) := by
    show (LinODE.sol _ S.ξ₂ _ S.ξ₂).1 = _
    rw [h0]
  have h0₂ : S.dpsiR ℓ z G S.ξ₂ = -(ℓ : ℂ) * ((Real.exp (-(ℓ : ℝ) * S.ξ₂) : ℝ) : ℂ) := by
    show (LinODE.sol _ S.ξ₂ _ S.ξ₂).2 = _
    rw [h0]
  have key := LinODE.IsSolOn.eqOn ordConnected_Ici hc.continuousOn
    (hsol'.mono (subset_univ _)) hexp self_mem_Ici
    (by rw [h0₁, neg_mul]) (by rw [h0₂, neg_mul]; push_cast; ring_nf)
  intro ξ hξ
  refine ⟨key.1 (show ξ ∈ Ici S.ξ₂ from hξ), ?_⟩
  rw [key.2 (show ξ ∈ Ici S.ξ₂ from hξ)]
  push_cast
  ring

/-- `lem:evans-basic`(3): `ψ_L = e^{ℓξ₁}ψ_ℓ` equals `e^{ℓξ}` for `ξ ≤ ξ₁`, and the Wronskian
`W = ψ_Lψ_R' - ψ_L'ψ_R` is independent of `ξ` and equals `-E_ℓ(λ;G)`. -/
theorem wronskian_eq_neg_evans (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (z : ℂ) (hz : 0 < z.re) (G : ℝ) :
    (∀ ξ : ℝ, ξ ≤ S.ξ₁ → S.psiL ℓ z G ξ = ((Real.exp (ℓ * ξ) : ℝ) : ℂ)) ∧
      ∀ ξ : ℝ, S.wrFn ℓ z G ξ = -S.evans ℓ z G := by
  obtain ⟨hsolL, -, -, -, -, hleft⟩ := psi_spec S hS ℓ hℓ z hz G
  obtain ⟨hsolR, -, -, hright⟩ := psiR_spec S hS ℓ hℓ z hz G
  refine ⟨fun ξ hξ => ?_, fun ξ => ?_⟩
  · rw [psiL, (hleft ξ hξ).1, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  · have hL := hsolL.const_mul ((Real.exp (ℓ * S.ξ₁) : ℝ) : ℂ)
    have hW := LinODE.wronskian_eq ordConnected_univ hL hsolR ξ (mem_univ _) S.ξ₂ (mem_univ _)
    have hW' : S.wrFn ℓ z G ξ = S.wrFn ℓ z G S.ξ₂ := hW
    rw [hW']
    obtain ⟨hR1, hR2⟩ := hright S.ξ₂ le_rfl
    simp only [wrFn, LinODE.wronskian, psiL, dpsiL, evans_def]
    rw [hR1, hR2]
    have e : ((Real.exp (ℓ * S.ξ₁) : ℝ) : ℂ) * ((Real.exp (-(ℓ * S.ξ₂)) : ℝ) : ℂ) =
        ((Real.exp (-(ℓ : ℝ) * (S.ξ₂ - S.ξ₁)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    linear_combination (-(S.dpsi ℓ z G S.ξ₂ + (ℓ : ℂ) * S.psi ℓ z G S.ξ₂)) * e

end SectorSetting

/-! ### `lem:evans-basic`, last assertion: the ring in reference units -/

open RingData

/-- Proof of `lem:evans-basic`, last assertion (`04_ring.tex:347-349`): for the ring in reference
units, `f_ξ = ϖ'`. -/
theorem ringRefSetting_fxi {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) :
    (ringRefSetting χ).fxi ξ = deriv (prof χ) ξ := by
  rw [SectorSetting.fxi, EvansBasicH.ringRefSetting_dom hχ (Real.exp_pos ξ), Real.log_exp,
    mul_left_comm, mul_inv_cancel₀ (Real.exp_ne_zero ξ), mul_one]

/-- Proof of `lem:evans-basic`, last assertion (`04_ring.tex:348-350`):
`Ω(e^ξ;G) = Ω_G(ξ)` for the ring in reference units. -/
theorem ringRefSetting_Omega {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (G ξ : ℝ) :
    (ringRefSetting χ).Omega G (Real.exp ξ) = OmegaG χ G ξ := by
  rw [SectorSetting.Omega, ringRefSetting_om, EvansBasicH.circ_ringRef_exp, OmegaG]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have he : (Real.exp ξ ^ 2)⁻¹ = Real.exp (-2 * ξ) := by
    rw [show -2 * ξ = -(ξ + ξ) by ring, Real.exp_neg, Real.exp_add, sq]
  rw [he, mul_div_cancel_left₀ _ hπ, add_comm]

/-- The Riccati coefficient of the ring in reference units is the statement layer's
`riccatiCoeff` (`04_ring.tex:350-352`). -/
theorem ringRefSetting_Vric {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) (z : ℂ)
    (G ξ : ℝ) : (ringRefSetting χ).Vric ℓ z G ξ = riccatiCoeff χ ℓ z G ξ := by
  rw [SectorSetting.Vric, ringRefSetting_fxi hχ, ringRefSetting_Omega hχ, riccatiCoeff]

/-- `lem:evans-basic`, last assertion (`04_ring.tex:300-302`): for the ring in reference units
(`ω̄ = ω̄_c`, `(ξ₁,ξ₂) = (ξL, ξR)`), the Evans function of `def:evans` is the function `E_ℓ` of
Hypothesis (N) (the statement layer's `evans`). -/
theorem ringRefSetting_evans {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (z : ℂ) (hz : 0 < z.re) (G : ℝ) : (ringRefSetting χ).evans ℓ z G = evans χ ℓ z G := by
  have hS := ringRefSetting_valid hχ
  obtain ⟨hsol, h1, h1', -⟩ := SectorSetting.psi_spec (ringRefSetting χ) hS ℓ hℓ z hz G
  have hV : ∀ ξ, (ringRefSetting χ).Vric ℓ z G ξ = riccatiCoeff χ ℓ z G ξ :=
    ringRefSetting_Vric hχ ℓ z G
  have hξ₁ := ringRefSetting_ξ₁ χ
  have hξ₂ := ringRefSetting_ξ₂ χ
  have hE : IsEvansSolution χ ℓ z G ((ringRefSetting χ).psi ℓ z G)
      ((ringRefSetting χ).dpsi ℓ z G) := by
    refine ⟨fun ξ _ => (hsol.hasDerivWithinAt ξ (mem_univ ξ)).mono (subset_univ _),
      fun ξ _ => ?_, ?_, ?_⟩
    · rw [← hV ξ]
      exact (hsol.hasDerivWithinAt' ξ (mem_univ ξ)).mono (subset_univ _)
    · rw [← hξ₁]
      exact h1
    · rw [← hξ₁]
      exact h1'
  rw [evans_eq_of_isEvansSolution χ hχ ℓ z hz G hE, SectorSetting.evans_def, hξ₁, hξ₂]

end NonUniqueEuler
