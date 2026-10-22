import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.H.Sec4.EvansSimple.GenEigen.Basic
import NonUniqueEuler.I.Sec4.EvansBasic
import NonUniqueEuler.I.Sec4.Resolvent.Reduction
import NonUniqueEuler.I.Infra.ODE.Existence
import NonUniqueEuler.I.Infra.ODE.Explicit
import NonUniqueEuler.I.Infra.ODE.Smooth
import NonUniqueEuler.I.Infra.ODE.Uniqueness
import NonUniqueEuler.I.Infra.ODE.Wronskian

/-!
# Proof: the generalized eigenprofile `g₁` when `J = 0` (step of `thm:evans-simple`(3))

Proof of `I/Sec4/EvansSimple/GenEigen.lean` (`04_ring.tex:536-555`).

Let `F_* = -e^{2ξ} M_*(e^ξ) g_*(e^ξ)` (`S.Fres ℓ z G (-g_*)`), smooth on `ℝ` and vanishing when
`e^ξ ∉ [r₁,r₂]`. Let `ψ` be the global solution of `ψ'' = V_ℓψ + F_*` with
`ψ(ξ₁-1) = ψ'(ξ₁-1) = 0` (`exists_isInhomSolOn_univ`); it vanishes on `(-∞, ξ₁-1]` (uniqueness,
`F_* = 0` there). On `[ξ₂+1, ∞)`, `V_ℓ = ℓ²` and `F_* = 0`, so `ψ = A e^{ℓξ} + B e^{-ℓξ}`, and
`ψ_* = B₁ e^{-ℓξ}` with `B₁ ≠ 0` (`E_ℓ = 0`; `psi_right`). The Wronskian identity
(`wronskian_sub_eq_integral`) gives `W(ψ_*, ψ)(ξ₂+1) = ∫ ψ_* F_* = -J = 0`, and
`W(ψ_*, ψ) = 2ℓB₁A` there, so `A = 0`. Then `g₁ = M_*(-g_* + k_ℓ ψ(log r))` satisfies
`𝒢_ℓ g₁ = ψ(log r)` (`green_eq_of_bvp`), whence `L_ℓ g₁ - λ_* g₁ = g_*` pointwise.

**Deviation.** The manuscript writes `ψ` by the variation-of-constants formula with a second
solution `φ₂`; here `ψ` is the solution with zero data at `ξ₁ - 1`, which is the same function
(both solve the equation and vanish to the left of `ξ₁`), and the condition at `+∞` is read off
from the Wronskian of `ψ_*` and `ψ` instead of the coefficient of `φ₂`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler

namespace GenEigenAux

open SectorSetting LinODE

/-- At a zero of `E_ℓ`: on `[ξ₂, ∞)`, `ψ_* = B₁ e^{-ℓξ}` and `ψ_*' = -ℓ B₁ e^{-ℓξ}` with
`B₁ ≠ 0` (`04_ring.tex:544-545`). -/
theorem psi_right (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) :
    ∃ B₁ : ℂ, B₁ ≠ 0 ∧ ∀ ξ : ℝ, S.ξ₂ ≤ ξ →
      S.psi ℓ z G ξ = B₁ * Complex.exp (-((ℓ : ℂ) * ξ)) ∧
        S.dpsi ℓ z G ξ = -(ℓ : ℂ) * (B₁ * Complex.exp (-((ℓ : ℂ) * ξ))) := by
  obtain ⟨hsol, h1, -, -, -, -⟩ := psi_spec S hS ℓ hℓ z hz G
  have hVc : Continuous (S.Vric ℓ z G) := ((sector_riccati S hS ℓ hℓ G).2.1 z hz).continuous
  have hV2 : ∀ ξ ∈ Ici S.ξ₂, S.Vric ℓ z G ξ = (ℓ : ℂ) ^ 2 := by
    have hcl : IsClosed {ξ | S.Vric ℓ z G ξ = (ℓ : ℂ) ^ 2} := isClosed_eq hVc continuous_const
    have hsub : Ioi S.ξ₂ ⊆ {ξ | S.Vric ℓ z G ξ = (ℓ : ℂ) ^ 2} := fun ξ hξ =>
      (sector_riccati S hS ℓ hℓ G).2.2.2.2 z ξ fun h => absurd h.2 (not_le.2 hξ)
    intro ξ hξ
    rw [← closure_Ioi] at hξ
    exact hcl.closure_subset_iff.2 hsub hξ
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  obtain ⟨A₁, B₁, hAB⟩ :=
    exists_eq_exp_add_exp ordConnected_Ici hℓ0 hV2 (hsol.mono (subset_univ _))
  have hA₁ : A₁ = 0 := by
    have h := hAB S.ξ₂ self_mem_Ici
    rw [evans_def, h.1, h.2] at hE
    have hx : ((Real.exp (-(ℓ : ℝ) * (S.ξ₂ - S.ξ₁)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
    have he : Complex.exp ((ℓ : ℂ) * S.ξ₂) ≠ 0 := Complex.exp_ne_zero _
    have h2 : 2 * (ℓ : ℂ) * Complex.exp ((ℓ : ℂ) * S.ξ₂) * A₁ = 0 := by
      have := (mul_eq_zero.1 hE).resolve_left hx
      linear_combination this
    exact (mul_eq_zero.1 h2).resolve_left (mul_ne_zero (mul_ne_zero two_ne_zero hℓ0) he)
  refine ⟨B₁, ?_, fun ξ hξ => ?_⟩
  · rintro rfl
    have h := hAB S.ξ₂ self_mem_Ici
    rw [hA₁] at h
    simp only [zero_mul, add_zero, sub_zero, mul_zero] at h
    have hz0 := IsSolOn.eqOn_zero ordConnected_univ hVc.continuousOn hsol (mem_univ S.ξ₂) h.1 h.2
    have h3 : S.psi ℓ z G S.ξ₁ = 0 := hz0.1 (mem_univ S.ξ₁)
    rw [h1] at h3
    exact one_ne_zero h3
  · have h := hAB ξ hξ
    rw [hA₁] at h
    constructor
    · rw [h.1]
      ring
    · rw [h.2]
      ring

/-- **The boundary value problem at `J = 0`** (`04_ring.tex:536-551`): there is a smooth
solution `ψ` of `ψ'' = V_ℓψ + F_*` on `ℝ` that vanishes on `(-∞, ξ₁ - 1]` and is a multiple of
`e^{-ℓξ}` on `[ξ₂ + 1, ∞)`. -/
theorem exists_bvp (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) (hJ : S.J ℓ z G = 0) :
    ∃ φ φ' : ℝ → ℂ,
      IsInhomSolOn (S.Vric ℓ z G) (S.Fres ℓ z G (fun r => -S.gStar ℓ z G r)) univ φ φ' ∧
        ContDiff ℝ ∞ φ ∧ (∀ ξ : ℝ, ξ ≤ S.ξ₁ - 1 → φ ξ = 0) ∧
        ∃ B : ℂ, ∀ ξ : ℝ, S.ξ₂ + 1 ≤ ξ → φ ξ = B * ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ) := by
  have hVs : ContDiff ℝ ∞ (S.Vric ℓ z G) := (sector_riccati S hS ℓ hℓ G).2.1 z hz
  have hVc : Continuous (S.Vric ℓ z G) := hVs.continuous
  have hFs : ContDiff ℝ ∞ (S.Fres ℓ z G (fun r => -S.gStar ℓ z G r)) :=
    contDiff_Fstar S hS ℓ hℓ hz G hE
  have hFc : Continuous (S.Fres ℓ z G (fun r => -S.gStar ℓ z G r)) := hFs.continuous
  have h12 := hS.ξ₁_le_ξ₂
  -- `F_*` vanishes on `(-∞, ξ₁ - 1]` and on `[ξ₂ + 1, ∞)`
  have hF0 : ∀ ξ : ℝ, (ξ ≤ S.ξ₁ - 1 ∨ S.ξ₂ + 1 ≤ ξ) →
      S.Fres ℓ z G (fun r => -S.gStar ℓ z G r) ξ = 0 := by
    intro ξ hξ
    apply Fstar_eq_zero S hS ℓ z G
    rintro ⟨h1, h2⟩
    rcases hξ with h | h
    · have : Real.exp ξ < S.r₁ := by
        calc Real.exp ξ ≤ Real.exp (S.ξ₁ - 1) := Real.exp_le_exp.2 h
          _ < Real.exp S.ξ₁ := Real.exp_lt_exp.2 (by linarith)
          _ = S.r₁ := Real.exp_log hS.r₁_pos
      linarith
    · have : S.r₂ < Real.exp ξ := by
        calc S.r₂ = Real.exp S.ξ₂ := (Real.exp_log hS.r₂_pos).symm
          _ < Real.exp (S.ξ₂ + 1) := Real.exp_lt_exp.2 (by linarith)
          _ ≤ Real.exp ξ := Real.exp_le_exp.2 h
      linarith
  obtain ⟨φ, φ', hsol, h0, h0'⟩ := exists_isInhomSolOn_univ hVc hFc (S.ξ₁ - 1) 0 0
  have hsmooth := (IsInhomSolOn.contDiff hVs hFs hsol).1
  -- on a set where `F_* = 0`, `(φ, φ')` solves the homogeneous equation
  have hhom : ∀ s : Set ℝ, (∀ ξ ∈ s, S.Fres ℓ z G (fun r => -S.gStar ℓ z G r) ξ = 0) →
      IsSolOn (S.Vric ℓ z G) s φ φ' := fun s hs =>
    ⟨fun ξ _ => (hsol.hasDerivWithinAt ξ (mem_univ ξ)).mono (subset_univ s),
      fun ξ hξ => by
        have := (hsol.hasDerivWithinAt' ξ (mem_univ ξ)).mono (subset_univ s)
        rwa [hs ξ hξ, add_zero] at this⟩
  have hleft : ∀ ξ : ℝ, ξ ≤ S.ξ₁ - 1 → φ ξ = 0 := by
    have h := IsSolOn.eqOn_zero ordConnected_Iic hVc.continuousOn
      (hhom (Iic (S.ξ₁ - 1)) fun ξ hξ => hF0 ξ (Or.inl hξ)) self_mem_Iic h0 h0'
    intro ξ hξ
    exact h.1 hξ
  refine ⟨φ, φ', hsol, hsmooth, hleft, ?_⟩
  -- the right half-line
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  have hV2 : ∀ ξ ∈ Ici (S.ξ₂ + 1), S.Vric ℓ z G ξ = (ℓ : ℂ) ^ 2 := fun ξ hξ =>
    (sector_riccati S hS ℓ hℓ G).2.2.2.2 z ξ fun h => by
      have := h.2
      simp only [mem_Ici] at hξ
      linarith
  obtain ⟨A, B, hAB⟩ := exists_eq_exp_add_exp ordConnected_Ici hℓ0 hV2
    (hhom (Ici (S.ξ₂ + 1)) fun ξ hξ => hF0 ξ (Or.inr hξ))
  obtain ⟨B₁, hB₁, hpsi⟩ := psi_right S hS ℓ hℓ z hz G hE
  obtain ⟨hpsol, -⟩ := psi_spec S hS ℓ hℓ z hz G
  -- the Wronskian of `ψ_*` and `φ`
  have hW := wronskian_sub_eq_integral ordConnected_univ continuous_zero.continuousOn
    hFc.continuousOn hpsol.toInhom hsol (mem_univ (S.ξ₁ - 1)) (mem_univ (S.ξ₂ + 1))
  have hint : ∫ ζ in (S.ξ₁ - 1)..(S.ξ₂ + 1),
      (S.psi ℓ z G ζ * S.Fres ℓ z G (fun r => -S.gStar ℓ z G r) ζ -
        (0 : ℝ → ℂ) ζ * φ ζ) = 0 := by
    simp only [Pi.zero_apply, zero_mul, sub_zero]
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · have := J_eq_neg_integral S ℓ z G
      rw [hJ] at this
      linear_combination this
    · intro ξ hξ
      rw [hF0 ξ ?_, mul_zero]
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at hξ
      rcases hξ with h | h
      · exact Or.inl h
      · exact Or.inr h.le
  have hW0 : wronskian (S.psi ℓ z G) (S.dpsi ℓ z G) φ φ' (S.ξ₁ - 1) = 0 := by
    simp [wronskian, h0, h0']
  have hWc : wronskian (S.psi ℓ z G) (S.dpsi ℓ z G) φ φ' (S.ξ₂ + 1) = 0 := by
    have := hW.trans hint
    rwa [hW0, sub_zero] at this
  have hA : A = 0 := by
    obtain ⟨hφ1, hφ2⟩ := hAB (S.ξ₂ + 1) self_mem_Ici
    obtain ⟨hp1, hp2⟩ := hpsi (S.ξ₂ + 1) (by linarith)
    simp only [wronskian] at hWc
    rw [hφ1, hφ2, hp1, hp2] at hWc
    have hee : Complex.exp ((ℓ : ℂ) * ((S.ξ₂ + 1 : ℝ) : ℂ)) *
        Complex.exp (-((ℓ : ℂ) * ((S.ξ₂ + 1 : ℝ) : ℂ))) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have h2 : 2 * (ℓ : ℂ) * B₁ * A = 0 := by
      linear_combination hWc - 2 * (ℓ : ℂ) * B₁ * A * hee
    exact (mul_eq_zero.1 h2).resolve_left (mul_ne_zero (mul_ne_zero two_ne_zero hℓ0) hB₁)
  refine ⟨B, fun ξ hξ => ?_⟩
  rw [(hAB ξ hξ).1, hA, zero_mul, zero_add, Complex.ofReal_exp]
  push_cast
  ring

end GenEigenAux

namespace SectorSetting

/-- `thm:evans-simple`(3), first half, on profiles (`04_ring.tex:536-555`): if `J = 0`, there is
a smooth profile `g₁` supported in `[r₁, r₂]` with `L_ℓ(G) g₁ - λ_* g₁ = g_*` on `(0,∞)`. -/
theorem evansSimple_genEigen (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) (hJ : S.J ℓ z G = 0) :
    ∃ g₁ : ℝ → ℂ, ContDiffOn ℝ ∞ g₁ (Ioi 0) ∧
      (∀ r : ℝ, 0 < r → r ∉ Icc S.r₁ S.r₂ → g₁ r = 0) ∧
      ∀ r : ℝ, 0 < r → S.LsecFn ℓ G g₁ r - z * g₁ r = S.gStar ℓ z G r := by
  obtain ⟨φ, φ', hsol, hsmooth, hleft, B, hright⟩ :=
    GenEigenAux.exists_bvp S hS ℓ hℓ z hz G hE hJ
  obtain ⟨hgs, hgsupp, -⟩ := eigen_of_evans_eq_zero S hS ℓ hℓ z hz G hE
  have hVc : Continuous (S.Vric ℓ z G) := ((sector_riccati S hS ℓ hℓ G).2.1 z hz).continuous
  have hFc : Continuous (S.Fres ℓ z G (fun r => -S.gStar ℓ z G r)) :=
    (GenEigenAux.contDiff_Fstar S hS ℓ hℓ hz G hE).continuous
  have hd : ∀ ξ, HasDerivAt φ (φ' ξ) ξ := fun ξ =>
    hasDerivWithinAt_univ.1 (hsol.hasDerivWithinAt ξ (mem_univ ξ))
  have hd' : ∀ ξ, HasDerivAt φ'
      (S.Vric ℓ z G ξ * φ ξ + S.Fres ℓ z G (fun r => -S.gStar ℓ z G r) ξ) ξ := fun ξ =>
    hasDerivWithinAt_univ.1 (hsol.hasDerivWithinAt' ξ (mem_univ ξ))
  have hφc : Continuous φ := hsmooth.continuous
  have hφ'c : Continuous φ' := continuous_iff_continuousAt.2 fun ξ => (hd' ξ).continuousAt
  have heq : ∀ a b : ℝ, φ' b - φ' a = ∫ t in a..b,
      (S.Vric ℓ z G t * φ t + S.Fres ℓ z G (fun r => -S.gStar ℓ z G r) t) := fun a b =>
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd' x)
      (((hVc.mul hφc).add hFc).intervalIntegrable a b)).symm
  have hL : ∀ ξ : ℝ, ξ ≤ S.ξ₁ - 1 → φ ξ = (0 : ℂ) * ((Real.exp (ℓ * ξ) : ℝ) : ℂ) :=
    fun ξ hξ => by rw [hleft ξ hξ, zero_mul]
  obtain ⟨-, hgreen⟩ := green_eq_of_bvp S hS ℓ hℓ z hz G
    (GenEigenAux.isProfileL2_neg_gStar S hS ℓ hℓ hz G hE) hd hφ'c heq hL hright
  refine ⟨fun r => S.Mres ℓ z G r * (-S.gStar ℓ z G r + S.kcoef ℓ r * φ (Real.log r)),
    ?_, ?_, ?_⟩
  · have hlog : ContDiffOn ℝ ∞ (fun r => φ (Real.log r)) (Ioi 0) :=
      hsmooth.comp_contDiffOn (Real.contDiffOn_log.mono fun r hr => ne_of_gt hr)
    exact (GenEigenAux.contDiffOn_Mres S hS hz ℓ G).mul
      (hgs.neg.add ((GenEigenAux.contDiffOn_kcoef S hS ℓ).mul hlog))
  · intro r hr hrI
    simp only [hgsupp r hr hrI, GenEigenAux.kcoef_eq_zero S hS ℓ hr hrI, neg_zero, zero_mul,
      add_zero, mul_zero]
  · intro r hr
    have hg : green ℓ (fun r => S.Mres ℓ z G r *
        (-S.gStar ℓ z G r + S.kcoef ℓ r * φ (Real.log r))) r = φ (Real.log r) :=
      hgreen r hr
    rw [LsecFn_eq, hg]
    have hM := GenEigenAux.denom_mul_Mres S hz (ℓ : ℤ) G r
    dsimp only
    linear_combination (-(-S.gStar ℓ z G r + S.kcoef ℓ r * φ (Real.log r))) * hM

end SectorSetting

end NonUniqueEuler
