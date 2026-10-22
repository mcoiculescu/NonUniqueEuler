import NonUniqueEuler.H.Sec4.EvansSimple.Range.Voc
import NonUniqueEuler.H.Sec4.EvansSimple.Range.Forcing
import NonUniqueEuler.I.Sec4.EvansBasic
import NonUniqueEuler.I.Sec4.Sector
import NonUniqueEuler.I.Infra.ODE.Existence
import NonUniqueEuler.I.Infra.ODE.Wronskian
import NonUniqueEuler.I.Sec4.Resolvent.Reduction

/-!
# Helpers for `P/Sec4/EvansSimple/Range`: the boundary value problem at a zero of `E_ℓ`

The argument of `thm:evans-simple`(3) (`04_ring.tex:536-551`) with a general right side `g`:
at a zero `λ_*` of `E_ℓ`, let `φ₂` solve `φ₂'' = V_ℓφ₂` with `ψ_*φ₂' - ψ_*'φ₂ = 1`
(`exists_second_sol`); with `F = e^{2ξ}(M_* g)(e^ξ)` and `c < log ρ₋`,
`ψ = φ₂ ∫_c^ξ ψ_*F - ψ_* ∫_c^ξ φ₂F` solves `ψ'' = V_ℓψ + F` (integrated form,
`voc_integrated`). It vanishes left of `c`; right of `d > log ρ₊` it is
`φ₂ ∫_ℝ ψ_*F - ψ_* ∫_c^d φ₂F`, and `∫_ℝ ψ_*F = ∫_0^∞ g ψ_*(log r) M_* r dr = 0` by hypothesis,
while `ψ_* = B e^{-ℓξ}` on `[ξ₂, ∞)` because `E_ℓ = 0` (`bvp_of_orth`). The converse part of the
reduction (`green_eq_of_bvp`, `I/Sec4/Resolvent/Reduction.lean`) then gives a profile solution
`q = M_*(g + k_ℓψ(log r))` of `λ_* q - L_ℓ q = g` (`exists_profile_sol`).
-/

noncomputable section

open MeasureTheory Set Filter

namespace NonUniqueEuler.EvansRangeAux

open SectorSetting LinODE

theorem continuous_Vric (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) : Continuous (S.Vric ℓ z G) :=
  ((sector_riccati S hS ℓ hℓ G).2.1 z hz).continuous

/-- For `E = 0`, `ψ_ℓ = B e^{-ℓξ}` on `[ξ₂, ∞)` (copied from `H/Sec4/Resolvent/Profile.lean`). -/
theorem psi_right_of_evans_eq_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    {z : ℂ} (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) :
    ∃ B : ℂ, ∀ ξ : ℝ, S.ξ₂ ≤ ξ → S.psi ℓ z G ξ = B * ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ) := by
  obtain ⟨Ap, Am, hpsi, hev⟩ := evans_coef S hS ℓ hℓ z hz G
  have hAp : Ap = 0 := by
    rw [hE] at hev
    have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
    have hexp : ((Real.exp (ℓ * S.ξ₁) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
    have := hev.symm
    simp only [mul_eq_zero, two_ne_zero, hℓ0, hexp, false_or] at this
    exact this
  exact ⟨Am, fun ξ hξ => by rw [hpsi ξ hξ, hAp, zero_mul, zero_add]⟩

/-- A second solution `φ₂` of `φ₂'' = V_ℓφ₂` with `ψ_ℓφ₂' - ψ_ℓ'φ₂ ≡ 1`. -/
theorem exists_second_sol (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) :
    ∃ v v' : ℝ → ℂ, IsSolOn (S.Vric ℓ z G) univ v v' ∧
      ∀ ξ, S.psi ℓ z G ξ * v' ξ - S.dpsi ℓ z G ξ * v ξ = 1 := by
  obtain ⟨v, v', hv, hv0, hv1⟩ :=
    exists_isSolOn_univ (continuous_Vric S hS ℓ hℓ hz G) S.ξ₁ 0 1
  obtain ⟨hu, hu0, hu1, -⟩ := psi_spec S hS ℓ hℓ z hz G
  refine ⟨v, v', hv, fun ξ => ?_⟩
  have h := wronskian_eq ordConnected_univ hu hv ξ (mem_univ _) S.ξ₁ (mem_univ _)
  simp only [wronskian] at h
  rw [h, hu0, hu1, hv0, hv1]
  ring

/-- **The boundary value problem at a zero of `E_ℓ`** (`04_ring.tex:540-551`, general right
side): if `E_ℓ(λ;G) = 0` and `∫_0^∞ g ψ_*(log r) M_* r dr = 0`, then `ψ'' = V_ℓψ + F`
(`F = S.Fres ℓ z G g`) has a `C¹` solution, in integrated form, that is a multiple of `e^{ℓξ}`
on a left half-line and of `e^{-ℓξ}` on a right half-line. -/
theorem bvp_of_orth (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) {g : ℝ → ℂ} (hg : S.IsProfileL2 g)
    (h0 : ∫ r in Ioi (0 : ℝ), g r * S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ) = 0) :
    ∃ φ φ' : ℝ → ℂ, (∀ ξ, HasDerivAt φ (φ' ξ) ξ) ∧ Continuous φ' ∧
      (∀ a b : ℝ, φ' b - φ' a = ∫ t in a..b, (S.Vric ℓ z G t * φ t + S.Fres ℓ z G g t)) ∧
      (∃ (c₁ : ℝ) (A : ℂ), ∀ ξ : ℝ, ξ ≤ c₁ → φ ξ = A * ((Real.exp (ℓ * ξ) : ℝ) : ℂ)) ∧
      (∃ (c₂ : ℝ) (B : ℂ), ∀ ξ : ℝ, c₂ ≤ ξ → φ ξ = B * ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ)) := by
  obtain ⟨v, v', hv, hW⟩ := exists_second_sol S hS ℓ hℓ hz G
  obtain ⟨hu, -, -, hψcd, -⟩ := psi_spec S hS ℓ hℓ z hz G
  obtain ⟨Bψ, hBψ⟩ := psi_right_of_evans_eq_zero S hS ℓ hℓ hz G hE
  have hFi : Integrable (S.Fres ℓ z G g) := integrable_Fres S hS hz ℓ G hg
  have hF : ∀ a b, IntervalIntegrable (S.Fres ℓ z G g) volume a b :=
    fun a b => hFi.intervalIntegrable
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun ξ =>
    ((isSolOn_univ_iff.1 hv).1 ξ).continuousAt
  have hUF : ∀ a b, IntervalIntegrable (fun t => S.psi ℓ z G t * S.Fres ℓ z G g t) volume a b :=
    fun a b => (hF a b).continuousOn_mul hψcd.continuous.continuousOn
  have hVF : ∀ a b, IntervalIntegrable (fun t => v t * S.Fres ℓ z G g t) volume a b :=
    fun a b => (hF a b).continuousOn_mul hvc.continuousOn
  have hlog : Real.log S.ρm < Real.log S.ρp := Real.log_lt_log hS.ρm_pos hS.ρm_lt_ρp
  have hξ₂ : S.ξ₂ < Real.log S.ρp := Real.log_lt_log hS.r₂_pos hS.r₂_lt_ρp
  have hc : Real.log S.ρm - 1 < Real.log S.ρm := by linarith
  have hd : Real.log S.ρp < Real.log S.ρp + 1 := by linarith
  have hcd : Real.log S.ρm - 1 ≤ Real.log S.ρp + 1 := by linarith
  obtain ⟨hder, hcont, heq⟩ :=
    voc_integrated (continuous_Vric S hS ℓ hℓ hz G) hu hv hW hF (Real.log S.ρm - 1)
  refine ⟨_, _, hder, hcont, heq, ⟨Real.log S.ρm - 1, 0, fun ξ hξ => ?_⟩,
    ⟨Real.log S.ρp + 1,
      -((∫ t in (Real.log S.ρm - 1)..(Real.log S.ρp + 1), v t * S.Fres ℓ z G g t) * Bψ),
      fun ξ hξ => ?_⟩⟩
  · rw [intervalIntegral_mul_Fres_left S hS ℓ z G hg _ hc hξ,
      intervalIntegral_mul_Fres_left S hS ℓ z G hg _ hc hξ]
    ring
  · rw [intervalIntegral_mul_Fres_right S hS ℓ z G hg hUF _ hd hξ,
      intervalIntegral_mul_Fres_right S hS ℓ z G hg hVF _ hd hξ,
      intervalIntegral_mul_Fres_eq_integral S hS ℓ z G hg _ hc hd hcd, integral_mul_Fres, h0,
      hBψ ξ (by linarith)]
    ring

/-- `z h - L_ℓ h = (λ + iℓΩ) h - k_ℓ 𝒢_ℓ h` (copied from `H/Sec4/Resolvent/Profile.lean`). -/
theorem z_mul_sub_LsecFn (S : SectorSetting) (ℓ : ℤ) (z : ℂ) (G : ℝ) (h : ℝ → ℂ) (r : ℝ) :
    z * h r - S.LsecFn ℓ G h r =
      (z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)) * h r - S.kcoef ℓ r * green ℓ h r := by
  rw [LsecFn_eq]
  ring

/-- **Profile-level solvability at a zero of `E_ℓ`**: if `E_ℓ(λ;G) = 0`, `g ∈ Y^0_ℓ` and
`∫_0^∞ g ψ_*(log r) M_* r dr = 0`, then `λ q - L_ℓ q = g` on `(0,∞)` for some `q ∈ Y^0_ℓ`. -/
theorem exists_profile_sol (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) {g : ℝ → ℂ} (hg : S.IsProfileL2 g)
    (h0 : ∫ r in Ioi (0 : ℝ), g r * S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ) = 0) :
    ∃ q : ℝ → ℂ, S.IsProfileL2 q ∧ ∀ r : ℝ, 0 < r → z * q r - S.LsecFn ℓ G q r = g r := by
  obtain ⟨φ, φ', hφ, hφc, hφeq, ⟨c₁, A, hA⟩, ⟨c₂, B, hB⟩⟩ :=
    bvp_of_orth S hS ℓ hℓ hz G hE hg h0
  obtain ⟨hη, hgreen⟩ := green_eq_of_bvp S hS ℓ hℓ z hz G hg hφ hφc hφeq hA hB
  set q : ℝ → ℂ := fun r => S.Mres ℓ z G r * (g r + S.kcoef ℓ r * φ (Real.log r)) with hq
  refine ⟨q, hη, fun r hr => ?_⟩
  rw [z_mul_sub_LsecFn S ℓ z G q r, hgreen r hr, hq]
  rw [← mul_assoc, denom_mul_Mres S hz (ℓ : ℤ) G r, one_mul]
  ring

end NonUniqueEuler.EvansRangeAux
