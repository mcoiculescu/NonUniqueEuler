import NonUniqueEuler.H.Sec4.Resolvent.Basic
import NonUniqueEuler.I.Sec4.Resolvent.Reduction
import NonUniqueEuler.I.Sec4.Resolvent.PsiG
import NonUniqueEuler.I.Sec4.EvansBasic
import NonUniqueEuler.I.Sec4.Sector
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Infra.ODE.Uniqueness
import NonUniqueEuler.I.Infra.SobolevOneD.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Helpers for `P/Sec4/Resolvent`: `lem:resolvent` at the level of radial profiles

Profile-level parts of `lem:resolvent` (`04_ring.tex:366-448`), from the reduction to `eq:bvp`
(`I/Sec4/Resolvent/Reduction.lean`), the Wronskian formula (`I/Sec4/Resolvent/PsiG.lean`), and
`lem:evans-basic`:
* `resolventFn_spec` (part (1)): for `E ≠ 0` and `g ∈ Y^0_ℓ`, `η = M_λ(g + k_ℓψ_g)` is in
  `Y^0_ℓ` and `z η - L_ℓ η = g` on `(0,∞)`;
* `ae_eq_zero_of_resolvent_eq_zero` (part (1), injectivity): for `E ≠ 0`, `z h - L_ℓ h = 0`
  forces `h = 0`;
* `green_gStar` (part (2)): for `E = 0`, `𝒢_ℓ g_λ = ψ_ℓ(log r)`;
* `exists_eq_smul_gStar` (part (2), kernel): for `E = 0`, `L_ℓ h = z h` forces `h = c g_λ`;
* `contDiffOn_gStar`, `gStar_eq_zero_of_not_mem`, `exists_gStar_ne_zero`, `memH1On_gStar`:
  smoothness, support, non-vanishing and `H^s` membership of `g_λ`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.ResolventAux

open SectorSetting LinODE

/-! ### Elementary facts -/

theorem denom_ne_zero (S : SectorSetting) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ) (G r : ℝ) :
    z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem denom_mul_Mres (S : SectorSetting) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ) (G r : ℝ) :
    (z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)) * S.Mres ℓ z G r = 1 :=
  mul_inv_cancel₀ (denom_ne_zero S hz ℓ G r)

theorem isProfileL2_zero (S : SectorSetting) : S.IsProfileL2 (fun _ => (0 : ℂ)) :=
  ⟨MemLp.zero, Eventually.of_forall fun _ _ => rfl⟩

theorem Fres_zero (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G t : ℝ) :
    S.Fres ℓ z G (fun _ => (0 : ℂ)) t = 0 := by
  simp [Fres]

/-- `z h - L_ℓ h = (λ + iℓΩ) h - k_ℓ 𝒢_ℓ h`. -/
theorem z_mul_sub_LsecFn (S : SectorSetting) (ℓ : ℤ) (z : ℂ) (G : ℝ) (h : ℝ → ℂ) (r : ℝ) :
    z * h r - S.LsecFn ℓ G h r =
      (z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)) * h r - S.kcoef ℓ r * green ℓ h r := by
  rw [LsecFn_eq]
  ring

/-- A `C¹` function whose derivative satisfies `φ'(b) - φ'(a) = ∫_a^b V φ` with `V` continuous is a
classical solution of `φ'' = V φ` on `ℝ`. -/
theorem isSolOn_of_integrated {V φ φ' : ℝ → ℂ} (hV : Continuous V)
    (hφ : ∀ ξ, HasDerivAt φ (φ' ξ) ξ) (heq : ∀ a b : ℝ, φ' b - φ' a = ∫ t in a..b, V t * φ t) :
    IsSolOn V univ φ φ' := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun ξ => (hφ ξ).continuousAt
  have hc : Continuous fun t => V t * φ t := hV.mul hφc
  refine isSolOn_univ_iff.2 ⟨hφ, fun ξ => ?_⟩
  have hfun : φ' = fun x => φ' 0 + ∫ t in (0 : ℝ)..x, V t * φ t := by
    funext x
    rw [← heq 0 x]
    ring
  rw [hfun]
  exact ((hc.integral_hasStrictDerivAt 0 ξ).hasDerivAt).const_add _

theorem continuous_Vric (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) : Continuous (S.Vric ℓ z G) :=
  ((sector_riccati S hS ℓ hℓ G).2.1 z hz).continuous

theorem hasDerivAt_ofReal_exp_mul (c ξ : ℝ) :
    HasDerivAt (fun ξ : ℝ => ((Real.exp (c * ξ) : ℝ) : ℂ))
      ((c : ℂ) * ((Real.exp (c * ξ) : ℝ) : ℂ)) ξ := by
  have h1 : HasDerivAt (fun ξ : ℝ => Real.exp (c * ξ)) (Real.exp (c * ξ) * c) ξ := by
    simpa using ((hasDerivAt_id ξ).const_mul c).exp
  have h2 := h1.ofReal_comp
  convert h2 using 1
  push_cast
  ring

/-- A solution of `φ'' = V_ℓ φ` that is `A e^{ℓξ}` on a left half-line is `A ψ_L`. -/
theorem eq_psiL_of_left (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) {φ φ' : ℝ → ℂ} (hsol : IsSolOn (S.Vric ℓ z G) univ φ φ') {c : ℝ}
    {A : ℂ} (hL : ∀ ξ : ℝ, ξ ≤ c → φ ξ = A * ((Real.exp (ℓ * ξ) : ℝ) : ℂ)) (ξ : ℝ) :
    φ ξ = A * S.psiL ℓ z G ξ ∧ φ' ξ = A * S.dpsiL ℓ z G ξ := by
  obtain ⟨hpsi, -, -, -, -, hleft⟩ := psi_spec S hS ℓ hℓ z hz G
  set ξ₀ : ℝ := min c S.ξ₁ - 1 with hξ₀
  have hξ₀c : ξ₀ < c := by have := min_le_left c S.ξ₁; linarith
  have hξ₀1 : ξ₀ < S.ξ₁ := by have := min_le_right c S.ξ₁; linarith
  have hL' : IsSolOn (S.Vric ℓ z G) univ (S.psiL ℓ z G) (S.dpsiL ℓ z G) :=
    hpsi.const_mul ((Real.exp (ℓ * S.ξ₁) : ℝ) : ℂ)
  have hexp : Real.exp (ℓ * S.ξ₁) * Real.exp (ℓ * (ξ₀ - S.ξ₁)) = Real.exp (ℓ * ξ₀) := by
    rw [← Real.exp_add]
    ring_nf
  have hψL : S.psiL ℓ z G ξ₀ = ((Real.exp (ℓ * ξ₀) : ℝ) : ℂ) := by
    rw [psiL, (hleft ξ₀ hξ₀1.le).1, ← Complex.ofReal_mul, hexp]
  have hdψL : S.dpsiL ℓ z G ξ₀ = (ℓ : ℂ) * ((Real.exp (ℓ * ξ₀) : ℝ) : ℂ) := by
    rw [dpsiL, (hleft ξ₀ hξ₀1.le).2, mul_left_comm, ← Complex.ofReal_mul, hexp]
  -- the derivative of `φ` at `ξ₀`
  have hd1 : HasDerivAt φ (φ' ξ₀) ξ₀ :=
    (hsol.hasDerivWithinAt ξ₀ (mem_univ _)).hasDerivAt Filter.univ_mem
  have hev : φ =ᶠ[𝓝 ξ₀] fun ξ => A * ((Real.exp (ℓ * ξ) : ℝ) : ℂ) := by
    filter_upwards [Iio_mem_nhds hξ₀c] with ξ hξ
    exact hL ξ (le_of_lt hξ)
  have hd2 : HasDerivAt φ (A * ((ℓ : ℂ) * ((Real.exp (ℓ * ξ₀) : ℝ) : ℂ))) ξ₀ := by
    have := ((hasDerivAt_ofReal_exp_mul (ℓ : ℝ) ξ₀).const_mul A).congr_of_eventuallyEq hev
    rwa [Complex.ofReal_natCast] at this
  have hφ'0 : φ' ξ₀ = A * ((ℓ : ℂ) * ((Real.exp (ℓ * ξ₀) : ℝ) : ℂ)) := hd1.unique hd2
  have hun := IsSolOn.eqOn ordConnected_univ (continuous_Vric S hS ℓ hℓ hz G).continuousOn hsol
    (hL'.const_mul A) (mem_univ ξ₀) (by rw [hL ξ₀ hξ₀c.le, hψL]) (by rw [hφ'0, hdψL])
  exact ⟨hun.1 (mem_univ ξ), hun.2 (mem_univ ξ)⟩

/-- A solution of `φ'' = V_ℓ φ` that is `B e^{-ℓξ}` on a right half-line is `B ψ_R`. -/
theorem eq_psiR_of_right (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) {φ φ' : ℝ → ℂ} (hsol : IsSolOn (S.Vric ℓ z G) univ φ φ') {c : ℝ}
    {B : ℂ} (hR : ∀ ξ : ℝ, c ≤ ξ → φ ξ = B * ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ)) (ξ : ℝ) :
    φ ξ = B * S.psiR ℓ z G ξ ∧ φ' ξ = B * S.dpsiR ℓ z G ξ := by
  obtain ⟨hpsiR, -, -, hright⟩ := psiR_spec S hS ℓ hℓ z hz G
  set ξ₀ : ℝ := max c S.ξ₂ + 1 with hξ₀
  have hξ₀c : c < ξ₀ := by have := le_max_left c S.ξ₂; linarith
  have hξ₀2 : S.ξ₂ < ξ₀ := by have := le_max_right c S.ξ₂; linarith
  have hd1 : HasDerivAt φ (φ' ξ₀) ξ₀ :=
    (hsol.hasDerivWithinAt ξ₀ (mem_univ _)).hasDerivAt Filter.univ_mem
  have hev : φ =ᶠ[𝓝 ξ₀] fun ξ => B * ((Real.exp ((-(ℓ : ℝ)) * ξ) : ℝ) : ℂ) := by
    filter_upwards [Ioi_mem_nhds hξ₀c] with ξ hξ
    rw [hR ξ (le_of_lt hξ), neg_mul]
  have hd2 : HasDerivAt φ (B * (-(ℓ : ℂ) * ((Real.exp ((-(ℓ : ℝ)) * ξ₀) : ℝ) : ℂ))) ξ₀ := by
    have := ((hasDerivAt_ofReal_exp_mul (-(ℓ : ℝ)) ξ₀).const_mul B).congr_of_eventuallyEq hev
    rwa [Complex.ofReal_neg, Complex.ofReal_natCast] at this
  have hφ'0 := hd1.unique hd2
  have hun := IsSolOn.eqOn ordConnected_univ (continuous_Vric S hS ℓ hℓ hz G).continuousOn hsol
    (hpsiR.const_mul B) (mem_univ ξ₀) (by rw [hR ξ₀ hξ₀c.le, (hright ξ₀ hξ₀2.le).1])
    (by rw [hφ'0, (hright ξ₀ hξ₀2.le).2, show -(ℓ : ℝ) * ξ₀ = -(ℓ * ξ₀) by ring])
  exact ⟨hun.1 (mem_univ ξ), hun.2 (mem_univ ξ)⟩

/-- `eq:bvp` with `F = 0` and `E ≠ 0` has only the zero solution. -/
theorem eq_zero_of_bvp_hom (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G ≠ 0) {φ φ' : ℝ → ℂ}
    (hsol : IsSolOn (S.Vric ℓ z G) univ φ φ') {c₁ c₂ : ℝ} {A B : ℂ}
    (hL : ∀ ξ : ℝ, ξ ≤ c₁ → φ ξ = A * ((Real.exp (ℓ * ξ) : ℝ) : ℂ))
    (hR : ∀ ξ : ℝ, c₂ ≤ ξ → φ ξ = B * ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ)) (ξ : ℝ) : φ ξ = 0 := by
  have hl := eq_psiL_of_left S hS ℓ hℓ hz G hsol hL
  have hr := eq_psiR_of_right S hS ℓ hℓ hz G hsol hR
  have hW := (wronskian_eq_neg_evans S hS ℓ hℓ z hz G).2 ξ
  have hA : A = 0 := by
    have h1 : A * S.wrFn ℓ z G ξ = 0 := by
      have e1 := hl ξ
      have e2 := hr ξ
      simp only [wrFn, wronskian]
      calc A * (S.psiL ℓ z G ξ * S.dpsiR ℓ z G ξ - S.dpsiL ℓ z G ξ * S.psiR ℓ z G ξ)
          = (A * S.psiL ℓ z G ξ) * S.dpsiR ℓ z G ξ -
              (A * S.dpsiL ℓ z G ξ) * S.psiR ℓ z G ξ := by ring
        _ = (B * S.psiR ℓ z G ξ) * S.dpsiR ℓ z G ξ -
              (B * S.dpsiR ℓ z G ξ) * S.psiR ℓ z G ξ := by rw [← e1.1, ← e1.2, e2.1, e2.2]
        _ = 0 := by ring
    rw [hW] at h1
    exact (mul_eq_zero.1 h1).resolve_right (neg_ne_zero.2 hE)
  rw [(hl ξ).1, hA, zero_mul]

/-! ### Part (1): the resolvent formula and injectivity -/

/-- `lem:resolvent`(1), profile level: `η = M_λ(g + k_ℓψ_g)` is in `Y^0_ℓ` and solves
`z η - L_ℓ η = g` on `(0,∞)`. -/
theorem resolventFn_spec (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G ≠ 0) {g : ℝ → ℂ} (hg : S.IsProfileL2 g) :
    S.IsProfileL2 (S.resolventFn ℓ z G g) ∧
      ∀ r : ℝ, 0 < r → z * S.resolventFn ℓ z G g r - S.LsecFn ℓ G (S.resolventFn ℓ z G g) r =
        g r := by
  obtain ⟨φ', hφ, hφc, hφeq, ⟨A, hA⟩, ⟨B, hB⟩⟩ := psiG_spec S hS ℓ hℓ z hz G hE hg
  obtain ⟨hη, hgreen⟩ := green_eq_of_bvp S hS ℓ hℓ z hz G hg hφ hφc hφeq hA hB
  refine ⟨hη, fun r hr => ?_⟩
  rw [z_mul_sub_LsecFn]
  have h1 := hgreen r hr
  change green ℓ (S.resolventFn ℓ z G g) r = _ at h1
  rw [h1]
  simp only [resolventFn]
  rw [← mul_assoc, denom_mul_Mres S hz (ℓ : ℤ) G r, one_mul]
  ring

/-- `lem:resolvent`(1), profile level, injectivity: if `E ≠ 0`, `h ∈ Y^0_ℓ` and
`z h - L_ℓ h = 0` a.e. on `(0,∞)`, then `h = 0` a.e. on `(0,∞)`. -/
theorem ae_eq_zero_of_resolvent_eq_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) {z : ℂ} (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G ≠ 0) {h : ℝ → ℂ}
    (hh : S.IsProfileL2 h)
    (heq : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), z * h r - S.LsecFn ℓ G h r = 0) :
    h =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun _ => 0 := by
  obtain ⟨φ', hφ, -, hφeq, ⟨A, hA⟩, ⟨B, hB⟩⟩ :=
    bvp_of_resolvent_eq S hS ℓ hℓ z hz G (isProfileL2_zero S) hh heq
  simp only [Fres_zero, add_zero] at hφeq
  have hsol := isSolOn_of_integrated (continuous_Vric S hS ℓ hℓ hz G) hφ hφeq
  have h0 := eq_zero_of_bvp_hom S hS ℓ hℓ hz G hE hsol hA hB
  filter_upwards [heq, self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with r hr hr0
  have hg0 : green ℓ h r = 0 := by
    have := h0 (Real.log r)
    simp only [Real.exp_log hr0] at this
    exact this
  rw [z_mul_sub_LsecFn, hg0, mul_zero, sub_zero] at hr
  exact (mul_eq_zero.1 hr).resolve_left (denom_ne_zero S hz (ℓ : ℤ) G r)

/-! ### Part (2): the eigenfunction and the kernel -/

/-- `ψ_ℓ` is `C¹` and solves `ψ'' = V_ℓψ` in integrated form. -/
theorem psi_integrated (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) :
    (∀ ξ, HasDerivAt (S.psi ℓ z G) (S.dpsi ℓ z G ξ) ξ) ∧ Continuous (S.dpsi ℓ z G) ∧
      ∀ a b : ℝ, S.dpsi ℓ z G b - S.dpsi ℓ z G a =
        ∫ t in a..b, (S.Vric ℓ z G t * S.psi ℓ z G t + S.Fres ℓ z G (fun _ => 0) t) := by
  obtain ⟨hsol, -⟩ := psi_spec S hS ℓ hℓ z hz G
  obtain ⟨hd, hd'⟩ := isSolOn_univ_iff.1 hsol
  have hc : Continuous (S.dpsi ℓ z G) :=
    continuous_iff_continuousAt.2 fun ξ => (hd' ξ).continuousAt
  have hψc : Continuous (S.psi ℓ z G) :=
    continuous_iff_continuousAt.2 fun ξ => (hd ξ).continuousAt
  have hVc : Continuous fun t => S.Vric ℓ z G t * S.psi ℓ z G t :=
    (continuous_Vric S hS ℓ hℓ hz G).mul hψc
  refine ⟨hd, hc, fun a b => ?_⟩
  simp only [Fres_zero, add_zero]
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd' x)
    (hVc.intervalIntegrable a b)).symm

/-- For `E = 0`, `ψ_ℓ = A_- e^{-ℓξ}` on `[ξ₂, ∞)`. -/
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

/-- `ψ_ℓ = e^{-ℓξ₁} e^{ℓξ}` on `(-∞, ξ₁]`. -/
theorem psi_left (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) :
    ∀ ξ : ℝ, ξ ≤ S.ξ₁ → S.psi ℓ z G ξ =
      ((Real.exp (-(ℓ * S.ξ₁)) : ℝ) : ℂ) * ((Real.exp (ℓ * ξ) : ℝ) : ℂ) := by
  intro ξ hξ
  rw [((psi_spec S hS ℓ hℓ z hz G).2.2.2.2.2 ξ hξ).1, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem gStar_eq (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) :
    S.gStar ℓ z G =
      fun r => S.Mres ℓ z G r * ((fun _ => (0 : ℂ)) r + S.kcoef ℓ r * S.psi ℓ z G (Real.log r)) := by
  funext r
  simp only [gStar, zero_add]
  ring

/-- `lem:resolvent`(2): for `E = 0`, `𝒢_ℓ g_λ = ψ_ℓ(log r)` on `(0,∞)`; `g_λ ∈ Y^0_ℓ`. -/
theorem green_gStar (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) :
    S.IsProfileL2 (S.gStar ℓ z G) ∧
      ∀ r : ℝ, 0 < r → green ℓ (S.gStar ℓ z G) r = S.psi ℓ z G (Real.log r) := by
  obtain ⟨hd, hc, heq⟩ := psi_integrated S hS ℓ hℓ hz G
  obtain ⟨B, hB⟩ := psi_right_of_evans_eq_zero S hS ℓ hℓ hz G hE
  have h := green_eq_of_bvp S hS ℓ hℓ z hz G (isProfileL2_zero S) hd hc heq
    (psi_left S hS ℓ hℓ hz G) hB
  rw [gStar_eq]
  exact h

/-- `lem:resolvent`(2), kernel, profile level: for `E = 0`, if `h ∈ Y^0_ℓ` and `L_ℓ h = z h`
a.e. on `(0,∞)`, then `h = c g_λ` a.e. on `(0,∞)`. -/
theorem exists_eq_smul_gStar (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) {h : ℝ → ℂ} (hh : S.IsProfileL2 h)
    (heq : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), S.LsecFn ℓ G h r = z * h r) :
    ∃ c : ℂ, h =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r => c * S.gStar ℓ z G r := by
  have heq' : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), z * h r - S.LsecFn ℓ G h r = 0 := by
    filter_upwards [heq] with r hr
    rw [hr, sub_self]
  obtain ⟨φ', hφ, -, hφeq, ⟨A, hA⟩, -⟩ :=
    bvp_of_resolvent_eq S hS ℓ hℓ z hz G (isProfileL2_zero S) hh heq'
  simp only [Fres_zero, add_zero] at hφeq
  have hsol := isSolOn_of_integrated (continuous_Vric S hS ℓ hℓ hz G) hφ hφeq
  have hl := eq_psiL_of_left S hS ℓ hℓ hz G hsol hA
  refine ⟨A * ((Real.exp (ℓ * S.ξ₁) : ℝ) : ℂ), ?_⟩
  filter_upwards [heq', self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with r hr hr0
  have hg : green ℓ h r = A * S.psiL ℓ z G (Real.log r) := by
    have := (hl (Real.log r)).1
    simp only [Real.exp_log hr0] at this
    exact this
  rw [z_mul_sub_LsecFn, hg, sub_eq_zero] at hr
  have hM := denom_mul_Mres S hz (ℓ : ℤ) G r
  calc h r = (S.Mres ℓ z G r * (z + Complex.I * ((ℓ : ℤ) : ℂ) * ((S.Omega G r : ℝ) : ℂ))) * h r := by
        rw [mul_comm (S.Mres ℓ z G r), hM, one_mul]
    _ = S.Mres ℓ z G r * ((z + Complex.I * ((ℓ : ℤ) : ℂ) * ((S.Omega G r : ℝ) : ℂ)) * h r) := by
        ring
    _ = _ := by
        rw [hr, gStar, psiL]
        ring

/-! ### Properties of `g_λ` -/

theorem contDiff_omR (S : SectorSetting) (hS : S.Valid) : ContDiff ℝ ∞ S.omR :=
  hS.contDiff.comp Complex.ofRealCLM.contDiff

theorem contDiff_dom (S : SectorSetting) (hS : S.Valid) : ContDiff ℝ ∞ S.dom :=
  (contDiff_infty_iff_deriv.1 (contDiff_omR S hS)).2

theorem contDiffOn_kcoef (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) :
    ContDiffOn ℝ ∞ (S.kcoef ℓ) (Ioi 0) := by
  have h1 : ContDiff ℝ ∞ fun r : ℝ => ((S.dom r : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_dom S hS)
  have h2 : ContDiffOn ℝ ∞ (fun r : ℝ => ((r : ℝ) : ℂ)⁻¹) (Ioi 0) :=
    (Complex.ofRealCLM.contDiff.contDiffOn).inv fun r hr => by
      simpa using (ne_of_gt (show (0 : ℝ) < r from hr))
  have h3 : ContDiffOn ℝ ∞ (fun r : ℝ => Complex.I * (ℓ : ℂ) * ((S.dom r : ℝ) : ℂ) *
      ((r : ℝ) : ℂ)⁻¹) (Ioi 0) :=
    ((contDiffOn_const.mul h1.contDiffOn).mul h2)
  refine h3.congr fun r _ => ?_
  simp only [kcoef, div_eq_mul_inv]

theorem contDiffOn_Mres (S : SectorSetting) (hS : S.Valid) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ)
    (G : ℝ) : ContDiffOn ℝ ∞ (S.Mres ℓ z G) (Ioi 0) := by
  have h1 : ContDiffOn ℝ ∞ (fun r : ℝ => ((S.Omega G r : ℝ) : ℂ)) (Ioi 0) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_Omega S hS G)
  have h2 : ContDiffOn ℝ ∞ (fun r : ℝ => z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ))
      (Ioi 0) := contDiffOn_const.add (contDiffOn_const.mul h1)
  exact h2.inv fun r _ => denom_ne_zero S hz ℓ G r

theorem contDiffOn_psi_log (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) :
    ContDiffOn ℝ ∞ (fun r => S.psi ℓ z G (Real.log r)) (Ioi 0) := by
  have hψ : ContDiff ℝ ∞ (S.psi ℓ z G) := (psi_spec S hS ℓ hℓ z hz G).2.2.2.1
  exact hψ.comp_contDiffOn (Real.contDiffOn_log.mono fun r hr => ne_of_gt hr)

theorem contDiffOn_gStar (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) : ContDiffOn ℝ ∞ (S.gStar ℓ z G) (Ioi 0) :=
  ((contDiffOn_Mres S hS hz ℓ G).mul (contDiffOn_kcoef S hS ℓ)).mul
    (contDiffOn_psi_log S hS ℓ hℓ hz G)

theorem kcoef_eq_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) {r : ℝ} (hr : 0 < r)
    (hrI : r ∉ Icc S.r₁ S.r₂) : S.kcoef ℓ r = 0 := by
  simp [kcoef, hS.dom_eq_zero r hr hrI]

theorem gStar_eq_zero_of_not_mem (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (z : ℂ) (G : ℝ)
    {r : ℝ} (hr : 0 < r) (hrI : r ∉ Icc S.r₁ S.r₂) : S.gStar ℓ z G r = 0 := by
  simp [gStar, kcoef_eq_zero S hS ℓ hr hrI]

theorem exists_gStar_ne_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) :
    ∃ r : ℝ, 0 < r ∧ S.gStar ℓ z G r ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 : S.gStar ℓ z G =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun _ => (0 : ℂ) := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
      with r hr
    exact hcon r hr
  have h1 := (green_gStar S hS ℓ hℓ hz G hE).2 S.r₁ hS.r₁_pos
  rw [green_congr_ae h0] at h1
  have h2 : green ℓ (fun _ => (0 : ℂ)) S.r₁ = 0 := by simp [green]
  have hψ : S.psi ℓ z G (Real.log S.r₁) = 1 := (psi_spec S hS ℓ hℓ z hz G).2.1
  rw [h2] at h1
  change 0 = S.psi ℓ z G S.ξ₁ at h1
  rw [show S.ξ₁ = Real.log S.r₁ from rfl, hψ] at h1
  exact zero_ne_one h1

/-- The iterated derivatives of a profile vanishing on `(0,∞) \ [a, b]` vanish there too
(copied from `P/Infra/AngularFourier/NormHCont.lean`). -/
theorem iteratedDeriv_eq_zero_of_supp {a b : ℝ} {g : ℝ → ℂ}
    (hsupp : ∀ r : ℝ, 0 < r → r ∉ Icc a b → g r = 0) (j : ℕ) {r : ℝ} (hr : 0 < r)
    (hrI : r ∉ Icc a b) : iteratedDeriv j g r = 0 := by
  have hopen : IsOpen (Ioi (0 : ℝ) ∩ (Icc a b)ᶜ) := isOpen_Ioi.inter isClosed_Icc.isOpen_compl
  have hev : g =ᶠ[nhds r] fun _ => (0 : ℂ) := by
    filter_upwards [hopen.mem_nhds ⟨hr, hrI⟩] with x hx
    exact hsupp x hx.1 hx.2
  rw [Filter.EventuallyEq.iteratedDeriv_eq j hev]
  simp

theorem continuousOn_iteratedDeriv {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (j : ℕ) :
    ContinuousOn (iteratedDeriv j g) (Ioi 0) := by
  have h1 : ContinuousOn (iteratedDerivWithin j g (Ioi 0)) (Ioi 0) :=
    hg.continuousOn_iteratedDerivWithin (by exact_mod_cast le_top) isOpen_Ioi.uniqueDiffOn
  exact h1.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm

/-- A profile smooth on `(0,∞)` and vanishing on `(0,∞) \ [a, b]` (`a > 0`) lies in
`H^k((0,∞))` (copied from `P/Infra/AngularFourier/NormHCont.lean`). -/
theorem memH1On_of_smooth_supp (k : ℕ) {a b : ℝ} (ha : 0 < a) {g : ℝ → ℂ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (hsupp : ∀ r : ℝ, 0 < r → r ∉ Icc a b → g r = 0) :
    Sob.MemH1On k (Ioi 0) g := by
  refine Sob.memH1On_of_contDiffOn isOpen_Ioi (hg.of_le (by exact_mod_cast le_top))
    fun j _ => ?_
  set F := iteratedDeriv j g with hF
  have hIcc : Icc a b ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le ha hr.1
  have hcont : ContinuousOn F (Icc a b) := (continuousOn_iteratedDeriv hg j).mono hIcc
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have hF2 : MemLp F 2 (volume.restrict (Icc a b)) :=
    MemLp.of_bound (hcont.aestronglyMeasurable measurableSet_Icc) M
      ((ae_restrict_mem measurableSet_Icc).mono fun r hr => hM r hr)
  have hind : MemLp ((Icc a b).indicator F) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc).2 hF2
  refine (hind.restrict (Ioi 0)).ae_eq ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  by_cases hrI : r ∈ Icc a b
  · simp [indicator_of_mem hrI]
  · rw [indicator_of_notMem hrI]
    exact (iteratedDeriv_eq_zero_of_supp hsupp j hr hrI).symm

theorem memH1On_gStar (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) (s : ℕ) : Sob.MemH1On s (Ioi 0) (S.gStar ℓ z G) :=
  memH1On_of_smooth_supp s hS.r₁_pos (contDiffOn_gStar S hS ℓ hℓ hz G)
    fun _ hr hrI => gStar_eq_zero_of_not_mem S hS ℓ z G hr hrI

end NonUniqueEuler.ResolventAux
