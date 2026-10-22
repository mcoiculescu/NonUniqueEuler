import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.I.Sec4.Sector
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Infra.ODE.WeakIBP
import NonUniqueEuler.H.Sec4.Resolvent.Reduction.Basic

/-!
# Proof: the reduction of the resolvent equation to the boundary value problem `eq:bvp`
(sub-step of `lem:resolvent`)

Proof of `I/Sec4/Resolvent/Reduction.lean` (`04_ring.tex:391-410`). Helpers:
`H/Sec4/Resolvent/Reduction/Basic.lean` (namespace `NonUniqueEuler.ReductionAux`).

* `bvp_of_resolvent_eq`: `h = M_λ(g + k_ℓψ)` a.e. (`ψ = 𝒢_ℓh`); `(rψ')' = r h + ℓ²ψ/r` in
  integrated form (`ReductionAux.rmul_deriv_integrated`, from `green_spec`); the substitution
  `r = e^t` (`ReductionAux.integral_exp_comp`) and `e^{2t}M_λ(g + k_ℓX) = F + (V_ℓ - ℓ²)X`
  (`ReductionAux.exp_sq_mul_Mres`); growth from `ReductionAux.green_left/right`.
* `green_eq_of_bvp`: `η ∈ Y^0_ℓ` (`|M_λ| ≤ 1/Re λ`, `k_ℓ` supported in `[r₁,r₂]`); `ψ = φ ∘ log`
  solves the integrated radial equation (substitution and integration by parts against
  `v(t) = e^{-t}`, `LinODE.integral_mul_eq_of_integrated`); growth from the half-line forms;
  conclusion by `green_unique`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Asymptotics

namespace NonUniqueEuler

namespace ReductionAux

open SectorSetting

/-- The integrated radial equation for `ψ = φ ∘ log` after the substitution `r = e^t`
(`04_ring.tex:403-406`): from `φ'' = V_ℓφ + F` (integrated form), integration by parts against
`v(t) = e^{-t}` and `e^{2t}M_λ(g + k_ℓφ) = F + (V_ℓ - ℓ²)φ`. -/
theorem converse_integrated (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) {g : ℝ → ℂ} (hg : S.IsProfileL2 g) {φ φ' : ℝ → ℂ}
    (hφ : ∀ ξ : ℝ, HasDerivAt φ (φ' ξ) ξ) (hφ' : Continuous φ')
    (hφeq : ∀ a b : ℝ, φ' b - φ' a = ∫ t in a..b, (S.Vric ℓ z G t * φ t + S.Fres ℓ z G g t))
    (a b : ℝ) :
    φ' b / ((Real.exp b : ℝ) : ℂ) - φ' a / ((Real.exp a : ℝ) : ℂ) =
      ∫ t in a..b, ((Real.exp t : ℝ) : ℂ) *
        (S.Mres ℓ z G (Real.exp t) * (g (Real.exp t) + S.kcoef ℓ (Real.exp t) * φ t) -
          φ' t / ((Real.exp t : ℝ) : ℂ) / ((Real.exp t : ℝ) : ℂ) +
          (((ℓ : ℤ) : ℂ)) ^ 2 * φ t / ((Real.exp t : ℝ) : ℂ) ^ 2) := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun ξ => (hφ ξ).continuousAt
  have hV : Continuous (S.Vric ℓ z G) := ((sector_riccati S hS ℓ hℓ G).2.1 z hz).continuous
  set H : ℝ → ℂ := fun t => S.Vric ℓ z G t * φ t + S.Fres ℓ z G g t with hHdef
  have hHI : IntervalIntegrable H volume a b :=
    ((hV.mul hφc).intervalIntegrable a b).add (intervalIntegrable_Fres S hS ℓ hz G hg a b)
  have hU : ∀ t ∈ uIcc a b, φ' t = φ' a + ∫ s in a..t, H s := fun t _ => by
    rw [← hφeq a t]
    ring
  have hcont : Continuous fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)
  have hv : ∀ t ∈ uIcc a b, HasDerivAt (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ))
      (-((Real.exp (-t) : ℝ) : ℂ)) t := fun t _ => by
    have h1 := ((hasDerivAt_neg t).exp).ofReal_comp
    convert h1 using 1
    push_cast
    ring
  have hIBP : ∫ t in a..b, ((Real.exp (-t) : ℝ) : ℂ) * H t =
      ((Real.exp (-b) : ℝ) : ℂ) * φ' b - ((Real.exp (-a) : ℝ) : ℂ) * φ' a -
        ∫ t in a..b, (-((Real.exp (-t) : ℝ) : ℂ)) * φ' t :=
    LinODE.integral_mul_eq_of_integrated hHI hU hv hcont.neg.continuousOn
  have hI1 : IntervalIntegrable (fun t => ((Real.exp (-t) : ℝ) : ℂ) * H t) volume a b :=
    hHI.continuousOn_mul hcont.continuousOn
  have hI2 : IntervalIntegrable (fun t => (-((Real.exp (-t) : ℝ) : ℂ)) * φ' t) volume a b :=
    (hcont.neg.mul hφ').intervalIntegrable a b
  have hcongr : ∫ t in a..b, ((Real.exp t : ℝ) : ℂ) *
        (S.Mres ℓ z G (Real.exp t) * (g (Real.exp t) + S.kcoef ℓ (Real.exp t) * φ t) -
          φ' t / ((Real.exp t : ℝ) : ℂ) / ((Real.exp t : ℝ) : ℂ) +
          (((ℓ : ℤ) : ℂ)) ^ 2 * φ t / ((Real.exp t : ℝ) : ℂ) ^ 2) =
      ∫ t in a..b, (((Real.exp (-t) : ℝ) : ℂ) * H t +
        (-((Real.exp (-t) : ℝ) : ℂ)) * φ' t) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hE : ((Real.exp t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos t).ne'
    have hK := exp_sq_mul_Mres S ℓ z G g t (φ t)
    simp only [H, Real.exp_neg, Complex.ofReal_inv, Int.cast_natCast] at hK ⊢
    field_simp
    linear_combination hK
  rw [hcongr, intervalIntegral.integral_add hI1 hI2, hIBP, Real.exp_neg, Real.exp_neg,
    Complex.ofReal_inv, Complex.ofReal_inv]
  field_simp
  ring

end ReductionAux

namespace SectorSetting

open ReductionAux

/-- Proof of `lem:resolvent`, reduction to `eq:bvp`, direct part (`04_ring.tex:391-402`): if
`h, g ∈ Y^0_ℓ` (profiles) satisfy `z h - L_ℓ(G) h = g` a.e. on `(0,∞)`, then
`φ(ξ) = (𝒢_ℓ h)(e^ξ)` is `C¹` and solves `φ'' = V_ℓ φ + F` (`F = S.Fres ℓ z G g`) in integrated
form, with `φ = A e^{ℓξ}` for `ξ ≤ log ρ₋` and `φ = B e^{-ℓξ}` for `ξ ≥ log ρ₊`. -/
theorem bvp_of_resolvent_eq (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) {g h : ℝ → ℂ} (hg : S.IsProfileL2 g) (hh : S.IsProfileL2 h)
    (heq : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), z * h r - S.LsecFn ℓ G h r = g r) :
    ∃ φ' : ℝ → ℂ,
      (∀ ξ : ℝ, HasDerivAt (fun ξ => green ℓ h (Real.exp ξ)) (φ' ξ) ξ) ∧ Continuous φ' ∧
      (∀ a b : ℝ, φ' b - φ' a =
        ∫ t in a..b, (S.Vric ℓ z G t * green ℓ h (Real.exp t) + S.Fres ℓ z G g t)) ∧
      (∃ A : ℂ, ∀ ξ : ℝ, ξ ≤ Real.log S.ρm →
        green ℓ h (Real.exp ξ) = A * ((Real.exp (ℓ * ξ) : ℝ) : ℂ)) ∧
      (∃ B : ℂ, ∀ ξ : ℝ, Real.log S.ρp ≤ ξ →
        green ℓ h (Real.exp ξ) = B * ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ)) := by
  -- `g ∈ Y^0_ℓ` is not needed for the direct part
  have _ := hg
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  obtain ⟨⟨ψ', hψd, hψc, hψeq⟩, -, -⟩ := green_spec S hS hℓ0 hh
  -- `h = M_λ(g + k_ℓ 𝒢_ℓ h)` a.e. on `(0, ∞)`
  have hae : ∀ᵐ r ∂volume, r ∈ Ioi (0 : ℝ) →
      h r = S.Mres ℓ z G r * (g r + S.kcoef ℓ r * green ℓ h r) := by
    refine (ae_restrict_iff' measurableSet_Ioi).1 ?_
    filter_upwards [heq] with r hr
    have hD := denom_ne_zero S hz (ℓ : ℤ) G r
    rw [LsecFn_eq] at hr
    rw [Mres, eq_inv_mul_iff_mul_eq₀ hD]
    linear_combination hr
  refine ⟨fun ξ => ((Real.exp ξ : ℝ) : ℂ) * ψ' (Real.exp ξ), fun ξ => ?_, ?_, fun a b => ?_,
    ?_, ?_⟩
  · have h1 := HasDerivAt.scomp ξ (hψd (Real.exp ξ) (Real.exp_pos ξ)) (Real.hasDerivAt_exp ξ)
    simpa only [Function.comp_def, Complex.real_smul] using h1
  · exact (Complex.continuous_ofReal.comp Real.continuous_exp).mul
      (hψc.comp_continuous Real.continuous_exp fun ξ => Real.exp_pos ξ)
  · have hr := rmul_deriv_integrated hψd hψc hψeq (integrableOn_Ioi_of_isProfileL2 S hh)
      (Real.exp_pos a) (Real.exp_pos b)
    show ((Real.exp b : ℝ) : ℂ) * ψ' (Real.exp b) - ((Real.exp a : ℝ) : ℂ) * ψ' (Real.exp a) = _
    rw [hr]
    have hcongr : ∫ r in Real.exp a..Real.exp b,
          ((r : ℂ) * h r + (((ℓ : ℤ) : ℂ)) ^ 2 * green ℓ h r / (r : ℂ)) =
        ∫ r in Real.exp a..Real.exp b, ((r : ℂ) *
          (S.Mres ℓ z G r * (g r + S.kcoef ℓ r * green ℓ h r)) +
            (((ℓ : ℤ) : ℂ)) ^ 2 * green ℓ h r / (r : ℂ)) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with r hr hmem
      have hpos : 0 < r := (lt_min (Real.exp_pos a) (Real.exp_pos b)).trans_le hmem.1.le
      rw [hr hpos]
    rw [hcongr, integral_exp_comp]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hE : ((Real.exp t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos t).ne'
    have hK := exp_sq_mul_Mres S ℓ z G g t (green ℓ h (Real.exp t))
    simp only [Int.cast_natCast] at hK ⊢
    field_simp
    linear_combination hK
  · obtain ⟨A, hA⟩ := green_left S ℓ hh
    refine ⟨A, fun ξ hξ => ?_⟩
    rw [hA _ ((Real.le_log_iff_exp_le hS.ρm_pos).1 hξ), ← Real.exp_nat_mul]
  · obtain ⟨B, hB⟩ := green_right S ℓ hh
    refine ⟨B, fun ξ hξ => ?_⟩
    have hρp : 0 < S.ρp := hS.ρm_pos.trans hS.ρm_lt_ρp
    rw [hB _ ((Real.log_le_iff_le_exp hρp).1 hξ), Real.exp_neg, Real.exp_nat_mul, inv_pow]

/-- Proof of `lem:resolvent`, reduction to `eq:bvp`, converse part (`04_ring.tex:403-410`): if
`φ` is `C¹` and solves `φ'' = V_ℓ φ + F` (`F = S.Fres ℓ z G g`, `g ∈ Y^0_ℓ`) in integrated form,
with `φ = A e^{ℓξ}` on a left half-line and `φ = B e^{-ℓξ}` on a right half-line, then
`η = M_λ(g + k_ℓ φ(log r))` is in `Y^0_ℓ` and `𝒢_ℓ η = φ(log r)` on `(0, ∞)`. -/
theorem green_eq_of_bvp (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) {g : ℝ → ℂ} (hg : S.IsProfileL2 g) {φ φ' : ℝ → ℂ}
    (hφ : ∀ ξ : ℝ, HasDerivAt φ (φ' ξ) ξ) (hφ' : Continuous φ')
    (hφeq : ∀ a b : ℝ, φ' b - φ' a = ∫ t in a..b, (S.Vric ℓ z G t * φ t + S.Fres ℓ z G g t))
    {c₁ c₂ : ℝ} {A B : ℂ} (hL : ∀ ξ : ℝ, ξ ≤ c₁ → φ ξ = A * ((Real.exp (ℓ * ξ) : ℝ) : ℂ))
    (hR : ∀ ξ : ℝ, c₂ ≤ ξ → φ ξ = B * ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ)) :
    S.IsProfileL2 (fun r => S.Mres ℓ z G r * (g r + S.kcoef ℓ r * φ (Real.log r))) ∧
      ∀ r : ℝ, 0 < r →
        green ℓ (fun r => S.Mres ℓ z G r * (g r + S.kcoef ℓ r * φ (Real.log r))) r =
          φ (Real.log r) := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun ξ => (hφ ξ).continuousAt
  have hprof := isProfileL2_eta S hS ℓ hz G hg hφc
  -- `ψ = φ ∘ log` with `ψ' = φ'(log r)/r`
  have hd : ∀ r : ℝ, 0 < r →
      HasDerivAt (fun r => φ (Real.log r)) (φ' (Real.log r) / (r : ℂ)) r := by
    intro r hr
    have h1 := HasDerivAt.scomp r (hφ (Real.log r)) (Real.hasDerivAt_log hr.ne')
    refine h1.congr_deriv ?_
    simp only [Complex.real_smul, Complex.ofReal_inv]
    ring
  have hc : ContinuousOn (fun r : ℝ => φ' (Real.log r) / (r : ℂ)) (Ioi 0) :=
    (hφ'.comp_continuousOn (Real.continuousOn_log.mono fun r hr => (ne_of_gt hr))).div
      Complex.continuous_ofReal.continuousOn fun r hr => Complex.ofReal_ne_zero.2 (ne_of_gt hr)
  have hsol : IsRadialPoissonSol ℓ
      (fun r => S.Mres ℓ z G r * (g r + S.kcoef ℓ r * φ (Real.log r)))
      (fun r => φ (Real.log r)) := by
    refine ⟨fun r => φ' (Real.log r) / (r : ℂ), hd, hc, fun A' B' hA hB => ?_⟩
    obtain ⟨a, rfl⟩ : ∃ a, Real.exp a = A' := ⟨Real.log A', Real.exp_log hA⟩
    obtain ⟨b, rfl⟩ : ∃ b, Real.exp b = B' := ⟨Real.log B', Real.exp_log hB⟩
    rw [integral_exp_comp]
    simp only [Real.log_exp]
    exact converse_integrated S hS ℓ hℓ hz G hg hφ hφ' hφeq a b
  have h0 : (fun r => φ (Real.log r)) =O[𝓝[>] 0] fun r : ℝ => r ^ (ℓ : ℤ).natAbs := by
    refine IsBigO.of_bound ‖A‖ ?_
    filter_upwards [Ioo_mem_nhdsGT (Real.exp_pos c₁)] with r hr
    have hlog : Real.log r ≤ c₁ := (Real.log_le_iff_le_exp hr.1).2 hr.2.le
    rw [hL _ hlog, Int.natAbs_natCast, Real.exp_nat_mul, Real.exp_log hr.1, norm_mul,
      Complex.norm_real]
  have hinf : (fun r => φ (Real.log r)) =O[atTop]
      fun r : ℝ => r ^ (-((ℓ : ℤ).natAbs : ℤ)) := by
    refine IsBigO.of_bound ‖B‖ ?_
    filter_upwards [eventually_ge_atTop (Real.exp c₂)] with r hr
    have hr0 : 0 < r := (Real.exp_pos _).trans_le hr
    have hlog : c₂ ≤ Real.log r := (Real.le_log_iff_exp_le hr0).2 hr
    rw [hR _ hlog, Int.natAbs_natCast, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hr0,
      norm_mul, Complex.norm_real, zpow_neg, zpow_natCast]
  exact ⟨hprof, fun r hr => (green_unique S hS hℓ0 hprof hsol h0 hinf hr).symm⟩

end SectorSetting

end NonUniqueEuler
