import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.I.Infra.ODE.Param
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Sec4.EvansBasic
import NonUniqueEuler.H.Sec4.PropU.GstarDeriv.Slice

/-!
# Proof: the `r`-derivatives of `g_λ = M_λ k_ℓ ψ_ℓ(log r)` are jointly continuous in
`(r, λ, G)` (sub-step of `prop:U`(b))

Proof of `I/Sec4/PropU/GstarDeriv.lean` (`04_ring.tex:1403-1410`), following its sketch.
1. `GstarDerivP.contDiffOn_Vric`: `V_ℓ(ξ;λ,G)` is jointly `C^∞` on `ℝ × {Re λ > 0} × ℝ`
   (`Omega_eq_add`, `contDiffOn_Omega`; the denominator has real part `Re λ > 0`), so its
   `ξ`-derivatives are jointly continuous (`GstarDerivH.continuousOn_iteratedDeriv_slice`).
2. `GstarDerivP.psi_derivs`: `ψ_ℓ` is smooth in `ξ` (`psi_spec`) and all its `ξ`-derivatives
   are jointly continuous (`LinODE.continuousOn_iteratedDeriv_sol`).
3. `GstarDerivP.gStar_eq`: `g_λ(r) = r⁻² Φ(log r)` with `Φ = ψ'' - ℓ²ψ`, since
   `ψ'' = V_ℓψ` and `V_ℓ(log r) - ℓ² = r² M_λ(r) k_ℓ(r)`.
4. `GstarDerivH.continuousOn_iteratedDeriv_zpow_log` concludes.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler

namespace SectorSetting

namespace GstarDerivP

/-- `V_ℓ(ξ;λ,G)` is jointly `C^∞` in `(ξ, λ, G)` on `ℝ × {Re λ > 0} × ℝ`. -/
theorem contDiffOn_Vric (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℂ × ℝ => S.Vric ℓ q.2.1 q.2.2 q.1)
      (univ ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) := by
  have hom : ContDiff ℝ ∞ S.omR := hS.contDiff.comp Complex.ofRealCLM.contDiff
  have hdom : ContDiff ℝ ∞ S.dom := (contDiff_infty_iff_deriv.mp hom).2
  have hfxi : ContDiff ℝ ∞ S.fxi := Real.contDiff_exp.mul (hdom.comp Real.contDiff_exp)
  have hA : ContDiff ℝ ∞ (fun ξ => S.Omega 0 (Real.exp ξ)) :=
    (contDiffOn_Omega S hS 0).comp_contDiff Real.contDiff_exp fun ξ => Real.exp_pos ξ
  have hw : ContDiff ℝ ∞ (fun q : ℝ × ℂ × ℝ =>
      S.Omega 0 (Real.exp q.1) + q.2.2 * ((Real.exp q.1) ^ 2)⁻¹) := by
    have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℂ × ℝ => S.Omega 0 (Real.exp q.1)) :=
      hA.comp contDiff_fst
    have h2 : ContDiff ℝ ∞ (fun q : ℝ × ℂ × ℝ => ((Real.exp q.1) ^ 2)⁻¹) :=
      ((Real.contDiff_exp.comp contDiff_fst).pow 2).inv fun q =>
        pow_ne_zero 2 (Real.exp_pos _).ne'
    exact h1.add ((contDiff_snd.comp contDiff_snd).mul h2)
  have hden : ContDiff ℝ ∞ (fun q : ℝ × ℂ × ℝ => q.2.1 + Complex.I * (ℓ : ℂ) *
      (((S.Omega 0 (Real.exp q.1) + q.2.2 * ((Real.exp q.1) ^ 2)⁻¹ : ℝ)) : ℂ)) :=
    (contDiff_fst.comp contDiff_snd).add (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hw))
  have hden0 : ∀ q ∈ (univ : Set ℝ) ×ˢ ({z : ℂ | 0 < z.re} ×ˢ (univ : Set ℝ)),
      q.2.1 + Complex.I * (ℓ : ℂ) *
        (((S.Omega 0 (Real.exp q.1) + q.2.2 * ((Real.exp q.1) ^ 2)⁻¹ : ℝ)) : ℂ) ≠ 0 := by
    intro q hq h
    have hre := congrArg Complex.re h
    have hq' : 0 < q.2.1.re := hq.2.1
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.natCast_re,
      Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re] at hre
    linarith
  have hnum : ContDiff ℝ ∞ (fun q : ℝ × ℂ × ℝ => Complex.I * (ℓ : ℂ) * ((S.fxi q.1 : ℝ) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hfxi.comp contDiff_fst))
  have hmain := (contDiffOn_const (c := (ℓ : ℂ) ^ 2)
    (s := (univ : Set ℝ) ×ˢ ({z : ℂ | 0 < z.re} ×ˢ (univ : Set ℝ)))).add
    (hnum.contDiffOn.mul (hden.contDiffOn.inv hden0))
  refine hmain.congr fun q _ => ?_
  simp only [Vric, div_eq_mul_inv]
  rw [Omega_eq_add S q.2.2 (Real.exp q.1)]
  rfl

/-- The slices `ξ ↦ V_ℓ(ξ;λ,G)` are smooth for `Re λ > 0`. -/
theorem Vric_contDiff_slice (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) :
    ∀ p ∈ ({z : ℂ | 0 < z.re} ×ˢ (univ : Set ℝ)),
      ContDiff ℝ ∞ (fun ξ => S.Vric ℓ p.1 p.2 ξ) := by
  intro p hp
  have hV := contDiffOn_Vric S hS ℓ
  have hmaps : ∀ ξ : ℝ, (ξ, p) ∈ (univ : Set ℝ) ×ˢ ({z : ℂ | 0 < z.re} ×ˢ (univ : Set ℝ)) :=
    fun ξ => ⟨mem_univ _, hp⟩
  have hc : ContDiff ℝ ∞ (fun ξ : ℝ => (ξ, p)) := contDiff_id.prodMk contDiff_const
  -- elaborate without the expected type (unifying `?g ∘ ?f` with it unfolds `Vric`)
  have h := hV.comp_contDiff hc hmaps
  exact h

/-- The `ξ`-derivatives of `V_ℓ(ξ;λ,G)` are jointly continuous on `ℝ × {Re λ > 0} × ℝ`. -/
theorem Vric_iteratedDeriv_continuousOn (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (k : ℕ) :
    ContinuousOn
      (fun q : ℝ × ℂ × ℝ => iteratedDeriv k (fun ξ => S.Vric ℓ q.2.1 q.2.2 ξ) q.1)
      (univ ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) := by
  have hW : IsOpen ({z : ℂ | 0 < z.re} ×ˢ (univ : Set ℝ)) :=
    (isOpen_lt continuous_const Complex.continuous_re).prod isOpen_univ
  exact GstarDerivH.continuousOn_iteratedDeriv_slice hW k (contDiffOn_Vric S hS ℓ)

/-- `ψ_ℓ = (sol V_ℓ ξ₁ (1, ℓ)).1` (definitional). -/
theorem psi_eq_sol (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) :
    S.psi ℓ z G ξ = (LinODE.sol (fun η => S.Vric ℓ z G η) S.ξ₁ ((1 : ℂ), (ℓ : ℂ)) ξ).1 :=
  rfl

/-- All `ξ`-derivatives of `ψ_ℓ(ξ;λ,G)` are jointly continuous on `ℝ × {Re λ > 0} × ℝ`. -/
theorem psi_iteratedDeriv_continuousOn (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (k : ℕ) :
    ContinuousOn
      (fun q : ℝ × ℂ × ℝ => iteratedDeriv k (fun ξ => S.psi ℓ q.2.1 q.2.2 ξ) q.1)
      (univ ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) := by
  have hP := LinODE.continuousOn_iteratedDeriv_sol
    (V := fun ξ (p : ℂ × ℝ) => S.Vric ℓ p.1 p.2 ξ) (Vric_contDiff_slice S hS ℓ)
    (Vric_iteratedDeriv_continuousOn S hS ℓ) S.ξ₁
    (y₀ := fun _ => ((1 : ℂ), (ℓ : ℂ))) continuousOn_const k
  simp only [psi_eq_sol]
  exact hP

/-- `ψ_ℓ(ξ;λ,G)` is smooth in `ξ` for `Re λ > 0`, and all its `ξ`-derivatives are jointly
continuous on `ℝ × {Re λ > 0} × ℝ`. -/
theorem psi_derivs (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∀ p ∈ ({z : ℂ | 0 < z.re} ×ˢ (univ : Set ℝ)),
        ContDiff ℝ ∞ (fun ξ => S.psi ℓ p.1 p.2 ξ)) ∧
      ∀ k : ℕ, ContinuousOn
        (fun q : ℝ × ℂ × ℝ => iteratedDeriv k (fun ξ => S.psi ℓ q.2.1 q.2.2 ξ) q.1)
        (univ ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) :=
  ⟨fun p hp => (psi_spec S hS ℓ hℓ p.1 hp.1 p.2).2.2.2.1,
    psi_iteratedDeriv_continuousOn S hS ℓ⟩

/-- `g_λ(r) = r⁻² (ψ'' - ℓ²ψ)(log r)` for `r > 0` and `Re λ > 0` (`ψ'' = V_ℓψ` and
`V_ℓ(log r) - ℓ² = r² M_λ(r) k_ℓ(r)`). -/
theorem gStar_eq (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) {r : ℝ} (hr : 0 < r) :
    S.gStar ℓ z G r = r ^ (-2 : ℤ) •
      (deriv (fun η => deriv (fun η' => S.psi ℓ z G η') η) (Real.log r) +
        (-((ℓ : ℂ) ^ 2)) * S.psi ℓ z G (Real.log r)) := by
  obtain ⟨hsol, -, -, -, hder, -⟩ := psi_spec S hS ℓ hℓ z hz G
  have h2 : deriv (fun η => deriv (fun η' => S.psi ℓ z G η') η) (Real.log r) =
      S.Vric ℓ z G (Real.log r) * S.psi ℓ z G (Real.log r) := by
    have hd : (fun η => deriv (fun η' => S.psi ℓ z G η') η) = S.dpsi ℓ z G := hder
    rw [hd]
    exact ((LinODE.isSolOn_univ_iff.mp hsol).2 _).deriv
  rw [h2]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [gStar, Vric, Mres, kcoef, fxi, Real.exp_log hr, Complex.real_smul]
  push_cast
  field_simp
  ring

end GstarDerivP

/-- `prop:U`(b), core of the regularity in `C^k([r₁,r₂])` (`04_ring.tex:1403-1410`): for a valid
sector setting and `ℓ ≥ 1`, every `r`-derivative of `g_λ(r;G) = M_λ(r) k_ℓ(r) ψ_ℓ(log r;λ,G)` is
jointly continuous in `(r, λ, G)` on `(0,∞) × {Re λ > 0} × ℝ`. -/
theorem gStar_iteratedDeriv_continuousOn (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (j : ℕ) :
    ContinuousOn (fun q : ℝ × ℂ × ℝ => iteratedDeriv j (S.gStar ℓ q.2.1 q.2.2) q.1)
      (Ioi 0 ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) := by
  obtain ⟨hψ, hψd⟩ := GstarDerivP.psi_derivs S hS ℓ hℓ
  obtain ⟨h1, h1d⟩ :=
    GstarDerivH.derivs_deriv (Φ := fun ξ (p : ℂ × ℝ) => S.psi ℓ p.1 p.2 ξ) hψ hψd
  obtain ⟨h2, h2d⟩ :=
    GstarDerivH.derivs_deriv
      (Φ := fun ξ (p : ℂ × ℝ) => deriv (fun η => S.psi ℓ p.1 p.2 η) ξ) h1 h1d
  obtain ⟨hΦ, hΦd⟩ :=
    GstarDerivH.derivs_add_mul
      (Φ₁ := fun ξ (p : ℂ × ℝ) => deriv (fun η => deriv (fun η' => S.psi ℓ p.1 p.2 η') η) ξ)
      (Φ₂ := fun ξ (p : ℂ × ℝ) => S.psi ℓ p.1 p.2 ξ) (-((ℓ : ℂ) ^ 2)) h2 h2d hψ hψd
  refine (GstarDerivH.continuousOn_iteratedDeriv_zpow_log j (-2) hΦ hΦd).congr fun q hq => ?_
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [Ioi_mem_nhds hq.1] with r hr
  exact GstarDerivP.gStar_eq S hS ℓ hℓ hq.2.1 q.2.2 hr

end SectorSetting

end NonUniqueEuler
