import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Infra.ODE.Param
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Helpers for `P/Sec4/PropU`: joint continuity in `(r, λ, G)` and parametric integrals

* `psi_continuousOn_param`: `ψ_ℓ(ξ;λ,G)` is jointly continuous on `ℝ × {Re λ > 0} × ℝ`
  (`04_ring.tex:1403-1404`, "by the Picard argument"; `LinODE.continuousOn_sol`);
* `Omega_continuousOn`, `Mres_continuousOn`, `psiLog_continuousOn`: `Ω(r;G)`, `M_λ(r;G)` and
  `ψ_ℓ(log r;λ,G)` are jointly continuous on `(0,∞) × {Re λ > 0} × ℝ`;
* `continuousOn_comp_path`: composition with `G ↦ (λ(G), G)`;
* `continuousOn_intervalIntegral_rect`: `G ↦ ∫_c^d F(G,r) dr` is continuous on `[g₀,g₁]` when
  `F` is jointly continuous on the rectangle;
* `setIntegral_Ioi_eq_intervalIntegral`: integrals over `(0,∞)` of functions vanishing outside
  `[c,d] ⊂ (0,∞)`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

namespace NonUniqueEuler

namespace SectorSetting

namespace PropUH

/-- `r ↦ ω̄'(r)` is continuous. -/
theorem continuous_dom (S : SectorSetting) (hS : S.Valid) : Continuous S.dom := by
  have hom : ContDiff ℝ ∞ S.omR := hS.contDiff.comp Complex.ofRealCLM.contDiff
  exact hom.continuous_deriv (by simp)

/-- `Ω(r;G)` is jointly continuous on `(0,∞) × ℝ` (`Omega_eq_add`, `contDiffOn_Omega`). -/
theorem Omega_continuousOn₂ (S : SectorSetting) (hS : S.Valid) :
    ContinuousOn (fun p : ℝ × ℝ => S.Omega p.2 p.1) (Ioi 0 ×ˢ univ) := by
  have h0 := (contDiffOn_Omega S hS 0).continuousOn
  have h1 : ContinuousOn (fun p : ℝ × ℝ => S.Omega 0 p.1) (Ioi 0 ×ˢ univ) :=
    h0.comp continuousOn_fst fun p hp => hp.1
  have h2 : ContinuousOn (fun p : ℝ × ℝ => p.2 * (p.1 ^ 2)⁻¹) (Ioi 0 ×ˢ univ) :=
    continuousOn_snd.mul ((continuousOn_fst.pow 2).inv₀ fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  refine (h1.add h2).congr fun p _ => ?_
  exact Omega_eq_add S p.2 p.1

/-- `Ω(r;G)` as a function of `(r, λ, G)`. -/
theorem Omega_continuousOn (S : SectorSetting) (hS : S.Valid) :
    ContinuousOn (fun q : ℝ × ℂ × ℝ => S.Omega q.2.2 q.1)
      (Ioi 0 ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) :=
  (Omega_continuousOn₂ S hS).comp
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn
    fun _ hq => ⟨hq.1, mem_univ _⟩

theorem re_add_I_mul_ofReal (z : ℂ) (c : ℂ) (hc : c.im = 0) (x : ℝ) :
    (z + Complex.I * c * (x : ℂ)).re = z.re := by
  simp [Complex.add_re, Complex.mul_re, hc]

/-- `M_λ(r;G) = (λ + iℓΩ(r;G))⁻¹` is jointly continuous on `(0,∞) × {Re λ > 0} × ℝ`. -/
theorem Mres_continuousOn (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) :
    ContinuousOn (fun q : ℝ × ℂ × ℝ => S.Mres ℓ q.2.1 q.2.2 q.1)
      (Ioi 0 ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) := by
  have hΩ := (Complex.continuous_ofReal.comp_continuousOn (Omega_continuousOn S hS))
  have hden : ContinuousOn (fun q : ℝ × ℂ × ℝ =>
      q.2.1 + Complex.I * (ℓ : ℂ) * ((S.Omega q.2.2 q.1 : ℝ) : ℂ))
      (Ioi 0 ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) :=
    (continuous_fst.comp continuous_snd).continuousOn.add (continuousOn_const.mul hΩ)
  refine hden.inv₀ fun q hq => ?_
  intro h0
  have hre := congrArg Complex.re h0
  rw [re_add_I_mul_ofReal _ _ (by simp)] at hre
  simp only [Complex.zero_re] at hre
  exact (ne_of_gt hq.2.1) hre

/-- `ψ_ℓ(ξ;λ,G)` is jointly continuous in `(ξ, λ, G)` on `ℝ × {Re λ > 0} × ℝ`
(`04_ring.tex:1403-1404`; `LinODE.continuousOn_sol`). -/
theorem psi_continuousOn_param (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) :
    ContinuousOn (fun q : ℝ × ℂ × ℝ => S.psi ℓ q.2.1 q.2.2 q.1)
      (univ ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) := by
  have hdom := continuous_dom S hS
  have hfxi : Continuous S.fxi := Real.continuous_exp.mul (hdom.comp Real.continuous_exp)
  have hΩ : Continuous (fun p : ℝ × ℝ => S.Omega p.2 (Real.exp p.1)) :=
    continuousOn_univ.1 <| (Omega_continuousOn₂ S hS).comp
      ((Real.continuous_exp.comp continuous_fst).prodMk continuous_snd).continuousOn
      fun p _ => ⟨Real.exp_pos _, mem_univ _⟩
  set V : ℝ → ℂ × ℝ → ℂ := fun ξ p => S.Vric ℓ p.1 p.2 ξ with hVdef
  have hV : ContinuousOn (Function.uncurry V) (univ ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) := by
    have hnum : Continuous (fun q : ℝ × ℂ × ℝ => Complex.I * (ℓ : ℂ) * ((S.fxi q.1 : ℝ) : ℂ)) :=
      continuous_const.mul (Complex.continuous_ofReal.comp (hfxi.comp continuous_fst))
    have hden : Continuous (fun q : ℝ × ℂ × ℝ =>
        q.2.1 + Complex.I * (ℓ : ℂ) * ((S.Omega q.2.2 (Real.exp q.1) : ℝ) : ℂ)) :=
      (continuous_fst.comp continuous_snd).add (continuous_const.mul
        (Complex.continuous_ofReal.comp
          (hΩ.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))))
    have h := (continuous_const.continuousOn (s := univ ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ))
      (f := fun _ : ℝ × ℂ × ℝ => (ℓ : ℂ) ^ 2)).add
      (hnum.continuousOn.div hden.continuousOn fun q hq => by
        intro h0
        have hre := congrArg Complex.re h0
        rw [re_add_I_mul_ofReal _ _ (by simp)] at hre
        simp only [Complex.zero_re] at hre
        exact (ne_of_gt hq.2.1) hre)
    refine h.congr fun q _ => ?_
    simp only [hVdef, Function.uncurry, Vric, Pi.add_apply, Pi.div_apply]
  have hsol := LinODE.continuousOn_sol hV S.ξ₁ (y₀ := fun _ => ((1 : ℂ), (ℓ : ℂ)))
    continuousOn_const
  exact (continuous_fst.comp_continuousOn hsol).congr fun q _ => rfl

/-- `ψ_ℓ(log r;λ,G)` is jointly continuous on `(0,∞) × {Re λ > 0} × ℝ`. -/
theorem psiLog_continuousOn (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) :
    ContinuousOn (fun q : ℝ × ℂ × ℝ => S.psi ℓ q.2.1 q.2.2 (Real.log q.1))
      (Ioi 0 ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) := by
  have hlog : ContinuousOn (fun q : ℝ × ℂ × ℝ => (Real.log q.1, q.2))
      (Ioi 0 ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) :=
    (Real.continuousOn_log.comp continuousOn_fst fun q hq => ne_of_gt hq.1).prodMk
      continuous_snd.continuousOn
  exact (psi_continuousOn_param S hS ℓ).comp hlog fun q hq => ⟨mem_univ _, hq.2⟩

end PropUH

end SectorSetting

namespace Eig

namespace PropUH

/-- Composition of a function continuous on `(0,∞) × {Re λ > 0} × ℝ` with a path
`G ↦ (Z(G), G)`. -/
theorem continuousOn_comp_path {E : Type*} [TopologicalSpace E] {f : ℝ × ℂ × ℝ → E}
    (hf : ContinuousOn f (Ioi 0 ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ))) {Z : ℝ → ℂ} {T : Set ℝ}
    (hZ : ContinuousOn Z T) (hZre : ∀ G ∈ T, 0 < (Z G).re) {U : Set ℝ} (hU : U ⊆ Ioi 0) :
    ContinuousOn (fun p : ℝ × ℝ => f (p.2, Z p.1, p.1)) (T ×ˢ U) := by
  have hg : ContinuousOn (fun p : ℝ × ℝ => (p.2, Z p.1, p.1)) (T ×ˢ U) :=
    continuousOn_snd.prodMk ((hZ.comp continuousOn_fst fun p hp => hp.1).prodMk continuousOn_fst)
  exact hf.comp hg fun p hp => ⟨hU hp.2, hZre p.1 hp.1, mem_univ _⟩

/-- `G ↦ ∫_c^d F(G,r) dr` is continuous on `[g₀, g₁]` when `F` is jointly continuous on
`[g₀,g₁] × [c,d]` (clamp both variables with `projIcc`). -/
theorem continuousOn_intervalIntegral_rect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → ℝ → E} {g₀ g₁ c d : ℝ} (hg : g₀ ≤ g₁) (hcd : c ≤ d)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc g₀ g₁ ×ˢ Icc c d)) :
    ContinuousOn (fun G => ∫ r in c..d, F G r) (Icc g₀ g₁) := by
  set F' : ℝ → ℝ → E := fun G r => F (projIcc g₀ g₁ hg G) (projIcc c d hcd r) with hF'
  have hc : Continuous (Function.uncurry F') := by
    have hmap : Continuous (fun p : ℝ × ℝ =>
        (((projIcc g₀ g₁ hg p.1 : Icc g₀ g₁) : ℝ), ((projIcc c d hcd p.2 : Icc c d) : ℝ))) :=
      ((continuous_subtype_val.comp continuous_projIcc).comp continuous_fst).prodMk
        ((continuous_subtype_val.comp continuous_projIcc).comp continuous_snd)
    exact hF.comp_continuous hmap fun p => ⟨Subtype.mem _, Subtype.mem _⟩
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hc c d
  refine hcont.continuousOn.congr fun G hG => ?_
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hcd] at hr
  simp only [hF', projIcc_of_mem hg hG, projIcc_of_mem hcd hr]

/-- An integral over `(0,∞)` of a function vanishing off `[c,d] ⊂ (0,∞)` is the interval
integral over `[c,d]`. -/
theorem setIntegral_Ioi_eq_intervalIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hf : ∀ r : ℝ, 0 < r → r ∉ Icc c d → f r = 0) :
    ∫ r in Ioi (0 : ℝ), f r = ∫ r in c..d, f r := by
  rw [intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun r hr => lt_of_lt_of_le hc hr.1) fun r hr => hf r hr.1 hr.2

end PropUH

end Eig

end NonUniqueEuler
