import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.I.Sec4.Elliptic
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.SobolevOneD.Multiplier
import NonUniqueEuler.I.Infra.SobolevOneD.MultiplierLocal

/-!
# Proof of `I/Sec4/Resolvent/Regularity.lean`: `H^s` regularity of resolvent solutions

Proof of `lem:resolvent`(1), the regularity on `Y^s_ℓ` (`04_ring.tex:423-433`), restructured as
in the interface file: the solution `h ∈ Y^0_ℓ` of `z h - L_ℓ(G) h = g` satisfies
`h = M_λ (g + k_ℓ 𝒢_ℓ h)` a.e. on `(0,∞)`, and a bootstrap on the number of derivatives with
`lem:elliptic` (`𝒢_ℓ` gains two derivatives) and the multiplier lemmas gives `h ∈ H^s((0,∞))`.

Helpers (namespace `NonUniqueEuler.ResolventRegularityAux`):
* one-dimensional `H^k((0,∞))` facts: `memH1On_zero_of_memLp`, `memH1On_add`, `memH1On_congr`
  (weak derivatives only see the a.e. class on `(0,∞)`);
* smoothness and derivative bounds of the multipliers: `contDiffOn_kcoef`, `contDiffOn_Mres`,
  `exists_iteratedDeriv_bound` (some copied from `H/Sec4/Resolvent/Profile.lean`);
* `ae_eq_fixed_point`: `h = M_λ (g + k_ℓ 𝒢_ℓ h)` a.e. on `(0,∞)`.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace NonUniqueEuler

namespace ResolventRegularityAux

open Sob SectorSetting

/-! ### One-dimensional Sobolev facts on `(0,∞)` -/

/-- `L²` on a subset of the line gives local integrability there. -/
theorem locInt_of_memLp {V : Set ℝ} {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict V)) :
    LocallyIntegrableOn f V :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable one_le_two)

/-- `H^0(V) = L²(V)`. -/
theorem memH1On_zero_of_memLp {V : Set ℝ} {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict V)) :
    MemH1On 0 V f := by
  refine ⟨hf, fun j hj => ⟨f, hf, ?_⟩⟩
  obtain rfl : j = 0 := Nat.le_zero.1 hj
  intro φ _
  simp [derivList]

/-- Sums of `H^k((0,∞))` profiles. -/
theorem memH1On_add {k : ℕ} {f₁ f₂ : ℝ → ℂ} (h₁ : MemH1On k (Ioi 0) f₁)
    (h₂ : MemH1On k (Ioi 0) f₂) : MemH1On k (Ioi 0) (fun r => f₁ r + f₂ r) := by
  refine ⟨h₁.memLp.add h₂.memLp, fun j hj => ?_⟩
  obtain ⟨u₁, hu₁, hd₁⟩ := h₁.deriv j hj
  obtain ⟨u₂, hu₂, hd₂⟩ := h₂.deriv j hj
  exact ⟨u₁ + u₂, hu₁.add hu₂, HasWeakDerivOn.add isOpen_Ioi (locInt_of_memLp h₁.memLp)
    (locInt_of_memLp h₂.memLp) (locInt_of_memLp hu₁) (locInt_of_memLp hu₂) hd₁ hd₂⟩

/-- `H^k((0,∞))` membership passes to a function that is a.e. equal on `(0,∞)`. -/
theorem memH1On_congr {k : ℕ} {f f' : ℝ → ℂ} (hf : MemH1On k (Ioi 0) f)
    (hff' : f =ᵐ[volume.restrict (Ioi 0)] f') : MemH1On k (Ioi 0) f' := by
  have hae : ∀ᵐ x, x ∈ Ioi (0 : ℝ) → f x = f' x := (ae_restrict_iff' measurableSet_Ioi).1 hff'
  refine ⟨hf.memLp.ae_eq hff', fun j hj => ?_⟩
  obtain ⟨u, hu, hd⟩ := hf.deriv j hj
  exact ⟨u, hu, hd.congr_ae hae (Filter.Eventually.of_forall fun _ _ => rfl)⟩

/-- A profile in `Y^0_ℓ` is in `L²((0,∞))`. -/
theorem memLp_Ioi_of_isProfileL2 (S : SectorSetting) {h : ℝ → ℂ} (hh : S.IsProfileL2 h) :
    MemLp h 2 (volume.restrict (Ioi 0)) := by
  have hind : MemLp ((Icc S.ρm S.ρp).indicator h) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc).2 hh.1
  refine (hind.restrict (Ioi 0)).ae_eq ?_
  filter_upwards [hh.2] with r hr
  by_cases hrI : r ∈ Icc S.ρm S.ρp
  · simp [indicator_of_mem hrI]
  · rw [indicator_of_notMem hrI, hr hrI]

/-! ### The multipliers `k_ℓ` and `M_λ` -/

theorem denom_ne_zero (S : SectorSetting) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ) (G r : ℝ) :
    z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

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

theorem kcoef_eq_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) {r : ℝ} (hr : 0 < r)
    (hrI : r ∉ Icc S.r₁ S.r₂) : S.kcoef ℓ r = 0 := by
  simp [kcoef, hS.dom_eq_zero r hr hrI]

theorem continuousOn_iteratedDeriv {a : ℝ → ℂ} (ha : ContDiffOn ℝ ∞ a (Ioi 0)) (j : ℕ) :
    ContinuousOn (iteratedDeriv j a) (Ioi 0) := by
  have h1 : ContinuousOn (iteratedDerivWithin j a (Ioi 0)) (Ioi 0) :=
    ha.continuousOn_iteratedDerivWithin (by exact_mod_cast le_top) isOpen_Ioi.uniqueDiffOn
  exact h1.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm

/-- A function smooth on `(0,∞)` has bounded derivatives of order `≤ k` on a compact
`[α, β] ⊂ (0,∞)`. -/
theorem exists_iteratedDeriv_bound {a : ℝ → ℂ} (ha : ContDiffOn ℝ ∞ a (Ioi 0)) {α β : ℝ}
    (hα : 0 < α) (k : ℕ) :
    ∃ M : ℝ, ∀ i ≤ k, ∀ r ∈ Icc α β, ‖iteratedDeriv i a r‖ ≤ M := by
  have hIcc : Icc α β ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le hα hr.1
  have hc : ContinuousOn (fun r => ∑ i ∈ Finset.range (k + 1), ‖iteratedDeriv i a r‖)
      (Icc α β) :=
    continuousOn_finsetSum _ fun i _ => ((continuousOn_iteratedDeriv ha i).mono hIcc).norm
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨M, fun i hi r hr => ?_⟩
  have h1 := hM r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
  exact le_trans (Finset.single_le_sum (f := fun i => ‖iteratedDeriv i a r‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) h1

/-! ### The fixed-point identity -/

/-- `z h - L_ℓ h = g` gives `h = M_λ (g + k_ℓ 𝒢_ℓ h)` a.e. on `(0,∞)`. -/
theorem ae_eq_fixed_point (S : SectorSetting) (ℓ : ℤ) {z : ℂ} (hz : 0 < z.re) (G : ℝ)
    {g h : ℝ → ℂ}
    (heq : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), z * h r - S.LsecFn ℓ G h r = g r) :
    h =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun r => S.Mres ℓ z G r * (g r + S.kcoef ℓ r * green ℓ h r) := by
  filter_upwards [heq] with r hr
  have hd : (z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)) * S.Mres ℓ z G r = 1 :=
    mul_inv_cancel₀ (denom_ne_zero S hz ℓ G r)
  have e : g r + S.kcoef ℓ r * green ℓ h r =
      (z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)) * h r := by
    rw [← hr, LsecFn_eq]
    ring
  rw [e]
  linear_combination (-(h r)) * hd

end ResolventRegularityAux

namespace SectorSetting

open Sob ResolventRegularityAux

/-- Proof of `lem:resolvent`(1), regularity on `Y^s_ℓ` (`04_ring.tex:423-433`, restructured):
a solution `h ∈ Y^0_ℓ` of `z h - L_ℓ(G) h = g` with `g ∈ H^s((0,∞))` supported in `[ρ₋,ρ₊]`
lies in `H^s((0,∞))`. -/
theorem memH1On_of_resolvent_eq (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (z : ℂ) (hz : 0 < z.re) (G : ℝ) (s : ℕ) {g h : ℝ → ℂ} (hh : S.IsProfileL2 h)
    (hg : Sob.MemH1On s (Ioi 0) g)
    (hgI : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ Icc S.ρm S.ρp → g r = 0)
    (heq : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), z * h r - S.LsecFn ℓ G h r = g r) :
    Sob.MemH1On s (Ioi 0) h := by
  have hρm := hS.ρm_pos
  have hρ := hS.ρm_lt_ρp
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  have hk := contDiffOn_kcoef S hS (ℓ : ℤ)
  have hM := contDiffOn_Mres S hS hz (ℓ : ℤ) G
  obtain ⟨Mk, hMk⟩ := exists_iteratedDeriv_bound hk (β := S.r₂) hS.r₁_pos s
  obtain ⟨MM, hMM⟩ := exists_iteratedDeriv_bound hM (β := S.ρp) hρm s
  have hfix := ae_eq_fixed_point S (ℓ : ℤ) hz G heq
  -- the right side `g + k_ℓ 𝒢_ℓ h` vanishes off `[ρ₋, ρ₊]`
  have hFsupp : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ Icc S.ρm S.ρp →
      g r + S.kcoef ℓ r * green ℓ h r = 0 := by
    filter_upwards [hgI, ae_restrict_mem measurableSet_Ioi] with r hr hr0 hrI
    have hr' : r ∉ Icc S.r₁ S.r₂ := fun h' =>
      hrI ⟨hS.ρm_lt_r₁.le.trans h'.1, h'.2.trans hS.r₂_lt_ρp.le⟩
    rw [hr hrI, kcoef_eq_zero S hS _ hr0 hr']
    ring
  -- bootstrap on the number of derivatives
  have key : ∀ j, j ≤ s → Sob.MemH1On j (Ioi 0) h := by
    intro j
    induction j with
    | zero => exact fun _ => memH1On_zero_of_memLp (memLp_Ioi_of_isProfileL2 S hh)
    | succ j ih =>
      intro hj
      have hhj := ih (by omega)
      obtain ⟨C, -, hC⟩ := elliptic j hρm hρ hρm le_rfl
      have hG : Sob.MemH1On (j + 1) (Ioi 0) (green ℓ h) :=
        (hC (ℓ : ℤ) hℓ0 h hhj hh.2).1.mono_order (by omega)
      have hkG := (secNormSq_mul_le_of_vanish hS.r₁_pos (hk.of_le (by exact_mod_cast le_top))
        (fun r hr hrI => kcoef_eq_zero S hS _ hr hrI)
        (fun i hi r hr => hMk i (hi.trans hj) r hr) hG (ℓ : ℤ)).1
      have hF := memH1On_add (hg.mono_order hj) hkG
      have hMF := (secNormSq_mul_le hρm (hM.of_le (by exact_mod_cast le_top))
        (fun i hi r hr => hMM i (hi.trans hj) r hr) hF hFsupp (ℓ : ℤ)).1
      exact memH1On_congr hMF hfix.symm
  exact key s le_rfl

end SectorSetting

end NonUniqueEuler
