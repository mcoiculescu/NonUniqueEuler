import NonUniqueEuler.Defs.Infra.SectorSpace
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives
import NonUniqueEuler.I.Infra.AngularFourier.NormEquiv
import NonUniqueEuler.I.Infra.SectorSpace.Projection
import NonUniqueEuler.H.Infra.SectorSpace.Decomposition.Basic

/-!
# Proof: the sector decomposition of `Y^s` on an annulus (library I-SECT)

Proof of `I/Infra/SectorSpace/Decomposition.lean` (`04_ring.tex:174-185`, `lem:norm-equiv`
`04_ring.tex:843-864`).

* Single sector (`exists_norm_Ysec_equiv`, `exists_Ysec_ofProfile`, `Ysec.fn_ae_eq_ofProfile`):
  a sector function is `g_ℓ(r)e^{iℓθ}` (`Ang.isSectorFn_iff`), its profile is in `H^s((0,∞))`
  and supported in `[ρ₋, ρ₊]` (`Ang.memH1On_angularSector`), and `Ang.exists_norm_equiv_ofProfile`
  compares the norms; the norm of an element of the type is the `H^s` norm of any function a.e.
  equal to its function (`Sob.Hk.ext_fn`, `Sob.norm_toHk`).
* `exists_norm_equiv_Y`: the function of `P_ℓ w` is `w_ℓ(r) e^{iℓθ}` a.e.
  (`Ang.sectorProj_eq_angularSector`), so `‖P_ℓ w‖² ≍ ‖w_ℓ‖²_{s,ℓ}` uniformly in `ℓ`; combine with
  `Ang.exists_norm_equiv` (`‖w‖² ≍ ∑_ℓ ‖w_ℓ‖²_{s,ℓ}`).
* `hasSum_secProj`: the sectors of `w - ∑_{ℓ ∈ F} P_ℓ w` are `P_m w` for `m ∉ F` and `0` for
  `m ∈ F` (`secProj_inclSec`), so by the norm equivalence
  `‖w - ∑_{ℓ ∈ F} P_ℓ w‖² ≤ C ∑_{m ∉ F} ‖P_m w‖² → 0`.
* `exists_Y_of_summable`: by the same computation `‖∑_{ℓ ∈ t} g_ℓ‖² ≤ C ∑_{ℓ ∈ t} ‖g_ℓ‖²`, so the
  series is Cauchy in the complete space `Y^s`; its sum has sectors `g_m` (continuity of `P_m`).
-/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Sect

open Sob Ang

namespace DecompP

open DecompH

variable {s : ℕ} {ρm ρp : ℝ}

theorem ae_ne_zero : ∀ᵐ x : ℂ, x ≠ 0 :=
  measure_eq_zero_iff_ae_notMem.1 (measure_singleton 0)

/-- The function of `g ∈ Y^s_ℓ` is `g_ℓ(r) e^{iℓθ}`. -/
theorem Ysec_fn_ae_eq_ofProfile {ℓ : ℤ} (g : Ysec s (closedAnnulus ρm ρp) ℓ) :
    g.fn =ᵐ[volume] ofProfile ℓ (Polar.angularSector g.fn ℓ) :=
  (isSectorFn_iff (memLp_tupleFn _)).2.1 (Ysec.isSectorFn g)

/-- The function of `P_ℓ w` is `w_ℓ(r) e^{iℓθ}`. -/
theorem secProj_fn_ae_eq_ofProfile (ℓ : ℤ) (w : Y s (closedAnnulus ρm ρp)) :
    (secProj s _ ℓ w).fn =ᵐ[volume] ofProfile ℓ (Polar.angularSector w.fn ℓ) := by
  filter_upwards [(secProj_spec (isRotInvariant_closedAnnulus ρm ρp) ℓ).1 w, ae_ne_zero]
    with x hx h0
  rw [hx, sectorProj_eq_angularSector ℓ w.fn h0]
  rfl

/-- The profile norm equivalence, for the profiles of functions in `H^s` supported in the
annulus. -/
theorem exists_profile_bounds (s : ℕ) (hρm : 0 < ρm) (hρ : ρm < ρp) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ℓ : ℤ) (f : ℂ → ℂ), MemH s f →
      (∀ᵐ x ∂volume, x ∉ closedAnnulus ρm ρp → f x = 0) →
      MemH s (ofProfile ℓ (Polar.angularSector f ℓ)) ∧
        c * secNormSq s ℓ (Icc ρm ρp) (Polar.angularSector f ℓ) ≤
          normH s (ofProfile ℓ (Polar.angularSector f ℓ)) ^ 2 ∧
        normH s (ofProfile ℓ (Polar.angularSector f ℓ)) ^ 2 ≤
          C * secNormSq s ℓ (Icc ρm ρp) (Polar.angularSector f ℓ) := by
  obtain ⟨c, C, hc, hC, H⟩ := exists_norm_equiv_ofProfile s hρm hρ
  refine ⟨c, C, hc, hC, fun ℓ f hf hfK => ?_⟩
  have hp := memH1On_angularSector (ρp := ρp) hρm hf hfK ℓ
  exact H ℓ _ hp.1 hp.2

/-- `‖P_ℓ w‖² ≍ ‖w_ℓ‖²_{s,ℓ}`, uniformly in `ℓ`. -/
theorem exists_secProj_bounds (s : ℕ) (hρm : 0 < ρm) (hρ : ρm < ρp) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ℓ : ℤ) (w : Y s (closedAnnulus ρm ρp)),
      c * secNormSq s ℓ (Icc ρm ρp) (Polar.angularSector w.fn ℓ) ≤
          ‖secProj s _ ℓ w‖ ^ 2 ∧
        ‖secProj s _ ℓ w‖ ^ 2 ≤ C * secNormSq s ℓ (Icc ρm ρp) (Polar.angularSector w.fn ℓ) := by
  obtain ⟨c, C, hc, hC, H⟩ := exists_profile_bounds s hρm hρ
  refine ⟨c, C, hc, hC, fun ℓ w => ?_⟩
  obtain ⟨hm, h1, h2⟩ := H ℓ w.fn (Y.memH_fn w) (Y.supp w)
  rw [Ysec.norm_eq_normH_of_ae hm (secProj_fn_ae_eq_ofProfile ℓ w)]
  exact ⟨h1, h2⟩

/-- The sectors of a finite sum of sector elements. -/
theorem coe_secProj_sum_inclSec (m : ℤ) (F : Finset ℤ)
    (g : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ) :
    ((secProj s _ m (∑ ℓ ∈ F, inclSec s _ ℓ (g ℓ)) : Ysec s _ m) : SobTuple s) =
      if m ∈ F then (g m : SobTuple s) else 0 := by
  rw [map_sum, Submodule.coe_sum]
  simp_rw [secProj_inclSec (isRotInvariant_closedAnnulus ρm ρp)]
  exact Finset.sum_ite_eq F m _

theorem norm_secProj_sum_inclSec (m : ℤ) (F : Finset ℤ)
    (g : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ) :
    ‖secProj s _ m (∑ ℓ ∈ F, inclSec s _ ℓ (g ℓ))‖ ^ 2 =
      if m ∈ F then ‖g m‖ ^ 2 else 0 := by
  have h : ‖secProj s _ m (∑ ℓ ∈ F, inclSec s _ ℓ (g ℓ))‖ =
      ‖((secProj s _ m (∑ ℓ ∈ F, inclSec s _ ℓ (g ℓ)) : Ysec s _ m) : SobTuple s)‖ := rfl
  rw [h, coe_secProj_sum_inclSec]
  by_cases hm : m ∈ F
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm), ite_eq_left_of_eq_true _ _ (eq_true hm)]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm), ite_eq_right_of_eq_false _ _ (eq_false hm), norm_zero,
      sq, mul_zero]

theorem norm_secProj_sub_sum (m : ℤ) (F : Finset ℤ) (w : Y s (closedAnnulus ρm ρp)) :
    ‖secProj s _ m (w - ∑ ℓ ∈ F, inclSec s _ ℓ (secProj s _ ℓ w))‖ ^ 2 =
      if m ∈ F then 0 else ‖secProj s _ m w‖ ^ 2 := by
  have h : ‖secProj s _ m (w - ∑ ℓ ∈ F, inclSec s _ ℓ (secProj s _ ℓ w))‖ =
      ‖((secProj s _ m (w - ∑ ℓ ∈ F, inclSec s _ ℓ (secProj s _ ℓ w)) : Ysec s _ m) :
        SobTuple s)‖ := rfl
  rw [h, map_sub, Submodule.coe_sub, coe_secProj_sum_inclSec]
  by_cases hm : m ∈ F
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm), ite_eq_left_of_eq_true _ _ (eq_true hm), sub_self,
      norm_zero, sq, mul_zero]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm), ite_eq_right_of_eq_false _ _ (eq_false hm), sub_zero]
    rfl

end DecompP

open DecompH DecompP

/-- The two-sided bound `c ∑ ‖P_ℓ w‖² ≤ ‖w‖² ≤ C ∑ ‖P_ℓ w‖²`. -/
theorem exists_norm_equiv_Y (s : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w : Y s (closedAnnulus ρm ρp),
      Summable (fun ℓ : ℤ => ‖secProj s _ ℓ w‖ ^ 2) ∧
        c * ∑' ℓ : ℤ, ‖secProj s _ ℓ w‖ ^ 2 ≤ ‖w‖ ^ 2 ∧
        ‖w‖ ^ 2 ≤ C * ∑' ℓ : ℤ, ‖secProj s _ ℓ w‖ ^ 2 := by
  obtain ⟨c₁, C₁, hc₁, hC₁, H₁⟩ := exists_secProj_bounds s hρm hρ
  obtain ⟨c₂, C₂, hc₂, hC₂, H₂⟩ := exists_norm_equiv s hρm hρ
  refine ⟨c₂ / C₁, C₂ / c₁, div_pos hc₂ hC₁, div_pos hC₂ hc₁, fun w => ?_⟩
  obtain ⟨hS, hlo, hhi⟩ := H₂ w.fn (Y.memH_fn w) (Y.supp w)
  rw [Y.normH_fn] at hlo hhi
  have ha : Summable (fun ℓ : ℤ => ‖secProj s _ ℓ w‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun ℓ => sq_nonneg _) (fun ℓ => (H₁ ℓ w).2) (hS.mul_left C₁)
  have h1 : ∑' ℓ : ℤ, ‖secProj s _ ℓ w‖ ^ 2 ≤
      C₁ * ∑' ℓ : ℤ, secNormSq s ℓ (Icc ρm ρp) (Polar.angularSector w.fn ℓ) := by
    rw [← hS.tsum_mul_left C₁]
    exact Summable.tsum_le_tsum (fun ℓ => (H₁ ℓ w).2) ha (hS.mul_left C₁)
  have h2 : c₁ * ∑' ℓ : ℤ, secNormSq s ℓ (Icc ρm ρp) (Polar.angularSector w.fn ℓ) ≤
      ∑' ℓ : ℤ, ‖secProj s _ ℓ w‖ ^ 2 := by
    rw [← hS.tsum_mul_left c₁]
    exact Summable.tsum_le_tsum (fun ℓ => (H₁ ℓ w).1) (hS.mul_left c₁) ha
  refine ⟨ha, ?_, ?_⟩
  · calc c₂ / C₁ * ∑' ℓ : ℤ, ‖secProj s _ ℓ w‖ ^ 2
        ≤ c₂ / C₁ * (C₁ * ∑' ℓ : ℤ, secNormSq s ℓ (Icc ρm ρp) (Polar.angularSector w.fn ℓ)) :=
          mul_le_mul_of_nonneg_left h1 (div_pos hc₂ hC₁).le
      _ = c₂ * ∑' ℓ : ℤ, secNormSq s ℓ (Icc ρm ρp) (Polar.angularSector w.fn ℓ) := by
          field_simp
      _ ≤ ‖w‖ ^ 2 := hlo
  · calc ‖w‖ ^ 2 ≤ C₂ * ∑' ℓ : ℤ, secNormSq s ℓ (Icc ρm ρp) (Polar.angularSector w.fn ℓ) := hhi
      _ = C₂ / c₁ * (c₁ * ∑' ℓ : ℤ, secNormSq s ℓ (Icc ρm ρp) (Polar.angularSector w.fn ℓ)) := by
          field_simp
      _ ≤ C₂ / c₁ * ∑' ℓ : ℤ, ‖secProj s _ ℓ w‖ ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (div_pos hC₂ hc₁).le

/-- `w = ∑_ℓ P_ℓ w` in `Y^s`. -/
theorem hasSum_secProj {s : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    (w : Y s (closedAnnulus ρm ρp)) :
    HasSum (fun ℓ : ℤ => inclSec s _ ℓ (secProj s _ ℓ w)) w := by
  obtain ⟨c, C, hc, hC, H⟩ := exists_norm_equiv_Y s hρm hρ
  have ha := (H w).1
  set T := ∑' ℓ : ℤ, ‖secProj s _ ℓ w‖ ^ 2 with hTdef
  have hT : HasSum (fun ℓ : ℤ => ‖secProj s _ ℓ w‖ ^ 2) T := ha.hasSum
  have key : ∀ F : Finset ℤ, ‖w - ∑ ℓ ∈ F, inclSec s _ ℓ (secProj s _ ℓ w)‖ ^ 2 ≤
      C * (T - ∑ ℓ ∈ F, ‖secProj s _ ℓ w‖ ^ 2) := by
    intro F
    have hF : HasSum (fun m : ℤ => if m ∈ F then ‖secProj s _ m w‖ ^ 2 else 0)
        (∑ ℓ ∈ F, ‖secProj s _ ℓ w‖ ^ 2) := by
      have h0 : HasSum (fun m : ℤ => if m ∈ F then ‖secProj s _ m w‖ ^ 2 else 0)
          (∑ m ∈ F, if m ∈ F then ‖secProj s _ m w‖ ^ 2 else 0) :=
        hasSum_sum_of_ne_finset_zero (fun m hm => ite_eq_right_of_eq_false _ _ (eq_false hm))
      rwa [Finset.sum_congr rfl fun m hm => ite_eq_left_of_eq_true _ _ (eq_true hm)] at h0
    have hsub : HasSum
        (fun m : ℤ => ‖secProj s _ m (w - ∑ ℓ ∈ F, inclSec s _ ℓ (secProj s _ ℓ w))‖ ^ 2)
        (T - ∑ ℓ ∈ F, ‖secProj s _ ℓ w‖ ^ 2) := by
      refine (hT.sub hF).congr_fun fun m => ?_
      rw [norm_secProj_sub_sum]
      by_cases hm : m ∈ F
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hm), ite_eq_left_of_eq_true _ _ (eq_true hm),
          sub_self]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hm),
          ite_eq_right_of_eq_false _ _ (eq_false hm), sub_zero]
    have h := (H (w - ∑ ℓ ∈ F, inclSec s _ ℓ (secProj s _ ℓ w))).2.2
    rwa [hsub.tsum_eq] at h
  have hlim : Tendsto (fun F : Finset ℤ => Real.sqrt (C * (T - ∑ ℓ ∈ F, ‖secProj s _ ℓ w‖ ^ 2)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun F : Finset ℤ => ∑ ℓ ∈ F, ‖secProj s _ ℓ w‖ ^ 2) atTop (𝓝 T) := hT
    have h2 := (((tendsto_const_nhds (x := T)).sub h1).const_mul C).sqrt
    rwa [sub_self, mul_zero, Real.sqrt_zero] at h2
  have hconv : Tendsto (fun F : Finset ℤ => ∑ ℓ ∈ F, inclSec s _ ℓ (secProj s _ ℓ w)) atTop
      (𝓝 w) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun F => ?_) hlim
    rw [norm_sub_rev]
    exact (le_abs_self _).trans (Real.abs_le_sqrt (key F))
  exact hconv

/-- Synthesis from square-summable sector components. -/
theorem exists_Y_of_summable {s : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    (g : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ) (hg : Summable (fun ℓ : ℤ => ‖g ℓ‖ ^ 2)) :
    ∃ w : Y s (closedAnnulus ρm ρp), (∀ ℓ, secProj s _ ℓ w = g ℓ) ∧
      HasSum (fun ℓ : ℤ => inclSec s _ ℓ (g ℓ)) w := by
  obtain ⟨c, C, hc, hC, H⟩ := exists_norm_equiv_Y s hρm hρ
  have hK := isRotInvariant_closedAnnulus ρm ρp
  have hfin : ∀ t : Finset ℤ,
      ‖∑ ℓ ∈ t, inclSec s _ ℓ (g ℓ)‖ ^ 2 ≤ C * ∑ ℓ ∈ t, ‖g ℓ‖ ^ 2 := by
    intro t
    have hsum : HasSum (fun m : ℤ => ‖secProj s _ m (∑ ℓ ∈ t, inclSec s _ ℓ (g ℓ))‖ ^ 2)
        (∑ ℓ ∈ t, ‖g ℓ‖ ^ 2) := by
      have h0 : HasSum (fun m : ℤ => if m ∈ t then ‖g m‖ ^ 2 else 0)
          (∑ m ∈ t, if m ∈ t then ‖g m‖ ^ 2 else 0) :=
        hasSum_sum_of_ne_finset_zero (fun m hm => ite_eq_right_of_eq_false _ _ (eq_false hm))
      rw [Finset.sum_congr rfl fun m hm => ite_eq_left_of_eq_true _ _ (eq_true hm)] at h0
      exact h0.congr_fun fun m => norm_secProj_sum_inclSec m t g
    have h := (H (∑ ℓ ∈ t, inclSec s _ ℓ (g ℓ))).2.2
    rwa [hsum.tsum_eq] at h
  have hsumm : Summable (fun ℓ : ℤ => inclSec s _ ℓ (g ℓ)) := by
    rw [summable_iff_vanishing_norm]
    intro ε hε
    obtain ⟨u, hu⟩ := (summable_iff_vanishing_norm.1 hg) (ε ^ 2 / C) (by positivity)
    refine ⟨u, fun t ht => ?_⟩
    have h1 := hu t ht
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h1
    have h3 : ‖∑ ℓ ∈ t, inclSec s _ ℓ (g ℓ)‖ ^ 2 < ε ^ 2 :=
      calc ‖∑ ℓ ∈ t, inclSec s _ ℓ (g ℓ)‖ ^ 2 ≤ C * ∑ ℓ ∈ t, ‖g ℓ‖ ^ 2 := hfin t
        _ < C * (ε ^ 2 / C) := mul_lt_mul_of_pos_left h1 hC
        _ = ε ^ 2 := by field_simp
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  obtain ⟨w, hw⟩ := hsumm
  refine ⟨w, fun m => ?_, hw⟩
  have h1 : HasSum (fun ℓ => secProj s _ m (inclSec s _ ℓ (g ℓ))) (secProj s _ m w) :=
    (secProj s _ m).hasSum hw
  have hz : ∀ ℓ, ℓ ≠ m → secProj s _ m (inclSec s _ ℓ (g ℓ)) = 0 := by
    intro ℓ hℓ
    apply Subtype.ext
    rw [secProj_inclSec hK, ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm hℓ))]
    rfl
  have hm : secProj s _ m (inclSec s _ m (g m)) = g m := by
    apply Subtype.ext
    rw [secProj_inclSec hK, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  have h2 : HasSum (fun ℓ => secProj s _ m (inclSec s _ ℓ (g ℓ))) (g m) := by
    rw [← hm]
    exact hasSum_single m hz
  exact h1.unique h2

/-- On a single sector, the `Y^s_ℓ` norm is comparable to the profile norm `‖g_ℓ‖_{s,ℓ}`,
uniformly in `ℓ`. -/
theorem exists_norm_Ysec_equiv (s : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ℓ : ℤ) (g : Ysec s (closedAnnulus ρm ρp) ℓ),
      c * secNormSq s ℓ (Icc ρm ρp) (Polar.angularSector g.fn ℓ) ≤ ‖g‖ ^ 2 ∧
        ‖g‖ ^ 2 ≤ C * secNormSq s ℓ (Icc ρm ρp) (Polar.angularSector g.fn ℓ) := by
  obtain ⟨c, C, hc, hC, H⟩ := exists_profile_bounds s hρm hρ
  refine ⟨c, C, hc, hC, fun ℓ g => ?_⟩
  obtain ⟨hm, h1, h2⟩ := H ℓ g.fn (Ysec.memH_fn g) (Ysec.supp g)
  rw [Ysec.norm_eq_normH_of_ae hm (Ysec_fn_ae_eq_ofProfile g)]
  exact ⟨h1, h2⟩

/-- Every profile in `H^s((0, ∞))` supported in `[ρ₋, ρ₊]` defines an element of `Y^s_ℓ`. -/
theorem exists_Ysec_ofProfile {s : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) (ℓ : ℤ)
    {h : ℝ → ℂ} (hh : MemH1On s (Ioi 0) h)
    (hhI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0) :
    ∃ g : Ysec s (closedAnnulus ρm ρp) ℓ, g.fn =ᵐ[volume] ofProfile ℓ h := by
  obtain ⟨c, C, hc, hC, H⟩ := exists_norm_equiv_ofProfile s hρm hρ
  have hm : MemH s (ofProfile ℓ h) := (H ℓ h hh hhI).1
  have hF : tupleFn ((toHk s (ofProfile ℓ h) : Hk s) : SobTuple s) =ᵐ[volume] ofProfile ℓ h :=
    toHk_fn hm
  have hsupp : ∀ᵐ x ∂volume, x ∉ closedAnnulus ρm ρp → ofProfile ℓ h x = 0 := by
    filter_upwards [ae_comp_norm hhI] with x hx hxK
    rw [ofProfile, hx hxK, zero_mul]
  have hsec : IsSectorFn ℓ (tupleFn ((toHk s (ofProfile ℓ h) : Hk s) : SobTuple s)) := by
    rw [(isSectorFn_iff (memLp_tupleFn _)).1]
    filter_upwards [hF, sectorProj_congr_ae ℓ hF] with x h1 h2
    rw [h1, h2, sectorProj_ofProfile, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  have hmem : ((toHk s (ofProfile ℓ h) : Hk s) : SobTuple s) ∈
      YsecSub s (closedAnnulus ρm ρp) ℓ := by
    rw [mem_YsecSub_iff', mem_YSub_iff]
    refine ⟨⟨(toHk s (ofProfile ℓ h)).2, ?_⟩, hsec⟩
    filter_upwards [hF, hsupp] with x h1 h2 hxK
    rw [h1]
    exact h2 hxK
  exact ⟨⟨_, hmem⟩, hF⟩

-- `hρm` is part of the interface statement; it is not needed for this item.
set_option linter.unusedVariables false in
/-- The profile of an element of `Y^s_ℓ` recovers it. -/
theorem Ysec.fn_ae_eq_ofProfile {s : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) {ℓ : ℤ}
    (g : Ysec s (closedAnnulus ρm ρp) ℓ) :
    g.fn =ᵐ[volume] ofProfile ℓ (Polar.angularSector g.fn ℓ) :=
  Ysec_fn_ae_eq_ofProfile g

end NonUniqueEuler.Sect
