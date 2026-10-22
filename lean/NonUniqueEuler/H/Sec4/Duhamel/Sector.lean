import NonUniqueEuler.Defs.Sec4.Linear
import NonUniqueEuler.I.Sec4.SemigroupLaw
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition
import NonUniqueEuler.I.Infra.SectorSpace.BanachExp
import NonUniqueEuler.H.Sec4.Duhamel.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

/-!
# Helper for `lem:duhamel`: the semigroup in ring units, sector-wise Duhamel, continuity

Helper of `P/Sec4/Duhamel.lean` (restructuring R1: the proof is sector-wise with bounded
operators). For the ring in ring units (`ringPhiSetting χ`, valid by `lem:ring-facts`):

* `S_jointCont`: `(t, w) ↦ e^{tL(G)}w` is jointly continuous on `[0,T] × Y^s(N)`
  (`semigroup_bound`, `semigroup_continuousOn`);
* `integrand_continuousOn`, `integrand_intervalIntegrable`, `integral_continuousOn`,
  `duhamel_continuousOn`: the Duhamel integrand is continuous and the Duhamel integral is
  continuous in `t` (substitution `τ ↦ t - τ` and continuity of parametric primitives);
* `lower_duhamel`: the Duhamel integral in `Y^{k+1}` lowered to `Y^k` is the Duhamel integral in
  `Y^k` of the lowered data (`semigroup_lowerY`);
* `secProj_duhamel`: `P_ℓ` of the Duhamel integral is the sector Duhamel integral with
  `exp(tL_ℓ(G))` (`semigroup_sector`);
* `secProj_L`: `P_ℓ L(G) w = L_ℓ(G) P_ℓ w` for `w ∈ Y^{k+1}` (the generator identity
  `semigroup_hasDerivWithinAt` at `t = 0`, compared sector-wise with `d/dt exp(tL_ℓ)` at `0`);
* `ext_secProj`: elements of `Y^s(N)` are determined by their sector projections;
* `hasDerivWithinAt_lower_duhamel`: the main step of `lem:duhamel`, `∂_t u = L(G)u + g` in `Y^k`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.Lin.DuhamelAux

open Sect RingData SectorSetting

variable {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ)

include hχ

theorem annN_ρm_pos : 0 < a / 2 := (ringPhiSetting_valid hχ).ρm_pos

theorem annN_ρm_lt : a / 2 < 2 := (ringPhiSetting_valid hχ).ρm_lt_ρp

/-- Local uniform bound of `e^{tL(G)}` on `[0, T]`. -/
theorem S_bound (s : ℕ) (G T : ℝ) : ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ‖S χ s G t‖ ≤ B := by
  obtain ⟨B, hB⟩ := semigroup_bound (ringPhiSetting χ) (ringPhiSetting_valid hχ) s
    (abs_nonneg G) T
  exact ⟨B, fun t ht => hB G le_rfl t ht⟩

/-- Strong continuity of `e^{tL(G)}` on `[0, ∞)`. -/
theorem S_continuousOn (s : ℕ) (G : ℝ) (w : Y s annN) :
    ContinuousOn (fun t => S χ s G t w) (Ici 0) :=
  semigroup_continuousOn (ringPhiSetting χ) (ringPhiSetting_valid hχ) s G w

/-- Joint continuity of `(t, w) ↦ e^{tL(G)} w` on `[0, T] × Y^s(N)`. -/
theorem S_jointCont (s : ℕ) (G T : ℝ) :
    ContinuousOn (fun p : ℝ × Y s annN => S χ s G p.1 p.2) (Icc 0 T ×ˢ univ) := by
  obtain ⟨B, hB⟩ := S_bound hχ s G T
  exact continuousOn_apply_of_bound hB fun x => (S_continuousOn hχ s G x).mono Icc_subset_Ici_self

variable {s : ℕ} {G T : ℝ}

/-- The Duhamel integrand `τ ↦ e^{(t-τ)L} g(τ)` is continuous on `[0, t]`. -/
theorem integrand_continuousOn {g : ℝ → Y s annN} (hg : ContinuousOn g (Icc 0 T)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : ContinuousOn (fun τ => S χ s G (t - τ) (g τ)) (Icc 0 t) := by
  have hmaps : MapsTo (fun τ : ℝ => (t - τ, g τ)) (Icc 0 t) (Icc 0 T ×ˢ univ) := by
    intro τ hτ
    refine mk_mem_prod ⟨?_, ?_⟩ (mem_univ _)
    · linarith [hτ.2]
    · linarith [hτ.1, ht.2]
  have hc : ContinuousOn (fun τ : ℝ => (t - τ, g τ)) (Icc 0 t) :=
    (continuousOn_const.sub continuousOn_id).prodMk (hg.mono (Icc_subset_Icc_right ht.2))
  have := (S_jointCont hχ s G T).comp hc hmaps
  exact this

theorem integrand_intervalIntegrable {g : ℝ → Y s annN} (hg : ContinuousOn g (Icc 0 T))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ => S χ s G (t - τ) (g τ)) volume 0 t :=
  (integrand_continuousOn hχ hg ht).intervalIntegrable_of_Icc ht.1

/-- The Duhamel integral `t ↦ ∫₀ᵗ e^{(t-τ)L} g(τ) dτ` is continuous on `[0, T]`: after the
substitution `σ = t - τ` it is a parametric primitive of a jointly continuous function. -/
theorem integral_continuousOn (hT : 0 ≤ T) {g : ℝ → Y s annN} (hg : ContinuousOn g (Icc 0 T)) :
    ContinuousOn (fun t => ∫ τ in (0 : ℝ)..t, S χ s G (t - τ) (g τ)) (Icc 0 T) := by
  have hp : Continuous fun σ : ℝ => (projIcc 0 T hT σ : ℝ) :=
    continuous_subtype_val.comp continuous_projIcc
  have hpm : ∀ σ, (projIcc 0 T hT σ : ℝ) ∈ Icc 0 T := fun σ => (projIcc 0 T hT σ).2
  have hgp : Continuous fun σ => g (projIcc 0 T hT σ : ℝ) := hg.comp_continuous hp hpm
  have hin : Continuous fun z : ℝ × ℝ =>
      ((projIcc 0 T hT z.2 : ℝ), g (projIcc 0 T hT (z.1 - z.2) : ℝ)) :=
    (hp.comp continuous_snd).prodMk (hgp.comp (continuous_fst.sub continuous_snd))
  have hH0 := (S_jointCont hχ s G T).comp_continuous hin fun z => mk_mem_prod (hpm _) (mem_univ _)
  have hH : Continuous (Function.uncurry fun t σ : ℝ =>
      S χ s G (projIcc 0 T hT σ : ℝ) (g (projIcc 0 T hT (t - σ) : ℝ))) := hH0
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (a₀ := 0) (μ := volume) hH continuous_id
  refine hcont.continuousOn.congr fun t ht => ?_
  have e1 : (∫ τ in (0 : ℝ)..t, S χ s G (t - τ) (g τ)) =
      ∫ τ in (0 : ℝ)..t, (fun σ => S χ s G σ (g (t - σ))) (t - τ) := by
    simp only [sub_sub_cancel]
  simp only [id]
  rw [e1, intervalIntegral.integral_comp_sub_left (fun σ => S χ s G σ (g (t - σ))) t, sub_self,
    sub_zero]
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  rw [uIcc_of_le ht.1] at hσ
  have h1 : (projIcc 0 T hT σ : ℝ) = σ := by
    rw [projIcc_of_mem hT ⟨hσ.1, hσ.2.trans ht.2⟩]
  have h2 : (projIcc 0 T hT (t - σ) : ℝ) = t - σ := by
    rw [projIcc_of_mem hT ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩]
  simp only [h1, h2]

/-- `u ∈ C([0,T]; Y^s(N))` for the Duhamel integral of continuous data. -/
theorem duhamel_continuousOn (hT : 0 ≤ T) (f₀ : Y s annN) {g : ℝ → Y s annN}
    (hg : ContinuousOn g (Icc 0 T)) : ContinuousOn (duhamel χ s G f₀ g) (Icc 0 T) := by
  show ContinuousOn (fun t => S χ s G t f₀ + ∫ τ in (0 : ℝ)..t, S χ s G (t - τ) (g τ)) (Icc 0 T)
  exact ((S_continuousOn hχ s G f₀).mono Icc_subset_Ici_self).add (integral_continuousOn hχ hT hg)

/-- The lowered Duhamel integral is the Duhamel integral of the lowered data. -/
theorem lower_duhamel (k : ℕ) {f₀ : Y (k + 1) annN} {g : ℝ → Y (k + 1) annN}
    (hg : ContinuousOn g (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    lowerY k (k + 1) annN (duhamel χ (k + 1) G f₀ g t) =
      duhamel χ k G (lowerY k (k + 1) annN f₀) (fun τ => lowerY k (k + 1) annN (g τ)) t := by
  have hS := ringPhiSetting_valid hχ
  simp only [duhamel]
  rw [map_add, ← (lowerY k (k + 1) annN).intervalIntegral_comp_comm
    (integrand_intervalIntegrable hχ hg ht)]
  congr 1
  · exact semigroup_lowerY (ringPhiSetting χ) hS (Nat.le_succ k) G ht.1 f₀
  · refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le ht.1] at hτ
    exact semigroup_lowerY (ringPhiSetting χ) hS (Nat.le_succ k) G (sub_nonneg.2 hτ.2) (g τ)

/-- `P_ℓ` of the Duhamel integral is the sector Duhamel integral. -/
theorem secProj_duhamel (s : ℕ) {f : Y s annN} {F : ℝ → Y s annN}
    (hF : ContinuousOn F (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (ℓ : ℤ) :
    secProj s annN ℓ (duhamel χ s G f F t) =
      NormedSpace.exp ((t : ℂ) • Lsec χ s ℓ G) (secProj s annN ℓ f) +
        ∫ τ in (0 : ℝ)..t,
          NormedSpace.exp (((t - τ : ℝ) : ℂ) • Lsec χ s ℓ G) (secProj s annN ℓ (F τ)) := by
  have hS := ringPhiSetting_valid hχ
  simp only [duhamel]
  rw [map_add, ← (secProj s annN ℓ).intervalIntegral_comp_comm
    (integrand_intervalIntegrable hχ hF ht)]
  congr 1
  · exact (semigroup_sector (ringPhiSetting χ) hS s G ht.1 ℓ).1 f
  · refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le ht.1] at hτ
    exact (semigroup_sector (ringPhiSetting χ) hS s G (sub_nonneg.2 hτ.2) ℓ).1 (F τ)

/-- `lem:sector`(2), typed: `P_ℓ L(G) w = L_ℓ(G) P_ℓ w` for `w ∈ Y^{k+1}(N)`. -/
theorem secProj_L (k : ℕ) (G : ℝ) (w : Y (k + 1) annN) (ℓ : ℤ) :
    secProj k annN ℓ (L χ k G w) =
      Lsec χ k ℓ G (secProj k annN ℓ (lowerY k (k + 1) annN w)) := by
  have hS := ringPhiSetting_valid hχ
  have h1 : HasDerivWithinAt (fun τ => S χ k G τ (lowerY k (k + 1) annN w)) (L χ k G w)
      (Ici 0) 0 := by
    have h := (semigroup_hasDerivWithinAt (ringPhiSetting χ) hS k G w (le_refl (0 : ℝ))).1
    have e0 : (ringPhiSetting χ).semigroup (k + 1) G 0 w = w := by
      rw [semigroup_zero (ringPhiSetting χ) hS (k + 1) G]
      rfl
    rw [e0] at h
    exact h
  have h2 := ((secProj k annN ℓ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) h1
  set x := secProj k annN ℓ (lowerY k (k + 1) annN w) with hx
  have h3 : HasDerivWithinAt (fun τ : ℝ => NormedSpace.exp ((τ : ℂ) • Lsec χ k ℓ G) x)
      (Lsec χ k ℓ G x) (Icc 0 1) 0 := by
    have h := BanachExp.hasDerivWithinAt_duhamel (Lsec χ k ℓ G)
      (g := fun _ => (0 : Ysec k annN ℓ)) (T := 1) continuousOn_const x 0
      ⟨le_rfl, zero_le_one⟩
    simp only [map_zero, intervalIntegral.integral_zero, add_zero, Complex.ofReal_zero, zero_smul,
      NormedSpace.exp_zero, one_apply_eq_self] at h
    exact h
  have h4 : HasDerivWithinAt
      ((secProj k annN ℓ) ∘ fun τ => S χ k G τ (lowerY k (k + 1) annN w))
      (Lsec χ k ℓ G x) (Icc 0 1) 0 := by
    refine h3.congr_of_mem (fun τ hτ => ?_) (left_mem_Icc.2 zero_le_one)
    exact (semigroup_sector (ringPhiSetting χ) hS k G hτ.1 ℓ).1 _
  exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc zero_lt_one 0 (left_mem_Icc.2 zero_le_one))
    (h2.mono Icc_subset_Ici_self) h4

/-- Elements of `Y^s(N)` are determined by their sector projections. -/
theorem ext_secProj (s : ℕ) {w w' : Y s annN} (h : ∀ ℓ, secProj s annN ℓ w = secProj s annN ℓ w') :
    w = w' := by
  have h1 : HasSum (fun ℓ : ℤ => inclSec s annN ℓ (secProj s annN ℓ w)) w :=
    hasSum_secProj (annN_ρm_pos hχ) (annN_ρm_lt hχ) w
  have h2 : HasSum (fun ℓ : ℤ => inclSec s annN ℓ (secProj s annN ℓ w')) w' :=
    hasSum_secProj (annN_ρm_pos hχ) (annN_ρm_lt hχ) w'
  have e : (fun ℓ : ℤ => inclSec s annN ℓ (secProj s annN ℓ w)) =
      fun ℓ : ℤ => inclSec s annN ℓ (secProj s annN ℓ w') := funext fun ℓ => by rw [h ℓ]
  rw [e] at h1
  exact h1.unique h2

end NonUniqueEuler.Lin.DuhamelAux
