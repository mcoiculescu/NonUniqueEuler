import NonUniqueEuler.H.Sec4.SemigroupConstruct.Coupling
import NonUniqueEuler.H.Sec4.SemigroupConstruct.ExpTrans
import NonUniqueEuler.I.Infra.Sobolev.Leibniz

/-!
# Helpers for `lem:semigroup-construct`(2): the linearization `L(G) : Y^{s+1} → Y^s`

Helper file of `P/Sec4/SemigroupConstruct.lean` (fully proved). Manuscript `04_ring.tex:938-939`
and `:1000-1003` (`‖L^tr w‖_{H^s} ≤ C‖w‖_{H^{s+1}}`).

* `exists_sectorwise`: uniformly bounded sector operators `B_ℓ : Y^{s'}_ℓ → Y^s_ℓ` define a bounded
  operator `Y^{s'} → Y^s` acting sector-wise (`exists_norm_equiv_Y`, `exists_Y_of_summable`).
* `exists_norm_transLower_le`: `‖-iℓΩ g‖_{Y^s} ≤ C ‖g‖_{Y^{s+1}}` on `Y^{s+1}_ℓ`, uniformly in `ℓ`
  (`|ℓ| ‖g‖_{Y^s} ≤ C ‖g‖_{Y^{s+1}}` by `(1+ℓ²)‖g‖²_{s,ℓ} ≤ ‖g‖²_{s+1,ℓ}` and the norm
  equivalences).
* `memLp_transportPartFn`: `Ω ∂_θ w ∈ L²` for `w ∈ Y^{s+1}`.
* `exists_transportY1`: the transport part `L^tr : Y^{s+1} → Y^s`, `L^tr w = -Ω ∂_θ w`; its
  function is identified through the sector projections (`sectorProj_thetaDeriv`).
* `exists_LinY`: `L(G) = L^tr + 𝒦 ∘ (Y^{s+1} ⊆ Y^s)`.
-/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ContDiff

namespace NonUniqueEuler.SGC

open Sob Sect Ang SectorSetting

/-! ### Sector norms of consecutive orders -/

theorem secNormSq_succ_ge (s : ℕ) (ℓ : ℤ) {I : Set ℝ} (hIm : MeasurableSet I) (hI : I ⊆ Ici 0)
    (h : ℝ → ℂ) : (1 + (ℓ : ℝ) ^ 2) * Sob.secNormSq s ℓ I h ≤ Sob.secNormSq (s + 1) ℓ I h := by
  have hint : ∀ j, 0 ≤ ∫ r in I, ‖weakDeriv1On (Ioi 0) j h r‖ ^ 2 * r := fun j =>
    setIntegral_nonneg hIm fun r hr => mul_nonneg (sq_nonneg _) (hI hr)
  simp only [Sob.secNormSq]
  rw [Finset.sum_range_succ _ (s + 1), Finset.mul_sum]
  refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun j hj => ?_)
    (mul_nonneg (secWeight_nonneg _ _ _) (hint _))
  have hjs : j ≤ s := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [← mul_assoc]
  refine le_of_eq ?_
  congr 1
  simp only [secWeight]
  rw [show s + 1 - j = (s - j) + 1 by omega, pow_succ]
  ring

/-! ### Elements of `Y^s` are determined by their sector projections -/

theorem y_eq_of_secProj {s : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    {v w : Y s (closedAnnulus ρm ρp)}
    (h : ∀ ℓ, secProj s (closedAnnulus ρm ρp) ℓ v = secProj s (closedAnnulus ρm ρp) ℓ w) :
    v = w := by
  have hv := hasSum_secProj hρm hρ v
  have hw := hasSum_secProj hρm hρ w
  simp only [h] at hv
  exact hv.unique hw

/-- Uniformly bounded sector operators `Y^{s'}_ℓ → Y^s_ℓ` give an operator `Y^{s'} → Y^s`. -/
theorem exists_sectorwise {s s' : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    (B : ∀ ℓ : ℤ, Ysec s' (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s (closedAnnulus ρm ρp) ℓ)
    {M : ℝ} (hB : ∀ ℓ, ‖B ℓ‖ ≤ M) :
    ∃ T : Y s' (closedAnnulus ρm ρp) →L[ℂ] Y s (closedAnnulus ρm ρp),
      ∀ ℓ w, secProj s _ ℓ (T w) = B ℓ (secProj s' _ ℓ w) := by
  obtain ⟨c', C', hc', hC', h'⟩ := exists_norm_equiv_Y s' hρm hρ
  obtain ⟨c, C, hc, hC, h⟩ := exists_norm_equiv_Y s hρm hρ
  have hM : 0 ≤ M := le_trans (ContinuousLinearMap.opNorm_nonneg _) (hB 0)
  have hle : ∀ (w : Y s' (closedAnnulus ρm ρp)) ℓ,
      ‖B ℓ (secProj s' _ ℓ w)‖ ^ 2 ≤ M ^ 2 * ‖secProj s' _ ℓ w‖ ^ 2 := by
    intro w ℓ
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (((B ℓ).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hB ℓ) (norm_nonneg _))) 2
  have hsum : ∀ w : Y s' (closedAnnulus ρm ρp),
      Summable (fun ℓ => ‖B ℓ (secProj s' _ ℓ w)‖ ^ 2) := fun w =>
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (hle w) ((h' w).1.mul_left (M ^ 2))
  have hex : ∀ w : Y s' (closedAnnulus ρm ρp), ∃ v : Y s (closedAnnulus ρm ρp),
      ∀ ℓ, secProj s _ ℓ v = B ℓ (secProj s' _ ℓ w) := fun w => by
    obtain ⟨v, hv, -⟩ := exists_Y_of_summable hρm hρ _ (hsum w)
    exact ⟨v, hv⟩
  choose F hF using hex
  let Tl : Y s' (closedAnnulus ρm ρp) →ₗ[ℂ] Y s (closedAnnulus ρm ρp) :=
    { toFun := F
      map_add' := fun v w => y_eq_of_secProj hρm hρ fun ℓ => by
        rw [hF, map_add, map_add, map_add, hF, hF]
      map_smul' := fun a v => y_eq_of_secProj hρm hρ fun ℓ => by
        rw [hF, map_smul, map_smul, map_smul, hF, RingHom.id_apply] }
  have hbound : ∀ w, ‖Tl w‖ ≤ Real.sqrt (C * M ^ 2 / c') * ‖w‖ := by
    intro w
    have h1 := (h (F w)).2.2
    simp only [hF] at h1
    have h2 : ∑' ℓ, ‖B ℓ (secProj s' _ ℓ w)‖ ^ 2 ≤ M ^ 2 * ∑' ℓ, ‖secProj s' _ ℓ w‖ ^ 2 := by
      rw [← tsum_mul_left]
      exact (hsum w).tsum_le_tsum (hle w) ((h' w).1.mul_left _)
    have h3 := (h' w).2.1
    have hsq : ‖F w‖ ^ 2 ≤ (C * M ^ 2 / c') * ‖w‖ ^ 2 := by
      calc ‖F w‖ ^ 2 ≤ C * (M ^ 2 * ∑' ℓ, ‖secProj s' _ ℓ w‖ ^ 2) :=
            h1.trans (mul_le_mul_of_nonneg_left h2 hC.le)
        _ = (C * M ^ 2 / c') * (c' * ∑' ℓ, ‖secProj s' _ ℓ w‖ ^ 2) := by
            field_simp
        _ ≤ (C * M ^ 2 / c') * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by positivity),
      Real.sqrt_sq (norm_nonneg _)] at this
  exact ⟨Tl.mkContinuous _ hbound, fun ℓ w => hF w ℓ⟩

/-! ### `-iℓΩ : Y^{s+1}_ℓ → Y^s_ℓ`, uniformly in `ℓ` -/

/-- The multiplier `-iΩ(r;G)` (`transCoef = ℓ · transCoef1`). -/
def transCoef1 (S : SectorSetting) (G : ℝ) (r : ℝ) : ℂ := -(Complex.I * ((S.Omega G r : ℝ) : ℂ))

theorem contDiffOn_transCoef1 (S : SectorSetting) (hS : S.Valid) (G : ℝ) :
    ContDiffOn ℝ ∞ (transCoef1 S G) (Ioi 0) := by
  have h1 : ContDiffOn ℝ ∞ (fun r => ((S.Omega G r : ℝ) : ℂ)) (Ioi 0) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_Omega S hS G)
  exact (contDiffOn_const.mul h1).neg

/-- `|ℓ| ‖g‖_{Y^s} ≤ C ‖g‖_{Y^{s+1}}` on `Y^{s+1}_ℓ`, uniformly in `ℓ`. -/
theorem exists_abs_mul_norm_lowerSec_le {S : SectorSetting} (hS : S.Valid) (s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ℓ : ℤ) (g : Ysec (s + 1) S.Nstar ℓ),
      |(ℓ : ℝ)| * ‖lowerSec s (s + 1) S.Nstar ℓ g‖ ≤ K * ‖g‖ := by
  obtain ⟨c1, C1, hc1, hC1, h1⟩ := exists_norm_equiv_ofProfile s hS.ρm_pos hS.ρm_lt_ρp
  obtain ⟨c2, C2, hc2, hC2, h2⟩ := exists_norm_Ysec_equiv (s + 1) hS.ρm_pos hS.ρm_lt_ρp
  refine ⟨Real.sqrt (C1 / c2), Real.sqrt_pos.2 (by positivity), fun ℓ g => ?_⟩
  set g' := lowerSec s (s + 1) S.Nstar ℓ g
  set h := Polar.angularSector g.fn ℓ
  have hg'fn : g'.fn =ᵐ[volume] g.fn := (lowerSec_spec (Nat.le_succ s) S.Nstar ℓ).1 g
  have hgfn : g.fn =ᵐ[volume] ofProfile ℓ h := Ysec.fn_ae_eq_ofProfile hS.ρm_pos g
  obtain ⟨hm, hsupp⟩ := prof_spec hS g
  obtain ⟨-, -, hup⟩ := h1 ℓ h (hm.mono_order (Nat.le_succ s)) hsupp
  obtain ⟨hlow, -⟩ := h2 ℓ g
  have hn : ‖g'‖ = normH s (ofProfile ℓ h) := by
    rw [← (ysec_memH g').2]
    exact ((ysec_memH g').1.congr_ae (hg'fn.trans hgfn)).2.symm
  have hI : Icc S.ρm S.ρp ⊆ Ici 0 := fun r hr => hS.ρm_pos.le.trans hr.1
  have hsucc := secNormSq_succ_ge s ℓ measurableSet_Icc hI h
  have hsq : ((ℓ : ℝ) ^ 2) * ‖g'‖ ^ 2 ≤ (C1 / c2) * ‖g‖ ^ 2 := by
    rw [hn]
    have h0 : 0 ≤ normH s (ofProfile ℓ h) ^ 2 := sq_nonneg _
    calc ((ℓ : ℝ) ^ 2) * normH s (ofProfile ℓ h) ^ 2
        ≤ (1 + (ℓ : ℝ) ^ 2) * normH s (ofProfile ℓ h) ^ 2 := by nlinarith
      _ ≤ (1 + (ℓ : ℝ) ^ 2) * (C1 * secNormSq s ℓ (Icc S.ρm S.ρp) h) :=
          mul_le_mul_of_nonneg_left hup (by positivity)
      _ = C1 * ((1 + (ℓ : ℝ) ^ 2) * secNormSq s ℓ (Icc S.ρm S.ρp) h) := by ring
      _ ≤ C1 * secNormSq (s + 1) ℓ (Icc S.ρm S.ρp) h := mul_le_mul_of_nonneg_left hsucc hC1.le
      _ = (C1 / c2) * (c2 * secNormSq (s + 1) ℓ (Icc S.ρm S.ρp) h) := by field_simp
      _ ≤ (C1 / c2) * ‖g‖ ^ 2 := mul_le_mul_of_nonneg_left hlow (by positivity)
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)] at this

theorem exists_norm_transLower_le {S : SectorSetting} (hS : S.Valid) (s : ℕ) (G : ℝ) :
    ∃ M : ℝ, ∀ ℓ : ℤ,
      ‖(S.transSec s ℓ G).comp (lowerSec s (s + 1) S.Nstar ℓ)‖ ≤ M := by
  obtain ⟨Crm, hCrm, hrm⟩ := exists_radialMul_spec s hS.ρm_pos hS.ρm_lt_ρp
  obtain ⟨K, hK, hKb⟩ := exists_abs_mul_norm_lowerSec_le hS s
  have hb := memCk_of_contDiffOn_Ioi (contDiffOn_transCoef1 S hS G) hS.ρm_pos s (b := S.ρp)
  set Cb := Crm * normCk s (Icc S.ρm S.ρp) (transCoef1 S G)
  have hCb : 0 ≤ Cb := mul_nonneg hCrm.le (normCk_nonneg _ _ _)
  refine ⟨Cb * K, fun ℓ => ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g => ?_⟩
  obtain ⟨hspec, hnorm⟩ := hrm ℓ _ hb
  have hspec' : ∀ g : Ysec s S.Nstar ℓ, (radialMul s S.Nstar ℓ (transCoef1 S G) g).fn =ᵐ[volume]
      fun x => transCoef1 S G ‖x‖ * g.fn x := hspec
  have hnorm' : ‖radialMul s S.Nstar ℓ (transCoef1 S G)‖ ≤ Cb := hnorm
  set g' := lowerSec s (s + 1) S.Nstar ℓ g
  set R := radialMul s S.Nstar ℓ (transCoef1 S G)
  have heq : S.transSec s ℓ G g' = (ℓ : ℂ) • R g' := by
    refine ysec_ext ?_
    filter_upwards [transSec_spec S hS s ℓ G g', ysec_fn_smul (ℓ : ℂ) (R g'), hspec' g']
      with x h1 h2 h3
    rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul, transCoef, transCoef1]
    ring
  calc ‖((S.transSec s ℓ G).comp (lowerSec s (s + 1) S.Nstar ℓ)) g‖
      = ‖S.transSec s ℓ G g'‖ := rfl
    _ = ‖(ℓ : ℂ) • R g'‖ := by rw [heq]
    _ = ‖(ℓ : ℂ)‖ * ‖R g'‖ := norm_smul _ _
    _ = |(ℓ : ℝ)| * ‖R g'‖ := by rw [Complex.norm_intCast]
    _ ≤ |(ℓ : ℝ)| * (Cb * ‖g'‖) := by
        gcongr
        exact (R.le_opNorm g').trans (mul_le_mul_of_nonneg_right hnorm' (norm_nonneg _))
    _ = Cb * (|(ℓ : ℝ)| * ‖g'‖) := by ring
    _ ≤ Cb * (K * ‖g‖) := mul_le_mul_of_nonneg_left (hKb ℓ g) hCb
    _ = Cb * K * ‖g‖ := by ring

/-! ### `Ω ∂_θ w ∈ L²` -/

theorem aestronglyMeasurable_Omega_norm (S : SectorSetting) (hS : S.Valid) (G : ℝ) :
    AEStronglyMeasurable (fun x : ℂ => ((S.Omega G ‖x‖ : ℝ) : ℂ)) volume := by
  have hc : ContinuousOn (fun x : ℂ => ((S.Omega G ‖x‖ : ℝ) : ℂ)) {0}ᶜ :=
    Complex.continuous_ofReal.comp_continuousOn
      ((contDiffOn_Omega S hS G).continuousOn.comp continuous_norm.continuousOn
        fun x hx => norm_pos_iff.2 hx)
  have := hc.aestronglyMeasurable (μ := volume) (measurableSet_singleton 0).compl
  rwa [restrict_compl_singleton] at this

theorem memLp_weakPartial_of_Y {s : ℕ} {K : Set ℂ} (w : Y (s + 1) K) {γ : ℕ × ℕ}
    (hγ : γ ∈ multiIdx (s + 1)) : MemLp (weakPartial γ w.fn) 2 volume := by
  have h := Hk.der_ae_eq (yHk w) ⟨γ, hγ⟩
  exact (Lp.memLp _).ae_eq h

theorem memLp_transportPartFn {S : SectorSetting} (hS : S.Valid) (G : ℝ) {s : ℕ}
    (w : Y (s + 1) S.Nstar) : MemLp (S.transportPartFn G w.fn) 2 volume := by
  have h10 : (1, 0) ∈ multiIdx (s + 1) := mem_multiIdx.2 (by simp)
  have h01 : (0, 1) ∈ multiIdx (s + 1) := mem_multiIdx.2 (by simp)
  have hd10 := memLp_weakPartial_of_Y w h10
  have hd01 := memLp_weakPartial_of_Y w h01
  have hK : IsClosed S.Nstar := isClosed_closedAnnulus _ _
  have hz10 := MemH.weakPartial_eq_zero_outside hK (y_memH w).1 (y_supp w) h10
  have hz01 := MemH.weakPartial_eq_zero_outside hK (y_memH w).1 (y_supp w) h01
  obtain ⟨M, hM0, hM⟩ := exists_iteratedDeriv_Omega_le S hS 0 (abs_nonneg G)
  set g : ℂ → ℝ := fun x => M * S.ρp * (‖weakPartial (0, 1) w.fn x‖ + ‖weakPartial (1, 0) w.fn x‖)
  have hg : MemLp g 2 volume := (hd01.norm.add hd10.norm).const_mul (M * S.ρp)
  have hmeas : AEStronglyMeasurable (S.transportPartFn G w.fn) volume := by
    have hth : AEStronglyMeasurable (thetaDeriv w.fn) volume :=
      ((Complex.continuous_ofReal.comp Complex.continuous_re).aestronglyMeasurable.mul
        hd01.aestronglyMeasurable).sub
      ((Complex.continuous_ofReal.comp Complex.continuous_im).aestronglyMeasurable.mul
        hd10.aestronglyMeasurable)
    exact (aestronglyMeasurable_Omega_norm S hS G).neg.mul hth
  have hρp : 0 < S.ρp := hS.ρm_pos.trans hS.ρm_lt_ρp
  refine hg.of_le hmeas ?_
  filter_upwards [hz10, hz01] with x hx10 hx01
  have hgx : 0 ≤ g x := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hgx]
  by_cases hx : x ∈ S.Nstar
  · have hOm : |S.Omega G ‖x‖| ≤ M := by
      have := hM G le_rfl 0 le_rfl ‖x‖ hx
      simpa using this
    have hre : |x.re| ≤ S.ρp := (Complex.abs_re_le_norm x).trans hx.2
    have him : |x.im| ≤ S.ρp := (Complex.abs_im_le_norm x).trans hx.2
    simp only [transportPartFn, thetaDeriv, g]
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    calc |S.Omega G ‖x‖| * ‖(x.re : ℂ) * weakPartial (0, 1) w.fn x -
          (x.im : ℂ) * weakPartial (1, 0) w.fn x‖
        ≤ M * (S.ρp * ‖weakPartial (0, 1) w.fn x‖ + S.ρp * ‖weakPartial (1, 0) w.fn x‖) := by
          gcongr
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
          gcongr
      _ = M * S.ρp * (‖weakPartial (0, 1) w.fn x‖ + ‖weakPartial (1, 0) w.fn x‖) := by ring
  · simp only [transportPartFn, thetaDeriv, hx10 hx, hx01 hx]
    simp [hgx]

/-! ### The transport part `L^tr : Y^{s+1} → Y^s` -/

theorem exists_transportY1 (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ) :
    ∃ T : Y (s + 1) S.Nstar →L[ℂ] Y s S.Nstar, ∀ w : Y (s + 1) S.Nstar,
      (T w).fn =ᵐ[volume] S.transportPartFn G w.fn := by
  obtain ⟨M, hM⟩ := exists_norm_transLower_le hS s G
  obtain ⟨T, hT⟩ : ∃ T : Y (s + 1) S.Nstar →L[ℂ] Y s S.Nstar, ∀ ℓ w,
      secProj s S.Nstar ℓ (T w) = ((S.transSec s ℓ G).comp (lowerSec s (s + 1) S.Nstar ℓ))
        (secProj (s + 1) S.Nstar ℓ w) :=
    exists_sectorwise hS.ρm_pos hS.ρm_lt_ρp
      (fun ℓ => (S.transSec s ℓ G).comp (lowerSec s (s + 1) S.Nstar ℓ)) hM
  refine ⟨T, fun w => ae_eq_of_sectorProj (y_memLp _) (memLp_transportPartFn hS G w)
    fun ℓ => ?_⟩
  have hTw : secProj s S.Nstar ℓ (T w) =
      S.transSec s ℓ G (lowerSec s (s + 1) S.Nstar ℓ (secProj (s + 1) S.Nstar ℓ w)) := hT ℓ w
  have h1 := (secProj_spec (s := s) S.isRotInvariant_Nstar ℓ).1 (T w)
  rw [hTw] at h1
  have h2 := transSec_spec S hS s ℓ G (lowerSec s (s + 1) S.Nstar ℓ (secProj (s + 1) S.Nstar ℓ w))
  have h3 := (lowerSec_spec (Nat.le_succ s) S.Nstar ℓ).1 (secProj (s + 1) S.Nstar ℓ w)
  have h4 := (secProj_spec (s := s + 1) S.isRotInvariant_Nstar ℓ).1 w
  have h5 := sectorProj_thetaDeriv ((y_memH w).1.mono_order (by omega : 1 ≤ s + 1)) ℓ
  have h6 : sectorProj ℓ (S.transportPartFn G w.fn) =
      fun x => -((S.Omega G ‖x‖ : ℝ) : ℂ) * sectorProj ℓ (thetaDeriv w.fn) x :=
    sectorProj_radial_mul ℓ (fun r => -((S.Omega G r : ℝ) : ℂ)) (thetaDeriv w.fn)
  rw [h6]
  filter_upwards [h1, h2, h3, h4, h5] with x hx1 hx2 hx3 hx4 hx5
  rw [← hx1, hx2, hx3, hx4, hx5, transCoef]
  ring

/-! ### The linearization -/

theorem exists_LinY (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ) :
    ∃ T : Y (s + 1) S.Nstar →L[ℂ] Y s S.Nstar, ∀ w : Y (s + 1) S.Nstar,
      (T w).fn =ᵐ[volume] S.linFn G w.fn := by
  obtain ⟨Ttr, hTtr⟩ := exists_transportY1 S hS s G
  refine ⟨Ttr + (S.KY s).comp (lowerY s (s + 1) S.Nstar), fun w => ?_⟩
  have hlow : (lowerY s (s + 1) S.Nstar w).fn =ᵐ[volume] w.fn :=
    (lowerY_spec (Nat.le_succ s) S.Nstar).1 w
  have hK := KY_spec S hS s (lowerY s (s + 1) S.Nstar w)
  rw [couplingFn_congr_ae S hlow] at hK
  filter_upwards [y_fn_add (Ttr w) ((S.KY s).comp (lowerY s (s + 1) S.Nstar) w), hTtr w, hK]
    with x h1 h2 h3
  rw [ContinuousLinearMap.add_apply, h1, Pi.add_apply, h2, ContinuousLinearMap.comp_apply, h3]
  rfl

end NonUniqueEuler.SGC
