import NonUniqueEuler.Defs.Sec3.Transport
import NonUniqueEuler.Defs.Sec3.Paths
import NonUniqueEuler.H.Sec3.WeakCont.Basic
import NonUniqueEuler.H.Sec3.WeakCont.Path
import NonUniqueEuler.I.Sec3.WeakCont.Bounds
import NonUniqueEuler.I.Sec3.WeakCont.AeIdentity
import NonUniqueEuler.I.Sec3.WeakCont.Restart
import NonUniqueEuler.I.Infra.WeakL2.Paths
import NonUniqueEuler.I.Infra.JointRep.Representative
import NonUniqueEuler.I.Infra.JointRep.Slab
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Proof: `lem:weak-cont` (weakly continuous representative of a solution of `(te)`), `b = 2`

Proof of `I/Sec3/WeakCont.lean` (`03_compactness.tex:120-225`).

Structure (following the manuscript, `03_compactness.tex:147-225`):
1. Hölder bounds and integrability of the flux `c_ψ(t) = ∫ u(t) w(t)·∇ψ`
   (`I/Sec3/WeakCont/Bounds.lean`).
2. The a.e. identity `∫ u(t)ψ = ∫ u₀ψ + ∫_0^t c_ψ` for every `ψ ∈ C_c^∞`, via `lem:dbr`
   (`I/Sec3/WeakCont/AeIdentity.lean`).
3. The weakly continuous `L²`-valued path `P` with `‖P(t)‖ ≤ N` and `P(t) = u(t)` for a.e. `t`
   (`H/Sec3/WeakCont/Path.lean`: weak limits along a countable test family, Riesz); `ũ` is its
   jointly measurable representative (I-JOINT).
4. (b) for every `ψ ∈ C_c^∞` and every `t ∈ [0,T]`: both sides are continuous on `[0,T]` and agree
   a.e. (step 2). This replaces the manuscript's `C¹` approximation `ψ_i → ψ` (`:191-198`) by a
   continuity argument (deviation, same conclusion). Then `ũ(0) = u₀` (fundamental lemma,
   `u₀ ∈ L¹_loc`), so `u₀ ∈ L²`; the Lipschitz bound from step 1; the `L¹` bound from weak lower
   semicontinuity (`WeakL2.WeakContinuousOn.eLpNorm_le_of_ae`).
5. (c): `t₀ = 0` is the hypothesis (`ũ(0) = u₀` a.e.); `t₀ ∈ (0,T)` is
   `I/Sec3/WeakCont/Restart.lean`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak

/-- `lem:weak-cont` with `b = 2` (`03_compactness.tex:120-145`): a solution `u ∈ L^∞(0,T;L²)` of
`(te)` on `[0,T)` with field `w ∈ L^∞(0,T;L²(B_R))` (every `R`) and a locally integrable datum
`u₀` has a jointly measurable representative `ũ`, weakly continuous into `L²` on `[0,T]`, with
(a) `u₀ ∈ L²`, `ũ(0) = u₀`, `‖ũ(t)‖₂ ≤ N` and `‖ũ(t)‖₁ ≤ N₁` for every `t ∈ [0,T]` (`N`, `N₁`
essential bounds), (b) the integrated identity and the Lipschitz bound, (c) `(te)` on `[t₀,T)`
with datum `ũ(t₀)` for every `t₀ ∈ [0,T)`. -/
theorem weakCont {T N : ℝ} (hT : 0 < T) (hN0 : 0 ≤ N) {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ}
    {u₀ : ℂ → ℝ}
    (hw : ∀ R : ℝ, 0 < R → Prelim.MemLinfLp (Ioo 0 T) (ball (0 : ℂ) R) 2 w)
    (hu : Prelim.MemLinfLp (Ioo 0 T) univ 2 u) (hu₀ : LocallyIntegrable u₀ volume)
    (hte : SolvesTE 0 T u w u₀)
    (hN : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), eLpNorm (u t) 2 volume ≤ ENNReal.ofReal N) :
    ∃ ũ : ℝ → ℂ → ℝ, Measurable (Function.uncurry ũ) ∧
      IsWeakContL2On (Icc 0 T) ũ ∧
      Function.uncurry ũ =ᵐ[volume.restrict (slab T)] Function.uncurry u ∧
      (∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ũ t =ᵐ[volume] u t) ∧
      -- (a)
      MemLp u₀ 2 volume ∧ ũ 0 =ᵐ[volume] u₀ ∧
      (∀ t ∈ Icc 0 T, eLpNorm (ũ t) 2 volume ≤ ENNReal.ofReal N) ∧
      (∀ N₁ : ℝ, (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
          eLpNorm (u t) 1 volume ≤ ENNReal.ofReal N₁) →
        ∀ t ∈ Icc 0 T, eLpNorm (ũ t) 1 volume ≤ ENNReal.ofReal N₁) ∧
      -- (b), the identity
      (∀ ψ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
        ∀ t ∈ Icc 0 T,
          IntegrableOn (fun p : ℝ × ℂ => u p.1 p.2 * fderiv ℝ ψ p.2 (w p.1 p.2))
            (Ioo 0 t ×ˢ univ) ∧
          ∫ x, ũ t x * ψ x =
            (∫ x, u₀ x * ψ x) + ∫ s in Ioo 0 t, ∫ x, u s x * fderiv ℝ ψ x (w s x)) ∧
      -- (b), the Lipschitz bound
      (∀ (ψ : ℂ → ℝ) (R W G : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ →
        tsupport ψ ⊆ ball (0 : ℂ) R → 0 ≤ W →
        (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
          eLpNorm (w t) 2 (volume.restrict (ball (0 : ℂ) R)) ≤ ENNReal.ofReal W) →
        (∀ x, ‖fderiv ℝ ψ x‖ ≤ G) →
        ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
          |∫ x, (ũ t x - ũ s x) * ψ x| ≤ N * W * G * |t - s|) ∧
      -- (c)
      (∀ t₀ ∈ Ico 0 T, SolvesTE t₀ T u w (ũ t₀)) := by
  obtain ⟨P, hPcont, hPN, hPu⟩ := WeakCont.exists_weakContinuousOn_path hT hN0 hw hu hte hN
  set ũ : ℝ → ℂ → ℝ := JointRep.jointRep P (Icc 0 T) with hũdef
  have hJR : JointRep.IsJointRep ũ P (Icc 0 T) :=
    JointRep.isJointRep_jointRep_of_weakContinuousOn measurableSet_Icc hPcont
  have hũP : ∀ t ∈ Icc 0 T, ũ t =ᵐ[volume] P t := hJR.ae_eq
  -- weak continuity of `ũ`
  have hWC : IsWeakContL2On (Icc 0 T) ũ := by
    refine ⟨fun t ht => hJR.memLp ht, fun ψ hψ => (hPcont (hψ.toLp ψ)).congr fun t ht => ?_⟩
    simp only
    rw [WeakL2.inner_toLp_eq_integral _ hψ]
    exact integral_congr_ae ((hũP t ht).mono fun x hx => by simp only [hx])
  -- `ũ(t) = u(t)` for a.e. `t`
  have hũu : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ũ t =ᵐ[volume] u t := by
    filter_upwards [hPu, ae_restrict_mem measurableSet_Ioo] with t h1 htI
    exact (hũP t (Ioo_subset_Icc_self htI)).trans h1
  have hslab : Function.uncurry ũ =ᵐ[volume.restrict (slab T)] Function.uncurry u :=
    (hJR.mono Ioo_subset_Icc_self).ae_eq_slab_of_ae hu.aestronglyMeasurable
      (hPu.mono fun t h => h.symm)
  -- the `L²` bound at every time
  have hũN2 : ∀ t ∈ Icc 0 T, eLpNorm (ũ t) 2 volume ≤ ENNReal.ofReal N := by
    intro t ht
    rw [eLpNorm_congr_ae (hũP t ht)]
    exact WeakCont.eLpNorm_le_of_norm_le (hPN t ht)
  -- the identity (b): both sides are continuous on `[0,T]` and agree a.e.
  have hident : ∀ ψ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      ∀ t ∈ Icc 0 T, ∫ x, ũ t x * ψ x =
        (∫ x, u₀ x * ψ x) + ∫ s in Ioo 0 t, ∫ x, u s x * fderiv ℝ ψ x (w s x) := by
    intro ψ hψ hψc
    have hψL2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
    refine Measure.eqOn_of_ae_eq (μ := volume) ?_ (hWC.continuousOn ψ hψL2)
      (WeakCont.continuousOn_rhs u₀ hw hu hψ hψc) ?_
    · rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := T)).symm]
      filter_upwards [hũu, WeakCont.ae_integral_mul_eq hT hw hu hte hψ hψc] with t h1 h2
      rw [← h2]
      exact integral_congr_ae (h1.mono fun x hx => by simp only [hx])
    · rw [interior_Icc, closure_Ioo hT.ne]
  -- `ũ(0) = u₀`
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have h0 : ũ 0 =ᵐ[volume] u₀ := by
    have hloc : LocallyIntegrable (ũ 0) volume :=
      (hWC.memLp 0 h0mem).locallyIntegrable (by norm_num)
    refine ae_eq_of_integral_contDiff_smul_eq hloc hu₀ fun g hg hgc => ?_
    have h := hident g hg hgc 0 h0mem
    simp only [Ioo_self, Measure.restrict_empty, integral_zero_measure, add_zero] at h
    simp only [smul_eq_mul]
    simp_rw [mul_comm (g _)]
    exact h
  refine ⟨ũ, hJR.measurable, hWC, hslab, hũu, (hWC.memLp 0 h0mem).ae_eq h0, h0, hũN2, ?_, ?_,
    ?_, ?_⟩
  · -- (a), the `L¹` bound: weak lower semicontinuity
    intro N₁ hN₁ t ht
    have h' : ∀ᵐ s ∂(volume.restrict (Ioo 0 T)), eLpNorm (P s) 1 volume ≤ ENNReal.ofReal N₁ := by
      filter_upwards [hN₁, hPu] with s h1 h2
      rw [eLpNorm_congr_ae h2]
      exact h1
    rw [eLpNorm_congr_ae (hũP t ht)]
    exact WeakL2.WeakContinuousOn.eLpNorm_le_of_ae hT hPcont le_rfl h' t ht
  · -- (b), the identity
    intro ψ hψ hψc t ht
    refine ⟨?_, hident ψ hψ hψc t ht⟩
    exact (WeakCont.integrableOn_slab_mul_fderiv hw hu (WeakCont.contDiff_one_of_smooth hψ)
      hψc).mono_set (prod_mono (Ioo_subset_Ioo_right ht.2) subset_rfl)
  · -- (b), the Lipschitz bound
    intro ψ R W G hψ hψR hW hWae hG s hs t ht
    have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
    by_cases hR : R ≤ 0
    · have hψ0 : ∀ x, ψ x = 0 := fun x => image_eq_zero_of_notMem_tsupport fun hx => by
        have h := hψR hx
        rw [ball_eq_empty.2 hR] at h
        exact h
      simp only [hψ0, mul_zero, integral_zero, abs_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hN0 hW) hG0) (abs_nonneg _)
    · rw [not_le] at hR
      have hψc : HasCompactSupport ψ :=
        (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset (isClosed_tsupport ψ)
          (hψR.trans ball_subset_closedBall)
      have hψL2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
      have hb : ∀ᵐ r ∂(volume.restrict (Ioo 0 T)),
          |∫ x, u r x * fderiv ℝ ψ x (w r x)| ≤ N * W * G := by
        obtain ⟨Mu, hMu⟩ := hu.essBounded
        obtain ⟨Mw, hMw⟩ := (hw R hR).essBounded
        filter_upwards [hMu, hMw, hN, hWae] with r h1 h2 h3 h4
        exact WeakCont.abs_integral_mul_fderiv_le hN0 hW (WeakCont.contDiff_one_of_smooth hψ) hψR
          (by simpa only [Measure.restrict_univ] using h1.1) h3 h2.1 h4 hG
      have hi : ∀ r ∈ Icc 0 T, Integrable (fun x => ũ r x * ψ x) volume := fun r hr =>
        (hWC.memLp r hr).integrable_mul hψL2
      have hsplit : ∫ x, (ũ t x - ũ s x) * ψ x = (∫ x, ũ t x * ψ x) - ∫ x, ũ s x * ψ x := by
        simp_rw [sub_mul]
        exact integral_sub (hi t ht) (hi s hs)
      rw [hsplit, hident ψ hψ hψc t ht, hident ψ hψ hψc s hs, add_sub_add_left_eq_sub]
      exact WeakCont.abs_setIntegral_Ioo_sub_le (WeakCont.integrableOn_flux hw hu hψ hψc) hb hs ht
  · -- (c), restart at `t₀`
    intro t₀ ht₀
    rcases eq_or_lt_of_le ht₀.1 with h | h
    · subst h
      exact WeakCont.solvesTE_congr_datum hte h0
    · exact WeakCont.solvesTE_restart ⟨h, ht₀.2⟩ hte hWC hũN2 hũu

end NonUniqueEuler.Weak
