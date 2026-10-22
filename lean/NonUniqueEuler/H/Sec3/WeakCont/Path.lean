import NonUniqueEuler.H.Sec3.WeakCont.Basic
import NonUniqueEuler.I.Sec3.WeakCont.AeIdentity
import NonUniqueEuler.I.Infra.WeakL2.TestFamily

/-!
# `lem:weak-cont`: construction of the weakly continuous path (`03_compactness.tex:171-189`)

Let `𝓕 = {F k}` be a countable test family (`WeakL2.exists_isTestFamily`). For `ψ = F k` the
identity `∫ u(t) ψ = A_ψ(t) := ∫ u₀ψ + ∫_0^t c_ψ` holds for a.e. `t` (`ae_integral_mul_eq`), so it
holds for all `k` on a set `G ⊆ (0,T)` of full measure, on which also `‖u(t)‖₂ ≤ N`. `G` is dense
in `[0,T]`. For `t ∈ [0,T]` the classes `u(s)`, `s ∈ G`, `s → t`, are bounded by `N` and their
integrals against `F k` converge to `A_{F k}(t)`, so they converge weakly to some `P(t)`, `‖P(t)‖ ≤ N`
(`IsTestFamily.exists_weakTendsto`, Riesz). Then `∫ P(t) F k = A_{F k}(t)` for every `t ∈ [0,T]`
and `k`, which gives weak continuity (`IsTestFamily.weakTendsto_iff`) and `P(t) = u(t)` for
`t ∈ G` (density of `𝓕` in `L²`).

This replaces the manuscript's case distinction (`ũ(t) = u(t)` off the null set `𝒩`, a weak
limit on `𝒩`) by taking the weak limit at every time; the resulting path agrees with `u(t)` on `G`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology InnerProductSpace

namespace NonUniqueEuler.Weak.WeakCont

/-- The weakly continuous `L²`-valued path of `lem:weak-cont` (`03_compactness.tex:171-189`):
`P` is weakly continuous on `[0,T]`, bounded by `N`, and `P(t) = u(t)` for a.e. `t ∈ (0,T)`. -/
theorem exists_weakContinuousOn_path {T N : ℝ} (hT : 0 < T) (hN0 : 0 ≤ N) {u : ℝ → ℂ → ℝ}
    {w : ℝ → ℂ → ℂ} {u₀ : ℂ → ℝ}
    (hw : ∀ R : ℝ, 0 < R → Prelim.MemLinfLp (Ioo 0 T) (ball (0 : ℂ) R) 2 w)
    (hu : Prelim.MemLinfLp (Ioo 0 T) univ 2 u) (hte : SolvesTE 0 T u w u₀)
    (hN : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), eLpNorm (u t) 2 volume ≤ ENNReal.ofReal N) :
    ∃ P : ℝ → Lp ℝ 2 (volume : Measure ℂ), WeakL2.WeakContinuousOn P (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, ‖P t‖ ≤ N) ∧
      ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), (P t : ℂ → ℝ) =ᵐ[volume] u t := by
  obtain ⟨F, hF⟩ := WeakL2.exists_isTestFamily
  set A : ℕ → ℝ → ℝ := fun k t => (∫ x, u₀ x * F k x) +
    ∫ s in Ioo 0 t, ∫ x, u s x * fderiv ℝ (F k) x (w s x) with hA
  have hAcont : ∀ k, ContinuousOn (A k) (Icc 0 T) := fun k =>
    continuousOn_rhs u₀ hw hu (hF.contDiff k) (hF.hasCompactSupport k)
  set Pu : ℝ → Lp ℝ 2 (volume : Measure ℂ) := fun s => JointRep.toPath u s with hPu
  let p : ℝ → Prop := fun t => MemLp (u t) 2 volume ∧
    eLpNorm (u t) 2 volume ≤ ENNReal.ofReal N ∧ ∀ k, ∫ x, u t x * F k x = A k t
  have hp : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), p t := by
    obtain ⟨M, hM⟩ := hu.essBounded
    have hk : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∀ k, ∫ x, u t x * F k x = A k t :=
      ae_all_iff.2 fun k => ae_integral_mul_eq hT hw hu hte (hF.contDiff k) (hF.hasCompactSupport k)
    filter_upwards [hM, hN, hk] with t h1 h2 h3
    refine ⟨?_, h2, h3⟩
    simpa only [Measure.restrict_univ] using h1.1
  set G : Set ℝ := Ioo 0 T ∩ {t | p t} with hG
  have hGsub : G ⊆ Icc 0 T := fun s hs => Ioo_subset_Icc_self hs.1
  have hGcl : ∀ t ∈ Icc 0 T, (𝓝[G] t).NeBot := fun t ht =>
    mem_closure_iff_nhdsWithin_neBot.1 (mem_closure_of_ae hT hp ht)
  have hPuN : ∀ s ∈ G, ‖Pu s‖ ≤ N := by
    intro s hs
    refine norm_le_of_eLpNorm_le hN0 ?_
    rw [eLpNorm_congr_ae (JointRep.coeFn_toPath hs.2.1)]
    exact hs.2.2.1
  have hconv : ∀ t ∈ Icc 0 T, ∀ k,
      Tendsto (fun s => ∫ z, Pu s z * F k z) (𝓝[G] t) (𝓝 (A k t)) := by
    intro t ht k
    refine (((hAcont k) t ht).mono_left (nhdsWithin_mono t hGsub)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [integral_toPath_mul hs.2.1, hs.2.2.2 k]
  have hex : ∀ t ∈ Icc 0 T, ∃ x : Lp ℝ 2 (volume : Measure ℂ),
      ‖x‖ ≤ N ∧ WeakL2.WeakTendsto Pu (𝓝[G] t) x := by
    intro t ht
    have := hGcl t ht
    exact hF.exists_weakTendsto (eventually_nhdsWithin_of_forall hPuN)
      fun k => ⟨A k t, hconv t ht k⟩
  choose! P hPN hPw using hex
  have hPA : ∀ t ∈ Icc 0 T, ∀ k, ∫ z, P t z * F k z = A k t := by
    intro t ht k
    have := hGcl t ht
    exact tendsto_nhds_unique ((hPw t ht).integral_mul_tendsto (hF.memLp k 2)) (hconv t ht k)
  have hPcont : WeakL2.WeakContinuousOn P (Icc 0 T) := by
    intro y t ht
    have hw' : WeakL2.WeakTendsto P (𝓝[Icc 0 T] t) (P t) := by
      refine (hF.weakTendsto_iff (eventually_nhdsWithin_of_forall hPN)).2 fun k => ?_
      rw [hPA t ht k]
      refine ((hAcont k) t ht).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hPA s hs k).symm
    exact hw' y
  have hPG : ∀ t ∈ G, P t = Pu t := by
    intro t ht
    rw [← sub_eq_zero]
    refine eq_zero_of_inner_denseRange hF.denseRange_toL2 fun k => ?_
    rw [inner_sub_left, hF.inner_toL2, hF.inner_toL2, hPA t (hGsub ht) k,
      integral_toPath_mul ht.2.1, ht.2.2.2 k, sub_self]
  refine ⟨P, hPcont, hPN, ?_⟩
  filter_upwards [hp, ae_restrict_mem measurableSet_Ioo] with t ht htI
  rw [hPG t ⟨htI, ht⟩]
  exact JointRep.coeFn_toPath ht.1

end NonUniqueEuler.Weak.WeakCont
