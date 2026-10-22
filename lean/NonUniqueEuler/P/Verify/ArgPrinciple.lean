import NonUniqueEuler.Defs.Verify.Winding
import NonUniqueEuler.Defs.Verify.Contour
import NonUniqueEuler.I.Verify.WindingAlgebra
import NonUniqueEuler.I.Verify.WindingLift
import NonUniqueEuler.I.Verify.WindingRect
import NonUniqueEuler.I.Verify.ContourGeom
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.DiscreteSubset

/-!
# Proof: the argument principle for rectangles

Proof of the interface `NonUniqueEuler/I/Verify/ArgPrinciple.lean` (same declarations, same
statements).

**Manuscript.** Last assertion of Proposition A.4 (`A_verification.tex:486-488`, `:512`), used in
Lemma A.6 (`:540-560`).

**Route** (no divisors or factorized rational functions).
1. *Base case* (`ArgPrincipleAux.hasWinding_zero_of_ne_zero`): a function continuous on an open
   set containing the closed rectangle and zero-free on the closed rectangle has winding `0`
   along `∂R`. A convex open thickening `W` of the rectangle on which it is zero-free is simply
   connected (`Convex.contractibleSpace`), so it has a continuous logarithm on `W`
   (`Complex.exists_continuousOn_eqOn_exp_comp`) and `hasWinding_zero_of_exp` applies.
2. *Division by one linear factor* (`ArgPrincipleAux.order_dslope`): at a zero `z₀` of `f`,
   `f = (· - z₀) · dslope f z₀`, `dslope f z₀` is holomorphic where `f` is
   (`Complex.differentiableOn_dslope`), and the orders add (`analyticOrderAt_mul`).
3. *Induction on the total order* (`ArgPrincipleAux.hasWinding_of_zeros`): for a finite set
   `Z ⊆ R.openSet` containing all zeros of `f` in the closed rectangle, with finite orders of
   total `N`, the winding number is `N`: divide out one factor (step 2), use winding `1` of
   `(· - z₀) ∘ ∂R` (`hasWinding_bdryPath_sub_of_mem_openSet`) and `HasWinding.mul`.
4. *Finiteness* (`ArgPrincipleAux.finite_zeros`): `f` is analytic near the closed rectangle,
   which is connected, and `f ≠ 0` at a boundary point, so all orders are finite
   (`AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected`); the zeros are isolated
   (`codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top`), hence finitely many in the
   compact rectangle (`IsCompact.finite_sdiff_of_mem_codiscreteWithin`).
5. Zeros lie off `∂R = bdryPath '' [0, 4]` (`bdryPath_image`); `HasWinding.unique` identifies
   the winding with `n`.
-/

open Set Filter Topology

namespace NonUniqueEuler

namespace ArgPrincipleAux

/-- **Base case.** A function continuous on an open set containing the closed rectangle and
zero-free on the closed rectangle has winding number `0` along the boundary. -/
theorem hasWinding_zero_of_ne_zero {g : ℂ → ℂ} {R : QRect} (hR : R.Nondeg) {U : Set ℂ}
    (hU : IsOpen U) (hRU : R.closedSet ⊆ U) (hg : ContinuousOn g U)
    (hne : ∀ z ∈ R.closedSet, g z ≠ 0) :
    HasWinding (fun t => g (R.bdryPath t)) 0 4 0 := by
  have hV : IsOpen (U ∩ g ⁻¹' {0}ᶜ) := hg.isOpen_inter_preimage hU isOpen_compl_singleton
  have hRV : R.closedSet ⊆ U ∩ g ⁻¹' {0}ᶜ := fun z hz => ⟨hRU hz, hne z hz⟩
  obtain ⟨δ, hδ, hδV⟩ := R.isCompact_closedSet.exists_thickening_subset_open hV hRV
  have hWo : IsOpen (Metric.thickening δ R.closedSet) := Metric.isOpen_thickening
  have hWc : Convex ℝ (Metric.thickening δ R.closedSet) := R.convex_closedSet.thickening δ
  have hRW : R.closedSet ⊆ Metric.thickening δ R.closedSet := Metric.self_subset_thickening hδ _
  have hmem : ∀ t : ℝ, R.bdryPath t ∈ R.closedSet := fun t =>
    QRect.bdryPath_mem_closedSet hR.1.le hR.2.le t
  have hWne : (Metric.thickening δ R.closedSet).Nonempty := ⟨_, hRW (hmem 0)⟩
  have hWsc : IsSimplyConnected (Metric.thickening δ R.closedSet) := by
    have := hWc.contractibleSpace hWne
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨F, hFc, hFeq⟩ := Complex.exists_continuousOn_eqOn_exp_comp hWsc hWo
    (hg.mono (hδV.trans inter_subset_left)) (by
      rintro ⟨z, hz, hz0⟩
      exact (hδV hz).2 hz0)
  exact hasWinding_zero_of_exp (by norm_num) hFc (fun z hz => (hFeq hz).symm)
    R.continuous_bdryPath.continuousOn (fun t _ => hRW (hmem t)) R.bdryPath_four.symm

/-- **Division by one linear factor.** At a zero `z₀` of `f`, `f = (· - z₀) · dslope f z₀`, and
at every point `z` of finite order of `f` (where `f` is holomorphic nearby) the quotient has
finite order and `ord_z f = [z = z₀] + ord_z (dslope f z₀)`. -/
theorem order_dslope {f : ℂ → ℂ} {U : Set ℂ} (hf : DifferentiableOn ℂ f U) {z₀ : ℂ}
    (hz₀ : U ∈ 𝓝 z₀) (hfz₀ : f z₀ = 0) {z : ℂ} (hz : U ∈ 𝓝 z)
    (htop : analyticOrderAt f z ≠ ⊤) :
    analyticOrderAt (dslope f z₀) z ≠ ⊤ ∧
      analyticOrderNatAt f z =
        (if z = z₀ then 1 else 0) + analyticOrderNatAt (dslope f z₀) z := by
  have hh : DifferentiableOn ℂ (dslope f z₀) U := (Complex.differentiableOn_dslope hz₀).mpr hf
  have hfeq : f = (fun w => w - z₀) * dslope f z₀ := by
    funext w
    exact (sub_smul_dslope_of_zero hfz₀ w).symm
  have ha₁ : AnalyticAt ℂ (fun w => w - z₀) z := by fun_prop
  have ha₂ : AnalyticAt ℂ (dslope f z₀) z := hh.analyticAt hz
  have hord : analyticOrderAt f z =
      analyticOrderAt (fun w => w - z₀) z + analyticOrderAt (dslope f z₀) z := by
    have h := analyticOrderAt_mul ha₁ ha₂
    rwa [← hfeq] at h
  have hlin : analyticOrderAt (fun w => w - z₀) z = if z = z₀ then 1 else 0 := by
    split_ifs with h
    · subst h
      exact analyticOrderAt_id_sub_const_self
    · exact analyticOrderAt_id_sub_const_of_ne h
  have htop₁ : analyticOrderAt (fun w => w - z₀) z ≠ ⊤ := by
    rw [hlin]
    split_ifs <;> simp
  have htop₂ : analyticOrderAt (dslope f z₀) z ≠ ⊤ := by
    intro h
    apply htop
    rw [hord, h]
    simp
  refine ⟨htop₂, ?_⟩
  have hnat := analyticOrderNatAt_mul ha₁ ha₂ htop₁ htop₂
  rw [← hfeq] at hnat
  rw [hnat]
  congr 1
  simp only [analyticOrderNatAt, hlin]
  split_ifs <;> rfl

/-- **Induction on the total order.** If `Z ⊆ R.openSet` is a finite set containing all zeros
of `f` in the closed rectangle, the orders of `f` on `Z` are finite and add up to `N`, then
`f ∘ ∂R` has winding number `N`. -/
theorem hasWinding_of_zeros {R : QRect} (hR : R.Nondeg) {U : Set ℂ} (hU : IsOpen U)
    (hRU : R.closedSet ⊆ U) (Z : Finset ℂ) (hZ : ∀ z ∈ Z, z ∈ R.openSet) (N : ℕ) :
    ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      (∀ z ∈ R.closedSet, f z = 0 → z ∈ Z) →
      (∀ z ∈ Z, analyticOrderAt f z ≠ ⊤) →
      ∑ z ∈ Z, analyticOrderNatAt f z = N →
      HasWinding (fun t => f (R.bdryPath t)) 0 4 N := by
  have hZU : ∀ z ∈ Z, U ∈ 𝓝 z := fun z hz =>
    hU.mem_nhds (hRU (R.openSet_subset_closedSet (hZ z hz)))
  induction N with
  | zero =>
    intro f hf hzero htop hsum
    have hne : ∀ z ∈ R.closedSet, f z ≠ 0 := by
      intro z hz hfz
      have hzZ := hzero z hz hfz
      have h0 : analyticOrderNatAt f z = 0 := Finset.sum_eq_zero_iff.mp hsum z hzZ
      have han : AnalyticAt ℂ f z := hf.analyticAt (hZU z hzZ)
      have h0' : analyticOrderAt f z = 0 := by
        rw [← Nat.cast_analyticOrderNatAt (htop z hzZ), h0]
        rfl
      exact (han.analyticOrderAt_eq_zero.mp h0') hfz
    simpa using hasWinding_zero_of_ne_zero hR hU hRU hf.continuousOn hne
  | succ N ih =>
    intro f hf hzero htop hsum
    obtain ⟨z₀, hz₀Z, hz₀⟩ : ∃ z₀ ∈ Z, analyticOrderNatAt f z₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      rw [Finset.sum_eq_zero hcon] at hsum
      exact Nat.succ_ne_zero N hsum.symm
    have hfz₀ : f z₀ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hz₀
    have hh : DifferentiableOn ℂ (dslope f z₀) U :=
      (Complex.differentiableOn_dslope (hZU z₀ hz₀Z)).mpr hf
    have hfeq : ∀ w, f w = (w - z₀) * dslope f z₀ w := fun w =>
      (sub_smul_dslope_of_zero hfz₀ w).symm
    have hdec : ∀ z ∈ Z, analyticOrderAt (dslope f z₀) z ≠ ⊤ ∧
        analyticOrderNatAt f z =
          (if z = z₀ then 1 else 0) + analyticOrderNatAt (dslope f z₀) z := fun z hz =>
      order_dslope hf (hZU z₀ hz₀Z) hfz₀ (hZU z hz) (htop z hz)
    have hsum' : ∑ z ∈ Z, analyticOrderNatAt (dslope f z₀) z = N := by
      have : ∑ z ∈ Z, analyticOrderNatAt f z =
          ∑ z ∈ Z, ((if z = z₀ then 1 else 0) + analyticOrderNatAt (dslope f z₀) z) :=
        Finset.sum_congr rfl fun z hz => (hdec z hz).2
      rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq' Z z₀] at hsum
      simp only [hz₀Z, ↓reduceIte] at hsum
      omega
    have hzero' : ∀ z ∈ R.closedSet, dslope f z₀ z = 0 → z ∈ Z := by
      intro z hz hhz
      exact hzero z hz (by rw [hfeq z, hhz, mul_zero])
    have hwh := ih (dslope f z₀) hh hzero' (fun z hz => (hdec z hz).1) hsum'
    have hwl := QRect.hasWinding_bdryPath_sub_of_mem_openSet hR (hZ z₀ hz₀Z)
    have hw := hwl.mul hwh
    have hcast : ((1 : ℤ) + (N : ℤ)) = ((N + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast] at hw
    exact hw.congr fun t _ => (hfeq (R.bdryPath t)).symm

/-- **Finiteness.** A function holomorphic near the closed rectangle and nonzero at one of its
points has finite order everywhere on the closed rectangle and finitely many zeros there. -/
theorem finite_zeros {f : ℂ → ℂ} {R : QRect} {U : Set ℂ} (hU : IsOpen U)
    (hRU : R.closedSet ⊆ U) (hf : DifferentiableOn ℂ f U) {z₁ : ℂ} (hz₁ : z₁ ∈ R.closedSet)
    (hfz₁ : f z₁ ≠ 0) :
    (∀ z ∈ R.closedSet, analyticOrderAt f z ≠ ⊤) ∧
      {z | z ∈ R.closedSet ∧ f z = 0}.Finite := by
  have han : AnalyticOnNhd ℂ f R.closedSet := (hf.analyticOnNhd hU).mono hRU
  have htop : ∀ z ∈ R.closedSet, analyticOrderAt f z ≠ ⊤ := by
    intro z hz
    refine han.analyticOrderAt_ne_top_of_isPreconnected R.convex_closedSet.isPreconnected
      hz₁ hz ?_
    rw [(han z₁ hz₁).analyticOrderAt_eq_zero.mpr hfz₁]
    simp
  refine ⟨htop, ?_⟩
  have hcd := han.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top
  refine (R.isCompact_closedSet.finite_sdiff_of_mem_codiscreteWithin hcd).subset ?_
  rintro z ⟨hz, hfz⟩
  refine ⟨hz, ?_⟩
  rintro (h0 | h0)
  · exact ((han z hz).analyticOrderAt_eq_zero.mp h0) hfz
  · exact htop z hz h0

/-- Zeros of `f` in the closed rectangle lie in the open rectangle when `f ∘ ∂R` avoids `0`. -/
theorem mem_openSet_of_zero {f : ℂ → ℂ} {R : QRect} (hR : R.Nondeg)
    (hne : ∀ t ∈ Icc (0 : ℝ) 4, f (R.bdryPath t) ≠ 0) {z : ℂ} (hz : z ∈ R.closedSet)
    (hfz : f z = 0) : z ∈ R.openSet := by
  by_contra hzo
  have hb : z ∈ R.boundary := ⟨hz, hzo⟩
  rw [← QRect.bdryPath_image hR] at hb
  obtain ⟨t, ht, rfl⟩ := hb
  exact hne t ht hfz

end ArgPrincipleAux

open ArgPrincipleAux in
/-- **The argument principle for rectangles.** If `f` is holomorphic on an open set containing
the closed nondegenerate rectangle `R`, and `f ∘ ∂R` has winding number `n` around `0` (in
particular `f ≠ 0` on `∂R`), then `f` has finitely many zeros in the open rectangle, each of
finite order, and the sum of their orders is `n`. -/
theorem argument_principle_rect {f : ℂ → ℂ} {R : QRect} (hR : R.Nondeg) {U : Set ℂ}
    (hU : IsOpen U) (hRU : R.closedSet ⊆ U) (hf : DifferentiableOn ℂ f U) {n : ℤ}
    (hw : HasWinding (fun t => f (R.bdryPath t)) 0 4 n) :
    ∃ Z : Finset ℂ, (↑Z : Set ℂ) = {z | z ∈ R.openSet ∧ f z = 0} ∧
      (∀ z ∈ Z, analyticOrderAt f z ≠ ⊤) ∧
      ((∑ z ∈ Z, analyticOrderNatAt f z : ℕ) : ℤ) = n := by
  have hne := hw.ne_zero
  have hz₁ : R.bdryPath 0 ∈ R.closedSet := QRect.bdryPath_mem_closedSet hR.1.le hR.2.le 0
  have hfz₁ : f (R.bdryPath 0) ≠ 0 := hne 0 ⟨le_rfl, by norm_num⟩
  obtain ⟨htop, hfin⟩ := finite_zeros hU hRU hf hz₁ hfz₁
  have hmemZ : ∀ z, z ∈ hfin.toFinset ↔ z ∈ R.closedSet ∧ f z = 0 := fun z => by
    simp
  have hZopen : ∀ z ∈ hfin.toFinset, z ∈ R.openSet := fun z hz =>
    mem_openSet_of_zero hR hne ((hmemZ z).mp hz).1 ((hmemZ z).mp hz).2
  refine ⟨hfin.toFinset, ?_, ?_, ?_⟩
  · ext z
    rw [Finset.mem_coe, hmemZ]
    constructor
    · rintro ⟨hz, hfz⟩
      exact ⟨mem_openSet_of_zero hR hne hz hfz, hfz⟩
    · rintro ⟨hz, hfz⟩
      exact ⟨R.openSet_subset_closedSet hz, hfz⟩
  · exact fun z hz => htop z ((hmemZ z).mp hz).1
  · have hW := hasWinding_of_zeros hR hU hRU hfin.toFinset hZopen _ f hf
      (fun z hz hfz => (hmemZ z).mpr ⟨hz, hfz⟩) (fun z hz => htop z ((hmemZ z).mp hz).1) rfl
    exact hW.unique hw

open ArgPrincipleAux in
/-- **Winding number one**: exactly one zero in the closed rectangle; it lies in the open
rectangle and is simple. -/
theorem argument_principle_rect_one {f : ℂ → ℂ} {R : QRect} (hR : R.Nondeg) {U : Set ℂ}
    (hU : IsOpen U) (hRU : R.closedSet ⊆ U) (hf : DifferentiableOn ℂ f U)
    (hw : HasWinding (fun t => f (R.bdryPath t)) 0 4 1) :
    ∃ z₀ ∈ R.openSet, f z₀ = 0 ∧ deriv f z₀ ≠ 0 ∧ ∀ z ∈ R.closedSet, f z = 0 → z = z₀ := by
  obtain ⟨Z, hZ, htop, hsum⟩ := argument_principle_rect hR hU hRU hf hw
  have hmem : ∀ z, z ∈ Z ↔ z ∈ R.openSet ∧ f z = 0 := fun z => by
    rw [← Finset.mem_coe, hZ]
    rfl
  have hU' : ∀ z ∈ Z, U ∈ 𝓝 z := fun z hz =>
    hU.mem_nhds (hRU (R.openSet_subset_closedSet ((hmem z).mp hz).1))
  have hpos : ∀ z ∈ Z, 1 ≤ analyticOrderNatAt f z := by
    intro z hz
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    have h0' : analyticOrderAt f z = 0 := by
      rw [← Nat.cast_analyticOrderNatAt (htop z hz), h0]
      rfl
    exact ((hf.analyticAt (hU' z hz)).analyticOrderAt_eq_zero.mp h0') ((hmem z).mp hz).2
  have hsum' : ∑ z ∈ Z, analyticOrderNatAt f z = 1 := by exact_mod_cast hsum
  have hcard : Z.card ≤ 1 := by
    have := Finset.card_nsmul_le_sum Z (fun z => analyticOrderNatAt f z) 1 hpos
    simpa [hsum'] using this
  have hcard1 : Z.card = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h | h
    · rw [Finset.card_eq_zero] at h
      rw [h, Finset.sum_empty] at hsum'
      exact absurd hsum' (by norm_num)
    · exact h
  obtain ⟨z₀, rfl⟩ := Finset.card_eq_one.mp hcard1
  have hz₀ : z₀ ∈ ({z₀} : Finset ℂ) := Finset.mem_singleton_self z₀
  obtain ⟨hz₀o, hfz₀⟩ := (hmem z₀).mp hz₀
  rw [Finset.sum_singleton] at hsum'
  refine ⟨z₀, hz₀o, hfz₀, ?_, ?_⟩
  · -- order one: the quotient `dslope f z₀` does not vanish at `z₀`, and equals `deriv f z₀`
    obtain ⟨htop₂, hdec⟩ := order_dslope hf (hU' z₀ hz₀) hfz₀ (hU' z₀ hz₀) (htop z₀ hz₀)
    simp only [↓reduceIte, hsum'] at hdec
    have h0 : analyticOrderNatAt (dslope f z₀) z₀ = 0 := by omega
    have h0' : analyticOrderAt (dslope f z₀) z₀ = 0 := by
      rw [← Nat.cast_analyticOrderNatAt htop₂, h0]
      rfl
    have han : AnalyticAt ℂ (dslope f z₀) z₀ :=
      ((Complex.differentiableOn_dslope (hU' z₀ hz₀)).mpr hf).analyticAt (hU' z₀ hz₀)
    rw [← dslope_same]
    exact han.analyticOrderAt_eq_zero.mp h0'
  · intro z hz hfz
    have hzo := mem_openSet_of_zero hR hw.ne_zero hz hfz
    exact Finset.mem_singleton.mp ((hmem z).mpr ⟨hzo, hfz⟩)

open ArgPrincipleAux in
/-- **Winding number zero**: no zero in the closed rectangle. -/
theorem argument_principle_rect_zero {f : ℂ → ℂ} {R : QRect} (hR : R.Nondeg) {U : Set ℂ}
    (hU : IsOpen U) (hRU : R.closedSet ⊆ U) (hf : DifferentiableOn ℂ f U)
    (hw : HasWinding (fun t => f (R.bdryPath t)) 0 4 0) :
    ∀ z ∈ R.closedSet, f z ≠ 0 := by
  obtain ⟨Z, hZ, htop, hsum⟩ := argument_principle_rect hR hU hRU hf hw
  intro z hz hfz
  have hzo := mem_openSet_of_zero hR hw.ne_zero hz hfz
  have hzZ : z ∈ Z := by
    rw [← Finset.mem_coe, hZ]
    exact ⟨hzo, hfz⟩
  have hsum' : ∑ z ∈ Z, analyticOrderNatAt f z = 0 := by exact_mod_cast hsum
  have h0 : analyticOrderNatAt f z = 0 := Finset.sum_eq_zero_iff.mp hsum' z hzZ
  have h0' : analyticOrderAt f z = 0 := by
    rw [← Nat.cast_analyticOrderNatAt (htop z hzZ), h0]
    rfl
  have han : AnalyticAt ℂ f z :=
    hf.analyticAt (hU.mem_nhds (hRU (R.openSet_subset_closedSet hzo)))
  exact (han.analyticOrderAt_eq_zero.mp h0') hfz

end NonUniqueEuler
