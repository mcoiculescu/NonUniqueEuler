import NonUniqueEuler.H.Sec9.ActiveRing.Units

/-!
# Helpers for `P/Sec9/ActiveRing`: supports and symmetry of `P.activeConfig k`

Helper file of `P/Sec9/ActiveRing.lean` (`09_relay.tex:759-767`, `06_datum.tex:323-330`).
* `tsupport_unitsVort`: `supp (A_k⁻¹ g(r_k ·)) = r_k⁻¹ supp g`;
* `tsupport_omegaRing`: `supp ω(t)1_{S_k(t)} = S_k(t)` (`t ≥ 0`; `ω(t)1_{S_k(t)} = f^{(n)}_k ∘ Φ_t⁻¹`
  and `Φ_t` is a homeomorphism);
* `active_disjoint`, `active_sym`: the three parts of `P.activeConfig k` have pairwise disjoint
  supports and are `3`-fold symmetric (`lem:regions-basic`(2),(3) at `t = t♯_k`);
* `nuIn_tsupport`, `nuOut_tsupport`: the support conditions of `lem:reduction` from
  `D_{k+1}(t) ⊂ B_{ar_k/8}` and `S_i(t) ∩ B_{6r_k} = ∅` (as in the proof of `ringConfig_hyp`).
Everything here is proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace ActiveRingAux

open RingData Datum Approx

variable {P : Approx}

/-- `‖r_k y‖ = r_k ‖y‖`. -/
theorem norm_r_mul (hP : P.Valid) (k : ℕ) (y : ℂ) :
    ‖((P.r k : ℝ) : ℂ) * y‖ = P.r k * ‖y‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hP.r_pos k)]

/-- `r_k (r_k⁻¹ x) = x`. -/
theorem r_mul_r_inv (hP : P.Valid) (k : ℕ) (x : ℂ) :
    ((P.r k : ℝ) : ℂ) * (((P.r k : ℝ) : ℂ)⁻¹ * x) = x := by
  have hr : ((P.r k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hP.r_pos k).ne'
  rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul]

/-- `r_k⁻¹ (r_k y) = y`. -/
theorem r_inv_mul_r (hP : P.Valid) (k : ℕ) (y : ℂ) :
    ((P.r k : ℝ) : ℂ)⁻¹ * (((P.r k : ℝ) : ℂ) * y) = y := by
  have hr : ((P.r k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hP.r_pos k).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hr, one_mul]

/-- `supp (A_k⁻¹ g(r_k ·)) = r_k⁻¹ supp g`. -/
theorem tsupport_unitsVort (hP : P.Valid) (k : ℕ) (g : ℂ → ℝ) :
    tsupport (P.unitsVort k g) = (fun y : ℂ => ((P.r k : ℝ) : ℂ) * y) ⁻¹' tsupport g := by
  have hr : ((P.r k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hP.r_pos k).ne'
  have hA : (P.A k)⁻¹ ≠ 0 := inv_ne_zero (hP.A_pos k).ne'
  have hsupp : Function.support (P.unitsVort k g) =
      Function.support (g ∘ Homeomorph.mulLeft₀ (((P.r k : ℝ) : ℂ)) hr) := by
    ext y
    simp only [Function.mem_support, unitsVort, scaleVort, Function.comp_apply,
      Homeomorph.coe_mulLeft₀, ne_eq, mul_eq_zero, hA, false_or]
  have h1 : tsupport (P.unitsVort k g) =
      tsupport (g ∘ Homeomorph.mulLeft₀ (((P.r k : ℝ) : ℂ)) hr) := by
    rw [tsupport, hsupp, ← tsupport]
  rw [h1, tsupport_comp_eq_preimage]
  rfl

/-- `supp ω(t)1_{S_k(t)} = S_k(t)` for `t ≥ 0` and `1 ≤ k ≤ n`. -/
theorem tsupport_omegaRing (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) {t : ℝ} (ht : 0 ≤ t) :
    tsupport (P.omegaRing k t) = P.St k t := by
  rw [(regions_basic_three P hP hN hk ht).1,
    tsupport_comp_inverse (continuous_flowInv hP hN t) (continuous_flow hP hN t)
      (flowInv_flow hP hN t) (flow_flowInv hP hN t)]
  rfl

/-- `supp (s.indicator g) ⊂ s` for a closed set `s`. -/
theorem tsupport_indicator_subset {s : Set ℂ} (hs : IsClosed s) (g : ℂ → ℝ) :
    tsupport (s.indicator g) ⊆ s :=
  closure_minimal Set.support_indicator_subset hs

/-- The supports of the three parts of `P.activeConfig k` are pairwise disjoint
(`lem:regions-basic`(2) at `t = t♯_k`). -/
theorem active_disjoint (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) (ht : 0 ≤ P.tsh k) :
    Disjoint (tsupport (P.activeConfig k).ring0) (tsupport (P.activeConfig k).inner0) ∧
    Disjoint (tsupport (P.activeConfig k).ring0) (tsupport (P.activeConfig k).outer0) ∧
    Disjoint (tsupport (P.activeConfig k).inner0) (tsupport (P.activeConfig k).outer0) := by
  have hkI : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨hk, hkn⟩
  obtain ⟨-, -, hcpt, hdisj, -, -⟩ := regions_basic_two P hP hN ht
  set t := P.tsh k with ht_def
  have hIcc : ∀ i ∈ Finset.Icc (k + 1) P.n, i ∈ Finset.Icc 1 P.n ∧ k < i := fun i hi => by
    rw [Finset.mem_Icc] at hi
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, hi.2⟩, by omega⟩
  have hIco : ∀ i ∈ Finset.Ico 1 k, i ∈ Finset.Icc 1 P.n ∧ i < k := fun i hi => by
    rw [Finset.mem_Ico] at hi
    exact ⟨Finset.mem_Icc.mpr ⟨hi.1, by omega⟩, hi.2⟩
  have hclD : IsClosed (P.D (k + 1) t) :=
    isClosed_biUnion_finset fun i hi => (hcpt i (hIcc i hi).1).1.isClosed
  have hclO : IsClosed (⋃ i ∈ Finset.Ico 1 k, P.St i t) :=
    isClosed_biUnion_finset fun i hi => (hcpt i (hIco i hi).1).1.isClosed
  have hsupp_ring : tsupport (P.activeConfig k).ring0 ⊆
      (fun y : ℂ => ((P.r k : ℝ) : ℂ) * y) ⁻¹' P.St k t := by
    show tsupport (P.unitsVort k (P.omegaRing k t)) ⊆ _
    rw [tsupport_unitsVort hP, tsupport_omegaRing hP hN hkI ht]
  have hsupp_inner : tsupport (P.activeConfig k).inner0 ⊆
      (fun y : ℂ => ((P.r k : ℝ) : ℂ) * y) ⁻¹' P.D (k + 1) t := by
    show tsupport (P.unitsVort k (P.omegaGe (k + 1) t)) ⊆ _
    rw [tsupport_unitsVort hP]
    exact preimage_mono (tsupport_indicator_subset hclD _)
  have hsupp_outer : tsupport (P.activeConfig k).outer0 ⊆
      (fun y : ℂ => ((P.r k : ℝ) : ℂ) * y) ⁻¹' ⋃ i ∈ Finset.Ico 1 k, P.St i t := by
    show tsupport (P.unitsVort k (P.omegaOut k t)) ⊆ _
    rw [tsupport_unitsVort hP]
    exact preimage_mono (tsupport_indicator_subset hclO _)
  refine ⟨?_, ?_, ?_⟩
  · refine Disjoint.mono hsupp_ring hsupp_inner (Disjoint.preimage _ ?_)
    refine Set.disjoint_iUnion₂_right.mpr fun i hi => ?_
    exact hdisj k hkI i (hIcc i hi).1 (by have := (hIcc i hi).2; omega)
  · refine Disjoint.mono hsupp_ring hsupp_outer (Disjoint.preimage _ ?_)
    refine Set.disjoint_iUnion₂_right.mpr fun i hi => ?_
    exact hdisj k hkI i (hIco i hi).1 (by have := (hIco i hi).2; omega)
  · refine Disjoint.mono hsupp_inner hsupp_outer (Disjoint.preimage _ ?_)
    refine Set.disjoint_iUnion₂_left.mpr fun i hi => Set.disjoint_iUnion₂_right.mpr fun j hj => ?_
    exact hdisj i (hIcc i hi).1 j (hIco j hj).1
      (by have := (hIcc i hi).2; have := (hIco j hj).2; omega)

/-- Pointwise symmetry gives the statement layer's a.e. `3`-fold symmetry. -/
theorem isMFoldSymmetric_of_forall {g : ℂ → ℝ} (hg : ∀ x, g (rot (2 * Real.pi / 3) x) = g x) :
    IsMFoldSymmetric 3 g := by
  refine Filter.Eventually.of_forall fun x => ?_
  show g (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x) = g x
  rw [Nat.cast_ofNat]
  exact hg x

/-- Ring-`k` units preserve pointwise `3`-fold symmetry. -/
theorem unitsVort_symm (k : ℕ) {g : ℂ → ℝ} (hg : ∀ x, g (rot (2 * Real.pi / 3) x) = g x)
    (x : ℂ) : P.unitsVort k g (rot (2 * Real.pi / 3) x) = P.unitsVort k g x := by
  have h : ((P.r k : ℝ) : ℂ) * rot (2 * Real.pi / 3) x =
      rot (2 * Real.pi / 3) (((P.r k : ℝ) : ℂ) * x) := by
    simp only [rot]; ring
  simp only [unitsVort, scaleVort]
  rw [h, hg]

/-- The three parts of `P.activeConfig k` are `3`-fold symmetric (`lem:regions-basic`(3) at
`t = t♯_k`). -/
theorem active_sym (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) (ht : 0 ≤ P.tsh k) :
    IsMFoldSymmetric 3 (P.activeConfig k).ring0 ∧ IsMFoldSymmetric 3 (P.activeConfig k).inner0 ∧
      IsMFoldSymmetric 3 (P.activeConfig k).outer0 := by
  have hkI : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨hk, hkn⟩
  set t := P.tsh k with ht_def
  have hringsym : ∀ i ∈ Finset.Icc 1 P.n, ∀ x,
      P.omegaRing i t (rot (2 * Real.pi / 3) x) = P.omegaRing i t x := fun i hi =>
    (regions_basic_three P hP hN hi ht).2.2.2.2.2.2.1.2.2.2
  have hgesym : ∀ x, P.omegaGe (k + 1) t (rot (2 * Real.pi / 3) x) = P.omegaGe (k + 1) t x := by
    rcases Nat.lt_or_ge k P.n with hlt | hge
    · have hk1 : k + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      exact (regions_basic_three P hP hN hk1 ht).2.2.2.2.2.2.2.2.2.2
    · have hkn' : k = P.n := le_antisymm hkn hge
      intro x
      rw [hkn', omegaGe_succ_n]
      rfl
  have houtsym : ∀ x, P.omegaOut k t (rot (2 * Real.pi / 3) x) = P.omegaOut k t x := by
    intro x
    rw [(regions_basic_three P hP hN hkI ht).2.2.2.2.1]
    refine Finset.sum_congr rfl fun i hi => hringsym i ?_ x
    rw [Finset.mem_Ico] at hi
    exact Finset.mem_Icc.mpr ⟨hi.1, by omega⟩
  exact ⟨isMFoldSymmetric_of_forall (unitsVort_symm (P := P) k (hringsym k hkI)),
    isMFoldSymmetric_of_forall (unitsVort_symm (P := P) k hgesym),
    isMFoldSymmetric_of_forall (unitsVort_symm (P := P) k houtsym)⟩

/-- If `D_{k+1}(t) ⊂ B_{a r_k/8}`, then `supp ν^in_k(t) ⊂ \bar B_{a/8}`. -/
theorem nuIn_tsupport (hP : P.Valid) {k : ℕ} {t : ℝ} (hD : P.HInDefined k t) :
    tsupport (P.nuIn k t) ⊆ closedBall 0 (a / 8) := by
  have hr := hP.r_pos k
  have hcl : tsupport (P.omegaGe (k + 1) t) ⊆ closedBall 0 (a * P.r k / 8) :=
    (closure_mono (Set.support_indicator_subset.trans hD)).trans closure_ball_subset_closedBall
  intro y hy
  have h1 : ((P.r k : ℝ) : ℂ) * y ∈ closedBall 0 (a * P.r k / 8) := by
    have hy' := hy
    rw [nuIn, tsupport_unitsVort hP] at hy'
    exact hcl hy'
  rw [mem_closedBall, dist_zero_right, norm_r_mul hP] at h1
  rw [mem_closedBall, dist_zero_right]
  have h2 : P.r k * ‖y‖ ≤ P.r k * (a / 8) := by linarith
  exact le_of_mul_le_mul_left h2 hr

/-- If the rings `i < k` lie outside `B_{6 r_k}` at a time `t ≥ 0`, then
`supp ν^out_k(t) ∩ B_6 = ∅`. -/
theorem nuOut_tsupport (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hkn : k ≤ P.n)
    {t : ℝ} (ht : 0 ≤ t) (hO : P.HOutDefined k t) :
    tsupport (P.nuOut k t) ∩ ball 0 6 = ∅ := by
  have hr := hP.r_pos k
  obtain ⟨-, -, hRB2, -⟩ := regions_basic_two P hP hN ht
  have hIco : ∀ i ∈ Finset.Ico 1 k, i ∈ Finset.Icc 1 P.n := fun i hi => by
    rw [Finset.mem_Ico] at hi
    exact Finset.mem_Icc.mpr ⟨hi.1, by omega⟩
  have hcl : tsupport (P.omegaOut k t) ⊆ ⋃ i ∈ Finset.Ico 1 k, P.St i t :=
    tsupport_indicator_subset
      (isClosed_biUnion_finset fun i hi => (hRB2 i (hIco i hi)).1.isClosed) _
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨hy, hyb⟩
  have hy' : ((P.r k : ℝ) : ℂ) * y ∈ ⋃ i ∈ Finset.Ico 1 k, P.St i t := by
    rw [nuOut, tsupport_unitsVort hP] at hy
    exact hcl hy
  obtain ⟨i, hi, hiy⟩ := mem_iUnion₂.mp hy'
  have h2 : ((P.r k : ℝ) : ℂ) * y ∈ ball (0 : ℂ) (6 * P.r k) := by
    rw [mem_ball, dist_zero_right, norm_r_mul hP]
    rw [mem_ball, dist_zero_right] at hyb
    nlinarith
  exact (Set.eq_empty_iff_forall_notMem.mp (hO i hi)) (((P.r k : ℝ) : ℂ) * y) ⟨hiy, h2⟩

end ActiveRingAux

end Relay

end NonUniqueEuler
