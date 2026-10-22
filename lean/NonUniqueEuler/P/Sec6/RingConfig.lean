import NonUniqueEuler.Defs.Sec6.All
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec6.Adm
import NonUniqueEuler.I.SmoothB.SmoothCovariance
import NonUniqueEuler.I.Sec2.BSBasic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Proof: ring `k` in ring-`k` units as a configuration of `lem:reduction`

Proof of `I/Sec6/RingConfig.lean` (`06_datum.tex:138-156`, `:323-330`).

* `ringConfig_units`: the scaling covariance of `thm:smooth` (`Smooth.sol_scale`) applied to the
  datum `A_k⁻¹ f^{(n)}(r_k ·)` (`ringConfig_datum`) gives the solution, velocity, flow and inverse
  flow; `eq:omega-ge` (`regions_basic_three`) identifies the transported parts; the change of
  variables `x = r_k y` (`Measure.integral_comp_smul`) gives `G = G_k`; linearity of `K_BS *` on
  continuous compactly supported functions (absolute convergence, `lem:BS-basic`(b)) gives
  `h = h_k`.
* `ringConfig_hyp`: the datum is `C_c^∞` (`sol_scale`, `lem:adm`); the supports of the parts lie in
  `r_k⁻¹ S_k`, `r_k⁻¹ ⋃_{i>k} S_i`, `r_k⁻¹ ⋃_{i<k} S_i`, which are pairwise disjoint
  (`regions_basic_one`); the parts are pointwise `3`-fold symmetric (`regions_basic_three` at
  `t = 0`); `D_{k+1}(t) ⊂ B_{a r_k/8}` gives `supp ω_i(τ) ⊂ \bar B_{a/8}` and `S_i(t) ∩ B_{6 r_k} = ∅`
  (with `S_i(t)` compact, `regions_basic_two`) gives `supp ω_o(τ) ∩ B_6 = ∅`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Datum

namespace RingConfigAux

open RingData Approx

/-- The maximal flow at its own initial time is the identity (also in the junk case). -/
theorem maxFlow_self {F : ℝ → ℂ → ℂ} {U : Set (ℝ × ℂ)} {s : ℝ} {y : ℂ} :
    Smooth.maxFlow F U s s y = y := by
  classical
  by_cases h : ∃ (J : Set ℝ) (γ : ℝ → ℂ), Smooth.IsMaxSol F U s y J γ
  · exact (Smooth.isMaxSol_maxFlow h).init
  · rw [Smooth.maxFlow, dite_eq_right h]

/-- `Φ_0⁻¹ = id`. -/
theorem flowInv_zero (P : Approx) (x : ℂ) : P.flowInv 0 x = x := by
  simp only [flowInv, Smooth.flowOf]
  exact maxFlow_self

variable {P : Approx}

/-- `f^{(n)}` is an admissible datum of `thm:smooth` (`lem:adm`). -/
theorem isSmoothDatum (hP : P.Valid) (hN : NumericalHypothesis P.χ) :
    ∃ R₀ : ℝ, Smooth.IsSmoothDatum P.f R₀ := by
  obtain ⟨hcd, hcs, -⟩ :=
    (adm P.χ hP.admissible hN hP.datumParams ⟨hP.kseed_pos, hP.kseed_le⟩).1 P.n hP.two_le_n
  obtain ⟨R₀, hR₀⟩ := hcs.isCompact.isBounded.subset_ball 0
  exact ⟨R₀, hcd, hR₀⟩

/-- The datum of the configuration of ring `k`, written out. -/
theorem datum_eq {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ P.n) :
    (P.ringConfig k).datum = fun y => (P.A k)⁻¹ * P.f (((P.r k : ℝ) : ℂ) * y) :=
  P.ringConfig_datum hk hkn

/-- Scaling covariance of `thm:smooth` specialized to the configuration of ring `k`. -/
theorem scale_facts (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) :
    (∀ (τ : ℝ) (y : ℂ), (P.ringConfig k).sol τ y =
      (P.A k)⁻¹ * P.om (τ / P.A k) (((P.r k : ℝ) : ℂ) * y)) ∧
    (∀ (τ : ℝ) (y : ℂ), Smooth.vel (P.ringConfig k).datum τ y =
      (((P.A k * P.r k)⁻¹ : ℝ) : ℂ) * P.vel (τ / P.A k) (((P.r k : ℝ) : ℂ) * y)) ∧
    (∀ (τ : ℝ) (y : ℂ), (P.ringConfig k).flow τ y =
      ((P.r k : ℝ) : ℂ)⁻¹ * P.flow (τ / P.A k) (((P.r k : ℝ) : ℂ) * y)) ∧
    (∀ (τ : ℝ) (x : ℂ), (P.ringConfig k).flowInv τ x =
      ((P.r k : ℝ) : ℂ)⁻¹ * P.flowInv (τ / P.A k) (((P.r k : ℝ) : ℂ) * x)) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.ringConfig k).datum ∧
    HasCompactSupport (P.ringConfig k).datum := by
  obtain ⟨R₀, hD⟩ := isSmoothDatum hP hN
  obtain ⟨h1, h2, h3, h4, h5⟩ := Smooth.sol_scale hD (hP.A_pos k) (hP.r_pos k)
  have hdat := datum_eq (P := P) hk hkn
  refine ⟨fun τ y => ?_, fun τ y => ?_, fun τ y => ?_, fun τ x => ?_, ?_, ?_⟩
  · rw [OneRing.RingConfig.sol, hdat, h2, hP.om_eq]
  · rw [hdat, h3]
    simp only [Approx.vel, Smooth.vel, hP.om_eq]
  · rw [OneRing.RingConfig.flow, hdat, h4, hP.flow_eq, Complex.ofReal_inv]
  · rw [OneRing.RingConfig.flowInv, hdat, h5, hP.flowInv_eq, Complex.ofReal_inv]
  · rw [hdat]; exact h1.contDiff
  · rw [hdat]; exact h1.hasCompactSupport

/-- A part `A_k⁻¹ g(r_k ·)` transported by the flow of the configuration of ring `k`. -/
theorem unitsVort_flowInv (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) (g : ℂ → ℝ) (τ : ℝ) (x : ℂ) :
    P.unitsVort k g ((P.ringConfig k).flowInv τ x) =
      (P.A k)⁻¹ * g (P.flowInv (τ / P.A k) (((P.r k : ℝ) : ℂ) * x)) := by
  rw [(scale_facts hP hN hk hkn).2.2.2.1 τ x]
  have hr : ((P.r k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hP.r_pos k).ne'
  simp only [unitsVort, scaleVort]
  rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul]

/-- `ω_{≥k+1}(t) = (Σ_{i>k} f^{(n)}_i) ∘ Φ_t⁻¹` for `1 ≤ k ≤ n` (`eq:omega-ge`; both sides vanish for
`k = n`). -/
theorem omegaGe_succ (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) {t : ℝ} (ht : 0 ≤ t) :
    P.omegaGe (k + 1) t = fun x => ∑ i ∈ Finset.Ioc k P.n, P.term i (P.flowInv t x) := by
  rcases Nat.lt_or_ge k P.n with hlt | hge
  · have hk1 : k + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [(regions_basic_three P hP hN hk1 ht).2.1, Finset.Icc_add_one_left_eq_Ioc]
  · have hkn' : k = P.n := le_antisymm hkn hge
    rw [hkn', omegaGe_succ_n, Finset.Ioc_self]
    funext x
    simp

/-- The terms `f^{(n)}_i`, `1 ≤ i ≤ n`, are `C_c^∞` and pointwise `3`-fold symmetric
(`lem:regions-basic`(3) at `t = 0`). -/
theorem term_facts (hP : P.Valid) (hN : NumericalHypothesis P.χ) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 P.n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.term i) ∧ HasCompactSupport (P.term i) ∧
      ∀ x, P.term i (rot (2 * Real.pi / 3) x) = P.term i x := by
  obtain ⟨h1, -, -, -, -, -, ⟨hcd, hcs, -, hsym⟩, -⟩ := regions_basic_three P hP hN hi (le_refl 0)
  have h : P.omegaRing i 0 = P.term i := by
    rw [h1]
    funext x
    rw [flowInv_zero]
  rw [← h]
  exact ⟨hcd, hcs, hsym⟩

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

/-- Finite sums of pointwise symmetric functions are pointwise symmetric. -/
theorem sum_symm (s : Finset ℕ) {g : ℕ → ℂ → ℝ}
    (hg : ∀ i ∈ s, ∀ x, g i (rot (2 * Real.pi / 3) x) = g i x) (x : ℂ) :
    (fun y => ∑ i ∈ s, g i y) (rot (2 * Real.pi / 3) x) = (fun y => ∑ i ∈ s, g i y) x :=
  Finset.sum_congr rfl fun i hi => hg i hi x

/-- `supp (A_k⁻¹ g(r_k ·)) ⊂ r_k⁻¹ supp g`. -/
theorem tsupport_unitsVort_subset (k : ℕ) (g : ℂ → ℝ) :
    tsupport (P.unitsVort k g) ⊆ (fun y : ℂ => ((P.r k : ℝ) : ℂ) * y) ⁻¹' tsupport g := by
  have hc : Continuous fun y : ℂ => ((P.r k : ℝ) : ℂ) * y := continuous_const.mul continuous_id
  refine (closure_mono ?_).trans (tsupport_comp_subset_preimage g hc)
  intro y hy
  simp only [Function.mem_support, unitsVort, scaleVort, Function.comp_apply] at hy ⊢
  exact right_ne_zero_of_mul hy

/-- `supp Σ_{i ∈ s} g_i ⊂ ⋃_{i ∈ s} supp g_i`. -/
theorem tsupport_sum_subset (s : Finset ℕ) (g : ℕ → ℂ → ℝ) :
    tsupport (fun x => ∑ i ∈ s, g i x) ⊆ ⋃ i ∈ s, tsupport (g i) := by
  refine closure_minimal ?_ (isClosed_biUnion_finset fun i _ => isClosed_tsupport _)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hne
  apply hx
  refine Finset.sum_eq_zero fun i hi => ?_
  by_contra h
  exact hne (mem_iUnion₂.mpr ⟨i, hi, subset_tsupport _ h⟩)

/-- Ring-`k` units preserve continuity and compact support. -/
theorem unitsVort_cont (hP : P.Valid) (k : ℕ) {g : ℂ → ℝ} (hg : Continuous g)
    (hg' : HasCompactSupport g) :
    Continuous (P.unitsVort k g) ∧ HasCompactSupport (P.unitsVort k g) := by
  have hr : P.r k ≠ 0 := (hP.r_pos k).ne'
  have heq : P.unitsVort k g = fun y => (P.A k)⁻¹ * (fun x : ℂ => g (P.r k • x)) y := by
    funext y
    simp only [unitsVort, scaleVort, Complex.real_smul]
  rw [heq]
  refine ⟨continuous_const.mul (hg.comp (continuous_const_smul _)), ?_⟩
  exact (hg'.comp_smul hr).mul_left

/-- Linearity of `K_BS *` on `L¹ ∩ L^∞` (absolute convergence, `lem:BS-basic`(b)). -/
theorem velocity_add {f g : ℂ → ℝ} (hf : MemLp f 1 volume) (hf' : MemLp f ⊤ volume)
    (hg : MemLp g 1 volume) (hg' : MemLp g ⊤ volume) (x : ℂ) :
    velocity (fun y => f y + g y) x = velocity f x + velocity g x := by
  have h1 := (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf hf hf' x).1
  have h2 := (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf hg hg' x).1
  simp only [velocity]
  rw [← integral_add h1 h2]
  congr 1
  funext y
  push_cast
  ring

/-- The supports of the three parts of the configuration of ring `k` are pairwise disjoint
(`lem:regions-basic`(1)). -/
theorem hyp_disjoint (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) :
    Disjoint (tsupport (P.ringConfig k).ring0) (tsupport (P.ringConfig k).inner0) ∧
    Disjoint (tsupport (P.ringConfig k).ring0) (tsupport (P.ringConfig k).outer0) ∧
    Disjoint (tsupport (P.ringConfig k).inner0) (tsupport (P.ringConfig k).outer0) := by
  have hkI : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨hk, hkn⟩
  obtain ⟨-, hdisj, -, -⟩ := regions_basic_one P hP hN
  have hsupp_ring : tsupport (P.ringConfig k).ring0 ⊆
      (fun y : ℂ => ((P.r k : ℝ) : ℂ) * y) ⁻¹' P.S k :=
    tsupport_unitsVort_subset (P := P) k (P.term k)
  have hsupp_inner : tsupport (P.ringConfig k).inner0 ⊆
      (fun y : ℂ => ((P.r k : ℝ) : ℂ) * y) ⁻¹' ⋃ i ∈ Finset.Ioc k P.n, P.S i :=
    (tsupport_unitsVort_subset (P := P) k (fun x => ∑ i ∈ Finset.Ioc k P.n, P.term i x)).trans
      (preimage_mono (tsupport_sum_subset (Finset.Ioc k P.n) P.term))
  have hsupp_outer : tsupport (P.ringConfig k).outer0 ⊆
      (fun y : ℂ => ((P.r k : ℝ) : ℂ) * y) ⁻¹' ⋃ i ∈ Finset.Ico 1 k, P.S i :=
    (tsupport_unitsVort_subset (P := P) k (fun x => ∑ i ∈ Finset.Ico 1 k, P.term i x)).trans
      (preimage_mono (tsupport_sum_subset (Finset.Ico 1 k) P.term))
  have hIoc : ∀ i ∈ Finset.Ioc k P.n, i ∈ Finset.Icc 1 P.n ∧ k < i := fun i hi => by
    rw [Finset.mem_Ioc] at hi
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, hi.2⟩, hi.1⟩
  have hIco : ∀ i ∈ Finset.Ico 1 k, i ∈ Finset.Icc 1 P.n ∧ i < k := fun i hi => by
    rw [Finset.mem_Ico] at hi
    exact ⟨Finset.mem_Icc.mpr ⟨hi.1, by omega⟩, hi.2⟩
  refine ⟨?_, ?_, ?_⟩
  · refine Disjoint.mono hsupp_ring hsupp_inner (Disjoint.preimage _ ?_)
    refine Set.disjoint_iUnion₂_right.mpr fun i hi => ?_
    exact hdisj k hkI i (hIoc i hi).1 (by have := (hIoc i hi).2; omega)
  · refine Disjoint.mono hsupp_ring hsupp_outer (Disjoint.preimage _ ?_)
    refine Set.disjoint_iUnion₂_right.mpr fun i hi => ?_
    exact hdisj k hkI i (hIco i hi).1 (by have := (hIco i hi).2; omega)
  · refine Disjoint.mono hsupp_inner hsupp_outer (Disjoint.preimage _ ?_)
    refine Set.disjoint_iUnion₂_left.mpr fun i hi => Set.disjoint_iUnion₂_right.mpr fun j hj => ?_
    exact hdisj i (hIoc i hi).1 j (hIco j hj).1
      (by have := (hIoc i hi).2; have := (hIco j hj).2; omega)

/-- The three parts of the configuration of ring `k` are `3`-fold symmetric. -/
theorem hyp_sym (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) :
    IsMFoldSymmetric 3 (P.ringConfig k).ring0 ∧ IsMFoldSymmetric 3 (P.ringConfig k).inner0 ∧
      IsMFoldSymmetric 3 (P.ringConfig k).outer0 := by
  have hkI : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨hk, hkn⟩
  have hsymt : ∀ i ∈ Finset.Icc 1 P.n, ∀ x, P.term i (rot (2 * Real.pi / 3) x) = P.term i x :=
    fun i hi => (term_facts hP hN hi).2.2
  have hIoc : ∀ i ∈ Finset.Ioc k P.n, i ∈ Finset.Icc 1 P.n := fun i hi => by
    rw [Finset.mem_Ioc] at hi
    exact Finset.mem_Icc.mpr ⟨by omega, hi.2⟩
  have hIco : ∀ i ∈ Finset.Ico 1 k, i ∈ Finset.Icc 1 P.n := fun i hi => by
    rw [Finset.mem_Ico] at hi
    exact Finset.mem_Icc.mpr ⟨hi.1, by omega⟩
  have h1 : ∀ x, (P.ringConfig k).ring0 (rot (2 * Real.pi / 3) x) = (P.ringConfig k).ring0 x :=
    unitsVort_symm (P := P) k (g := P.term k) (hsymt k hkI)
  have h2 : ∀ x, (P.ringConfig k).inner0 (rot (2 * Real.pi / 3) x) = (P.ringConfig k).inner0 x :=
    unitsVort_symm (P := P) k (g := fun x => ∑ i ∈ Finset.Ioc k P.n, P.term i x)
      (sum_symm _ fun i hi => hsymt i (hIoc i hi))
  have h3 : ∀ x, (P.ringConfig k).outer0 (rot (2 * Real.pi / 3) x) = (P.ringConfig k).outer0 x :=
    unitsVort_symm (P := P) k (g := fun x => ∑ i ∈ Finset.Ico 1 k, P.term i x)
      (sum_symm _ fun i hi => hsymt i (hIco i hi))
  exact ⟨isMFoldSymmetric_of_forall h1, isMFoldSymmetric_of_forall h2,
    isMFoldSymmetric_of_forall h3⟩

/-- `‖r_k y‖ = r_k ‖y‖`. -/
theorem norm_r_mul (hP : P.Valid) (k : ℕ) (y : ℂ) :
    ‖((P.r k : ℝ) : ℂ) * y‖ = P.r k * ‖y‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hP.r_pos k)]

/-- If `D_{k+1}(t) ⊂ B_{a r_k/8}`, then `supp ν^in_k(t) ⊂ \bar B_{a/8}`. -/
theorem nuIn_tsupport (hP : P.Valid) {k : ℕ} {t : ℝ} (hD : P.HInDefined k t) :
    tsupport (P.nuIn k t) ⊆ closedBall 0 (a / 8) := by
  have hr := hP.r_pos k
  have hcl : tsupport (P.omegaGe (k + 1) t) ⊆ closedBall 0 (a * P.r k / 8) :=
    (closure_mono (Set.support_indicator_subset.trans hD)).trans closure_ball_subset_closedBall
  intro y hy
  have h1 : ((P.r k : ℝ) : ℂ) * y ∈ closedBall 0 (a * P.r k / 8) :=
    hcl (tsupport_unitsVort_subset (P := P) k (P.omegaGe (k + 1) t) hy)
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
    closure_minimal Set.support_indicator_subset
      (isClosed_biUnion_finset fun i hi => (hRB2 i (hIco i hi)).1.isClosed)
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨hy, hyb⟩
  have hy' : ((P.r k : ℝ) : ℂ) * y ∈ ⋃ i ∈ Finset.Ico 1 k, P.St i t :=
    hcl (tsupport_unitsVort_subset (P := P) k (P.omegaOut k t) hy)
  obtain ⟨i, hi, hiy⟩ := mem_iUnion₂.mp hy'
  have h2 : ((P.r k : ℝ) : ℂ) * y ∈ ball (0 : ℂ) (6 * P.r k) := by
    rw [mem_ball, dist_zero_right, norm_r_mul hP]
    rw [mem_ball, dist_zero_right] at hyb
    nlinarith
  exact (Set.eq_empty_iff_forall_notMem.mp (hO i hi)) (((P.r k : ℝ) : ℂ) * y) ⟨hiy, h2⟩

end RingConfigAux

namespace Approx

open RingData RingConfigAux

/-- **Ring `k` in ring-`k` units** (`06_datum.tex:138-156`, `:323-330`): for `1 ≤ k ≤ n`, the
configuration `P.ringConfig k` has solution `A_k⁻¹ω(τ/A_k, r_k ·)`, velocity `v(τ/A_k)_{[k]}` and
flow `r_k⁻¹Φ_{τ/A_k}(r_k ·)`; for `τ ≥ 0` its ring, inner and outer parts are the rescaled
`ω(t)1_{S_k(t)}`, `ν^in_k`, `ν^out_k` at `t = τ/A_k`, its perturbation is `w_k(τ/A_k)`, its field
is `h_k(τ)`; and its inner circulation is `G_k`. -/
theorem ringConfig_units (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ P.n) :
    (∀ (τ : ℝ) (y : ℂ), (P.ringConfig k).sol τ y = P.unitsVort k (P.om (τ / P.A k)) y) ∧
    (∀ (τ : ℝ) (y : ℂ), Smooth.vel (P.ringConfig k).datum τ y =
      P.unitsField k (P.vel (τ / P.A k)) y) ∧
    (∀ (τ : ℝ) (y : ℂ), (P.ringConfig k).flow τ y =
      ((P.r k : ℝ) : ℂ)⁻¹ * P.flow (τ / P.A k) (((P.r k : ℝ) : ℂ) * y)) ∧
    (∀ τ : ℝ, 0 ≤ τ → (P.ringConfig k).ringPart τ = P.unitsVort k (P.omegaRing k (τ / P.A k))) ∧
    (∀ τ : ℝ, 0 ≤ τ → (P.ringConfig k).innerPart τ = P.nuIn k (τ / P.A k)) ∧
    (∀ τ : ℝ, 0 ≤ τ → (P.ringConfig k).outerPart τ = P.nuOut k (τ / P.A k)) ∧
    (∀ τ : ℝ, 0 ≤ τ → (P.ringConfig k).w P.χ τ = P.w k (τ / P.A k)) ∧
    (P.ringConfig k).G = P.G k ∧
    ∀ τ : ℝ, 0 ≤ τ → ∀ y : ℂ, (P.ringConfig k).h τ y = P.hField k τ y := by
  obtain ⟨hsol, hvel, hflow, -, -, -⟩ := scale_facts hP hN hk hkn
  have hkI : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨hk, hkn⟩
  have hA := hP.A_pos k
  have hr := hP.r_pos k
  -- the three transported parts
  have hring : ∀ τ : ℝ, 0 ≤ τ →
      (P.ringConfig k).ringPart τ = P.unitsVort k (P.omegaRing k (τ / P.A k)) := by
    intro τ hτ
    funext x
    rw [OneRing.RingConfig.ringPart]
    show P.unitsVort k (P.term k) ((P.ringConfig k).flowInv τ x) = _
    rw [unitsVort_flowInv hP hN hk hkn,
      (regions_basic_three P hP hN hkI (div_nonneg hτ hA.le)).1]
    rfl
  have hinner : ∀ τ : ℝ, 0 ≤ τ → (P.ringConfig k).innerPart τ = P.nuIn k (τ / P.A k) := by
    intro τ hτ
    funext x
    show P.unitsVort k (fun x => ∑ i ∈ Finset.Ioc k P.n, P.term i x)
      ((P.ringConfig k).flowInv τ x) = _
    rw [unitsVort_flowInv hP hN hk hkn, nuIn, omegaGe_succ hP hN hk hkn (div_nonneg hτ hA.le)]
    rfl
  have houter : ∀ τ : ℝ, 0 ≤ τ → (P.ringConfig k).outerPart τ = P.nuOut k (τ / P.A k) := by
    intro τ hτ
    funext x
    show P.unitsVort k (fun x => ∑ i ∈ Finset.Ico 1 k, P.term i x)
      ((P.ringConfig k).flowInv τ x) = _
    rw [unitsVort_flowInv hP hN hk hkn, nuOut,
      (regions_basic_three P hP hN hkI (div_nonneg hτ hA.le)).2.2.2.1]
    rfl
  -- the inner circulation
  have hG : (P.ringConfig k).G = P.G k := by
    have h0 := omegaGe_succ hP hN hk hkn (le_refl (0 : ℝ))
    simp only [flowInv_zero] at h0
    simp only [OneRing.RingConfig.G, Approx.G, h0]
    set g : ℂ → ℝ := fun x => ∑ i ∈ Finset.Ioc k P.n, P.term i x with hg
    have hcv : ∫ x, (P.ringConfig k).inner0 x = (P.A k)⁻¹ * (((P.r k) ^ 2)⁻¹ * ∫ x, g x) := by
      show ∫ x, (P.A k)⁻¹ * g (((P.r k : ℝ) : ℂ) * x) = _
      rw [integral_const_mul]
      congr 1
      have hs : (fun x : ℂ => g (((P.r k : ℝ) : ℂ) * x)) = fun x : ℂ => g (P.r k • x) := by
        funext x
        rw [Complex.real_smul]
      rw [hs, Measure.integral_comp_smul, Complex.finrank_real_complex, smul_eq_mul,
        abs_of_pos (inv_pos.mpr (pow_pos hr 2))]
    rw [hcv]
    ring
  refine ⟨fun τ y => ?_, fun τ y => ?_, hflow, hring, hinner, houter, fun τ hτ => ?_, hG,
    fun τ hτ y => ?_⟩
  · exact hsol τ y
  · rw [hvel τ y]
    simp only [unitsField, scaleField]
    rw [Complex.ofReal_inv, ← div_eq_inv_mul]
  · funext x
    simp only [OneRing.RingConfig.w, Approx.w, wR]
    rw [hring τ hτ]
  · -- the field `h`
    have ht : 0 ≤ τ / P.A k := div_nonneg hτ hA.le
    set t := τ / P.A k with ht_def
    -- regularity of `ν^in_k`, `ν^out_k`
    have hin_reg : Continuous (P.nuIn k t) ∧ HasCompactSupport (P.nuIn k t) := by
      rcases Nat.lt_or_ge k P.n with hlt | hge
      · have hk1 : k + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        obtain ⟨-, -, -, -, -, -, -, ⟨hcd, hcs, -⟩⟩ := regions_basic_three P hP hN hk1 ht
        exact unitsVort_cont hP k hcd.continuous hcs
      · have hkn' : k = P.n := le_antisymm hkn hge
        have h0 : P.nuIn k t = fun _ => 0 := by
          funext y
          simp only [nuIn, unitsVort, scaleVort]
          rw [hkn', omegaGe_succ_n]
          simp
        rw [h0]
        exact ⟨continuous_const, HasCompactSupport.zero⟩
    have hout_reg : Continuous (P.nuOut k t) ∧ HasCompactSupport (P.nuOut k t) := by
      have hO := (regions_basic_three P hP hN hkI ht).2.2.2.2.1
      have hsub : ∀ i ∈ Finset.Ico 1 k, i ∈ Finset.Icc 1 P.n := fun i hi => by
        rw [Finset.mem_Ico] at hi
        exact Finset.mem_Icc.mpr ⟨hi.1, by omega⟩
      have hreg : ∀ i ∈ Finset.Ico 1 k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.omegaRing i t) ∧
          HasCompactSupport (P.omegaRing i t) := fun i hi => by
        obtain ⟨-, -, -, -, -, -, ⟨hcd, hcs, -⟩, -⟩ := regions_basic_three P hP hN (hsub i hi) ht
        exact ⟨hcd, hcs⟩
      have hc : Continuous (P.omegaOut k t) := by
        rw [hO]
        exact continuous_finsetSum _ fun i hi => (hreg i hi).1.continuous
      have hcs : HasCompactSupport (P.omegaOut k t) := by
        rw [hO]
        have h := HasCompactSupport.finset_sum (s := Finset.Ico 1 k)
          (f := fun i => P.omegaRing i t) fun i hi => (hreg i hi).2
        simpa only [Finset.sum_fn] using h
      exact unitsVort_cont hP k hc hcs
    have hadd := velocity_add (hin_reg.1.memLp_of_hasCompactSupport hin_reg.2)
      (hin_reg.1.memLp_of_hasCompactSupport hin_reg.2)
      (hout_reg.1.memLp_of_hasCompactSupport hout_reg.2)
      (hout_reg.1.memLp_of_hasCompactSupport hout_reg.2) y
    rw [OneRing.RingConfig.h, hinner τ hτ, houter τ hτ, hG, hadd, hField, hIn, hOut]
    ring

/-- **Ring `k` satisfies the hypotheses of `lem:reduction`** (`06_datum.tex:323-330`): if `T > 0`
and, for every `t ∈ [0, T]`, `D_{k+1}(t) ⊂ B_{ar_k/8}` and the rings `i < k` lie outside
`B_{6r_k}`, then `P.ringConfig k` satisfies `RingConfig.Hyp` on `[0, A_kT]` (with `G = G_k` and
`h = h_k`, `ringConfig_units`). -/
theorem ringConfig_hyp (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ P.n) {T : ℝ} (hT : 0 < T)
    (hdef : ∀ t ∈ Icc (0 : ℝ) T, P.HDefined k t) :
    (P.ringConfig k).Hyp (P.A k * T) := by
  obtain ⟨-, -, -, -, hcd, hcs⟩ := scale_facts hP hN hk hkn
  obtain ⟨-, -, -, -, hinner, houter, -⟩ := P.ringConfig_units hP hN hk hkn
  obtain ⟨d1, d2, d3⟩ := hyp_disjoint hP hN hk hkn
  obtain ⟨s1, s2, s3⟩ := hyp_sym hP hN hk hkn
  have hA := hP.A_pos k
  have htime : ∀ τ ∈ Icc (0 : ℝ) (P.A k * T), τ / P.A k ∈ Icc (0 : ℝ) T := fun τ hτ =>
    ⟨div_nonneg hτ.1 hA.le, (div_le_iff₀ hA).mpr (by linarith [hτ.2])⟩
  refine ⟨hcd, hcs, d1, d2, d3, s1, s2, s3, mul_pos hA hT, fun τ hτ => ?_, fun τ hτ => ?_⟩
  · rw [hinner τ hτ.1]
    exact nuIn_tsupport hP (hdef _ (htime τ hτ)).1
  · rw [houter τ hτ.1]
    exact nuOut_tsupport hP hN hkn (htime τ hτ).1 (hdef _ (htime τ hτ)).2

end Approx

end Datum

end NonUniqueEuler
