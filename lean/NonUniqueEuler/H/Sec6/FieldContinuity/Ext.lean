import NonUniqueEuler.Defs.Sec6.All
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec6.Adm
import NonUniqueEuler.I.SmoothB.SmoothFlow
import NonUniqueEuler.I.Infra.BSParam.ContDiff
import NonUniqueEuler.H.Sec6.FieldContinuity.Generic

/-!
# Helpers for `P/Sec6/FieldContinuity`: smooth space–time extensions of the fields

For a valid approximation `P` (`06_datum.tex:294-321`):

* `flow_facts`: `(t, y) ↦ Φ_t(y)` and `(t, x) ↦ Φ_t⁻¹(x)` are `C^∞` on `ℝ × ℝ²`, and
  `Φ_t ∘ Φ_t⁻¹ = id` (`thm:smooth`(4): `Smooth.flow_contDiff`, `Smooth.flow_diffeo`, the datum
  `f^{(n)}` being `C_c^∞` by `lem:adm`); `flowInv_zero_apply`: `Φ_0⁻¹ = id`;
* `term_smooth`, `sumTerms_smooth`: the terms `f^{(n)}_i` (and their finite sums) are `C_c^∞`
  (`lem:regions-basic`(3) at `t = 0`);
* `slab_flowInv`, `slab_extU`: for `g` with compact support, `g ∘ Φ_t⁻¹` vanishes outside a ball
  that is uniform for `|t| ≤ T` (the image of `[-T, T] × supp g` under the continuous map
  `(t, y) ↦ Φ_t(y)` is compact), also in ring-`k` units;
* `contDiff_velocity_extU`: the Biot–Savart velocity of `(τ, y) ↦ A⁻¹ g(Φ_{τ/A}⁻¹(r y))` is `C^∞`
  in `(τ, y)` (`I/Infra/BSParam/ContDiff.lean`);
* `hIn_ext`, `hOut_ext`, `hField_ext`: `h^in_k`, `h^out_k`, `h_k` agree at every ring-`k` time
  `τ ≥ 0` with fields that are `C^∞` in `(τ, y)` on `ℝ × (ℂ ∖ {0})` (`eq:omega-ge`);
* `omegaGe_moment_continuous`: `t ↦ Q_3[ω_{≥k+1}(t)]` is continuous on `[0, ∞)`.

**Remark (deviation).** The manuscript proves the continuity of `h^in_k` (resp.
`h^out_k`) using the confinement `D_{k+1}(t) ⊂ B_{a r_k/8}` (resp. the rings `i < k` outside
`B_{6 r_k}`) to keep the kernel away from its singularity. Here the vorticity
`ω_{≥k+1}(t) = g ∘ Φ_t⁻¹` is itself `C_c^∞` jointly in `(t, x)`, so its Biot–Savart velocity is
`C^∞` on all of `ℝ × ℝ²`; the confinement hypotheses are not needed (they only make `h^in_k`,
`h^out_k` the manuscript's objects). This is a simplification, not a change of statement.
-/

noncomputable section

open scoped ContDiff Topology
open MeasureTheory Set Metric Filter

namespace NonUniqueEuler

namespace Datum

namespace FieldContinuityAux

open RingData Approx

/-- The maximal flow at its own initial time is the identity (also in the junk case). -/
theorem maxFlow_self_eq' {F : ℝ → ℂ → ℂ} {U : Set (ℝ × ℂ)} {s : ℝ} {y : ℂ} :
    Smooth.maxFlow F U s s y = y := by
  classical
  by_cases h : ∃ (J : Set ℝ) (γ : ℝ → ℂ), Smooth.IsMaxSol F U s y J γ
  · exact (Smooth.isMaxSol_maxFlow h).init
  · rw [Smooth.maxFlow, dite_eq_right h]

/-- `Φ_0⁻¹ = id`. -/
theorem flowInv_zero_apply (P : Approx) (x : ℂ) : P.flowInv 0 x = x := by
  simp only [flowInv, Smooth.flowOf]
  exact maxFlow_self_eq'

variable {P : Approx}

/-- `thm:smooth`(4) for `ω^{(n)}`: the flow and its inverse are jointly `C^∞`, and
`Φ_t(Φ_t⁻¹(x)) = x`. -/
theorem flow_facts (hP : P.Valid) (hN : NumericalHypothesis P.χ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => P.flow p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => P.flowInv p.1 p.2) ∧
    ∀ t x, P.flow t (P.flowInv t x) = x := by
  obtain ⟨hcd, hcs, -⟩ :=
    (adm P.χ hP.admissible hN hP.datumParams ⟨hP.kseed_pos, hP.kseed_le⟩).1 P.n hP.two_le_n
  obtain ⟨R₀, hR₀⟩ := hcs.isCompact.isBounded.subset_ball 0
  have hD : Smooth.IsSmoothDatum P.f R₀ := ⟨hcd, hR₀⟩
  obtain ⟨h1, h2⟩ := Smooth.flow_contDiff hD
  refine ⟨?_, ?_, fun t x => ?_⟩
  · simpa only [hP.flow_eq] using h1
  · simpa only [hP.flowInv_eq] using h2
  · rw [hP.flow_eq, hP.flowInv_eq]
    exact (Smooth.flow_diffeo hD t).2.1 x

/-- The terms `f^{(n)}_i`, `1 ≤ i ≤ n`, are `C_c^∞` (`lem:regions-basic`(3) at `t = 0`). -/
theorem term_smooth (hP : P.Valid) (hN : NumericalHypothesis P.χ) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 P.n) :
    ContDiff ℝ ∞ (P.term i) ∧ HasCompactSupport (P.term i) := by
  obtain ⟨h1, -, -, -, -, -, ⟨hcd, hcs, -⟩, -⟩ := regions_basic_three P hP hN hi (le_refl 0)
  have h : P.omegaRing i 0 = P.term i := by
    rw [h1]
    funext x
    rw [flowInv_zero_apply]
  rw [← h]
  exact ⟨hcd, hcs⟩

/-- Finite sums of terms are `C_c^∞`. -/
theorem sumTerms_smooth (hP : P.Valid) (hN : NumericalHypothesis P.χ) {s : Finset ℕ}
    (hs : s ⊆ Finset.Icc 1 P.n) :
    ContDiff ℝ ∞ (fun x => ∑ i ∈ s, P.term i x) ∧
      HasCompactSupport (fun x => ∑ i ∈ s, P.term i x) := by
  constructor
  · exact ContDiff.sum fun i hi => (term_smooth hP hN (hs hi)).1
  · have h := HasCompactSupport.finset_sum (s := s) (f := fun i => P.term i)
      fun i hi => (term_smooth hP hN (hs hi)).2
    simpa only [Finset.sum_fn] using h

/-- For `g` with compact support, `g ∘ Φ_t⁻¹` vanishes outside a ball uniform in `|t| ≤ T`. -/
theorem slab_flowInv (hP : P.Valid) (hN : NumericalHypothesis P.χ) {g : ℂ → ℝ}
    (hg : HasCompactSupport g) (T : ℝ) :
    ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → g (P.flowInv t x) = 0 := by
  obtain ⟨hF, -, hR⟩ := flow_facts hP hN
  have hK : IsCompact ((fun p : ℝ × ℂ => P.flow p.1 p.2) '' (Icc (-T) T ×ˢ tsupport g)) :=
    (isCompact_Icc.prod hg).image hF.continuous
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨ρ, fun t ht x hx => ?_⟩
  by_contra hne
  have hmem : x ∈ (fun p : ℝ × ℂ => P.flow p.1 p.2) '' (Icc (-T) T ×ˢ tsupport g) :=
    ⟨(t, P.flowInv t x), ⟨ht, subset_tsupport _ hne⟩, hR t x⟩
  have h1 := hρ hmem
  rw [mem_closedBall, dist_zero_right] at h1
  linarith

/-- The extension `(τ, y) ↦ A⁻¹ g(Φ_{τ/A}⁻¹(r y))` is `C^∞`. -/
theorem contDiff_extU (hP : P.Valid) (hN : NumericalHypothesis P.χ) {g : ℂ → ℝ}
    (hg : ContDiff ℝ ∞ g) (A r : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => A⁻¹ * g (P.flowInv (p.1 / A) ((r : ℂ) * p.2))) := by
  obtain ⟨-, hFI, -⟩ := flow_facts hP hN
  have hin : ContDiff ℝ ∞ (fun p : ℝ × ℂ => (p.1 / A, (r : ℂ) * p.2)) :=
    (contDiff_fst.div_const A).prodMk (contDiff_const.mul contDiff_snd)
  exact contDiff_const.mul (hg.comp (hFI.comp hin))

/-- The extension in ring units vanishes outside a ball uniform in `|τ| ≤ T`. -/
theorem slab_extU (hP : P.Valid) (hN : NumericalHypothesis P.χ) {g : ℂ → ℝ}
    (hg : HasCompactSupport g) {A r : ℝ} (hA : 0 < A) (hr : 0 < r) (T : ℝ) :
    ∃ ρ : ℝ, ∀ τ ∈ Icc (-T) T, ∀ y : ℂ, ρ < ‖y‖ →
      A⁻¹ * g (P.flowInv (τ / A) ((r : ℂ) * y)) = 0 := by
  obtain ⟨ρ, hρ⟩ := slab_flowInv hP hN hg (T / A)
  refine ⟨ρ / r, fun τ hτ y hy => ?_⟩
  have h1 : τ / A ∈ Icc (-(T / A)) (T / A) := by
    constructor
    · rw [← neg_div]
      exact div_le_div_of_nonneg_right hτ.1 hA.le
    · exact div_le_div_of_nonneg_right hτ.2 hA.le
  have h2 : ρ < ‖(r : ℂ) * y‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    rw [div_lt_iff₀ hr] at hy
    linarith
  rw [hρ _ h1 _ h2, mul_zero]

/-- The Biot–Savart velocity of the extension is `C^∞` in `(τ, y)`. -/
theorem contDiff_velocity_extU (hP : P.Valid) (hN : NumericalHypothesis P.χ) {g : ℂ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) {A r : ℝ} (hA : 0 < A) (hr : 0 < r) :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ =>
      velocity (fun y => A⁻¹ * g (P.flowInv (p.1 / A) ((r : ℂ) * y))) p.2) :=
  BS.contDiff_velocityField_of_slabSupport (n := ⊤)
    (G := fun τ y => A⁻¹ * g (P.flowInv (τ / A) ((r : ℂ) * y)))
    (contDiff_extU hP hN hg A r) (slab_extU hP hN hgs hA hr)

/-- `eq:omega-ge` for `ω_{≥k+1}` (`1 ≤ k ≤ n`, `t ≥ 0`), including `k = n` (`ω_{≥n+1} = 0`). -/
theorem omegaGe_succ_eq (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) {t : ℝ} (ht : 0 ≤ t) :
    P.omegaGe (k + 1) t = fun x => ∑ i ∈ Finset.Icc (k + 1) P.n, P.term i (P.flowInv t x) := by
  rcases lt_or_eq_of_le hkn with hlt | heq
  · exact (regions_basic_three P hP hN (Finset.mem_Icc.2 ⟨by omega, hlt⟩) ht).2.1
  · subst heq
    rw [omegaGe_succ_n]
    funext x
    simp

/-- `eq:omega-ge` for the outer vorticity (`1 ≤ k ≤ n`, `t ≥ 0`). -/
theorem omegaOut_eq (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) {t : ℝ} (ht : 0 ≤ t) :
    P.omegaOut k t = fun x => ∑ i ∈ Finset.Ico 1 k, P.term i (P.flowInv t x) :=
  (regions_basic_three P hP hN (Finset.mem_Icc.2 ⟨hk, hkn⟩) ht).2.2.2.1

theorem Icc_succ_subset {k n : ℕ} (hk : 1 ≤ k) : Finset.Icc (k + 1) n ⊆ Finset.Icc 1 n := by
  intro i hi
  simp only [Finset.mem_Icc] at hi ⊢
  omega

theorem Ico_subset {k n : ℕ} (hkn : k ≤ n) : Finset.Ico 1 k ⊆ Finset.Icc 1 n := by
  intro i hi
  simp only [Finset.mem_Icc, Finset.mem_Ico] at hi ⊢
  omega

/-- **Smooth extension of the inner field**: `h^in_k(τ)` agrees, for `τ ≥ 0`, with a field that
is `C^∞` in `(τ, y)` on `ℝ × (ℂ ∖ {0})`. -/
theorem hIn_ext (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) :
    ∃ H : ℝ → ℂ → ℂ, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => H p.1 p.2) {p | p.2 ≠ 0} ∧
      ∀ τ, 0 ≤ τ → P.hIn k τ = H τ := by
  obtain ⟨hgc, hgs⟩ := sumTerms_smooth hP hN (Icc_succ_subset (n := P.n) hk)
  have hV := contDiff_velocity_extU hP hN hgc hgs (hP.A_pos k) (hP.r_pos k)
  refine ⟨fun τ y => velocity (fun y' => (P.A k)⁻¹ *
      (fun x => ∑ i ∈ Finset.Icc (k + 1) P.n, P.term i x)
        (P.flowInv (τ / P.A k) ((P.r k : ℂ) * y'))) y -
      (P.G k : ℂ) * (Complex.I * y) / ((‖y‖ ^ 2 : ℝ) : ℂ),
    hV.contDiffOn.sub (contDiffOn_monopole (P.G k)), fun τ hτ => ?_⟩
  have ht : 0 ≤ τ / P.A k := div_nonneg hτ (hP.A_pos k).le
  funext y
  simp only [hIn, nuIn, unitsVort, omegaGe_succ_eq hP hN hk hkn ht]
  rfl

/-- **Smooth extension of the outer field**: `h^out_k(τ)` agrees, for `τ ≥ 0`, with a field
that is `C^∞` in `(τ, y)`. -/
theorem hOut_ext (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) :
    ∃ H : ℝ → ℂ → ℂ, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => H p.1 p.2) {p | p.2 ≠ 0} ∧
      ∀ τ, 0 ≤ τ → P.hOut k τ = H τ := by
  obtain ⟨hgc, hgs⟩ := sumTerms_smooth hP hN (Ico_subset hkn)
  have hV := contDiff_velocity_extU hP hN hgc hgs (hP.A_pos k) (hP.r_pos k)
  refine ⟨fun τ y => velocity (fun y' => (P.A k)⁻¹ *
      (fun x => ∑ i ∈ Finset.Ico 1 k, P.term i x)
        (P.flowInv (τ / P.A k) ((P.r k : ℂ) * y'))) y, hV.contDiffOn, fun τ hτ => ?_⟩
  have ht : 0 ≤ τ / P.A k := div_nonneg hτ (hP.A_pos k).le
  funext y
  simp only [hOut, nuOut, unitsVort, omegaOut_eq hP hN hk hkn ht]
  rfl

/-- **Smooth extension of the external field** `h_k = h^in_k + h^out_k`. -/
theorem hField_ext (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) :
    ∃ H : ℝ → ℂ → ℂ, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => H p.1 p.2) {p | p.2 ≠ 0} ∧
      ∀ τ, 0 ≤ τ → P.hField k τ = H τ :=
  ext_add (hIn_ext hP hN hk hkn) (hOut_ext hP hN hk hkn)

/-- **Continuity of the moment** (`08_kick.tex:125-127`): for `1 ≤ k ≤ n`,
`t ↦ Q_3[ω_{≥k+1}(t)]` agrees on `[0, ∞)` with a continuous function. -/
theorem omegaGe_moment_continuous (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ P.n) :
    ∃ I : ℝ → ℂ, Continuous I ∧ ∀ t, 0 ≤ t →
      BS.Qm 3 (fun x => ((P.omegaGe (k + 1) t x : ℝ) : ℂ)) = I t := by
  obtain ⟨hgc, hgs⟩ := sumTerms_smooth hP hN (Icc_succ_subset (n := P.n) hk)
  obtain ⟨-, hFI, -⟩ := flow_facts hP hN
  set g : ℂ → ℝ := fun x => ∑ i ∈ Finset.Icc (k + 1) P.n, P.term i x with hg_def
  have hF : Continuous (Function.uncurry fun (t : ℝ) (x : ℂ) =>
      ((g (P.flowInv t x) : ℝ) : ℂ) * x ^ 3) :=
    (Complex.continuous_ofReal.comp (hgc.continuous.comp hFI.continuous)).mul
      (continuous_snd.pow 3)
  have hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ →
      ((g (P.flowInv t x) : ℝ) : ℂ) * x ^ 3 = 0 := by
    intro T
    obtain ⟨ρ, hρ⟩ := slab_flowInv hP hN hgs T
    exact ⟨ρ, fun t ht x hx => by rw [hρ t ht x hx, Complex.ofReal_zero, zero_mul]⟩
  refine ⟨fun t => ∫ x, ((g (P.flowInv t x) : ℝ) : ℂ) * x ^ 3,
    continuous_integral_of_slab hF hsupp, fun t ht => ?_⟩
  simp only [BS.Qm, omegaGe_succ_eq hP hN hk hkn ht, hg_def]

end FieldContinuityAux

end Datum

end NonUniqueEuler
