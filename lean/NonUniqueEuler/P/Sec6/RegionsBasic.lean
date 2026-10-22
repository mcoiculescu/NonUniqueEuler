import NonUniqueEuler.Defs.Sec6.All
import NonUniqueEuler.Defs.Sec7.Transfer
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.H.Sec6.RegionsBasic.Terms

/-!
# Proof: `lem:regions-basic` (elementary properties of the regions) and `eq:omega-ge`

Proof of `I/Sec6/RegionsBasic.lean` (`06_datum.tex:215-242`, proof `:244-292`); same
declarations, statements copied verbatim.

* (1) (`06_datum.tex:245-254`): `f^{(n)}_k = A_k G(·/r_k)` with a ring profile `G`
  (`RegionsBasicAux.term_eq_scale`); `S_k ⊂ 𝒩₋_k`, `S_k ⊂ {a r_k ≤ |x| ≤ r_k}` for `k < n`;
  disjointness from `r_k ≤ (a/16) r_i` (`i < k`), which gives `(5/4) r_k < a r_i`.
* (2) (`06_datum.tex:255-270`): `Φ_t ∘ O = O ∘ Φ_t` (`Smooth.vel_flow_rot_of_symm`), `Φ_t(0) = 0`
  because `O` fixes only `0`; `Φ_t` is a bijection, so the images inherit (1);
  `ω(t) = f^{(n)} ∘ Φ_t⁻¹` (`Smooth.sol_eq_comp_flowInv`).
* (3) (`06_datum.tex:271-284`): `1_{S_k(t)} = 1_{S_k} ∘ Φ_t⁻¹`, the disjoint unions, area
  preservation of `Φ_t⁻¹`.
* (4) (`06_datum.tex:286-292`): `w_k(t) = A_k⁻¹(ω(t)1_{S_k(t)})(r_k ·) - Φ`; Cauchy–Schwarz on `N`.

Helper lemmas: `H/Sec6/RegionsBasic/{Basic,Terms}.lean`, namespace
`NonUniqueEuler.Datum.Approx.RegionsBasicAux`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Datum

namespace Approx

open RingData

namespace RegionsBasicAux

variable {P : Approx}

theorem zero_notMem_S (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) : (0 : ℂ) ∉ P.S k := by
  intro h
  have h1 : 7 / 8 * a ≤ ‖((P.r k : ℝ) : ℂ)⁻¹ * 0‖ := (S_subset_Nmk hP hN hk h).1
  rw [mul_zero, norm_zero] at h1
  linarith [a_pos']

theorem S_disjoint_of_lt (hP : P.Valid) (hN : NumericalHypothesis P.χ) {i k : ℕ}
    (hi : i ∈ Finset.Icc 1 P.n) (hk : k ∈ Finset.Icc 1 P.n) (hik : i < k) :
    Disjoint (P.S i) (P.S k) := by
  rw [Set.disjoint_left]
  intro x hxi hxk
  obtain ⟨hi1, -⟩ := Finset.mem_Icc.1 hi
  obtain ⟨-, hkn⟩ := Finset.mem_Icc.1 hk
  have h1 := (S_subset_ann hP hN hi1 (by omega) hxi).1
  have h2 := norm_le_of_mem_S hP hN hk hxk
  have h3 := r_le_of_lt hP hi1 hik
  have h4 : 0 < a * P.r i := mul_pos a_pos' (hP.r_pos i)
  nlinarith

theorem S_disjoint (hP : P.Valid) (hN : NumericalHypothesis P.χ) :
    ∀ k ∈ Finset.Icc 1 P.n, ∀ l ∈ Finset.Icc 1 P.n, k ≠ l → Disjoint (P.S k) (P.S l) := by
  intro k hk l hl hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact S_disjoint_of_lt hP hN hk hl h
  · exact (S_disjoint_of_lt hP hN hl hk h).symm

theorem indicator_S_f (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) : (P.S k).indicator P.f = P.term k := by
  funext x
  by_cases hx : x ∈ P.S k
  · rw [indicator_of_mem hx, f_apply]
    refine Finset.sum_eq_single k (fun j hj hjk => ?_) (fun h => absurd hk h)
    apply image_eq_zero_of_notMem_tsupport (f := P.term j)
    intro hxj
    exact Set.disjoint_left.1 (S_disjoint hP hN j hj k hk hjk) hxj hx
  · rw [indicator_of_notMem hx]
    exact (image_eq_zero_of_notMem_tsupport (f := P.term k) hx).symm

/-- `supp f^{(n)} ⊂ S_1 ∪ … ∪ S_n`. -/
theorem tsupport_f_subset (P : Approx) :
    tsupport P.f ⊆ ⋃ k ∈ Finset.Icc 1 P.n, P.S k := by
  refine closure_minimal (fun x hx => ?_) (isClosed_biUnion_finset fun k _ => isClosed_tsupport _)
  rw [Function.mem_support, f_apply] at hx
  obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  exact mem_biUnion hk (subset_tsupport _ hk0)

end RegionsBasicAux

open RegionsBasicAux

/-- **`lem:regions-basic`(1)** (`06_datum.tex:219-222`): the sets `S_1, …, S_n` are compact, avoid
`0`, are invariant under `O_{2π/3}` and pairwise disjoint; `f^{(n)}1_{S_k} = f^{(n)}_k`;
`S_k ⊂ {a r_k ≤ |x| ≤ r_k}` for `k < n` and `S_n ⊂ 𝒩₋_n`. -/
theorem regions_basic_one (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) :
    (∀ k ∈ Finset.Icc 1 P.n, IsCompact (P.S k) ∧ (0 : ℂ) ∉ P.S k ∧
      rot (2 * Real.pi / 3) '' P.S k = P.S k ∧ (P.S k).indicator P.f = P.term k) ∧
    (∀ k ∈ Finset.Icc 1 P.n, ∀ l ∈ Finset.Icc 1 P.n, k ≠ l → Disjoint (P.S k) (P.S l)) ∧
    (∀ k : ℕ, 1 ≤ k → k < P.n → P.S k ⊆ {x : ℂ | a * P.r k ≤ ‖x‖ ∧ ‖x‖ ≤ P.r k}) ∧
    P.S P.n ⊆ P.Nmk P.n := by
  refine ⟨fun k hk => ⟨(term_isGood hP hN hk).2.1, zero_notMem_S hP hN hk,
    image_rot_tsupport (term_isGood hP hN hk).2.2.2, indicator_S_f hP hN hk⟩,
    S_disjoint hP hN, fun k hk hkn => S_subset_ann hP hN hk hkn,
    S_subset_Nmk hP hN (Finset.mem_Icc.2 ⟨hP.one_le_n, le_rfl⟩)⟩

/-- **`lem:regions-basic`(2)** (`06_datum.tex:223-226`): for `t ≥ 0`, `Φ_t ∘ O = O ∘ Φ_t` and
`Φ_t(0) = 0`; the sets `S_k(t)` are compact, avoid `0`, are `O`-invariant and pairwise disjoint;
`supp ω(t) ⊂ S_1(t) ∪ … ∪ S_n(t)`, hence `ω(t) = Σ_{k=1}^n ω(t)1_{S_k(t)}`. -/
theorem regions_basic_two (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {t : ℝ}
    (ht : 0 ≤ t) :
    (∀ y : ℂ, P.flow t (rot (2 * Real.pi / 3) y) = rot (2 * Real.pi / 3) (P.flow t y)) ∧
    P.flow t 0 = 0 ∧
    (∀ k ∈ Finset.Icc 1 P.n, IsCompact (P.St k t) ∧ (0 : ℂ) ∉ P.St k t ∧
      rot (2 * Real.pi / 3) '' P.St k t = P.St k t) ∧
    (∀ k ∈ Finset.Icc 1 P.n, ∀ l ∈ Finset.Icc 1 P.n, k ≠ l → Disjoint (P.St k t) (P.St l t)) ∧
    tsupport (P.om t) ⊆ (⋃ k ∈ Finset.Icc 1 P.n, P.St k t) ∧
    P.om t = fun x => ∑ k ∈ Finset.Icc 1 P.n, P.omegaRing k t x := by
  obtain ⟨hl, hr, hc, -, -, hom, hrot, -⟩ := flow_props hP hN t
  obtain ⟨h1, hdisj, -, -⟩ := regions_basic_one P hP hN
  have hinj : Function.Injective (P.flow t) := fun y y' hyy' => by
    rw [← hl y, ← hl y', hyy']
  have h0 : P.flow t 0 = 0 := by
    apply eq_zero_of_rot_eq
    rw [← hrot 0, RegionsBasicAux.rot_zero]
  have hdisjSt : ∀ k ∈ Finset.Icc 1 P.n, ∀ l ∈ Finset.Icc 1 P.n, k ≠ l →
      Disjoint (P.St k t) (P.St l t) := fun k hk l hl' hkl =>
    (Set.disjoint_image_iff hinj).2 (hdisj k hk l hl' hkl)
  have hsupp : tsupport (P.om t) ⊆ ⋃ k ∈ Finset.Icc 1 P.n, P.St k t := by
    obtain ⟨e, he, -⟩ := exists_flowInv_homeomorph hP hN t
    have hom' : P.om t = P.f ∘ ⇑e := by
      funext x
      rw [hom x, Function.comp, he]
    intro x hx
    rw [hom', tsupport_comp_eq_preimage, mem_preimage, he] at hx
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 (tsupport_f_subset P hx)
    exact mem_biUnion hk ⟨P.flowInv t x, hxk, hr x⟩
  refine ⟨hrot, h0, fun k hk => ⟨(h1 k hk).1.image hc.continuous, ?_,
    image_rot_image hrot (h1 k hk).2.2.1⟩, hdisjSt, hsupp, ?_⟩
  · rintro ⟨y, hy, hy0⟩
    have : y = 0 := hinj (hy0.trans h0.symm)
    exact (h1 k hk).2.1 (this ▸ hy)
  · have hpd : ((Finset.Icc 1 P.n : Finset ℕ) : Set ℕ).PairwiseDisjoint (fun k => P.St k t) :=
      fun i hi j hj hij => hdisjSt i (Finset.mem_coe.1 hi) j (Finset.mem_coe.1 hj) hij
    funext x
    show P.om t x = ∑ k ∈ Finset.Icc 1 P.n, (P.St k t).indicator (P.om t) x
    rw [← Finset.indicator_biUnion_apply _ _ hpd,
      Set.indicator_eq_self.2 ((subset_tsupport _).trans hsupp)]

/-- **`lem:regions-basic`(3)** and **`eq:omega-ge`** (`06_datum.tex:227-236`): for `1 ≤ k ≤ n` and
`t ≥ 0`, `ω(t)1_{S_k(t)} = f^{(n)}_k ∘ Φ_t⁻¹`, `ω_{≥k}(t) = (Σ_{i=k}^n f^{(n)}_i) ∘ Φ_t⁻¹ =
Σ_{i=k}^n ω(t)1_{S_i(t)}`, likewise `ω(t)1_{S_1(t)∪…∪S_{k-1}(t)} = (Σ_{i<k} f^{(n)}_i) ∘ Φ_t⁻¹ =
Σ_{i<k} ω(t)1_{S_i(t)}`, `∫ ω(t)1_{S_k(t)} = A_k r_k²‖Φ‖_{L¹}`, and `ω(t)1_{S_k(t)}` and
`ω_{≥k}(t)` are `C_c^∞`, nonnegative and (pointwise) `3`-fold symmetric. -/
theorem regions_basic_three (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) {t : ℝ} (ht : 0 ≤ t) :
    P.omegaRing k t = (fun x => P.term k (P.flowInv t x)) ∧
    P.omegaGe k t = (fun x => ∑ i ∈ Finset.Icc k P.n, P.term i (P.flowInv t x)) ∧
    P.omegaGe k t = (fun x => ∑ i ∈ Finset.Icc k P.n, P.omegaRing i t x) ∧
    P.omegaOut k t = (fun x => ∑ i ∈ Finset.Ico 1 k, P.term i (P.flowInv t x)) ∧
    P.omegaOut k t = (fun x => ∑ i ∈ Finset.Ico 1 k, P.omegaRing i t x) ∧
    ∫ x, P.omegaRing k t x = P.A k * P.r k ^ 2 * PhiL1 P.χ ∧
    (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.omegaRing k t) ∧ HasCompactSupport (P.omegaRing k t) ∧
      (∀ x, 0 ≤ P.omegaRing k t x) ∧
      ∀ x, P.omegaRing k t (rot (2 * Real.pi / 3) x) = P.omegaRing k t x) ∧
    (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.omegaGe k t) ∧ HasCompactSupport (P.omegaGe k t) ∧
      (∀ x, 0 ≤ P.omegaGe k t x) ∧
      ∀ x, P.omegaGe k t (rot (2 * Real.pi / 3) x) = P.omegaGe k t x) := by
  obtain ⟨hl, hr, -, hci, hmp, hom, -, hroti⟩ := flow_props hP hN t
  obtain ⟨h1, -, -, -⟩ := regions_basic_one P hP hN
  obtain ⟨-, -, -, hdisjSt, -, -⟩ := regions_basic_two P hP hN ht
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hk
  have hmem : ∀ i x, x ∈ P.St i t ↔ P.flowInv t x ∈ P.S i := fun i x => by
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [hl]
    · intro h
      exact ⟨_, h, hr x⟩
  have hring : ∀ i ∈ Finset.Icc 1 P.n,
      P.omegaRing i t = fun x => P.term i (P.flowInv t x) := by
    intro i hi
    funext x
    show (P.St i t).indicator (P.om t) x = P.term i (P.flowInv t x)
    rw [← (h1 i hi).2.2.2]
    by_cases hx : x ∈ P.St i t
    · rw [indicator_of_mem hx, hom, indicator_of_mem ((hmem i x).1 hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hmem i x).2 h))]
  -- the sums over `Icc k n` and `Ico 1 k`
  have hsubGe : ∀ i ∈ Finset.Icc k P.n, i ∈ Finset.Icc 1 P.n := fun i hi => by
    rw [Finset.mem_Icc] at hi ⊢
    omega
  have hsubOut : ∀ i ∈ Finset.Ico 1 k, i ∈ Finset.Icc 1 P.n := fun i hi => by
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_Icc]
    omega
  have hge2 : P.omegaGe k t = fun x => ∑ i ∈ Finset.Icc k P.n, P.omegaRing i t x := by
    have hpd : ((Finset.Icc k P.n : Finset ℕ) : Set ℕ).PairwiseDisjoint (fun i => P.St i t) :=
      fun i hi j hj hij => hdisjSt i (hsubGe i (Finset.mem_coe.1 hi)) j
        (hsubGe j (Finset.mem_coe.1 hj)) hij
    funext x
    show (⋃ i ∈ Finset.Icc k P.n, P.St i t).indicator (P.om t) x = _
    rw [Finset.indicator_biUnion_apply _ _ hpd]
    rfl
  have hge1 : P.omegaGe k t = fun x => ∑ i ∈ Finset.Icc k P.n, P.term i (P.flowInv t x) := by
    rw [hge2]
    funext x
    exact Finset.sum_congr rfl fun i hi => congrFun (hring i (hsubGe i hi)) x
  have hout2 : P.omegaOut k t = fun x => ∑ i ∈ Finset.Ico 1 k, P.omegaRing i t x := by
    have hpd : ((Finset.Ico 1 k : Finset ℕ) : Set ℕ).PairwiseDisjoint (fun i => P.St i t) :=
      fun i hi j hj hij => hdisjSt i (hsubOut i (Finset.mem_coe.1 hi)) j
        (hsubOut j (Finset.mem_coe.1 hj)) hij
    funext x
    show (⋃ i ∈ Finset.Ico 1 k, P.St i t).indicator (P.om t) x = _
    rw [Finset.indicator_biUnion_apply _ _ hpd]
    rfl
  have hout1 : P.omegaOut k t = fun x => ∑ i ∈ Finset.Ico 1 k, P.term i (P.flowInv t x) := by
    rw [hout2]
    funext x
    exact Finset.sum_congr rfl fun i hi => congrFun (hring i (hsubOut i hi)) x
  -- the integral (area preservation)
  have hcv : ∀ g : ℂ → ℝ, Continuous g → ∫ x, g (P.flowInv t x) = ∫ x, g x := fun g hg => by
    rw [← integral_map hci.continuous.aemeasurable
      (by rw [hmp.map_eq]; exact hg.aestronglyMeasurable), hmp.map_eq]
  have hint : ∫ x, P.omegaRing k t x = P.A k * P.r k ^ 2 * PhiL1 P.χ := by
    rw [hring k hk, hcv _ (term_isGood hP hN hk).1.continuous]
    exact integral_term hP hN hk
  -- smoothness, support, positivity, symmetry
  obtain ⟨e, he, -⟩ := exists_flowInv_homeomorph hP hN t
  have hce : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ⇑e := by rw [he]; exact hci
  have hre : ∀ x, e (rot (2 * Real.pi / 3) x) = rot (2 * Real.pi / 3) (e x) := by
    rw [he]; exact hroti
  have hgRing : IsGood (2 * Real.pi / 3) (fun x => P.term k (P.flowInv t x)) := by
    have h := isGood_comp (term_isGood hP hN hk) e hce hre
    rw [he] at h
    exact h
  have hgGe : IsGood (2 * Real.pi / 3)
      (fun x => ∑ i ∈ Finset.Icc k P.n, P.term i (P.flowInv t x)) := by
    have h := isGood_comp (isGood_sum (Finset.Icc k P.n) fun i hi => term_isGood hP hN (hsubGe i hi))
      e hce hre
    rw [he] at h
    exact h
  refine ⟨hring k hk, hge1, hge2, hout1, hout2, hint, ?_, ?_⟩
  · rw [hring k hk]
    exact hgRing
  · rw [hge1]
    exact hgGe

/-- **`lem:regions-basic`(4)** (`06_datum.tex:237-240`): if `S_k(t) ⊂ N_k` (`t ≥ 0`), then
`w_k(t) ∈ C_c^∞` is (pointwise) `3`-fold symmetric and supported in `N`, `w_k(t) ∈ X^s` for every
`s`, `∫ w_k(t) = 0`, `‖w_k(t)‖_{L¹} ≤ 2‖Φ‖_{L¹}` and `‖w_k(t)‖_{L¹} ≤ |N|^{1/2}‖w_k(t)‖_{L²}`. -/
theorem regions_basic_four (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) {t : ℝ} (ht : 0 ≤ t) (hS : P.PertDefined k t) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.wR k t) ∧ HasCompactSupport (P.wR k t) ∧
    tsupport (P.wR k t) ⊆ annN ∧
    (∀ y, P.wR k t (rot (2 * Real.pi / 3) y) = P.wR k t y) ∧
    (∀ s : ℕ, Lin.MemXFn s (P.w k t)) ∧
    (∫ y, P.wR k t y) = 0 ∧
    eLpNorm (P.wR k t) 1 volume ≤ ENNReal.ofReal (2 * PhiL1 P.χ) ∧
    eLpNorm (P.wR k t) 1 volume ≤ ENNReal.ofReal Rings.CL1 * eLpNorm (P.wR k t) 2 volume := by
  obtain ⟨-, -, -, -, -, hint, hg, -⟩ := regions_basic_three P hP hN hk ht
  obtain ⟨hgc, hgs, hg0, hgsym⟩ := hg
  obtain ⟨-, -, hSt, -, -, -⟩ := regions_basic_two P hP hN ht
  have hR := ringFacts_of_admissible hP.admissible
  have hA := hP.A_pos k
  have hr := hP.r_pos k
  set g := P.omegaRing k t with hgdef
  set u : ℂ → ℝ := fun y => (P.A k)⁻¹ * g ((P.r k : ℂ) * y) with hudef
  have hw : P.wR k t = fun y => u y - ringPhi P.χ y := rfl
  have huc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u :=
    contDiff_const.mul (hgc.comp (contDiff_const.mul contDiff_id))
  have hus : HasCompactSupport u := hasCompactSupport_scale_mul hgs _ hr.ne'
  have hu0 : ∀ y, 0 ≤ u y := fun y => mul_nonneg (inv_nonneg.2 hA.le) (hg0 _)
  have hΦc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ringPhi P.χ) := hR.1
  have hΦs : HasCompactSupport (ringPhi P.χ) := hR.2.1
  have hΦ0 : ∀ y, 0 ≤ ringPhi P.χ y := fun y => (hR.2.2.2.1 y).1
  have hwc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.wR k t) := by
    rw [hw]; exact huc.sub hΦc
  have hws : HasCompactSupport (P.wR k t) := by
    rw [hw]; exact hus.sub hΦs
  -- support in `N`
  have hgsupp : tsupport g ⊆ P.St k t :=
    closure_minimal (fun x hx => by
      by_contra h
      exact hx (indicator_of_notMem h _)) ((hSt k hk).1.isClosed)
  have husupp : tsupport u ⊆ annN := by
    intro y hy
    have h1 : (P.r k : ℂ) * y ∈ P.St k t := hgsupp (tsupport_scale_mul_subset _ g _ hy)
    have h2 := hS h1
    rwa [Nk, mul_mem_scaleSet hr.ne'] at h2
  have hΦsupp : tsupport (ringPhi P.χ) ⊆ annN := fun y hy => by
    obtain ⟨h1, h2⟩ := hR.2.2.2.2.2.1 hy
    have ha := hR.2.2.2.2.2.2.1
    exact show a / 2 ≤ ‖y‖ ∧ ‖y‖ ≤ 2 from ⟨by linarith, by linarith⟩
  have hwsupp : tsupport (P.wR k t) ⊆ annN := by
    rw [hw]
    exact (tsupport_sub u (ringPhi P.χ)).trans (union_subset husupp hΦsupp)
  have hwz : ∀ y, y ∉ annN → P.wR k t y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (hwsupp h))
  -- symmetry
  have hwsym : ∀ y, P.wR k t (rot (2 * Real.pi / 3) y) = P.wR k t y := by
    intro y
    rw [hw]
    show (P.A k)⁻¹ * g ((P.r k : ℂ) * rot (2 * Real.pi / 3) y) -
        ringPhi P.χ (rot (2 * Real.pi / 3) y) =
      (P.A k)⁻¹ * g ((P.r k : ℂ) * y) - ringPhi P.χ y
    rw [← rot_ofReal_mul, hgsym, hR.2.2.1]
  -- `X^s`
  have hXs : ∀ s : ℕ, Lin.MemXFn s (P.w k t) := by
    intro s
    have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.w k t) :=
      Complex.ofRealCLM.contDiff.comp hwc
    have hcs : HasCompactSupport (P.w k t) := hws.comp_left Complex.ofReal_zero
    refine ⟨(Sob.memH_of_contDiff_hasCompactSupport hcd hcs s).1,
      Filter.Eventually.of_forall fun y hy => ?_, Filter.Eventually.of_forall fun y => ?_⟩
    · show ((P.wR k t y : ℝ) : ℂ) = 0
      rw [hwz y hy, Complex.ofReal_zero]
    · have e3 : (2 * Real.pi / ((3 : ℕ) : ℝ)) = 2 * Real.pi / 3 := by norm_num
      show ((P.wR k t (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) y) : ℝ) : ℂ) = ((P.wR k t y : ℝ) : ℂ)
      rw [e3, hwsym]
  -- integrals
  have huint : Integrable u := huc.continuous.integrable_of_hasCompactSupport hus
  have hΦint : Integrable (ringPhi P.χ) := hΦc.continuous.integrable_of_hasCompactSupport hΦs
  have hIu : ∫ y, u y = PhiL1 P.χ := by
    rw [hudef, integral_scale_mul _ _ hr, hint]
    field_simp
  have hIΦ : ∫ y, ringPhi P.χ y = PhiL1 P.χ := integral_ringPhi hR
  have hI : (∫ y, P.wR k t y) = 0 := by
    rw [hw, integral_sub huint hΦint, hIu, hIΦ, sub_self]
  -- `L¹` bounds
  have hL1 : eLpNorm (P.wR k t) 1 volume ≤ ENNReal.ofReal (2 * PhiL1 P.χ) := by
    have h := eLpNorm_sub_le (p := 1) huint.aestronglyMeasurable hΦint.aestronglyMeasurable le_rfl
    rw [eLpNorm_one_of_nonneg huint hu0, eLpNorm_one_of_nonneg hΦint hΦ0, hIu, hIΦ,
      ← ENNReal.ofReal_add (PhiL1_nonneg _) (PhiL1_nonneg _), ← two_mul] at h
    rw [hw]
    exact h
  have hCS : eLpNorm (P.wR k t) 1 volume ≤
      ENNReal.ofReal Rings.CL1 * eLpNorm (P.wR k t) 2 volume :=
    eLpNorm_one_le_CL1 hwc.continuous.aestronglyMeasurable hwz
  exact ⟨hwc, hws, hwsupp, hwsym, hXs, hI, hL1, hCS⟩

end Approx

end Datum

end NonUniqueEuler
