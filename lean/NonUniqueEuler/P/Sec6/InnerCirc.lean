import NonUniqueEuler.Defs.Sec6.All
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec6.Adm
import NonUniqueEuler.I.SmoothB.SmoothFlow

/-!
# Proof: `lem:inner-circ` (the inner circulations) and `eq:conserved`

Proof of `I/Sec6/InnerCirc.lean` (`06_datum.tex:332-338`, proof `:339-359`); same declarations,
statements copied verbatim.

* `eq:conserved` (`06_datum.tex:343-346`): by `eq:omega-ge` (`regions_basic_three`),
  `ω_{≥k}(t) = g ∘ Φ_t⁻¹` with `g = Σ_{i=k}^n f^{(n)}_i`; `Φ_t⁻¹` preserves area
  (`Smooth.flow_measurePreserving`, applied to the datum `f^{(n)}`, which is `C_c^∞` by `lem:adm`),
  so `∫ F(ω_{≥k}(t)) = ∫ F(g)`. Since `f^{(n)}_i = f^{(n)} 1_{S_i}` and the `S_i` are pairwise
  disjoint (`regions_basic_one`), `F(g) = Σ_i F(f^{(n)}_i)` pointwise (`F(0) = 0`), and each
  `F(f^{(n)}_i) = 1_{S_i} F(f^{(n)})` is integrable.
* `lem:inner-circ`: `F(s) = s` gives the time independence; `∫ f^{(n)}_i = A_ir_i²‖Φ‖_{L¹}`
  (`regions_basic_three` at `t = 0`, with the same change of variables) gives
  `2πG_kA_kr_k² = ‖Φ‖_{L¹} Σ_{i>k} A_ir_i²`; `A_{i+1}r_{i+1}² = μs_i² A_ir_i²` with
  `μs_i² ≤ 2(a/16)² < 1/2` gives `Σ_{i>k} A_ir_i² ≤ 2μs_k² A_kr_k²`, hence `G_k ≤ C_G μ s_k²`.

Helper lemmas are in the namespace `NonUniqueEuler.Datum.Approx.InnerCircAux`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Datum

namespace Approx

open RingData

namespace InnerCircAux

/-- `f^{(n)}` is `C^∞` with compact support (`lem:adm`). -/
theorem f_contDiff_hasCompactSupport (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P.f ∧ HasCompactSupport P.f := by
  obtain ⟨h1, -, -⟩ := adm P.χ hP.admissible hN hP.datumParams ⟨hP.kseed_pos, hP.kseed_le⟩
  obtain ⟨hc, hs, -⟩ := h1 P.n hP.two_le_n
  exact ⟨hc, hs⟩

/-- `Φ_t⁻¹` preserves area and is continuous (`thm:smooth`(4) for the datum `f^{(n)}`). -/
theorem flowInv_measurePreserving (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    (t : ℝ) : MeasurePreserving (P.flowInv t) volume volume ∧ Continuous (P.flowInv t) := by
  obtain ⟨hc, hs⟩ := f_contDiff_hasCompactSupport P hP hN
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_ball (0 : ℂ)).1 hs.isCompact.isBounded
  have hD : Smooth.IsSmoothDatum P.f R := ⟨hc, hR⟩
  rw [hP.flowInv_eq t]
  exact ⟨(Smooth.flow_measurePreserving hD t).2, (Smooth.flow_diffeo hD t).2.2.2.1.continuous⟩

/-- Change of variables `x ↦ Φ_t⁻¹(x)` in an integral. -/
theorem integral_comp_flowInv (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    (t : ℝ) {g : ℂ → ℝ} (hg : AEStronglyMeasurable g volume) :
    ∫ x, g (P.flowInv t x) = ∫ x, g x := by
  obtain ⟨hmp, hcont⟩ := flowInv_measurePreserving P hP hN t
  rw [← integral_map hcont.measurable.aemeasurable (by rwa [hmp.map_eq]), hmp.map_eq]

/-- `F(f^{(n)}_i) = 1_{S_i} F(f^{(n)})` for `F(0) = 0`, `1 ≤ i ≤ n`. -/
theorem comp_term_eq (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {F : ℝ → ℝ}
    (hF0 : F 0 = 0) {i : ℕ} (hi : i ∈ Finset.Icc 1 P.n) (x : ℂ) :
    F (P.term i x) = (P.S i).indicator (F ∘ P.f) x := by
  obtain ⟨h1, -, -, -⟩ := regions_basic_one P hP hN
  rw [← (h1 i hi).2.2.2]
  exact (congrFun (Set.indicator_comp_of_zero hF0) x).symm

/-- `F(f^{(n)})` is integrable for continuous `F` with `F(0) = 0`. -/
theorem integrable_comp_f (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {F : ℝ → ℝ}
    (hF : Continuous F) (hF0 : F 0 = 0) : Integrable (F ∘ P.f) volume := by
  obtain ⟨hc, hs⟩ := f_contDiff_hasCompactSupport P hP hN
  exact (hF.comp hc.continuous).integrable_of_hasCompactSupport (hs.comp_left hF0)

/-- `∫ f^{(n)}_i = A_i r_i² ‖Φ‖_{L¹}` for `1 ≤ i ≤ n` (`lem:regions-basic`(3) at `t = 0`). -/
theorem integral_term (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 P.n) :
    ∫ x, P.term i x = P.A i * P.r i ^ 2 * PhiL1 P.χ := by
  obtain ⟨h1, -, -, -, -, h6, -⟩ := regions_basic_three P hP hN hi (le_refl (0 : ℝ))
  have hfi : Integrable ((P.S i).indicator (id ∘ P.f)) volume :=
    (integrable_comp_f P hP hN continuous_id rfl).indicator
      ((regions_basic_one P hP hN).1 i hi).1.isClosed.measurableSet
  have hterm : P.term i = (P.S i).indicator (id ∘ P.f) := by
    funext x
    exact comp_term_eq P hP hN (F := id) rfl hi x
  calc ∫ x, P.term i x = ∫ x, P.term i (P.flowInv 0 x) := by
        refine (integral_comp_flowInv P hP hN 0 ?_).symm
        rw [hterm]
        exact hfi.aestronglyMeasurable
    _ = ∫ x, P.omegaRing i 0 x := by rw [h1]
    _ = P.A i * P.r i ^ 2 * PhiL1 P.χ := h6

/-- `0 < a < 1`. -/
theorem a_lt_one' : a < 1 := by
  unfold a
  rw [Real.exp_lt_one_iff]
  norm_num [ξL, ξR]

/-- `s_i ≤ s̄`. -/
theorem s_le_sbar (P : Approx) (hP : P.Valid) (i : ℕ) : P.s i ≤ P.sbar := by
  rw [s_def, ratio]
  apply div_le_self hP.datumParams.sbar_pos.le
  apply one_le_pow₀
  linarith [hP.datumParams.one_lt_μ]

/-- `μ s_i² ≤ 1/2` (`μ ≤ 2`, `s_i ≤ s̄ ≤ a/16 < 1/16`). -/
theorem mu_s_sq_le (P : Approx) (hP : P.Valid) (i : ℕ) : P.μ * P.s i ^ 2 ≤ 1 / 2 := by
  have hμ2 := hP.datumParams.μ_le_two
  have hs0 := (hP.s_pos i).le
  have hs1 : P.s i ≤ 1 / 16 := by
    have := s_le_sbar P hP i
    have := hP.datumParams.sbar_le
    have := a_lt_one'
    linarith
  have hs2 : P.s i ^ 2 ≤ (1 / 16) ^ 2 := pow_le_pow_left₀ hs0 hs1 2
  calc P.μ * P.s i ^ 2 ≤ 2 * (1 / 16) ^ 2 := mul_le_mul hμ2 hs2 (sq_nonneg _) (by norm_num)
    _ ≤ 1 / 2 := by norm_num

/-- `A_{i+1} r_{i+1}² = μ s_i² A_i r_i²` for `i ≥ 1`. -/
theorem Ar2_succ (P : Approx) {i : ℕ} (hi : 1 ≤ i) :
    P.A (i + 1) * P.r (i + 1) ^ 2 = P.μ * P.s i ^ 2 * (P.A i * P.r i ^ 2) := by
  simp only [A_def, r_def, s_def]
  rw [amp_succ _ _ hi, radius_succ _ _ hi]
  ring

/-- The geometric bound with remainder: `Σ_{i=k+1}^m A_ir_i² + 2A_{m+1}r_{m+1}² ≤ 2A_{k+1}r_{k+1}²`. -/
theorem sum_Ar2_aux (P : Approx) (hP : P.Valid) {k : ℕ} (m : ℕ) (hm : k ≤ m) :
    ∑ i ∈ Finset.Ioc k m, P.A i * P.r i ^ 2 + 2 * (P.A (m + 1) * P.r (m + 1) ^ 2) ≤
      2 * (P.A (k + 1) * P.r (k + 1) ^ 2) := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hkm ih =>
    rw [Finset.sum_Ioc_succ_top hkm]
    have h1 := Ar2_succ P (i := m + 1) (by omega)
    have h2 := mu_s_sq_le P hP (m + 1)
    have h3 : 0 ≤ P.A (m + 1) * P.r (m + 1) ^ 2 :=
      (mul_pos (hP.A_pos _) (pow_pos (hP.r_pos _) 2)).le
    have h4 : 2 * (P.A (m + 1 + 1) * P.r (m + 1 + 1) ^ 2) ≤ P.A (m + 1) * P.r (m + 1) ^ 2 := by
      rw [h1]
      nlinarith [mul_le_mul_of_nonneg_right h2 h3]
    linarith

/-- `Σ_{i=k+1}^n A_ir_i² ≤ 2μ s_k² A_k r_k²` for `1 ≤ k ≤ n`. -/
theorem sum_Ar2_le (P : Approx) (hP : P.Valid) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ P.n) :
    ∑ i ∈ Finset.Ioc k P.n, P.A i * P.r i ^ 2 ≤ 2 * (P.μ * P.s k ^ 2 * (P.A k * P.r k ^ 2)) := by
  have h := sum_Ar2_aux P hP P.n hkn
  have h3 : 0 ≤ P.A (P.n + 1) * P.r (P.n + 1) ^ 2 :=
    (mul_pos (hP.A_pos _) (pow_pos (hP.r_pos _) 2)).le
  rw [← Ar2_succ P hk]
  linarith

end InnerCircAux

open InnerCircAux

/-- **`eq:conserved`** (`06_datum.tex:343-346`): for every continuous `F` with `F(0) = 0`, every
`1 ≤ k ≤ n + 1` and every `t ≥ 0`, `∫ F(ω_{≥k}(t)) dx = Σ_{i=k}^n ∫ F(f^{(n)}_i) dx`. -/
theorem conserved (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {F : ℝ → ℝ}
    (hF : Continuous F) (hF0 : F 0 = 0) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ P.n + 1) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫ x, F (P.omegaGe k t x) = ∑ i ∈ Finset.Icc k P.n, ∫ x, F (P.term i x) := by
  rcases Nat.lt_or_ge P.n k with hlt | hle
  · have hk' : k = P.n + 1 := by omega
    subst hk'
    rw [omegaGe_succ_n, Finset.Icc_eq_empty (by omega)]
    simp [hF0]
  · have hkI : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨hk, hle⟩
    obtain ⟨-, h2, -⟩ := regions_basic_three P hP hN hkI ht
    obtain ⟨h1, hdisj, -, -⟩ := regions_basic_one P hP hN
    have hsub : ∀ i ∈ Finset.Icc k P.n, i ∈ Finset.Icc 1 P.n := fun i hi => by
      rw [Finset.mem_Icc] at hi ⊢; omega
    have hpd : ((Finset.Icc k P.n : Finset ℕ) : Set ℕ).PairwiseDisjoint P.S := by
      intro i hi j hj hij
      exact hdisj i (hsub i (Finset.mem_coe.1 hi)) j (hsub j (Finset.mem_coe.1 hj)) hij
    set U := ⋃ i ∈ Finset.Icc k P.n, P.S i with hUdef
    have hUclosed : IsClosed U :=
      isClosed_biUnion_finset fun i hi => (h1 i (hsub i hi)).1.isClosed
    have hint := integrable_comp_f P hP hN hF hF0
    have hsum : ∀ x, ∑ i ∈ Finset.Icc k P.n, F (P.term i x) = U.indicator (F ∘ P.f) x := by
      intro x
      rw [hUdef, Finset.indicator_biUnion_apply _ _ hpd]
      exact Finset.sum_congr rfl fun i hi => comp_term_eq P hP hN hF0 (hsub i hi) x
    have hFU : ∀ x, F (∑ i ∈ Finset.Icc k P.n, P.term i x) = U.indicator (F ∘ P.f) x := by
      intro x
      have hx : ∑ i ∈ Finset.Icc k P.n, P.term i x = U.indicator P.f x := by
        rw [hUdef, Finset.indicator_biUnion_apply _ _ hpd]
        exact Finset.sum_congr rfl fun i hi => (congrFun (h1 i (hsub i hi)).2.2.2 x).symm
      rw [hx]
      exact (congrFun (Set.indicator_comp_of_zero hF0) x).symm
    have hmeas : AEStronglyMeasurable (fun x => F (∑ i ∈ Finset.Icc k P.n, P.term i x)) volume := by
      have : (fun x => F (∑ i ∈ Finset.Icc k P.n, P.term i x)) = U.indicator (F ∘ P.f) :=
        funext hFU
      rw [this]
      exact (hint.indicator hUclosed.measurableSet).aestronglyMeasurable
    simp only [h2]
    calc ∫ x, F (∑ i ∈ Finset.Icc k P.n, P.term i (P.flowInv t x))
        = ∫ x, F (∑ i ∈ Finset.Icc k P.n, P.term i x) :=
          integral_comp_flowInv P hP hN t
            (g := fun y => F (∑ i ∈ Finset.Icc k P.n, P.term i y)) hmeas
      _ = ∫ x, ∑ i ∈ Finset.Icc k P.n, F (P.term i x) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          show F (∑ i ∈ Finset.Icc k P.n, P.term i x) = ∑ i ∈ Finset.Icc k P.n, F (P.term i x)
          rw [hFU x, hsum x]
      _ = ∑ i ∈ Finset.Icc k P.n, ∫ x, F (P.term i x) := by
          refine integral_finsetSum _ fun i hi => ?_
          have : (fun x => F (P.term i x)) = (P.S i).indicator (F ∘ P.f) :=
            funext fun x => comp_term_eq P hP hN hF0 (hsub i hi) x
          rw [this]
          exact hint.indicator (h1 i (hsub i hi)).1.isClosed.measurableSet

/-- **`lem:inner-circ`** (`06_datum.tex:332-338`): `∫ ω_{≥k+1}(t)` is independent of `t ≥ 0`;
`2πG_kA_kr_k² = ‖Φ‖_{L¹} Σ_{i=k+1}^n A_ir_i²`; `0 ≤ G_k ≤ C_G μ s_k² ≤ C_G μ s̄²` for `1 ≤ k ≤ n`;
and if `C_G μ s̄² ≤ G₁`, then `G_k ∈ [0, G₁]` for `1 ≤ k ≤ n` (so `P.GSmall`). -/
theorem inner_circ (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) :
    (∀ k ∈ Finset.Icc 1 P.n, ∀ t : ℝ, 0 ≤ t →
      ∫ x, P.omegaGe (k + 1) t x = ∫ x, P.omegaGe (k + 1) 0 x) ∧
    (∀ k ∈ Finset.Icc 1 P.n, 2 * Real.pi * P.G k * P.A k * P.r k ^ 2 =
      PhiL1 P.χ * ∑ i ∈ Finset.Ioc k P.n, P.A i * P.r i ^ 2) ∧
    (∀ k ∈ Finset.Icc 1 P.n, 0 ≤ P.G k ∧ P.G k ≤ CG P.χ * P.μ * P.s k ^ 2 ∧
      CG P.χ * P.μ * P.s k ^ 2 ≤ CG P.χ * P.μ * P.sbar ^ 2) ∧
    (CG P.χ * P.μ * P.sbar ^ 2 ≤ Gbar →
      (∀ k ∈ Finset.Icc 1 P.n, P.G k ∈ Icc 0 Gbar) ∧ P.GSmall) := by
  -- `∫ ω_{≥k+1}(t) = Σ_{i=k+1}^n ∫ f^{(n)}_i` (`eq:conserved` with `F(s) = s`)
  have hcons : ∀ k ∈ Finset.Icc 1 P.n, ∀ t : ℝ, 0 ≤ t →
      ∫ x, P.omegaGe (k + 1) t x = ∑ i ∈ Finset.Icc (k + 1) P.n, ∫ x, P.term i x := by
    intro k hk t ht
    have hk' := Finset.mem_Icc.1 hk
    have h := conserved P hP hN (F := fun s => s) continuous_id' rfl (k := k + 1) (by omega)
      (by omega) ht
    exact h
  -- `∫ ω_{≥k+1}(0) = ‖Φ‖_{L¹} Σ_{i=k+1}^n A_i r_i²`
  have hint0 : ∀ k ∈ Finset.Icc 1 P.n,
      ∫ x, P.omegaGe (k + 1) 0 x = PhiL1 P.χ * ∑ i ∈ Finset.Ioc k P.n, P.A i * P.r i ^ 2 := by
    intro k hk
    have hk' := Finset.mem_Icc.1 hk
    rw [hcons k hk 0 le_rfl, ← Finset.Icc_add_one_left_eq_Ioc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_Icc.1 hi
    rw [integral_term P hP hN (Finset.mem_Icc.2 ⟨by omega, hi'.2⟩)]
    ring
  have hbpos : ∀ i, 0 < P.A i * P.r i ^ 2 := fun i => mul_pos (hP.A_pos i) (pow_pos (hP.r_pos i) 2)
  have hGeq : ∀ k ∈ Finset.Icc 1 P.n, P.G k =
      (2 * Real.pi * P.A k * P.r k ^ 2)⁻¹ *
        (PhiL1 P.χ * ∑ i ∈ Finset.Ioc k P.n, P.A i * P.r i ^ 2) := by
    intro k hk
    rw [G, hint0 k hk]
  have hμ0 : 0 < P.μ := by linarith [hP.datumParams.one_lt_μ]
  -- the bounds `0 ≤ G_k ≤ C_G μ s_k² ≤ C_G μ s̄²`
  have hbounds : ∀ k ∈ Finset.Icc 1 P.n, 0 ≤ P.G k ∧ P.G k ≤ CG P.χ * P.μ * P.s k ^ 2 ∧
      CG P.χ * P.μ * P.s k ^ 2 ≤ CG P.χ * P.μ * P.sbar ^ 2 := by
    intro k hk
    have hk' := Finset.mem_Icc.1 hk
    have hA := hP.A_pos k
    have hr := hP.r_pos k
    have hc : 0 < 2 * Real.pi * P.A k * P.r k ^ 2 := by positivity
    have hΦ := PhiL1_nonneg P.χ
    have hsum0 : 0 ≤ ∑ i ∈ Finset.Ioc k P.n, P.A i * P.r i ^ 2 :=
      Finset.sum_nonneg fun i _ => (hbpos i).le
    have hsum := sum_Ar2_le P hP hk'.1 hk'.2
    refine ⟨?_, ?_, ?_⟩
    · rw [hGeq k hk]
      exact mul_nonneg (inv_nonneg.2 hc.le) (mul_nonneg hΦ hsum0)
    · rw [hGeq k hk]
      calc (2 * Real.pi * P.A k * P.r k ^ 2)⁻¹ *
            (PhiL1 P.χ * ∑ i ∈ Finset.Ioc k P.n, P.A i * P.r i ^ 2)
          ≤ (2 * Real.pi * P.A k * P.r k ^ 2)⁻¹ *
            (PhiL1 P.χ * (2 * (P.μ * P.s k ^ 2 * (P.A k * P.r k ^ 2)))) := by
            gcongr
        _ = CG P.χ * P.μ * P.s k ^ 2 := by
            rw [CG]
            field_simp
    · have hs0 := (hP.s_pos k).le
      have hsle := s_le_sbar P hP k
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hsle 2)
        (mul_nonneg (CG_nonneg _) hμ0.le)
  refine ⟨?_, ?_, hbounds, ?_⟩
  · intro k hk t ht
    rw [hcons k hk t ht, hcons k hk 0 le_rfl]
  · intro k hk
    have hc : 2 * Real.pi * P.A k * P.r k ^ 2 ≠ 0 := by
      have := hP.A_pos k
      have := hP.r_pos k
      positivity
    have hA := (hP.A_pos k).ne'
    have hr := (hP.r_pos k).ne'
    rw [← hint0 k hk, G]
    field_simp
  · intro hsmall
    have hk : ∀ k ∈ Finset.Icc 1 P.n, P.G k ∈ Icc 0 Gbar := by
      intro k hk
      obtain ⟨h0, h1, h2⟩ := hbounds k hk
      exact ⟨h0, by linarith⟩
    exact ⟨hk, fun k hk' => (hk k hk').2⟩

end Approx

end Datum

end NonUniqueEuler
