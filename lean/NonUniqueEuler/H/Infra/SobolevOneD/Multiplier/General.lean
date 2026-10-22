import Mathlib.MeasureTheory.Function.L2Space
import NonUniqueEuler.H.Infra.SobolevOneD.Multiplier.Leibniz
import NonUniqueEuler.H.Infra.SobolevOneD.Multiplier.Bound
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helper for `P/Infra/SobolevOneD/Multiplier`: multipliers on `H^k(V)`, `V ⊆ ℝ` open

For `a ∈ C^k(V)` with `|a^{(i)}| ≤ M` on a closed set `K` (`i ≤ k`) and `g ∈ H^k(V)` vanishing
a.e. on `V` outside `K` (`mul_general`):
* `a g ∈ H^k(V)`;
* pointwise a.e. on `V`, `|∂^j(ag)|² ≤ M² 2^j ∑_{i ≤ j} C(j,i) |∂^{j-i} g|²` for `j ≤ k`.

Steps: the chosen weak derivatives of `g` form a chain (`family_facts`); they vanish a.e. on `V`
outside `K` (`weakDeriv_eq_zero_outside`: on the open set `V \ K` both `∂^m g` and `0` are weak
derivatives); the weak Leibniz formula (`leibniz_dir`) with uniqueness (`weakDerivOn_ae_eq`);
the pointwise Cauchy–Schwarz bound (`norm_leibniz_sq_le`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob.MultAux

/-- `L²` on an open set implies local integrability there. -/
theorem locallyIntegrableOn_of_memLp {V : Set ℝ} (hV : IsOpen V) {h : ℝ → ℂ}
    (hL2 : MemLp h 2 (volume.restrict V)) : LocallyIntegrableOn h V := by
  have h1 : LocallyIntegrable h (volume.restrict V) := hL2.locallyIntegrable (by norm_num)
  rw [locallyIntegrableOn_iff hV.isLocallyClosed]
  intro K hK hKc
  have h2 : IntegrableOn h K (volume.restrict V) := h1.integrableOn_isCompact hKc
  rwa [IntegrableOn, Measure.restrict_restrict_of_subset hK] at h2

/-- The chosen weak derivatives of an `H^k(V)` function. -/
theorem family_facts {k : ℕ} {V : Set ℝ} (hV : IsOpen V) {g : ℝ → ℂ} (hg : MemH1On k V g) :
    (∀ m ≤ k, LocallyIntegrableOn (weakDeriv1On V m g) V ∧
      HasWeakDerivOn V (derivList m) g (weakDeriv1On V m g) ∧
      MemLp (weakDeriv1On V m g) 2 (volume.restrict V)) ∧
    (∀ m < k, HasWeakDerivOn V [1] (weakDeriv1On V m g) (weakDeriv1On V (m + 1) g)) ∧
    (∀ᵐ x, x ∈ V → weakDeriv1On V 0 g x = g x) := by
  have hm : ∀ m ≤ k, LocallyIntegrableOn (weakDeriv1On V m g) V ∧
      HasWeakDerivOn V (derivList m) g (weakDeriv1On V m g) ∧
      MemLp (weakDeriv1On V m g) 2 (volume.restrict V) := by
    intro m hmk
    obtain ⟨h, hL2, hw⟩ := hg.deriv m hmk
    have hloc := locallyIntegrableOn_of_memLp hV hL2
    obtain ⟨h1, h2⟩ := weakDerivOn_spec hloc hw
    refine ⟨h1, h2, ?_⟩
    have hae := weakDerivOn_ae_eq hV hloc hw
    refine hL2.ae_eq ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' hV.measurableSet]
    filter_upwards [hae] with r hr hrV using (hr hrV).symm
  refine ⟨hm, fun m hmk => ?_, ?_⟩
  · have a := (hm m hmk.le).2.1
    have b := (hm (m + 1) hmk).2.1
    have e : derivList (m + 1) = derivList m ++ [1] := List.replicate_succ' ..
    rw [e] at b
    exact HasWeakDerivOn.of_append a b
  · exact weakDerivOn_ae_eq hV (locallyIntegrableOn_of_memLp hV hg.memLp)
      (hasWeakDerivOn_nil_self g)

/-- Weak derivatives of a function vanishing a.e. on `V` outside a closed set `K` vanish a.e.
on `V` outside `K`. -/
theorem weakDeriv_eq_zero_outside {V K : Set ℝ} (hV : IsOpen V) (hK : IsClosed K)
    {vs : List ℝ} {g G : ℝ → ℂ} (hgK : ∀ᵐ x, x ∈ V → x ∉ K → g x = 0)
    (hGl : LocallyIntegrableOn G V) (hw : HasWeakDerivOn V vs g G) :
    ∀ᵐ x, x ∈ V → x ∉ K → G x = 0 := by
  have hU : IsOpen (V ∩ Kᶜ) := hV.inter hK.isOpen_compl
  have h1 : HasWeakDerivOn (V ∩ Kᶜ) vs g G := hw.mono inter_subset_left
  have h2 : HasWeakDerivOn (V ∩ Kᶜ) vs g (fun _ => 0) := by
    intro φ hφ
    simp only [zero_mul, integral_zero, mul_zero]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hgK] with x hx
    by_cases hxU : x ∈ V ∩ Kᶜ
    · simp [hx hxU.1 hxU.2]
    · have hd := hφ.iterDirDeriv vs
      have : iterDirDeriv vs φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxU (hd.subset h))
      simp [this]
  have := HasWeakDerivOn.ae_eq hU (hGl.mono_set inter_subset_left) locallyIntegrableOn_zero h1 h2
  filter_upwards [this] with x hx hxV hxK using hx ⟨hxV, hxK⟩

/-- The Leibniz sum `∑_{i ≤ j} C(j,i) a^{(i)} ∂^{j-i} g`. -/
def lsum (j : ℕ) (a : ℝ → ℂ) (V : Set ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * (iteratedDeriv i a x * weakDeriv1On V (j - i) g x)

/-- **Multipliers on `H^k(V)`.** -/
theorem mul_general {k : ℕ} {V K : Set ℝ} (hV : IsOpen V) (hK : IsClosed K) {a g : ℝ → ℂ}
    (ha : ContDiffOn ℝ k a V) {M : ℝ} (hM : ∀ i ≤ k, ∀ x ∈ K, ‖iteratedDeriv i a x‖ ≤ M)
    (hg : MemH1On k V g) (hgK : ∀ᵐ x ∂(volume.restrict V), x ∉ K → g x = 0) :
    MemH1On k V (fun x => a x * g x) ∧
    ∀ j ≤ k, ∀ᵐ x ∂(volume.restrict V), ‖weakDeriv1On V j (fun x => a x * g x) x‖ ^ 2 ≤
      M ^ 2 * 2 ^ j *
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖weakDeriv1On V (j - i) g x‖ ^ 2 := by
  obtain ⟨hfam, hchain, h0⟩ := family_facts hV hg
  have hVm : MeasurableSet V := hV.measurableSet
  have hgK' : ∀ᵐ x, x ∈ V → x ∉ K → g x = 0 := (ae_restrict_iff' hVm).1 hgK
  have hvan : ∀ m ≤ k, ∀ᵐ x, x ∈ V → x ∉ K → weakDeriv1On V m g x = 0 := fun m hm =>
    weakDeriv_eq_zero_outside hV hK hgK' (hfam m hm).1 (hfam m hm).2.1
  have hvanAll : ∀ᵐ x, ∀ m, m ≤ k → x ∈ V → x ∉ K → weakDeriv1On V m g x = 0 := by
    refine ae_all_iff.2 fun m => ?_
    by_cases hm : m ≤ k
    · filter_upwards [hvan m hm] with x hx _ using hx
    · exact Eventually.of_forall fun x h => absurd h hm
  -- the Leibniz formula
  have hL : ∀ j ≤ k, HasWeakDerivOn V (derivList j) (fun x => a x * g x) (lsum j a V g) := by
    intro j hj
    have := leibniz_dir hV ha (D := fun m => weakDeriv1On V m g) (fun m hm => (hfam m hm).1)
      hchain j hj
    refine this.congr_ae ?_ (Eventually.of_forall fun x _ => rfl)
    filter_upwards [h0] with x hx hxV
    rw [hx hxV]
  -- `L²` bounds
  have hmulL2 : ∀ i ≤ k, ∀ m ≤ k,
      MemLp (fun x => iteratedDeriv i a x * weakDeriv1On V m g x) 2 (volume.restrict V) := by
    intro i hi m hm
    refine (hfam m hm).2.2.of_le_mul (c := |M|) ?_ ?_
    · exact ((continuousOn_iteratedDeriv hV ha hi).aestronglyMeasurable hVm).mul
        (hfam m hm).2.2.aestronglyMeasurable
    · rw [ae_restrict_iff' hVm]
      filter_upwards [hvan m hm] with x hx hxV
      rw [norm_mul]
      by_cases hxK : x ∈ K
      · exact mul_le_mul_of_nonneg_right ((hM i hi x hxK).trans (le_abs_self M)) (norm_nonneg _)
      · rw [hx hxV hxK]
        simp
  have hlsumL2 : ∀ j ≤ k, MemLp (lsum j a V g) 2 (volume.restrict V) := by
    intro j hj
    refine memLp_finsetSum _ fun i hi => ?_
    have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    exact (hmulL2 i (hi'.trans hj) (j - i) (by omega)).const_mul _
  refine ⟨⟨?_, fun j hj => ⟨lsum j a V g, hlsumL2 j hj, hL j hj⟩⟩, ?_⟩
  · refine hg.memLp.of_le_mul (c := |M|)
      ((ha.continuousOn.aestronglyMeasurable hVm).mul hg.memLp.aestronglyMeasurable) ?_
    rw [ae_restrict_iff' hVm]
    filter_upwards [hgK'] with x hx hxV
    rw [norm_mul]
    by_cases hxK : x ∈ K
    · have h00 := hM 0 (Nat.zero_le _) x hxK
      rw [iteratedDeriv_zero] at h00
      exact mul_le_mul_of_nonneg_right (h00.trans (le_abs_self M)) (norm_nonneg _)
    · rw [hx hxV hxK]
      simp
  · intro j hj
    have hae := weakDerivOn_ae_eq hV (locallyIntegrableOn_of_memLp hV (hlsumL2 j hj)) (hL j hj)
    rw [ae_restrict_iff' hVm]
    filter_upwards [hae, hvanAll] with x hx hvx hxV
    change ‖weakDerivOn V (derivList j) (fun x => a x * g x) x‖ ^ 2 ≤ _
    rw [hx hxV]
    by_cases hxK : x ∈ K
    · exact norm_leibniz_sq_le (fun i => iteratedDeriv i a x) (fun m => weakDeriv1On V m g x)
        (fun i hi => hM i (hi.trans hj) x hxK)
    · have hz : lsum j a V g x = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [hvx (j - i) (by omega) hxV hxK]
        simp
      rw [hz, norm_zero]
      have hnn : 0 ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * ‖weakDeriv1On V (j - i) g x‖ ^ 2 :=
        Finset.sum_nonneg fun i _ => by positivity
      have : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [this]
      positivity

end NonUniqueEuler.Sob.MultAux
