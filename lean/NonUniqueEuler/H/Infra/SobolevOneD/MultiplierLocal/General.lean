import Mathlib.MeasureTheory.Function.L2Space
import NonUniqueEuler.H.Infra.SobolevOneD.MultiplierLocal.Leibniz
import NonUniqueEuler.H.Infra.SobolevOneD.MultiplierLocal.Bound
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helper for `P/Infra/SobolevOneD/MultiplierLocal`: multipliers bounded on all of `V`

For an open `V ⊆ ℝ`, `a ∈ C^k(V)` with `|a^{(i)}| ≤ M` on **all of** `V` (`i ≤ k`) and any
`g ∈ H^k(V)` (no support condition; `mul_bounded`):
* `a g ∈ H^k(V)`;
* pointwise a.e. on `V`, `|∂^j(ag)|² ≤ M² 2^j ∑_{i ≤ j} C(j,i) |∂^{j-i} g|²` for `j ≤ k`.

This is `MultAux.mul_general` of `H/Infra/SobolevOneD/Multiplier/General.lean` with the support
hypothesis on `g` replaced by the bound of `a^{(i)}` on all of `V` (the support hypothesis was used
there only to make the bounds hold outside `K`).

`norm_iteratedDeriv_le_of_vanish`: if `a` vanishes on `(0, ∞) \ [α, β]` and `|a^{(i)}| ≤ M` on
`[α, β]`, then `|a^{(i)}| ≤ |M|` on all of `(0, ∞)`: on the open set `(0, ∞) \ [α, β]` the
function `a` vanishes identically, so its iterated derivatives vanish there
(`Filter.EventuallyEq.iteratedDeriv_eq`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace NonUniqueEuler.Sob.MultLocAux

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

/-- The Leibniz sum `∑_{i ≤ j} C(j,i) a^{(i)} ∂^{j-i} g`. -/
def lsum (j : ℕ) (a : ℝ → ℂ) (V : Set ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * (iteratedDeriv i a x * weakDeriv1On V (j - i) g x)

/-- **Multipliers bounded on `V` act on `H^k(V)`.** -/
theorem mul_bounded {k : ℕ} {V : Set ℝ} (hV : IsOpen V) {a g : ℝ → ℂ}
    (ha : ContDiffOn ℝ k a V) {M : ℝ} (hM : ∀ i ≤ k, ∀ x ∈ V, ‖iteratedDeriv i a x‖ ≤ M)
    (hg : MemH1On k V g) :
    MemH1On k V (fun x => a x * g x) ∧
    ∀ j ≤ k, ∀ᵐ x ∂(volume.restrict V), ‖weakDeriv1On V j (fun x => a x * g x) x‖ ^ 2 ≤
      M ^ 2 * 2 ^ j *
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖weakDeriv1On V (j - i) g x‖ ^ 2 := by
  obtain ⟨hfam, hchain, h0⟩ := family_facts hV hg
  have hVm : MeasurableSet V := hV.measurableSet
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
      refine Eventually.of_forall fun x hxV => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((hM i hi x hxV).trans (le_abs_self M)) (norm_nonneg _)
  have hlsumL2 : ∀ j ≤ k, MemLp (lsum j a V g) 2 (volume.restrict V) := by
    intro j hj
    refine memLp_finsetSum _ fun i hi => ?_
    have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    exact (hmulL2 i (hi'.trans hj) (j - i) (by omega)).const_mul _
  refine ⟨⟨?_, fun j hj => ⟨lsum j a V g, hlsumL2 j hj, hL j hj⟩⟩, ?_⟩
  · refine hg.memLp.of_le_mul (c := |M|)
      ((ha.continuousOn.aestronglyMeasurable hVm).mul hg.memLp.aestronglyMeasurable) ?_
    rw [ae_restrict_iff' hVm]
    refine Eventually.of_forall fun x hxV => ?_
    rw [norm_mul]
    have h00 := hM 0 (Nat.zero_le _) x hxV
    rw [iteratedDeriv_zero] at h00
    exact mul_le_mul_of_nonneg_right (h00.trans (le_abs_self M)) (norm_nonneg _)
  · intro j hj
    have hae := weakDerivOn_ae_eq hV (locallyIntegrableOn_of_memLp hV (hlsumL2 j hj)) (hL j hj)
    rw [ae_restrict_iff' hVm]
    filter_upwards [hae] with x hx hxV
    change ‖weakDerivOn V (derivList j) (fun x => a x * g x) x‖ ^ 2 ≤ _
    rw [hx hxV]
    exact norm_leibniz_sq_le (fun i => iteratedDeriv i a x) (fun m => weakDeriv1On V m g x)
      (fun i hi => hM i (hi.trans hj) x hxV)

/-- A function vanishing on `(0, ∞) \ [α, β]`, with `|a^{(i)}| ≤ M` on `[α, β]`, has
`|a^{(i)}| ≤ |M|` on all of `(0, ∞)`. -/
theorem norm_iteratedDeriv_le_of_vanish {k : ℕ} {α β : ℝ} {a : ℝ → ℂ}
    (haI : ∀ r : ℝ, 0 < r → r ∉ Icc α β → a r = 0) {M : ℝ}
    (hM : ∀ i ≤ k, ∀ r ∈ Icc α β, ‖iteratedDeriv i a r‖ ≤ M) :
    ∀ i ≤ k, ∀ x ∈ Ioi (0 : ℝ), ‖iteratedDeriv i a x‖ ≤ |M| := by
  intro i hi x hx
  by_cases hxI : x ∈ Icc α β
  · exact (hM i hi x hxI).trans (le_abs_self M)
  · have hU : IsOpen (Ioi (0 : ℝ) ∩ (Icc α β)ᶜ) := isOpen_Ioi.inter isClosed_Icc.isOpen_compl
    have hev : a =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hU.mem_nhds ⟨hx, hxI⟩] with y hy using haI y hy.1 hy.2
    rw [hev.iteratedDeriv_eq, iteratedDeriv_fun_const_zero, norm_zero]
    exact abs_nonneg M

end NonUniqueEuler.Sob.MultLocAux
