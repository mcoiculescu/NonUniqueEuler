import NonUniqueEuler.Defs.Sec6.Datum
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Helpers for `lem:adm`: the terms of `f^{(n)}` (smooth, compact support, `≥ 0`, symmetric)

Helper of `P/Sec6/Adm.lean`, first paragraph of the proof of `lem:adm` (`06_datum.tex:94-99`):
`f^{(n)}` is a finite sum of nonnegative `3`-fold symmetric `C_c^∞` functions.

* `AdmH.IsGoodProfile θ G`: `G ∈ C_c^∞`, `G ≥ 0`, `G ∘ O_θ = G` pointwise;
* `AdmH.isGoodProfile_scale`: stable under `G ↦ c G(·/r)` (`c ≥ 0`, `r ≠ 0`);
* `AdmH.isGoodProfile_sum`: stable under finite sums;
* `AdmH.isGoodProfile_approxDatum`: `f^{(n)}` is good for `θ = 2π/3`, given `lem:ring-facts`
  (`RingFacts χ`) and the properties of `Φ^κ` from `lem:seed` (`IsSeedFlow`), as hypotheses.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.Datum.AdmH

open RingData

/-- `G ∈ C_c^∞(ℝ²)`, `G ≥ 0` and `G ∘ O_θ = G` pointwise. -/
def IsGoodProfile (θ : ℝ) (G : ℂ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧ HasCompactSupport G ∧ (∀ y, 0 ≤ G y) ∧
    ∀ y, G (rot θ y) = G y

theorem isGoodProfile_scale {θ : ℝ} {G : ℂ → ℝ} (hG : IsGoodProfile θ G) {c : ℝ} (hc : 0 ≤ c)
    {r : ℝ} (hr : r ≠ 0) : IsGoodProfile θ (fun x => c * G (x / (r : ℂ))) := by
  obtain ⟨h1, h2, h3, h4⟩ := hG
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  refine ⟨contDiff_const.mul (h1.comp (contDiff_id.div_const _)), ?_,
    fun x => mul_nonneg hc (h3 _), fun x => ?_⟩
  · have e : (fun x : ℂ => c * G (x / (r : ℂ))) =
        (fun _ => c) * (G ∘ (Homeomorph.mulRight₀ ((r : ℂ)⁻¹) (inv_ne_zero hr'))) := by
      funext x
      simp [div_eq_mul_inv]
    rw [e]
    exact (h2.comp_homeomorph _).mul_left
  · show c * G (rot θ x / (r : ℂ)) = c * G (x / (r : ℂ))
    rw [show rot θ x / (r : ℂ) = rot θ (x / (r : ℂ)) by simp only [rot, mul_div_assoc], h4]

theorem isGoodProfile_zero (θ : ℝ) : IsGoodProfile θ (fun _ => 0) :=
  ⟨contDiff_const, HasCompactSupport.zero, fun _ => le_rfl, fun _ => rfl⟩

theorem isGoodProfile_add {θ : ℝ} {G H : ℂ → ℝ} (hG : IsGoodProfile θ G)
    (hH : IsGoodProfile θ H) : IsGoodProfile θ (fun x => G x + H x) :=
  ⟨hG.1.add hH.1, hG.2.1.add hH.2.1, fun y => add_nonneg (hG.2.2.1 y) (hH.2.2.1 y),
    fun y => by simp only [hG.2.2.2 y, hH.2.2.2 y]⟩

theorem isGoodProfile_sum {θ : ℝ} {ι : Type*} (s : Finset ι) {F : ι → ℂ → ℝ}
    (hF : ∀ i ∈ s, IsGoodProfile θ (F i)) : IsGoodProfile θ (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isGoodProfile_zero θ
  | insert i s hi ih =>
    have e : (fun x => ∑ j ∈ insert i s, F j x) = fun x => F i x + ∑ j ∈ s, F j x := by
      funext x
      rw [Finset.sum_insert hi]
    rw [e]
    exact isGoodProfile_add (hF i (Finset.mem_insert_self i s))
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

/-- **`f^{(n)}` is a finite sum of nonnegative `3`-fold symmetric `C_c^∞` functions**
(`06_datum.tex:94-98`), given `lem:ring-facts` and the properties of `Φ^{κ_seed}`. -/
theorem isGoodProfile_approxDatum {χ : ℝ → ℝ} (hR : RingFacts χ) {A₁ μ sbar κs : ℝ}
    (hp : DatumParams A₁ μ sbar)
    (hS : IsGoodProfile (2 * Real.pi / 3) (OneRing.PhiSeed χ κs)) (n : ℕ) :
    IsGoodProfile (2 * Real.pi / 3) (approxDatum χ A₁ μ sbar κs n) := by
  have hΦ : IsGoodProfile (2 * Real.pi / 3) (ringPhi χ) :=
    ⟨hR.1, hR.2.1, fun y => (hR.2.2.2.1 y).1, fun y => hR.2.2.1 _ y⟩
  have hμ : 0 < μ := by linarith [hp.one_lt_μ]
  show IsGoodProfile _ (fun x => ∑ k ∈ Finset.Icc 1 n, approxTerm χ A₁ μ sbar κs n k x)
  refine isGoodProfile_sum _ fun k hk => ?_
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
  have hA : 0 ≤ amp A₁ μ k := (amp_pos hp.A₁_pos hμ k).le
  have hr : radius sbar μ k ≠ 0 := (radius_pos hp.sbar_pos hμ k).ne'
  rcases lt_or_eq_of_le hkn with hlt | rfl
  · have e : approxTerm χ A₁ μ sbar κs n k =
        fun x => amp A₁ μ k * ringPhi χ (x / ((radius sbar μ k : ℝ) : ℂ)) :=
      funext fun x => approxTerm_of_lt hk1 hlt x
    rw [e]
    exact isGoodProfile_scale hΦ hA hr
  · have e : approxTerm χ A₁ μ sbar κs k k =
        fun x => amp A₁ μ k * OneRing.PhiSeed χ κs (x / ((radius sbar μ k : ℝ) : ℂ)) :=
      funext fun x => approxTerm_self x
    rw [e]
    exact isGoodProfile_scale hS hA hr

end NonUniqueEuler.Datum.AdmH
