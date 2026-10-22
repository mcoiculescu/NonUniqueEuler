import Mathlib.Data.Nat.Choose.Sum
import NonUniqueEuler.Defs.Infra.SobolevOneD
import NonUniqueEuler.H.Infra.SobolevOneD.Multiplier.Mollify
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helper for `P/Infra/SobolevOneD/Multiplier`: the weak Leibniz rule on an open set `V ⊆ ℝ`

For `χ` of class `C^N` on the open set `V ⊆ ℝ` (no boundedness needed) and a family `D j` of
functions locally integrable on `V` with `(D j)' = D (j+1)` weakly on `V` (`j < N`), the weak
derivative of order `n ≤ N` of `χ D₀` on `V` is `∑_{j ≤ n} C(n,j) χ^{(j)} D_{n-j}`
(`leibniz_dir`).

Steps (adapted from `H/Infra/Sobolev/Leibniz/Product.lean`, the plane case).
* `contDiff_mul_of_tsupport`: `χ φ` is globally `C^n` when `χ` is `C^n` on `V` and `φ` is `C^n`
  with `tsupport φ ⊆ V`.
* `hasWeakDerivOn_mul`: `(χ u)' = χ' u + χ u'`, by testing `u'` against the `C¹` compactly
  supported function `χ φ` (`integral_mul_deriv_of_contDiff_one`).
* `leibniz_dir`: induction on `n` (Pascal's rule `Finset.sum_choose_succ_mul`,
  `HasWeakDerivOn.trans`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace NonUniqueEuler.Sob.MultAux

/-- Iterated derivatives of a function of class `C^N` on an open set. -/
theorem contDiffOn_iteratedDeriv {V : Set ℝ} (hV : IsOpen V) {χ : ℝ → ℂ} {N : ℕ}
    (hχ : ContDiffOn ℝ N χ V) : ∀ j m : ℕ, j + m ≤ N → ContDiffOn ℝ m (iteratedDeriv j χ) V := by
  intro j
  induction j with
  | zero =>
    intro m hm
    rw [iteratedDeriv_zero]
    exact hχ.of_le (by exact_mod_cast (by omega : m ≤ N))
  | succ j ih =>
    intro m hm
    rw [iteratedDeriv_succ]
    exact (ih (m + 1) (by omega)).deriv_of_isOpen hV (by push_cast; exact le_rfl)

theorem continuousOn_iteratedDeriv {V : Set ℝ} (hV : IsOpen V) {χ : ℝ → ℂ} {N : ℕ}
    (hχ : ContDiffOn ℝ N χ V) {j : ℕ} (hj : j ≤ N) : ContinuousOn (iteratedDeriv j χ) V :=
  (contDiffOn_iteratedDeriv hV hχ j 0 (by omega)).continuousOn

/-- A function vanishing outside the closed support of `φ` is eventually zero near points
outside `V ⊇ tsupport φ`. -/
theorem eventually_mul_eq_zero {V : Set ℝ} {f φ : ℝ → ℂ} (hφV : tsupport φ ⊆ V) {x : ℝ}
    (hx : x ∉ V) : (fun y => f y * φ y) =ᶠ[𝓝 x] fun _ => 0 := by
  have h : φ =ᶠ[𝓝 x] 0 := (notMem_tsupport_iff_eventuallyEq).1 (fun h => hx (hφV h))
  filter_upwards [h] with y hy
  simp [hy]

theorem contDiff_mul_of_tsupport {V : Set ℝ} (hV : IsOpen V) {n : ℕ} {f φ : ℝ → ℂ}
    (hf : ContDiffOn ℝ n f V) (hφ : ContDiff ℝ n φ) (hφV : tsupport φ ⊆ V) :
    ContDiff ℝ n (fun x => f x * φ x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ V
  · exact (hf.contDiffAt (hV.mem_nhds hx)).mul hφ.contDiffAt
  · exact contDiffAt_const.congr_of_eventuallyEq (eventually_mul_eq_zero hφV hx)

theorem continuous_mul_of_tsupport {V : Set ℝ} (hV : IsOpen V) {f φ : ℝ → ℂ}
    (hf : ContinuousOn f V) (hφ : Continuous φ) (hφV : tsupport φ ⊆ V) :
    Continuous (fun x => f x * φ x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ V
  · exact (hf.continuousAt (hV.mem_nhds hx)).mul hφ.continuousAt
  · exact continuousAt_const.congr (eventually_mul_eq_zero hφV hx).symm

/-- Peeling off the inner derivatives: if `g = ∂_{ws} f` and `h = ∂_{ws ++ vs} f` weakly,
then `h = ∂_{vs} g` weakly. -/
theorem HasWeakDerivOn.of_append {V : Set ℝ} {ws vs : List ℝ} {f g h : ℝ → ℂ}
    (hfg : HasWeakDerivOn V ws f g) (hfh : HasWeakDerivOn V (ws ++ vs) f h) :
    HasWeakDerivOn V vs g h := by
  intro φ hφ
  have e1 := hfg _ (hφ.iterDirDeriv vs)
  have e2 := hfh φ hφ
  rw [iterDirDeriv_append] at e2
  have e := e1.symm.trans e2
  rw [List.length_append, pow_add, mul_assoc] at e
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) e

theorem hasWeakDerivOn_nil_self {V : Set ℝ} (f : ℝ → ℂ) : HasWeakDerivOn V [] f f := by
  intro φ _
  simp

/-- The product rule on `V`, for `χ ∈ C¹(V)` and a function `u` locally integrable on `V` with a
locally integrable weak derivative `g = u'` on `V`. -/
theorem hasWeakDerivOn_mul {V : Set ℝ} (hV : IsOpen V) {χ u g : ℝ → ℂ}
    (hχ : ContDiffOn ℝ 1 χ V) (hu : LocallyIntegrableOn u V) (hg : LocallyIntegrableOn g V)
    (h : HasWeakDerivOn V [1] u g) :
    HasWeakDerivOn V [1] (fun x => χ x * u x) (fun x => deriv χ x * u x + χ x * g x) := by
  intro φ hφ
  simp only [iterDirDeriv_cons, iterDirDeriv_nil, List.length_singleton, pow_one, neg_one_mul]
  change ∫ x, χ x * u x * deriv φ x = -∫ x, (deriv χ x * u x + χ x * g x) * φ x
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by exact_mod_cast le_top)
  have hψ : ContDiff ℝ 1 (fun x => χ x * φ x) :=
    contDiff_mul_of_tsupport hV (by exact_mod_cast hχ) (by exact_mod_cast hφ1) hφ.subset
  have hψc : HasCompactSupport (fun x => χ x * φ x) := hφ.compact.mul_left
  have hψV : tsupport (fun x => χ x * φ x) ⊆ V := tsupport_mul_subset_right.trans hφ.subset
  have hdψ : ∀ x, deriv (fun y => χ y * φ y) x = deriv χ x * φ x + χ x * deriv φ x := by
    intro x
    by_cases hx : x ∈ V
    · exact deriv_fun_mul ((hχ.contDiffAt (hV.mem_nhds hx)).differentiableAt one_ne_zero)
        (hφ1.differentiable one_ne_zero x)
    · have h0 : φ =ᶠ[𝓝 x] 0 :=
        (notMem_tsupport_iff_eventuallyEq).1 (fun h' => hx (hφ.subset h'))
      have e1 : deriv (fun y => χ y * φ y) x = 0 := by
        rw [(eventually_mul_eq_zero hφ.subset hx).deriv_eq]
        simp
      have e2 : deriv φ x = 0 := by
        rw [h0.deriv_eq]
        simp
      rw [e1, e2, h0.eq_of_nhds]
      simp
  have hA := integral_mul_deriv_of_contDiff_one hV hu hg h hψ hψc hψV
  have hdχ : ContinuousOn (deriv χ) V := hχ.continuousOn_deriv_of_isOpen hV le_rfl
  have i1 : Integrable (fun x => u x * deriv (fun y => χ y * φ y) x) :=
    integrable_mul_of_tsupport hu (hψ.continuous_deriv le_rfl) hψc.deriv
      (tsupport_deriv_subset.trans hψV)
  have i2 : Integrable (fun x => u x * (deriv χ x * φ x)) :=
    integrable_mul_of_tsupport hu (continuous_mul_of_tsupport hV hdχ hφ.continuous hφ.subset)
      hφ.compact.mul_left (tsupport_mul_subset_right.trans hφ.subset)
  have i3 : Integrable (fun x => g x * (χ x * φ x)) :=
    integrable_mul_of_tsupport hg hψ.continuous hψc hψV
  calc ∫ x, χ x * u x * deriv φ x
      = ∫ x, (u x * deriv (fun y => χ y * φ y) x - u x * (deriv χ x * φ x)) := by
        congr 1
        funext x
        rw [hdψ]
        ring
    _ = (∫ x, u x * deriv (fun y => χ y * φ y) x) - ∫ x, u x * (deriv χ x * φ x) :=
        integral_sub i1 i2
    _ = -((∫ x, g x * (χ x * φ x)) + ∫ x, u x * (deriv χ x * φ x)) := by
        rw [hA]
        ring
    _ = -∫ x, (deriv χ x * u x + χ x * g x) * φ x := by
        rw [← integral_add i3 i2]
        congr 2
        funext x
        ring

/-- Linearity for finite combinations, on `V`. -/
theorem hasWeakDerivOn_sum {V : Set ℝ} {ι : Type*} (s : Finset ι) {vs : List ℝ} (c : ι → ℂ)
    {F G : ι → ℝ → ℂ} (hF : ∀ i ∈ s, LocallyIntegrableOn (F i) V)
    (hG : ∀ i ∈ s, LocallyIntegrableOn (G i) V) (h : ∀ i ∈ s, HasWeakDerivOn V vs (F i) (G i)) :
    HasWeakDerivOn V vs (fun x => ∑ i ∈ s, c i * F i x) (fun x => ∑ i ∈ s, c i * G i x) := by
  intro φ hφ
  have hd := hφ.iterDirDeriv vs
  have iF : ∀ i ∈ s, Integrable (fun x => c i * (F i x * iterDirDeriv vs φ x)) := fun i hi =>
    (integrable_mul_of_tsupport (hF i hi) hd.continuous hd.compact hd.subset).const_mul _
  have iG : ∀ i ∈ s, Integrable (fun x => c i * (G i x * φ x)) := fun i hi =>
    (integrable_mul_of_tsupport (hG i hi) hφ.continuous hφ.compact hφ.subset).const_mul _
  calc ∫ x, (∑ i ∈ s, c i * F i x) * iterDirDeriv vs φ x
      = ∫ x, ∑ i ∈ s, c i * (F i x * iterDirDeriv vs φ x) := by
        congr 1
        funext x
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i ∈ s, ∫ x, c i * (F i x * iterDirDeriv vs φ x) := integral_finsetSum s iF
    _ = ∑ i ∈ s, (-1 : ℂ) ^ vs.length * ∫ x, c i * (G i x * φ x) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [integral_const_mul, integral_const_mul, h i hi φ hφ]
        ring
    _ = (-1 : ℂ) ^ vs.length * ∫ x, ∑ i ∈ s, c i * (G i x * φ x) := by
        rw [integral_finsetSum s iG, Finset.mul_sum]
    _ = (-1 : ℂ) ^ vs.length * ∫ x, (∑ i ∈ s, c i * G i x) * φ x := by
        congr 2
        funext x
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- The weak Leibniz formula on `V`: `(χ D₀)^{(n)} = ∑_{j ≤ n} C(n,j) χ^{(j)} D_{n-j}`. -/
theorem leibniz_dir {V : Set ℝ} (hV : IsOpen V) {N : ℕ} {χ : ℝ → ℂ} (hχ : ContDiffOn ℝ N χ V)
    {D : ℕ → ℝ → ℂ} (hD : ∀ j ≤ N, LocallyIntegrableOn (D j) V)
    (hDD : ∀ j < N, HasWeakDerivOn V [1] (D j) (D (j + 1))) :
    ∀ n ≤ N, HasWeakDerivOn V (derivList n) (fun x => χ x * D 0 x)
      (fun x => ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) * (iteratedDeriv j χ x * D (n - j) x)) := by
  intro n
  induction n with
  | zero =>
    intro _ φ _
    simp [derivList]
  | succ n ih =>
    intro hn
    have IH := ih (by omega)
    have hcont : ∀ j, j ≤ N → ContinuousOn (iteratedDeriv j χ) V := fun j hj =>
      continuousOn_iteratedDeriv hV hχ hj
    have step := hasWeakDerivOn_sum (V := V) (Finset.range (n + 1)) (vs := [1])
      (fun j => (n.choose j : ℂ))
      (F := fun j x => iteratedDeriv j χ x * D (n - j) x)
      (G := fun j x => iteratedDeriv (j + 1) χ x * D (n - j) x +
        iteratedDeriv j χ x * D (n - j + 1) x)
      (fun j hj => by
        have hj' := Finset.mem_range.1 hj
        exact (hD _ (by omega)).continuousOn_mul (hcont j (by omega)) hV.isLocallyClosed)
      (fun j hj => by
        have hj' := Finset.mem_range.1 hj
        exact ((hD _ (by omega)).continuousOn_mul (hcont (j + 1) (by omega))
          hV.isLocallyClosed).add
          ((hD _ (by omega)).continuousOn_mul (hcont j (by omega)) hV.isLocallyClosed))
      (fun j hj => by
        have hj' := Finset.mem_range.1 hj
        have h1 : ContDiffOn ℝ 1 (iteratedDeriv j χ) V :=
          contDiffOn_iteratedDeriv hV hχ j 1 (by omega)
        have := hasWeakDerivOn_mul hV h1 (hD (n - j) (by omega)) (hD (n - j + 1) (by omega))
          (hDD (n - j) (by omega))
        rw [← iteratedDeriv_succ] at this
        exact this)
    have htr := IH.trans step
    have e1 : [(1 : ℝ)] ++ derivList n = derivList (n + 1) := rfl
    rw [e1] at htr
    convert htr using 2 with x
    rw [Finset.sum_choose_succ_mul (fun i k => iteratedDeriv i χ x * D k x) n]
    rw [add_comm]
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have : n + 1 - j = n - j + 1 := by omega
    rw [this]

end NonUniqueEuler.Sob.MultAux
