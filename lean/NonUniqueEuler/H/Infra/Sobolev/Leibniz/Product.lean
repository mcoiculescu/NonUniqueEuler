import Mathlib.Data.Nat.Choose.Sum
import NonUniqueEuler.H.Infra.Sobolev.Leibniz.Mollify
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helper for `P/Infra/Sobolev/Leibniz`: the weak Leibniz rule for `C^k` multipliers

For `χ` of class `C^k` on the plane (no boundedness needed) and a family `F δ` of locally
integrable functions with `∂₁ F δ = F (δ + e₁)` and `∂₂ F δ = F (δ + e₂)` weakly
(`|δ| < k`), the weak derivative of `χ F₀` of order `γ`, `|γ| ≤ k`, is
`∑_{β ≤ γ} C(γ,β) ∂^β χ F (γ - β)` (`leibniz_2d`).

Steps.
* `hasWeakDerivOn_mul`: one direction, `∂_v(χ u) = ∂_vχ u + χ ∂_v u`, by testing `∂_v u`
  against the `C¹` compactly supported function `χ φ` (`integral_mul_dirDeriv_of_contDiff_one`).
* `leibniz_dir`: the one-direction formula `∂_v^n (χ D₀) = ∑_j C(n,j) ∂_v^j χ D_{n-j}` by
  induction on `n` (Pascal's rule `Finset.sum_choose_succ_mul`, `HasWeakDerivOn.trans`).
* `leibniz_2d`: `∂^γ = ∂₁^{γ₁} ∂₂^{γ₂}`: first the formula in the direction `I`, then in the
  direction `1` for each term, and `∂₁^i ∂₂^j χ = ∂^{(i,j)} χ` by definition of `pdList`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace NonUniqueEuler.Sob.LeibnizAux

/-- Iterated directional derivatives of a `C^n` function. -/
theorem contDiff_iterDirDeriv {f : ℂ → ℂ} {n : ℕ} (hf : ContDiff ℝ n f) (ws : List ℂ) :
    ∀ m : ℕ, m + ws.length ≤ n → ContDiff ℝ m (iterDirDeriv ws f) := by
  induction ws with
  | nil =>
    intro m hm
    exact hf.of_le (by exact_mod_cast (by simpa using hm))
  | cons w ws ih =>
    intro m hm
    have h1 := ih (m + 1) (by simp only [List.length_cons] at hm; omega)
    have h2 := h1.fderiv_right (m := m) (by push_cast; exact le_rfl)
    exact h2.clm_apply contDiff_const

theorem continuous_iterDirDeriv {f : ℂ → ℂ} {n : ℕ} (hf : ContDiff ℝ n f) {ws : List ℂ}
    (hws : ws.length ≤ n) : Continuous (iterDirDeriv ws f) :=
  (contDiff_iterDirDeriv hf ws 0 (by omega)).continuous

theorem dirDeriv_continuous {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ) (v : ℂ) :
    Continuous (dirDeriv v ψ) :=
  (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem dirDeriv_hasCompactSupport {ψ : ℂ → ℂ} (hψc : HasCompactSupport ψ) (v : ℂ) :
    HasCompactSupport (dirDeriv v ψ) := by
  have : dirDeriv v ψ = (fun L : ℂ →L[ℝ] ℂ => L v) ∘ fderiv ℝ ψ := rfl
  rw [this]
  exact (hψc.fderiv ℝ).comp_left (by simp)

/-- Peeling off the inner derivatives: if `g = ∂_{ws} f` and `h = ∂_{ws ++ vs} f` weakly,
then `h = ∂_{vs} g` weakly. -/
theorem HasWeakDerivOn.of_append {V : Set ℂ} {ws vs : List ℂ} {f g h : ℂ → ℂ}
    (hfg : HasWeakDerivOn V ws f g) (hfh : HasWeakDerivOn V (ws ++ vs) f h) :
    HasWeakDerivOn V vs g h := by
  intro φ hφ
  have e1 := hfg _ (hφ.iterDirDeriv vs)
  have e2 := hfh φ hφ
  rw [iterDirDeriv_append] at e2
  have e := e1.symm.trans e2
  rw [List.length_append, pow_add, mul_assoc] at e
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) e

theorem hasWeakDerivOn_nil_self {V : Set ℂ} (f : ℂ → ℂ) : HasWeakDerivOn V [] f f := by
  intro φ _
  simp

/-- The product rule in one direction, for `χ ∈ C¹` and a locally integrable `u` with a
locally integrable weak derivative `g = ∂_v u`. -/
theorem hasWeakDerivOn_mul {χ u g : ℂ → ℂ} {v : ℂ} (hχ : ContDiff ℝ 1 χ)
    (hu : LocallyIntegrable u) (hg : LocallyIntegrable g) (h : HasWeakDerivOn univ [v] u g) :
    HasWeakDerivOn univ [v] (fun x => χ x * u x)
      (fun x => dirDeriv v χ x * u x + χ x * g x) := by
  intro φ hφ
  simp only [iterDirDeriv_cons, iterDirDeriv_nil, List.length_singleton, pow_one, neg_one_mul]
  set ψ : ℂ → ℂ := fun x => χ x * φ x with hψdef
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by exact_mod_cast le_top)
  have hψ : ContDiff ℝ 1 ψ := hχ.mul hφ1
  have hψc : HasCompactSupport ψ := hφ.compact.mul_left
  have hdψ : ∀ x, dirDeriv v ψ x = dirDeriv v χ x * φ x + χ x * dirDeriv v φ x := by
    intro x
    simp only [dirDeriv, hψdef]
    rw [fderiv_fun_mul (hχ.differentiable one_ne_zero x) (hφ1.differentiable one_ne_zero x)]
    simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hA := integral_mul_dirDeriv_of_contDiff_one hu hg h hψ hψc
  have hdχ : Continuous (dirDeriv v χ) := dirDeriv_continuous hχ v
  have i1 : Integrable (fun x => u x * dirDeriv v ψ x) :=
    integrable_mul_of_hasCompactSupport hu (dirDeriv_continuous hψ v)
      (dirDeriv_hasCompactSupport hψc v)
  have i2 : Integrable (fun x => u x * (dirDeriv v χ x * φ x)) :=
    integrable_mul_of_hasCompactSupport hu (hdχ.mul hφ.continuous) hφ.compact.mul_left
  have i3 : Integrable (fun x => g x * ψ x) :=
    integrable_mul_of_hasCompactSupport hg hψ.continuous hψc
  calc ∫ x, χ x * u x * dirDeriv v φ x
      = ∫ x, (u x * dirDeriv v ψ x - u x * (dirDeriv v χ x * φ x)) := by
        congr 1
        funext x
        rw [hdψ]
        ring
    _ = (∫ x, u x * dirDeriv v ψ x) - ∫ x, u x * (dirDeriv v χ x * φ x) := integral_sub i1 i2
    _ = -((∫ x, g x * ψ x) + ∫ x, u x * (dirDeriv v χ x * φ x)) := by
        rw [hA]
        ring
    _ = -∫ x, (dirDeriv v χ x * u x + χ x * g x) * φ x := by
        rw [← integral_add i3 i2]
        congr 2
        funext x
        simp only [hψdef]
        ring

/-- Linearity for finite combinations (on the plane). -/
theorem hasWeakDerivOn_sum {ι : Type*} (s : Finset ι) {vs : List ℂ} (c : ι → ℂ)
    {F G : ι → ℂ → ℂ} (hF : ∀ i ∈ s, LocallyIntegrable (F i))
    (hG : ∀ i ∈ s, LocallyIntegrable (G i)) (h : ∀ i ∈ s, HasWeakDerivOn univ vs (F i) (G i)) :
    HasWeakDerivOn univ vs (fun x => ∑ i ∈ s, c i * F i x) (fun x => ∑ i ∈ s, c i * G i x) := by
  intro φ hφ
  have hd := hφ.iterDirDeriv vs
  have iF : ∀ i ∈ s, Integrable (fun x => c i * (F i x * iterDirDeriv vs φ x)) := fun i hi =>
    (integrable_mul_of_hasCompactSupport (hF i hi) hd.continuous hd.compact).const_mul _
  have iG : ∀ i ∈ s, Integrable (fun x => c i * (G i x * φ x)) := fun i hi =>
    (integrable_mul_of_hasCompactSupport (hG i hi) hφ.continuous hφ.compact).const_mul _
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

/-- The one-direction Leibniz formula `∂_v^n (χ D₀) = ∑_{j ≤ n} C(n,j) ∂_v^j χ D_{n-j}`. -/
theorem leibniz_dir (v : ℂ) {N : ℕ} {χ : ℂ → ℂ} (hχ : ContDiff ℝ N χ) {D : ℕ → ℂ → ℂ}
    (hD : ∀ j ≤ N, LocallyIntegrable (D j))
    (hDD : ∀ j < N, HasWeakDerivOn univ [v] (D j) (D (j + 1))) :
    ∀ n ≤ N, HasWeakDerivOn univ (List.replicate n v) (fun x => χ x * D 0 x)
      (fun x => ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) * (iterDirDeriv (List.replicate j v) χ x * D (n - j) x)) := by
  intro n
  induction n with
  | zero =>
    intro _ φ _
    simp
  | succ n ih =>
    intro hn
    have IH := ih (by omega)
    have hcont : ∀ j, j ≤ N → Continuous (iterDirDeriv (List.replicate j v) χ) := fun j hj =>
      continuous_iterDirDeriv hχ (by simpa using hj)
    have step := hasWeakDerivOn_sum (Finset.range (n + 1)) (vs := [v])
      (fun j => (n.choose j : ℂ))
      (F := fun j x => iterDirDeriv (List.replicate j v) χ x * D (n - j) x)
      (G := fun j x => iterDirDeriv (List.replicate (j + 1) v) χ x * D (n - j) x +
        iterDirDeriv (List.replicate j v) χ x * D (n - j + 1) x)
      (fun j hj => by
        have hj' := Finset.mem_range.1 hj
        exact (hD _ (by omega)).continuous_mul (hcont j (by omega)))
      (fun j hj => by
        have hj' := Finset.mem_range.1 hj
        exact ((hD _ (by omega)).continuous_mul (hcont (j + 1) (by omega))).add
          ((hD _ (by omega)).continuous_mul (hcont j (by omega))))
      (fun j hj => by
        have hj' := Finset.mem_range.1 hj
        have h1 : ContDiff ℝ 1 (iterDirDeriv (List.replicate j v) χ) :=
          contDiff_iterDirDeriv hχ _ 1 (by simp; omega)
        exact hasWeakDerivOn_mul h1 (hD _ (by omega)) (hD _ (by omega)) (hDD _ (by omega)))
    have htr := IH.trans step
    have e1 : [v] ++ List.replicate n v = List.replicate (n + 1) v := rfl
    rw [e1] at htr
    convert htr using 2 with x
    rw [Finset.sum_choose_succ_mul (fun i k => iterDirDeriv (List.replicate i v) χ x * D k x) n]
    rw [add_comm]
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have : n + 1 - j = n - j + 1 := by omega
    rw [this]

/-- The two-dimensional Leibniz formula for a family of weak derivatives. -/
theorem leibniz_2d {k : ℕ} {χ : ℂ → ℂ} (hχ : ContDiff ℝ k χ) {F : ℕ × ℕ → ℂ → ℂ}
    (hF : ∀ δ ∈ multiIdx k, LocallyIntegrable (F δ))
    (h1 : ∀ δ : ℕ × ℕ, δ.1 + δ.2 < k → HasWeakDerivOn univ [1] (F δ) (F (δ.1 + 1, δ.2)))
    (h2 : ∀ δ : ℕ × ℕ, δ.1 + δ.2 < k →
      HasWeakDerivOn univ [Complex.I] (F δ) (F (δ.1, δ.2 + 1)))
    {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    HasWeakDerivOn univ (pdList γ) (fun x => χ x * F (0, 0) x)
      (fun x => ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ) * partialD β χ x *
        F (γ.1 - β.1, γ.2 - β.2) x) := by
  have hγk := mem_multiIdx.1 hγ
  obtain ⟨a, b⟩ := γ
  simp only at hγk ⊢
  have hFi : ∀ i j, i + j ≤ k → LocallyIntegrable (F (i, j)) := fun i j hij =>
    hF (i, j) (mem_multiIdx.2 hij)
  -- the inner formula, in the direction `I`
  have inner := leibniz_dir Complex.I (N := b) (χ := χ) (hχ.of_le (by exact_mod_cast (by omega)))
    (D := fun j => F (0, j)) (fun j hj => hFi 0 j (by omega))
    (fun j hj => h2 (0, j) (by simp; omega)) b le_rfl
  -- the outer formulas, in the direction `1`
  have hχj : ∀ j ∈ Finset.range (b + 1),
      ContDiff ℝ a (iterDirDeriv (List.replicate j Complex.I) χ) := fun j hj => by
    have hj' := Finset.mem_range.1 hj
    exact contDiff_iterDirDeriv hχ _ a (by simp; omega)
  have hcont : ∀ i j, i + j ≤ k →
      Continuous (iterDirDeriv (List.replicate i 1) (iterDirDeriv (List.replicate j Complex.I) χ)) :=
    fun i j hij => by
      rw [← iterDirDeriv_append]
      exact continuous_iterDirDeriv hχ (by simp; omega)
  have outer := hasWeakDerivOn_sum (Finset.range (b + 1)) (vs := List.replicate a 1)
    (fun j => (b.choose j : ℂ))
    (F := fun j x => iterDirDeriv (List.replicate j Complex.I) χ x * F (0, b - j) x)
    (G := fun j x => ∑ i ∈ Finset.range (a + 1), (a.choose i : ℂ) *
      (iterDirDeriv (List.replicate i 1) (iterDirDeriv (List.replicate j Complex.I) χ) x *
        F (a - i, b - j) x))
    (fun j hj => by
      have hj' := Finset.mem_range.1 hj
      exact (hFi 0 (b - j) (by omega)).continuous_mul
        (continuous_iterDirDeriv hχ (by simp; omega)))
    (fun j hj => by
      have hj' := Finset.mem_range.1 hj
      refine locallyIntegrable_finsetSum _ fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      exact ((hFi (a - i) (b - j) (by omega)).continuous_mul
        (hcont i j (by omega))).smul ((a.choose i : ℂ)))
    (fun j hj => by
      have hj' := Finset.mem_range.1 hj
      exact leibniz_dir 1 (hχj j hj) (D := fun i => F (i, b - j))
        (fun i hi => hFi i (b - j) (by omega))
        (fun i hi => h1 (i, b - j) (by simp; omega)) a le_rfl)
  have htr := inner.trans outer
  have e1 : List.replicate a (1 : ℂ) ++ List.replicate b Complex.I = pdList (a, b) := rfl
  rw [e1] at htr
  convert htr using 2 with x
  rw [leIdx, Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [partialD, pdList, iterDirDeriv_append]
  push_cast
  ring

end NonUniqueEuler.Sob.LeibnizAux
