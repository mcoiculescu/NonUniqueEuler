import NonUniqueEuler.H.Infra.SobolevOneD.Energy.Commute

/-!
# Helper for `P/Infra/SobolevOneD/Energy`: weak derivatives of `yukawa ℓ f` for `f ∈ H^k`

For `f ∈ H^k(ℝ)` vanishing a.e. outside `[a, b]`, with `f_j = weakDeriv1On univ j f`:
* `f_j ∈ L²`, `f_j` is the weak `j`-th derivative of `f`, and `f_j = 0` a.e. outside `[a, b]`
  (`memLp_weakDeriv1On`, `weakDeriv1On_eq_zero_outside`);
* `f_{j+1} = ∂ f_j` weakly (`hasWeakDerivOn_weakDeriv1On_succ`);
* `yukawa ℓ f_j = ∂^j (yukawa ℓ f)` weakly for `j ≤ k`, and
  `Y1 ℓ f_k = ∂^{k+1}`, `Y2 ℓ f_k = ∂^{k+2}` (`hasWeakDerivOn_yukawa_iter`,
  `hasWeakDerivOn_yukawa_top1`, `hasWeakDerivOn_yukawa_top2`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace NonUniqueEuler.Sob.EnergyAux

theorem derivList_succ (j : ℕ) : derivList 1 ++ derivList j = derivList (j + 1) := rfl

theorem derivList_add_two (j : ℕ) : derivList 2 ++ derivList j = derivList (j + 2) := rfl

theorem derivList_succ' (j : ℕ) : derivList j ++ derivList 1 = derivList (j + 1) := by
  simp [derivList, List.replicate_succ']

theorem locallyIntegrableOn_of_memLp {g : ℝ → ℂ} (hg : MemLp g 2 volume) (s : Set ℝ) :
    LocallyIntegrableOn g s :=
  (hg.locallyIntegrable one_le_two).locallyIntegrableOn s

theorem memLp_restrict_univ_iff {g : ℝ → ℂ} :
    MemLp g 2 (volume.restrict univ) ↔ MemLp g 2 volume := by
  rw [Measure.restrict_univ]

/-- The chosen weak derivatives of `f ∈ H^k` are in `L²` and are weak derivatives. -/
theorem memLp_weakDeriv1On {k : ℕ} {f : ℝ → ℂ} (hf : MemH1On k univ f) {j : ℕ} (hj : j ≤ k) :
    MemLp (weakDeriv1On univ j f) 2 volume ∧
      HasWeakDerivOn univ (derivList j) f (weakDeriv1On univ j f) := by
  obtain ⟨h, hh, hfh⟩ := hf.deriv j hj
  rw [memLp_restrict_univ_iff] at hh
  have hloc := locallyIntegrableOn_of_memLp hh univ
  have hspec := weakDerivOn_spec hloc hfh
  have hae := weakDerivOn_ae_eq isOpen_univ hloc hfh
  refine ⟨hh.ae_eq ?_, hspec.2⟩
  filter_upwards [hae] with x hx
  exact (hx (mem_univ x)).symm

/-- A weak derivative of a function vanishing outside `[a, b]` vanishes outside `[a, b]`. -/
theorem weakDeriv1On_eq_zero_outside {k : ℕ} {f : ℝ → ℂ} (hf : MemH1On k univ f) {a b : ℝ}
    (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0) {j : ℕ} (hj : j ≤ k) :
    ∀ᵐ x, x ∉ Icc a b → weakDeriv1On univ j f x = 0 := by
  obtain ⟨hL2, hw⟩ := memLp_weakDeriv1On hf hj
  set U : Set ℝ := (Icc a b)ᶜ with hU
  have hUo : IsOpen U := isClosed_Icc.isOpen_compl
  have h0 : HasWeakDerivOn U (derivList j) f 0 := by
    intro φ hφ
    simp only [Pi.zero_apply, zero_mul, integral_zero, mul_zero]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hfab] with x hx
    by_cases hmem : x ∈ Icc a b
    · have hnot : x ∉ tsupport (iterDirDeriv (derivList j) φ) := fun h =>
        ((hφ.iterDirDeriv (derivList j)).subset h) hmem
      rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
      rfl
    · rw [hx hmem, zero_mul]
      rfl
  have hae := HasWeakDerivOn.ae_eq hUo (locallyIntegrableOn_of_memLp hL2 U)
    (locallyIntegrableOn_zero) (hw.mono (subset_univ U)) h0
  filter_upwards [hae] with x hx hxU
  exact hx hxU

/-- `f_{j+1} = ∂ f_j` weakly. -/
theorem hasWeakDerivOn_weakDeriv1On_succ {k : ℕ} {f : ℝ → ℂ} (hf : MemH1On k univ f) {j : ℕ}
    (hj : j + 1 ≤ k) :
    HasWeakDerivOn univ (derivList 1) (weakDeriv1On univ j f) (weakDeriv1On univ (j + 1) f) := by
  have hj0 := (memLp_weakDeriv1On hf (by omega : j ≤ k)).2
  have hj1 := (memLp_weakDeriv1On hf hj).2
  intro φ hφ
  have e0 := hj0 _ (hφ.iterDirDeriv (derivList 1))
  have e1 := hj1 φ hφ
  rw [← iterDirDeriv_append, derivList_succ'] at e0
  rw [e0] at e1
  simp only [derivList_length] at e1 ⊢
  have hsq : ((-1 : ℂ) ^ j) * ((-1 : ℂ) ^ j) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [pow_succ] at e1
  linear_combination (-1 : ℂ) ^ j * e1 - ((∫ x, weakDeriv1On univ j f x *
    iterDirDeriv (derivList 1) φ x) + ∫ x, weakDeriv1On univ (j + 1) f x * φ x) * hsq

theorem yukawa_congr_ae (ℓ : ℤ) {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) : yukawa ℓ f = yukawa ℓ g := by
  funext x
  unfold yukawa
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

theorem weakDeriv1On_zero_ae {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    weakDeriv1On univ 0 f =ᵐ[volume] f := by
  have hloc := locallyIntegrableOn_of_memLp hf univ
  have h0 : HasWeakDerivOn univ (derivList 0) f f := fun φ _ => by simp [derivList]
  have hae := weakDerivOn_ae_eq isOpen_univ hloc h0
  filter_upwards [hae] with x hx
  exact hx (mem_univ x)

section Iter

variable {ℓ : ℤ} (hℓ : ℓ ≠ 0) {k : ℕ} {f : ℝ → ℂ} (hf : MemH1On k univ f) {a b : ℝ}
  (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0)
include hℓ hf hfab

omit hℓ in
theorem integrable_weakDeriv1On {j : ℕ} (hj : j ≤ k) : Integrable (weakDeriv1On univ j f) :=
  integrable_of_memLp_two (memLp_weakDeriv1On hf hj).1 (weakDeriv1On_eq_zero_outside hf hfab hj)

/-- `∂^j (yukawa ℓ f) = yukawa ℓ f_j` weakly, for `j ≤ k`. -/
theorem hasWeakDerivOn_yukawa_iter {j : ℕ} (hj : j ≤ k) :
    HasWeakDerivOn univ (derivList j) (yukawa ℓ f) (yukawa ℓ (weakDeriv1On univ j f)) := by
  induction j with
  | zero =>
    rw [yukawa_congr_ae ℓ (weakDeriv1On_zero_ae (memLp_restrict_univ_iff.1 hf.memLp))]
    intro φ _
    simp [derivList]
  | succ j ih =>
    have h1 := ih (by omega)
    have h2 := hasWeakDerivOn_yukawa_of_weak hℓ (integrable_weakDeriv1On hf hfab (by omega))
      (integrable_weakDeriv1On hf hfab hj) (weakDeriv1On_eq_zero_outside hf hfab (by omega))
      (weakDeriv1On_eq_zero_outside hf hfab hj) (hasWeakDerivOn_weakDeriv1On_succ hf hj)
    have := h1.trans h2
    rwa [derivList_succ] at this

theorem hasWeakDerivOn_yukawa_top1 :
    HasWeakDerivOn univ (derivList (k + 1)) (yukawa ℓ f) (Y1 ℓ (weakDeriv1On univ k f)) := by
  have := (hasWeakDerivOn_yukawa_iter hℓ hf hfab le_rfl).trans
    (hasWeakDerivOn_yukawa_one hℓ (integrable_weakDeriv1On hf hfab le_rfl))
  rwa [derivList_succ] at this

theorem hasWeakDerivOn_yukawa_add_two {i : ℕ} (hi : i ≤ k) :
    HasWeakDerivOn univ (derivList (i + 2)) (yukawa ℓ f) (Y2 ℓ (weakDeriv1On univ i f)) := by
  have := (hasWeakDerivOn_yukawa_iter hℓ hf hfab hi).trans
    (hasWeakDerivOn_yukawa_two hℓ (integrable_weakDeriv1On hf hfab hi)
      (weakDeriv1On_eq_zero_outside hf hfab hi))
  rwa [derivList_add_two] at this

end Iter

end NonUniqueEuler.Sob.EnergyAux
