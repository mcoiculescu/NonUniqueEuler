import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import NonUniqueEuler.Defs.Infra.SobolevOneD
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.SobolevOneD.Multiplier

/-!
# Helper for `P/Infra/AngularFourier/NormEquiv/FiniteSum`: profiles on `(0, ∞)`

One-dimensional facts used in the induction step of `exists_normH_sum_ofProfile_le`
(`04_ring.tex:843-864`, upper bound of `lem:norm-equiv`).

* `memH1On_spec`: the chosen weak derivatives of `g ∈ H^k(V)` are `L²(V)` weak derivatives;
* `memH1On_deriv`: for `g ∈ H^{k+1}(V)`, `g' ∈ H^k(V)` and `∂^j g' = ∂^{j+1} g`;
* `ae_zero_outside_of_hasWeakDerivOn`: a weak derivative of a profile supported in `[ρ₋, ρ₊]`
  vanishes a.e. outside `[ρ₋, ρ₊]`;
* `memH1On_lincomb`, `secNormSq_lincomb_le`: linear combinations;
* weights: `secNormSq_shift_le` (`1 + m² ≤ 3(1 + ℓ²)` for `|m - ℓ| ≤ 1`),
  `sq_mul_secNormSq_le` (`ℓ² ‖g‖²_{k,ℓ} ≤ ‖g‖²_{k+1,ℓ}`), `secNormSq_deriv_le`
  (`‖g'‖²_{k,m} ≤ ‖g‖²_{k+1,m}`);
* `profile_bound`: the profiles `A = (h' ± ℓh/r)/2` of `∂_z`, `∂_z̄` of `h(r)e^{iℓθ}` satisfy
  `‖A‖²_{k,ℓ±1} ≤ K ‖h‖²_{k+1,ℓ}`, uniformly in `ℓ` (multiplier `1/r`,
  `Sob.secNormSq_mul_le`).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang.FiniteSumAux

open Sob

/-- `L²` on a subset of the line gives local integrability there. -/
theorem locInt_of_memLp {V : Set ℝ} {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict V)) :
    LocallyIntegrableOn f V :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable one_le_two)

/-- For `g ∈ H^k(V)`, `V` open, the chosen weak derivatives are `L²(V)` weak derivatives. -/
theorem memH1On_spec {k : ℕ} {V : Set ℝ} (hV : IsOpen V) {g : ℝ → ℂ} (hg : MemH1On k V g)
    {j : ℕ} (hj : j ≤ k) :
    MemLp (weakDeriv1On V j g) 2 (volume.restrict V) ∧
      HasWeakDerivOn V (derivList j) g (weakDeriv1On V j g) := by
  obtain ⟨u, hu, hgu⟩ := hg.deriv j hj
  have hul := locInt_of_memLp hu
  have hae := weakDerivOn_ae_eq hV hul hgu
  refine ⟨hu.ae_eq ((ae_restrict_iff' hV.measurableSet).2 ?_), (weakDerivOn_spec hul hgu).2⟩
  exact hae.mono fun x hx hxV => (hx hxV).symm

theorem derivList_one_append (j : ℕ) : derivList 1 ++ derivList j = derivList (j + 1) := by
  simp [derivList, List.replicate_succ]

/-- `∂^j (∂g) = ∂^{j+1} g` weakly. -/
theorem hasWeakDerivOn_deriv_succ {V : Set ℝ} {g g' u : ℝ → ℂ} {j : ℕ}
    (h1 : HasWeakDerivOn V (derivList 1) g g') (hj : HasWeakDerivOn V (derivList (j + 1)) g u) :
    HasWeakDerivOn V (derivList j) g' u := by
  intro φ hφ
  have e0 := h1 _ (hφ.iterDirDeriv (derivList j))
  have e1 := hj φ hφ
  rw [← iterDirDeriv_append, derivList_one_append] at e0
  simp only [derivList_length] at e0 e1 ⊢
  linear_combination e0 - e1

/-- For `g ∈ H^{k+1}(V)`: `g' ∈ H^k(V)` and `∂^j g' = ∂^{j+1} g` a.e. on `V`. -/
theorem memH1On_deriv {k : ℕ} {V : Set ℝ} (hV : IsOpen V) {g : ℝ → ℂ}
    (hg : MemH1On (k + 1) V g) :
    MemH1On k V (weakDeriv1On V 1 g) ∧ ∀ j ≤ k, ∀ᵐ r, r ∈ V →
      weakDeriv1On V j (weakDeriv1On V 1 g) r = weakDeriv1On V (j + 1) g r := by
  have h1 := memH1On_spec hV hg (j := 1) (by omega)
  have hd : ∀ j ≤ k, HasWeakDerivOn V (derivList j) (weakDeriv1On V 1 g)
      (weakDeriv1On V (j + 1) g) := fun j hj =>
    hasWeakDerivOn_deriv_succ h1.2 (memH1On_spec hV hg (j := j + 1) (by omega)).2
  refine ⟨⟨h1.1, fun j hj => ⟨_, (memH1On_spec hV hg (j := j + 1) (by omega)).1, hd j hj⟩⟩,
    fun j hj => ?_⟩
  exact weakDerivOn_ae_eq hV (locInt_of_memLp (memH1On_spec hV hg (j := j + 1) (by omega)).1)
    (hd j hj)

/-- A weak derivative on `(0,∞)` of a profile vanishing outside `[ρ₋, ρ₊]` vanishes there. -/
theorem ae_zero_outside_of_hasWeakDerivOn {ρm ρp : ℝ} {vs : List ℝ} {g g' : ℝ → ℂ}
    (hgI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → g r = 0)
    (hg' : LocallyIntegrableOn g' (Ioi 0)) (h : HasWeakDerivOn (Ioi 0) vs g g') :
    ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → g' r = 0 := by
  set U : Set ℝ := Ioi 0 ∩ (Icc ρm ρp)ᶜ with hU
  have hUo : IsOpen U := isOpen_Ioi.inter isClosed_Icc.isOpen_compl
  have hUsub : U ⊆ Ioi 0 := inter_subset_left
  have hg0 : ∀ᵐ r, r ∈ Ioi (0 : ℝ) → r ∉ Icc ρm ρp → g r = 0 :=
    (ae_restrict_iff' measurableSet_Ioi).1 hgI
  have h0 : HasWeakDerivOn U vs g (fun _ => 0) := by
    intro φ hφ
    have hz : ∫ x, g x * iterDirDeriv vs φ x = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hg0] with x hx
      by_cases hxU : x ∈ U
      · simp [hx hxU.1 hxU.2]
      · have : iterDirDeriv vs φ x = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hxU ((hφ.iterDirDeriv vs).subset h)
        simp [this]
    simp [hz]
  have hae := HasWeakDerivOn.ae_eq hUo (hg'.mono_set hUsub) locallyIntegrableOn_zero
    (h.mono hUsub) h0
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hae] with r hr hr0 hrI
  exact hr ⟨hr0, hrI⟩

/-- Linear combinations of `H^k((0,∞))` profiles; their weak derivatives. -/
theorem memH1On_lincomb {k : ℕ} {f₁ f₂ : ℝ → ℂ} (h₁ : MemH1On k (Ioi 0) f₁)
    (h₂ : MemH1On k (Ioi 0) f₂) (c₁ c₂ : ℂ) :
    MemH1On k (Ioi 0) (fun r => c₁ * f₁ r + c₂ * f₂ r) ∧ ∀ j ≤ k, ∀ᵐ r, r ∈ Ioi (0 : ℝ) →
      weakDeriv1On (Ioi 0) j (fun r => c₁ * f₁ r + c₂ * f₂ r) r =
        c₁ * weakDeriv1On (Ioi 0) j f₁ r + c₂ * weakDeriv1On (Ioi 0) j f₂ r := by
  have hd : ∀ j ≤ k, MemLp (fun r => c₁ * weakDeriv1On (Ioi 0) j f₁ r +
        c₂ * weakDeriv1On (Ioi 0) j f₂ r) 2 (volume.restrict (Ioi 0)) ∧
      HasWeakDerivOn (Ioi 0) (derivList j) (fun r => c₁ * f₁ r + c₂ * f₂ r)
        (fun r => c₁ * weakDeriv1On (Ioi 0) j f₁ r + c₂ * weakDeriv1On (Ioi 0) j f₂ r) := by
    intro j hj
    obtain ⟨a2, ad⟩ := memH1On_spec isOpen_Ioi h₁ hj
    obtain ⟨b2, bd⟩ := memH1On_spec isOpen_Ioi h₂ hj
    refine ⟨(a2.const_mul c₁).add (b2.const_mul c₂), ?_⟩
    exact HasWeakDerivOn.add isOpen_Ioi (locInt_of_memLp (h₁.memLp.const_mul c₁))
      (locInt_of_memLp (h₂.memLp.const_mul c₂)) (locInt_of_memLp (a2.const_mul c₁))
      (locInt_of_memLp (b2.const_mul c₂)) (ad.const_mul c₁) (bd.const_mul c₂)
  refine ⟨⟨(h₁.memLp.const_mul c₁).add (h₂.memLp.const_mul c₂), fun j hj => ⟨_, hd j hj⟩⟩,
    fun j hj => ?_⟩
  exact weakDerivOn_ae_eq isOpen_Ioi (locInt_of_memLp (hd j hj).1) (hd j hj).2

/-- `|f|² r` is integrable on a bounded `I ⊆ (0, R]` for `f ∈ L²((0,∞))`. -/
theorem integrableOn_normSq_mul {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioi 0)))
    {I : Set ℝ} (hIm : MeasurableSet I) {R : ℝ} (hI : I ⊆ Ioc 0 R) :
    IntegrableOn (fun r => ‖f r‖ ^ 2 * r) I := by
  have h2' : IntegrableOn (fun r => ‖f r‖ ^ 2) (Ioi 0) := hf.integrable_norm_pow two_ne_zero
  have h2 : IntegrableOn (fun r => ‖f r‖ ^ 2) I := h2'.mono_set (hI.trans Ioc_subset_Ioi_self)
  refine Integrable.mono' (h2.const_mul R)
    (h2.aestronglyMeasurable.mul continuous_id.aestronglyMeasurable) ?_
  rw [ae_restrict_iff' hIm]
  refine Filter.Eventually.of_forall fun r hr => ?_
  have hr' := hI hr
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hr'.1.le)]
  calc ‖f r‖ ^ 2 * r ≤ ‖f r‖ ^ 2 * R := mul_le_mul_of_nonneg_left hr'.2 (sq_nonneg _)
    _ = R * ‖f r‖ ^ 2 := mul_comm _ _

theorem norm_lincomb_sq_le (c₁ c₂ a b : ℂ) :
    ‖c₁ * a + c₂ * b‖ ^ 2 ≤ 2 * ‖c₁‖ ^ 2 * ‖a‖ ^ 2 + 2 * ‖c₂‖ ^ 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le (c₁ * a) (c₂ * b)
  rw [norm_mul, norm_mul] at h
  have h0 : 0 ≤ ‖c₁ * a + c₂ * b‖ := norm_nonneg _
  have hx : 0 ≤ ‖c₁‖ * ‖a‖ := by positivity
  have hy : 0 ≤ ‖c₂‖ * ‖b‖ := by positivity
  nlinarith [sq_nonneg (‖c₁‖ * ‖a‖ - ‖c₂‖ * ‖b‖), mul_le_mul h h h0 (add_nonneg hx hy)]

/-- `‖c₁f₁ + c₂f₂‖²_{k,m;I} ≤ 2|c₁|²‖f₁‖²_{k,m;I} + 2|c₂|²‖f₂‖²_{k,m;I}`. -/
theorem secNormSq_lincomb_le {k : ℕ} {f₁ f₂ : ℝ → ℂ} (h₁ : MemH1On k (Ioi 0) f₁)
    (h₂ : MemH1On k (Ioi 0) f₂) (c₁ c₂ : ℂ) (m : ℤ) {I : Set ℝ} (hIm : MeasurableSet I)
    {R : ℝ} (hI : I ⊆ Ioc 0 R) :
    secNormSq k m I (fun r => c₁ * f₁ r + c₂ * f₂ r) ≤
      2 * ‖c₁‖ ^ 2 * secNormSq k m I f₁ + 2 * ‖c₂‖ ^ 2 * secNormSq k m I f₂ := by
  obtain ⟨-, hae⟩ := memH1On_lincomb h₁ h₂ c₁ c₂
  unfold secNormSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have i₁ := integrableOn_normSq_mul (memH1On_spec isOpen_Ioi h₁ hjk).1 hIm hI
  have i₂ := integrableOn_normSq_mul (memH1On_spec isOpen_Ioi h₂ hjk).1 hIm hI
  have hint : ∫ r in I, ‖weakDeriv1On (Ioi 0) j (fun r => c₁ * f₁ r + c₂ * f₂ r) r‖ ^ 2 * r ≤
      2 * ‖c₁‖ ^ 2 * (∫ r in I, ‖weakDeriv1On (Ioi 0) j f₁ r‖ ^ 2 * r) +
        2 * ‖c₂‖ ^ 2 * (∫ r in I, ‖weakDeriv1On (Ioi 0) j f₂ r‖ ^ 2 * r) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (i₁.const_mul _) (i₂.const_mul _)]
    refine integral_mono_of_nonneg ?_ ((i₁.const_mul _).add (i₂.const_mul _)) ?_
    · rw [Filter.EventuallyLE, ae_restrict_iff' hIm]
      exact Filter.Eventually.of_forall fun r hr => mul_nonneg (sq_nonneg _) (hI hr).1.le
    · rw [Filter.EventuallyLE, ae_restrict_iff' hIm]
      filter_upwards [hae j hjk] with r hr hrI
      rw [hr (Ioc_subset_Ioi_self (hI hrI))]
      have hr0 : 0 ≤ r := (hI hrI).1.le
      have := mul_le_mul_of_nonneg_right
        (norm_lincomb_sq_le c₁ c₂ (weakDeriv1On (Ioi 0) j f₁ r) (weakDeriv1On (Ioi 0) j f₂ r)) hr0
      linarith
  have hw := secWeight_nonneg k j m
  calc secWeight k j m * ∫ r in I, ‖weakDeriv1On (Ioi 0) j (fun r => c₁ * f₁ r + c₂ * f₂ r) r‖ ^ 2 * r
      ≤ secWeight k j m * (2 * ‖c₁‖ ^ 2 * (∫ r in I, ‖weakDeriv1On (Ioi 0) j f₁ r‖ ^ 2 * r) +
        2 * ‖c₂‖ ^ 2 * (∫ r in I, ‖weakDeriv1On (Ioi 0) j f₂ r‖ ^ 2 * r)) :=
        mul_le_mul_of_nonneg_left hint hw
    _ = _ := by ring

/-! ### Weights -/

theorem secWeight_shift_le {k j : ℕ} {ℓ m : ℤ} (hm : (m : ℝ) ^ 2 ≤ 2 * (ℓ : ℝ) ^ 2 + 2) :
    secWeight k j m ≤ 3 ^ k * secWeight k j ℓ := by
  unfold secWeight
  have h1 : 1 + (m : ℝ) ^ 2 ≤ 3 * (1 + (ℓ : ℝ) ^ 2) := by nlinarith [sq_nonneg (ℓ : ℝ)]
  have h3 : (3 : ℝ) ^ (k - j) ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) (Nat.sub_le k j)
  calc (1 + (m : ℝ) ^ 2) ^ (k - j) ≤ (3 * (1 + (ℓ : ℝ) ^ 2)) ^ (k - j) :=
        pow_le_pow_left₀ (by positivity) h1 _
    _ = 3 ^ (k - j) * (1 + (ℓ : ℝ) ^ 2) ^ (k - j) := mul_pow _ _ _
    _ ≤ 3 ^ k * (1 + (ℓ : ℝ) ^ 2) ^ (k - j) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)

theorem setIntegral_normSq_mul_nonneg {I : Set ℝ} (hIm : MeasurableSet I) (hI : I ⊆ Ici 0)
    (f : ℝ → ℂ) : 0 ≤ ∫ r in I, ‖f r‖ ^ 2 * r :=
  setIntegral_nonneg hIm fun _ hr => mul_nonneg (sq_nonneg _) (hI hr)

/-- `‖g‖²_{k,m;I} ≤ 3^k ‖g‖²_{k,ℓ;I}` when `m² ≤ 2ℓ² + 2` (e.g. `m = ℓ ± 1`). -/
theorem secNormSq_shift_le {k : ℕ} {ℓ m : ℤ} (hm : (m : ℝ) ^ 2 ≤ 2 * (ℓ : ℝ) ^ 2 + 2)
    {I : Set ℝ} (hIm : MeasurableSet I) (hI : I ⊆ Ici 0) (g : ℝ → ℂ) :
    secNormSq k m I g ≤ 3 ^ k * secNormSq k ℓ I g := by
  unfold secNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h0 := setIntegral_normSq_mul_nonneg hIm hI (weakDeriv1On (Ioi 0) j g)
  calc secWeight k j m * ∫ r in I, ‖weakDeriv1On (Ioi 0) j g r‖ ^ 2 * r
      ≤ (3 ^ k * secWeight k j ℓ) * ∫ r in I, ‖weakDeriv1On (Ioi 0) j g r‖ ^ 2 * r :=
        mul_le_mul_of_nonneg_right (secWeight_shift_le hm) h0
    _ = _ := by ring

/-- `ℓ² ‖g‖²_{k,ℓ;I} ≤ ‖g‖²_{k+1,ℓ;I}`. -/
theorem sq_mul_secNormSq_le {k : ℕ} (ℓ : ℤ) {I : Set ℝ} (hIm : MeasurableSet I)
    (hI : I ⊆ Ici 0) (g : ℝ → ℂ) :
    (ℓ : ℝ) ^ 2 * secNormSq k ℓ I g ≤ secNormSq (k + 1) ℓ I g := by
  unfold secNormSq
  rw [Finset.mul_sum, Finset.sum_range_succ _ (k + 1)]
  have hlast : 0 ≤ secWeight (k + 1) (k + 1) ℓ *
      ∫ r in I, ‖weakDeriv1On (Ioi 0) (k + 1) g r‖ ^ 2 * r :=
    mul_nonneg (secWeight_nonneg _ _ _) (setIntegral_normSq_mul_nonneg hIm hI _)
  refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun j hj => ?_) hlast
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have h0 := setIntegral_normSq_mul_nonneg hIm hI (weakDeriv1On (Ioi 0) j g)
  have hw : (ℓ : ℝ) ^ 2 * secWeight k j ℓ ≤ secWeight (k + 1) j ℓ := by
    unfold secWeight
    rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]
    have hp := pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + (ℓ : ℝ) ^ 2) (k - j)
    have hl : (ℓ : ℝ) ^ 2 ≤ 1 + (ℓ : ℝ) ^ 2 := by linarith
    calc (ℓ : ℝ) ^ 2 * (1 + (ℓ : ℝ) ^ 2) ^ (k - j)
        ≤ (1 + (ℓ : ℝ) ^ 2) * (1 + (ℓ : ℝ) ^ 2) ^ (k - j) := mul_le_mul_of_nonneg_right hl hp
      _ = (1 + (ℓ : ℝ) ^ 2) ^ (k - j) * (1 + (ℓ : ℝ) ^ 2) := mul_comm _ _
  calc (ℓ : ℝ) ^ 2 * (secWeight k j ℓ * ∫ r in I, ‖weakDeriv1On (Ioi 0) j g r‖ ^ 2 * r)
      = ((ℓ : ℝ) ^ 2 * secWeight k j ℓ) * ∫ r in I, ‖weakDeriv1On (Ioi 0) j g r‖ ^ 2 * r := by
        ring
    _ ≤ secWeight (k + 1) j ℓ * ∫ r in I, ‖weakDeriv1On (Ioi 0) j g r‖ ^ 2 * r :=
        mul_le_mul_of_nonneg_right hw h0

/-- `‖g'‖²_{k,m;I} ≤ ‖g‖²_{k+1,m;I}` for `g ∈ H^{k+1}((0,∞))`. -/
theorem secNormSq_deriv_le {k : ℕ} {g : ℝ → ℂ} (hg : MemH1On (k + 1) (Ioi 0) g) (m : ℤ)
    {I : Set ℝ} (hIm : MeasurableSet I) (hI : I ⊆ Ioi 0) :
    secNormSq k m I (weakDeriv1On (Ioi 0) 1 g) ≤ secNormSq (k + 1) m I g := by
  obtain ⟨-, hae⟩ := memH1On_deriv isOpen_Ioi hg
  have hI' : I ⊆ Ici 0 := hI.trans Ioi_subset_Ici_self
  unfold secNormSq
  rw [Finset.sum_range_succ' _ (k + 1)]
  have h0term : 0 ≤ secWeight (k + 1) 0 m * ∫ r in I, ‖weakDeriv1On (Ioi 0) 0 g r‖ ^ 2 * r :=
    mul_nonneg (secWeight_nonneg _ _ _) (setIntegral_normSq_mul_nonneg hIm hI' _)
  refine le_add_of_le_of_nonneg (le_of_eq (Finset.sum_congr rfl fun j hj => ?_)) h0term
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hw : secWeight k j m = secWeight (k + 1) (j + 1) m := by
    unfold secWeight
    rw [Nat.add_sub_add_right]
  rw [hw]
  congr 1
  refine setIntegral_congr_ae hIm ?_
  filter_upwards [hae j hjk] with r hr hrI
  rw [hr (hI hrI)]

/-! ### The multiplier `1/r` -/

theorem contDiffOn_inv_ofReal (n : ℕ) :
    ContDiffOn ℝ n (fun r : ℝ => ((r : ℂ))⁻¹) (Ioi 0) := by
  have h : ContDiffOn ℝ n (fun r : ℝ => (r : ℂ)) (Ioi 0) :=
    Complex.ofRealCLM.contDiff.contDiffOn
  exact h.inv fun r hr => Complex.ofReal_ne_zero.2 (ne_of_gt hr)

theorem exists_bound_iteratedDeriv_inv (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) :
    ∃ M : ℝ, ∀ i ≤ k, ∀ r ∈ Icc ρm ρp,
      ‖iteratedDeriv i (fun r : ℝ => ((r : ℂ))⁻¹) r‖ ≤ M := by
  have hsub : Icc ρm ρp ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le hρm hr.1
  have hb : ∀ i : ℕ, ∃ M : ℝ, ∀ r ∈ Icc ρm ρp,
      ‖iteratedDeriv i (fun r : ℝ => ((r : ℂ))⁻¹) r‖ ≤ M := by
    intro i
    have hc : ContinuousOn (iteratedDerivWithin i (fun r : ℝ => ((r : ℂ))⁻¹) (Ioi 0)) (Ioi 0) :=
      (contDiffOn_inv_ofReal i).continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ioi 0)
    have hc' : ContinuousOn (iteratedDeriv i (fun r : ℝ => ((r : ℂ))⁻¹)) (Icc ρm ρp) :=
      (hc.congr (iteratedDerivWithin_of_isOpen isOpen_Ioi).symm).mono hsub
    exact isCompact_Icc.exists_bound_of_continuousOn hc'
  choose M hM using hb
  refine ⟨∑ i ∈ Finset.range (k + 1), |M i|, fun i hi r hr => ?_⟩
  calc _ ≤ M i := hM i r hr
    _ ≤ |M i| := le_abs_self _
    _ ≤ _ := Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))

/-! ### The profiles of `∂_z`, `∂_z̄` -/

/-- The profile `A = (h' + c h/r)/2`, `|c| ≤ |ℓ|`, of a sector `ℓ` function with
`h ∈ H^{k+1}((0,∞))` supported in `[ρ₋, ρ₊]` lies in `H^k((0,∞))`, is supported in `[ρ₋, ρ₊]`,
and `‖A‖²_{k,m} ≤ K ‖h‖²_{k+1,ℓ}` for `m² ≤ 2ℓ² + 2`, with `K` independent of `ℓ, m, c, h`. -/
theorem profile_bound (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ℓ m : ℤ) (c : ℂ) (h : ℝ → ℂ), MemH1On (k + 1) (Ioi 0) h →
      (∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0) →
      ‖c‖ ^ 2 ≤ (ℓ : ℝ) ^ 2 → (m : ℝ) ^ 2 ≤ 2 * (ℓ : ℝ) ^ 2 + 2 →
      MemH1On k (Ioi 0)
          (fun r => (2 : ℂ)⁻¹ * (weakDeriv1On (Ioi 0) 1 h r + c * h r / (r : ℂ))) ∧
        (∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp →
          (2 : ℂ)⁻¹ * (weakDeriv1On (Ioi 0) 1 h r + c * h r / (r : ℂ)) = 0) ∧
        secNormSq k m (Icc ρm ρp)
            (fun r => (2 : ℂ)⁻¹ * (weakDeriv1On (Ioi 0) 1 h r + c * h r / (r : ℂ))) ≤
          K * secNormSq (k + 1) ℓ (Icc ρm ρp) h := by
  obtain ⟨M, hM⟩ := exists_bound_iteratedDeriv_inv k (ρp := ρp) hρm
  refine ⟨3 ^ (k + 1) * (1 + 4 ^ (k + 1) * M ^ 2), by positivity,
    fun ℓ m c h hh hhI hc hm => ?_⟩
  have hsub : Icc ρm ρp ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le hρm hr.1
  have hsub' : Icc ρm ρp ⊆ Ioc 0 ρp := fun r hr => ⟨hsub hr, hr.2⟩
  have hsubI : Icc ρm ρp ⊆ Ici 0 := hsub.trans Ioi_subset_Ici_self
  have hk : MemH1On k (Ioi 0) h := hh.mono_order (Nat.le_succ k)
  obtain ⟨hq, hqn⟩ := secNormSq_mul_le hρm (contDiffOn_inv_ofReal k) hM hk hhI m
  obtain ⟨hd, -⟩ := memH1On_deriv isOpen_Ioi hh
  have hfun : (fun r => (2 : ℂ)⁻¹ * (weakDeriv1On (Ioi 0) 1 h r + c * h r / (r : ℂ))) =
      fun r => (2 : ℂ)⁻¹ * weakDeriv1On (Ioi 0) 1 h r +
        ((2 : ℂ)⁻¹ * c) * (((r : ℂ))⁻¹ * h r) := by
    funext r
    ring
  -- support
  have hsupp : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp →
      (2 : ℂ)⁻¹ * (weakDeriv1On (Ioi 0) 1 h r + c * h r / (r : ℂ)) = 0 := by
    have h1 := memH1On_spec isOpen_Ioi hh (j := 1) (by omega)
    have hd0 := ae_zero_outside_of_hasWeakDerivOn hhI (locInt_of_memLp h1.1) h1.2
    filter_upwards [hhI, hd0] with r e1 e2 hr
    rw [e1 hr, e2 hr]
    simp
  refine ⟨?_, hsupp, ?_⟩
  · rw [hfun]
    exact (memH1On_lincomb hd hq _ _).1
  · rw [hfun]
    have hl := secNormSq_lincomb_le hd hq (2 : ℂ)⁻¹ ((2 : ℂ)⁻¹ * c) m measurableSet_Icc hsub'
    -- the pieces
    set T := secNormSq (k + 1) ℓ (Icc ρm ρp) h with hT
    have hT0 : 0 ≤ T := secNormSq_nonneg _ _ measurableSet_Icc hsubI _
    have ha : secNormSq k m (Icc ρm ρp) (weakDeriv1On (Ioi 0) 1 h) ≤ 3 ^ (k + 1) * T :=
      (secNormSq_deriv_le hh m measurableSet_Icc hsub).trans
        (secNormSq_shift_le hm measurableSet_Icc hsubI h)
    have hs' : secNormSq k m (Icc ρm ρp) h ≤ 3 ^ k * secNormSq k ℓ (Icc ρm ρp) h :=
      secNormSq_shift_le hm measurableSet_Icc hsubI h
    have hsT : (ℓ : ℝ) ^ 2 * secNormSq k ℓ (Icc ρm ρp) h ≤ T :=
      sq_mul_secNormSq_le ℓ measurableSet_Icc hsubI h
    have hb0 : 0 ≤ secNormSq k m (Icc ρm ρp) (fun r => ((r : ℂ))⁻¹ * h r) :=
      secNormSq_nonneg _ _ measurableSet_Icc hsubI _
    have hs0 : 0 ≤ secNormSq k ℓ (Icc ρm ρp) h := secNormSq_nonneg _ _ measurableSet_Icc hsubI _
    have hn2 : ‖(2 : ℂ)⁻¹‖ ^ 2 = 1 / 4 := by
      rw [norm_inv, Complex.norm_ofNat]; norm_num
    have hnc : ‖(2 : ℂ)⁻¹ * c‖ ^ 2 = ‖c‖ ^ 2 / 4 := by
      rw [norm_mul, mul_pow, hn2]; ring
    rw [hn2, hnc] at hl
    have hM0 : 0 ≤ (4 : ℝ) ^ (k + 1) * M ^ 2 := by positivity
    have hcb : ‖c‖ ^ 2 * secNormSq k m (Icc ρm ρp) (fun r => ((r : ℂ))⁻¹ * h r) ≤
        3 ^ k * (4 ^ (k + 1) * M ^ 2) * T := by
      calc ‖c‖ ^ 2 * secNormSq k m (Icc ρm ρp) (fun r => ((r : ℂ))⁻¹ * h r)
          ≤ (ℓ : ℝ) ^ 2 * (4 ^ (k + 1) * M ^ 2 * (3 ^ k * secNormSq k ℓ (Icc ρm ρp) h)) := by
            gcongr
            exact hqn.trans (mul_le_mul_of_nonneg_left hs' hM0)
        _ = 3 ^ k * (4 ^ (k + 1) * M ^ 2) * ((ℓ : ℝ) ^ 2 * secNormSq k ℓ (Icc ρm ρp) h) := by
            ring
        _ ≤ 3 ^ k * (4 ^ (k + 1) * M ^ 2) * T := by gcongr
    have h3 : (3 : ℝ) ^ k ≤ 3 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
    have h3' : (3 : ℝ) ^ k * (4 ^ (k + 1) * M ^ 2) * T ≤ 3 ^ (k + 1) * (4 ^ (k + 1) * M ^ 2) * T := by
      gcongr
    calc _ ≤ 2 * (1 / 4) * secNormSq k m (Icc ρm ρp) (weakDeriv1On (Ioi 0) 1 h) +
          2 * (‖c‖ ^ 2 / 4) * secNormSq k m (Icc ρm ρp) (fun r => ((r : ℂ))⁻¹ * h r) := hl
      _ ≤ 3 ^ (k + 1) * (1 + 4 ^ (k + 1) * M ^ 2) * T := by
          have p1 : 0 ≤ (3 : ℝ) ^ (k + 1) * T := by positivity
          have p2 : 0 ≤ (3 : ℝ) ^ (k + 1) * (4 ^ (k + 1) * M ^ 2) * T := by positivity
          have e : (3 : ℝ) ^ (k + 1) * (1 + 4 ^ (k + 1) * M ^ 2) * T =
              3 ^ (k + 1) * T + 3 ^ (k + 1) * (4 ^ (k + 1) * M ^ 2) * T := by ring
          rw [e]
          linarith [ha, hcb, h3', p1, p2]

end NonUniqueEuler.Ang.FiniteSumAux
