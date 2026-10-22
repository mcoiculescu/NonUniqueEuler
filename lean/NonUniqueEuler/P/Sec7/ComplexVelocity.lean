import NonUniqueEuler.Defs.Sec7.All
import NonUniqueEuler.I.Infra.Multipole.CauchySmooth
import NonUniqueEuler.I.Infra.Multipole.Holomorphic

/-!
# Proof: `eq:complex-velocity`, `eq:derivative-norm` (the complex form of a velocity field)

Proof of the interface `NonUniqueEuler/I/Sec7/ComplexVelocity.lean` (`07_several_rings.tex:43-66`).

1. `complexForm (velocity g) = BS.complexVelocity g = (2πi)⁻¹ C[g]` (`BS.complexVelocity_eq`),
   holomorphic off `tsupport g` by `Multipole.differentiableOn_cauchyTransform` (off the closed
   set `tsupport g` every point has a ball on which `g` vanishes identically).
2. The complex form of the monopole is `(∫g) conj (K_BS z) = (∫g)/(2πiz)`
   (`Multipole.conj_biotSavartKernel`); the complex form is additive, so the complex form of
   `E_g` is the difference, holomorphic off `tsupport g ∪ {0}`.
3. `V = conj ∘ F` with `F = complexForm V`; by `Multipole.iteratedFDeriv_real_conj_apply_eq` each
   entry of `∇^qV(x)` along a tuple of unit vectors `e ∈ {1, i}` has modulus `|F^{(q)}(x)|`;
   the `2^q` squares sum to `2^q |F^{(q)}(x)|²`.
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate

namespace NonUniqueEuler

namespace Rings

open RingData Datum

/-- **`eq:complex-velocity`** (`07_several_rings.tex:43-57`). For real `g ∈ L¹`: the complex form
of `K_BS * g` is `(2πi)⁻¹ ∫ g(ζ)/(z-ζ) dA(ζ)` off `supp g` and is holomorphic there; the complex
form of the monopole is `(∫g)/(2πiz)` (`z ≠ 0`); the complex form of the non-monopole field
`E_g = K_BS * g - (∫g)K_BS` is holomorphic on `ℂ ∖ (supp g ∪ {0})`. -/
theorem complex_velocity {g : ℂ → ℝ} (hg : MemLp g 1 volume) :
    (∀ z : ℂ, z ∉ tsupport g →
      complexForm (velocity g) z = (2 * Real.pi * Complex.I)⁻¹ * ∫ ζ, (g ζ : ℂ) / (z - ζ)) ∧
    DifferentiableOn ℂ (complexForm (velocity g)) (tsupport g)ᶜ ∧
    (∀ z : ℂ, z ≠ 0 →
      complexForm (BS.monopole g) z = ((∫ y, g y : ℝ) : ℂ) / (2 * Real.pi * Complex.I * z)) ∧
    DifferentiableOn ℂ (complexForm (BS.extField g)) (tsupport g ∪ {0})ᶜ := by
  have hgi : Integrable (fun w => (g w : ℂ)) := (memLp_one_iff_integrable.mp hg).ofReal
  -- the complex form of the velocity is `(2πi)⁻¹ C[g]` everywhere
  have hcf : complexForm (velocity g) = fun z =>
      (2 * Real.pi * Complex.I)⁻¹ * Multipole.cauchyTransform (fun w => (g w : ℂ)) z := by
    funext z
    rw [complexForm_velocity, BS.complexVelocity_eq]
  have hF : ∀ z, complexForm (velocity g) z =
      (2 * Real.pi * Complex.I)⁻¹ * ∫ ζ, (g ζ : ℂ) / (z - ζ) := by
    intro z
    rw [complexForm_velocity, BS.complexVelocity_eq, Multipole.cauchyTransform]
    simp only [div_eq_mul_inv]
  have hU : IsOpen (tsupport g)ᶜ := (isClosed_tsupport g).isOpen_compl
  have hsep : ∀ z ∈ (tsupport g)ᶜ, ∃ δ > 0, ∀ᵐ w, w ∈ ball z δ → (g w : ℂ) = 0 := by
    intro z hz
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU z hz
    refine ⟨δ, hδ, Filter.Eventually.of_forall fun w hw => ?_⟩
    have hw' : w ∉ tsupport g := hball hw
    rw [image_eq_zero_of_notMem_tsupport hw', Complex.ofReal_zero]
  have hdiff : DifferentiableOn ℂ (complexForm (velocity g)) (tsupport g)ᶜ := by
    rw [hcf]
    exact (Multipole.differentiableOn_cauchyTransform hgi hU hsep).const_mul _
  -- the complex form of the monopole, everywhere
  have hmono : ∀ z, complexForm (BS.monopole g) z =
      ((∫ y, g y : ℝ) : ℂ) / (2 * Real.pi * Complex.I * z) := by
    intro z
    rw [complexForm_apply, BS.monopole, map_mul, Complex.conj_ofReal,
      Multipole.conj_biotSavartKernel, div_eq_mul_inv]
  refine ⟨fun z _ => hF z, hdiff, fun z _ => hmono z, ?_⟩
  have hext : complexForm (BS.extField g) = fun z =>
      complexForm (velocity g) z - ((∫ y, g y : ℝ) : ℂ) / (2 * Real.pi * Complex.I * z) := by
    funext z
    rw [← hmono z, complexForm_apply, complexForm_apply, complexForm_apply, BS.extField, map_sub]
  rw [hext]
  refine DifferentiableOn.sub (hdiff.mono (compl_subset_compl.mpr subset_union_left)) ?_
  refine DifferentiableOn.div (differentiableOn_const _)
    ((differentiableOn_const _).mul differentiableOn_id) ?_
  intro z hz
  have hz0 : z ≠ 0 := fun h => hz (Or.inr h)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero) hz0

/-- **`eq:derivative-norm`** (`07_several_rings.tex:57-66`). If the complex form `F = V₁ - iV₂`
of a vector field `V` is holomorphic on an open set `U`, then for `x ∈ U` and `q ≥ 0` the array
norm of `∇^qV(x)` is `2^{q/2} |F^{(q)}(x)|`. -/
theorem derivative_norm {V : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ (complexForm V) U) (q : ℕ) {x : ℂ} (hx : x ∈ U) :
    iterDerivArrayNorm q V x = Real.sqrt (2 ^ q) * ‖iteratedDeriv q (complexForm V) x‖ := by
  have hV : (fun y => conj (complexForm V y)) = V := by
    funext y
    rw [complexForm_apply, Complex.conj_conj]
  -- each entry along unit directions has modulus `|F^{(q)}(x)|`
  have hentry : ∀ v : Fin q → ℂ, (∀ j, ‖v j‖ = 1) →
      ‖iteratedFDeriv ℝ q V x v‖ = ‖iteratedDeriv q (complexForm V) x‖ := by
    intro v hv
    have h := Multipole.iteratedFDeriv_real_conj_apply_eq hU hF hx q v
    rw [hV] at h
    rw [h, Complex.norm_conj, norm_mul, norm_prod]
    simp only [hv, Finset.prod_const_one, mul_one]
  have hbasis : ∀ (i : Fin q → Fin 2) (j : Fin q), ‖(![(1 : ℂ), Complex.I] (i j))‖ = 1 := by
    intro i j
    generalize i j = k
    fin_cases k <;> simp
  unfold iterDerivArrayNorm
  rw [Finset.sum_congr rfl (fun i _ => by rw [hentry _ (hbasis i)])]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  push_cast
  rfl

end Rings

end NonUniqueEuler
