import NonUniqueEuler.H.Sec4.EvansSimple.Abstract

/-!
# Helper for `thm:evans-simple`(2) in the conjugate sector: transport by a conjugation

Helper of `P/Sec4/EvansSimple.lean` (fully proved; manuscript-independent). Namespace
`NonUniqueEuler.EvansSimpleAux`. Manuscript `lem:resolvent`, last assertion (`04_ring.tex:446-448`):
complex conjugation `C : Y^s_ℓ → Y^s_{-ℓ}` intertwines `L_ℓ` and `L_{-ℓ}`, so the spectral data of
`L_ℓ` at `λ_*` transport to `L_{-ℓ}` at `conj λ_*`.

* `conj_symm_smul`: `C⁻¹` is conjugate-linear;
* `exists_conj_functional`: `y ↦ conj(f(C⁻¹ y))` is a continuous `ℂ`-linear functional;
* `conj_transport`: the hypotheses of `isSimpleSpectralProj_of_range` transport through `C`.
-/

noncomputable section

open ComplexConjugate

namespace NonUniqueEuler.EvansSimpleAux

open Dunford

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

theorem conj_symm_smul (C : E ≃ₗᵢ[ℝ] F) (hC : ∀ (c : ℂ) (x : E), C (c • x) = conj c • C x)
    (c : ℂ) (y : F) : C.symm (c • y) = conj c • C.symm y := by
  apply C.injective
  rw [C.apply_symm_apply, hC, C.apply_symm_apply, Complex.conj_conj]

/-- `y ↦ conj(f(C⁻¹ y))` is a continuous `ℂ`-linear functional. -/
theorem exists_conj_functional (C : E ≃ₗᵢ[ℝ] F)
    (hC : ∀ (c : ℂ) (x : E), C (c • x) = conj c • C x) (f : E →L[ℂ] ℂ) :
    ∃ f' : F →L[ℂ] ℂ, ∀ y : F, f' y = conj (f (C.symm y)) := by
  let f' : F →L[ℂ] ℂ :=
    { toFun := fun y => conj (f (C.symm y))
      map_add' := fun a b => by simp only [map_add]
      map_smul' := fun c y => by
        simp only [conj_symm_smul C hC, map_smul, smul_eq_mul, map_mul, Complex.conj_conj,
          RingHom.id_apply]
      cont := Complex.continuous_conj.comp (f.continuous.comp C.symm.continuous) }
  exact ⟨f', fun y => rfl⟩

/-- **Transport through a conjugation** of the criterion `isSimpleSpectralProj_of_range`. -/
theorem conj_transport [CompleteSpace F] (C : E ≃ₗᵢ[ℝ] F)
    (hC : ∀ (c : ℂ) (x : E), C (c • x) = conj c • C x) {A : E →L[ℂ] E} {A' : F →L[ℂ] F}
    (hAA' : ∀ x, A' (C x) = C (A x)) {z₀ : ℂ} {f : E →L[ℂ] ℂ} {g : E}
    (hfg : f g = 1) (hAg : A g = z₀ • g) (hfA : ∀ x, f (A x) = z₀ * f x)
    (hker : ∀ x, A x = z₀ • x → ∃ c : ℂ, x = c • g)
    (hrange : ∀ h, f h = 0 → ∃ x, A x - z₀ • x = h) {f' : F →L[ℂ] ℂ}
    (hf' : ∀ y, f' y = conj (f (C.symm y))) :
    f' (C g) = 1 ∧ A' (C g) = conj z₀ • C g ∧
      IsSimpleSpectralProj A' (rankOneProj f' (C g)) (conj z₀) := by
  have hsymmA : ∀ y, C.symm (A' y) = A (C.symm y) := by
    intro y
    apply C.injective
    rw [C.apply_symm_apply, ← hAA', C.apply_symm_apply]
  have h1 : f' (C g) = 1 := by rw [hf', C.symm_apply_apply, hfg, map_one]
  have h2 : A' (C g) = conj z₀ • C g := by rw [hAA', hAg, hC]
  refine ⟨h1, h2, isSimpleSpectralProj_of_range h1 h2 ?_ ?_ ?_⟩
  · intro y
    rw [hf', hf', hsymmA, hfA, map_mul]
  · intro y hy
    have h3 : A (C.symm y) = z₀ • C.symm y := by
      rw [← hsymmA, hy, conj_symm_smul C hC, Complex.conj_conj]
    obtain ⟨c, hc⟩ := hker _ h3
    refine ⟨conj c, ?_⟩
    rw [← hC, ← hc, C.apply_symm_apply]
  · intro y hy
    rw [hf', map_eq_zero] at hy
    obtain ⟨x, hx⟩ := hrange _ hy
    refine ⟨C x, ?_⟩
    rw [hAA', ← hC, ← map_sub, hx, C.apply_symm_apply]

end NonUniqueEuler.EvansSimpleAux
