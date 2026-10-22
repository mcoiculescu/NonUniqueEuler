import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Proof: weak derivatives (library I-HK)

Proof of `NonUniqueEuler/I/Infra/Sobolev/WeakDeriv.lean` (same declarations, same statements).

* `ae_eq`: the two weak derivatives have the same pairing with every test function; testing
  against real smooth compactly supported functions and applying
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` gives `g₁ = g₂` a.e. on `V`.
* `hasWeakDerivOn_of_contDiffOn`: induction on `vs`; for `vs = v :: ws` we commute
  `∂_v ∂_{ws} φ = ∂_{ws} ∂_v φ` (smoothness of `φ`), use the induction hypothesis with the test
  function `∂_v φ`, and integrate by parts once
  (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, which only needs differentiability
  of `∂_{ws} f` on `tsupport φ ⊆ V`).
* `perm`/`trans`: directional derivatives of a smooth function commute
  (`ContDiffAt.isSymmSndFDerivAt`), so `iterDirDeriv vs φ` only depends on `vs` up to
  permutation.

Helper lemmas are in the namespace `NonUniqueEuler.Sob.WeakDerivAux`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

namespace WeakDerivAux

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Test functions -/

theorem testFn_eq_zero {V : Set E} {φ : E → ℂ} (hφ : IsTestFn V φ) {x : E} (hx : x ∉ V) :
    φ x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.subset h))

/-- A real test function, viewed as a complex one. -/
theorem isTestFn_ofReal {V : Set E} {ρ : E → ℝ} (h1 : ContDiff ℝ ∞ ρ) (h2 : HasCompactSupport ρ)
    (h3 : tsupport ρ ⊆ V) : IsTestFn V (fun x => (ρ x : ℂ)) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp h1, h2.comp_left Complex.ofReal_zero, ?_⟩
  exact (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero ρ).trans h3

/-! ### Commuting directional derivatives of smooth functions -/

theorem contDiff_dirDeriv {φ : E → ℂ} (h : ContDiff ℝ ∞ φ) (v : E) :
    ContDiff ℝ ∞ (dirDeriv v φ) :=
  (ContDiff.fderiv_right (m := ∞) h (by simp)).clm_apply contDiff_const

theorem contDiff_iterDirDeriv {φ : E → ℂ} (h : ContDiff ℝ ∞ φ) (vs : List E) :
    ContDiff ℝ ∞ (iterDirDeriv vs φ) := by
  induction vs with
  | nil => simpa using h
  | cons v vs ih => simpa using contDiff_dirDeriv ih v

theorem dirDeriv_dirDeriv_eq {φ : E → ℂ} (h : ContDiff ℝ ∞ φ) (v w x : E) :
    dirDeriv v (dirDeriv w φ) x = fderiv ℝ (fderiv ℝ φ) x v w := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (ContDiff.fderiv_right (m := ∞) h (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun y => fderiv ℝ φ y w) ((fderiv ℝ (fderiv ℝ φ) x).flip w) x := by
    have := (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
    simpa using this
  show fderiv ℝ (fun y => fderiv ℝ φ y w) x v = _
  rw [hx.fderiv]
  rfl

theorem dirDeriv_comm {φ : E → ℂ} (h : ContDiff ℝ ∞ φ) (v w : E) :
    dirDeriv v (dirDeriv w φ) = dirDeriv w (dirDeriv v φ) := by
  funext x
  rw [dirDeriv_dirDeriv_eq h, dirDeriv_dirDeriv_eq h]
  exact (h.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

/-- For smooth `φ`, `iterDirDeriv vs φ` only depends on `vs` up to permutation. -/
theorem iterDirDeriv_perm {vs ws : List E} (hp : vs.Perm ws) {φ : E → ℂ}
    (h : ContDiff ℝ ∞ φ) : iterDirDeriv vs φ = iterDirDeriv ws φ := by
  induction hp with
  | nil => rfl
  | cons x _ ih => simp only [iterDirDeriv_cons, ih]
  | swap x y l =>
    simp only [iterDirDeriv_cons]
    exact dirDeriv_comm (contDiff_iterDirDeriv h l) y x
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### Classical derivatives on an open set -/

theorem contDiffOn_iterDirDeriv {V : Set E} (hV : IsOpen V) {f : E → ℂ} {n : ℕ}
    (hf : ContDiffOn ℝ n f V) (ws : List E) :
    ∀ m : ℕ, m + ws.length ≤ n → ContDiffOn ℝ m (iterDirDeriv ws f) V := by
  induction ws with
  | nil =>
    intro m hm
    exact hf.of_le (by exact_mod_cast (by simpa using hm))
  | cons w ws ih =>
    intro m hm
    have h1 := ih (m + 1) (by simp only [List.length_cons] at hm; omega)
    have h2 := h1.fderiv_of_isOpen hV (m := m) (by push_cast; exact le_rfl)
    exact h2.clm_apply contDiffOn_const

end Calculus

section Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]

/-! ### Integrability against test functions -/

/-- A locally integrable function on `V` times a test function supported in `V` is
integrable. -/
theorem integrable_mul_testFn [OpensMeasurableSpace E] {V : Set E} {g φ : E → ℂ}
    (hg : LocallyIntegrableOn g V) (hφ : IsTestFn V φ) : Integrable (fun x => g x * φ x) := by
  have hK : IsCompact (tsupport φ) := hφ.compact
  have h1 : IntegrableOn g (tsupport φ) := hg.integrableOn_compact_subset hφ.subset hK
  have h2 : IntegrableOn (fun x => g x * φ x) (tsupport φ) :=
    h1.mul_continuousOn hφ.continuous.continuousOn hK
  refine h2.integrable_of_forall_notMem_eq_zero (fun x hx => ?_)
  simp [image_eq_zero_of_notMem_tsupport hx]

/-- Invariance of the pairing under a.e. modification on `V`. -/
theorem integral_mul_testFn_congr {V : Set E} {f f' φ : E → ℂ} (hφ : IsTestFn V φ)
    (hf : ∀ᵐ x, x ∈ V → f x = f' x) : ∫ x, f' x * φ x = ∫ x, f x * φ x := by
  refine integral_congr_ae ?_
  filter_upwards [hf] with x hx
  by_cases hxV : x ∈ V
  · rw [hx hxV]
  · simp [testFn_eq_zero hφ hxV]

end Measure

section Haar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- A function continuous on the open set `V` times a test function supported in `V` is
integrable. -/
theorem integrable_continuousOn_mul_testFn {V : Set E} (hV : IsOpen V) {a φ : E → ℂ}
    (ha : ContinuousOn a V) (hφ : IsTestFn V φ) : Integrable (fun x => a x * φ x) :=
  integrable_mul_testFn (ha.locallyIntegrableOn hV.measurableSet) hφ

omit [(volume : Measure E).IsAddHaarMeasure] in
/-- Two locally integrable functions with the same pairings against all test functions
supported in the open set `V` agree a.e. on `V`. -/
theorem ae_eq_of_integral_testFn {V : Set E} (hV : IsOpen V) {g₁ g₂ : E → ℂ}
    (hg₁ : LocallyIntegrableOn g₁ V) (hg₂ : LocallyIntegrableOn g₂ V)
    (key : ∀ φ, IsTestFn V φ → ∫ x, g₁ x * φ x = ∫ x, g₂ x * φ x) :
    ∀ᵐ x, x ∈ V → g₁ x = g₂ x := by
  have h := hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hg₁.sub hg₂)
    (fun ρ hρ hρc hρV => by
      have hφ := isTestFn_ofReal hρ hρc hρV
      have i1 := integrable_mul_testFn hg₁ hφ
      have i2 := integrable_mul_testFn hg₂ hφ
      calc ∫ x, ρ x • (g₁ - g₂) x = ∫ x, (g₁ x * (ρ x : ℂ) - g₂ x * (ρ x : ℂ)) := by
            congr 1
            ext x
            simp only [Pi.sub_apply, Complex.real_smul]
            ring
        _ = 0 := by rw [integral_sub i1 i2, key _ hφ, sub_self])
  filter_upwards [h] with x hx hxV
  exact sub_eq_zero.1 (hx hxV)

/-- One integration by parts: for `F` of class `C¹` on the open set `V` and a test function
`ψ` supported in `V`, `∫ F ∂_v ψ = - ∫ (∂_v F) ψ`. -/
theorem integral_mul_dirDeriv {V : Set E} (hV : IsOpen V) {F ψ : E → ℂ}
    (hF : ContDiffOn ℝ 1 F V) (hψ : IsTestFn V ψ) (v : E) :
    ∫ x, F x * dirDeriv v ψ x = - ∫ x, dirDeriv v F x * ψ x := by
  have hFd : ∀ x ∈ V, DifferentiableAt ℝ F x := fun x hx =>
    (hF.differentiableOn one_ne_zero x hx).differentiableAt (hV.mem_nhds hx)
  have hFc : ContinuousOn F V := hF.continuousOn
  have hF'c : ContinuousOn (dirDeriv v F) V :=
    (hF.continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_continuousOn_mul_testFn hV hF'c hψ)
    (integrable_continuousOn_mul_testFn hV hFc (hψ.dirDeriv v))
    (integrable_continuousOn_mul_testFn hV hFc hψ)
    (fun x hx => hFd x (hψ.subset hx))
    (fun x _ => (hψ.smooth.differentiable (by simp)).differentiableAt)

end Haar

end WeakDerivAux

open WeakDerivAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- Uniqueness: two locally integrable weak derivatives on an open set agree a.e. on it. -/
theorem HasWeakDerivOn.ae_eq {V : Set E} (hV : IsOpen V) {vs : List E} {f g₁ g₂ : E → ℂ}
    (hg₁ : LocallyIntegrableOn g₁ V) (hg₂ : LocallyIntegrableOn g₂ V)
    (h₁ : HasWeakDerivOn V vs f g₁) (h₂ : HasWeakDerivOn V vs f g₂) :
    ∀ᵐ x, x ∈ V → g₁ x = g₂ x := by
  refine ae_eq_of_integral_testFn hV hg₁ hg₂ (fun φ hφ => ?_)
  have e := (h₁ φ hφ).symm.trans (h₂ φ hφ)
  have hne : ((-1 : ℂ) ^ vs.length) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ hne e

/-- The chosen weak derivative agrees a.e. on `V` with any locally integrable weak
derivative. -/
theorem weakDerivOn_ae_eq {V : Set E} (hV : IsOpen V) {vs : List E} {f g : E → ℂ}
    (hg : LocallyIntegrableOn g V) (h : HasWeakDerivOn V vs f g) :
    ∀ᵐ x, x ∈ V → weakDerivOn V vs f x = g x := by
  obtain ⟨h1, h2⟩ := weakDerivOn_spec hg h
  exact HasWeakDerivOn.ae_eq hV h1 hg h2 h

/-- Zero-th order: `HasWeakDerivOn V [] f g` means `f = g` a.e. on `V` (for locally integrable
`f`, `g` and open `V`). -/
theorem hasWeakDerivOn_nil_iff {V : Set E} (hV : IsOpen V) {f g : E → ℂ}
    (hf : LocallyIntegrableOn f V) (hg : LocallyIntegrableOn g V) :
    HasWeakDerivOn V [] f g ↔ ∀ᵐ x, x ∈ V → f x = g x := by
  have hff : HasWeakDerivOn V [] f f := fun φ _ => by simp
  constructor
  · intro h
    exact HasWeakDerivOn.ae_eq hV hf hg hff h
  · intro h φ hφ
    rw [hff φ hφ, integral_mul_testFn_congr hφ h]

/-- Linearity of weak derivatives. -/
theorem HasWeakDerivOn.add {V : Set E} (hV : IsOpen V) {vs : List E} {f₁ f₂ g₁ g₂ : E → ℂ}
    (hf₁ : LocallyIntegrableOn f₁ V) (hf₂ : LocallyIntegrableOn f₂ V)
    (hg₁ : LocallyIntegrableOn g₁ V) (hg₂ : LocallyIntegrableOn g₂ V)
    (h₁ : HasWeakDerivOn V vs f₁ g₁) (h₂ : HasWeakDerivOn V vs f₂ g₂) :
    HasWeakDerivOn V vs (f₁ + f₂) (g₁ + g₂) := by
  intro φ hφ
  have hψ := hφ.iterDirDeriv vs
  simp only [Pi.add_apply, add_mul]
  rw [integral_add (integrable_mul_testFn hf₁ hψ) (integrable_mul_testFn hf₂ hψ),
    integral_add (integrable_mul_testFn hg₁ hφ) (integrable_mul_testFn hg₂ hφ), h₁ φ hφ,
    h₂ φ hφ, mul_add]

theorem HasWeakDerivOn.const_mul {V : Set E} {vs : List E} {f g : E → ℂ}
    (h : HasWeakDerivOn V vs f g) (c : ℂ) :
    HasWeakDerivOn V vs (fun x => c * f x) (fun x => c * g x) := by
  intro φ hφ
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, h φ hφ]
  ring

/-- Classical derivatives are weak derivatives: if `f` is `C^n` on the open set `V`,
`n ≥ |vs|`, then `∂_{vs} f` (computed classically) is the weak derivative on `V`. -/
theorem hasWeakDerivOn_of_contDiffOn {V : Set E} (hV : IsOpen V) {vs : List E} {f : E → ℂ}
    {n : ℕ} (hn : vs.length ≤ n) (hf : ContDiffOn ℝ n f V) :
    HasWeakDerivOn V vs f (iterDirDeriv vs f) := by
  induction vs with
  | nil => intro φ _; simp
  | cons v ws ih =>
    intro φ hφ
    have hws : ws.length ≤ n := by simp only [List.length_cons] at hn; omega
    have hF : ContDiffOn ℝ 1 (iterDirDeriv ws f) V :=
      contDiffOn_iterDirDeriv hV hf ws 1 (by simp only [List.length_cons] at hn; omega)
    have e1 : iterDirDeriv (v :: ws) φ = iterDirDeriv ws (dirDeriv v φ) := by
      rw [iterDirDeriv_perm (List.perm_append_singleton v ws).symm hφ.smooth,
        iterDirDeriv_append]
      rfl
    rw [e1, ih hws _ (hφ.dirDeriv v), integral_mul_dirDeriv hV hF hφ v, iterDirDeriv_cons,
      List.length_cons, pow_succ]
    ring

/-- Invariance under a.e. modification on `V`. -/
theorem HasWeakDerivOn.congr_ae {V : Set E} {vs : List E} {f f' g g' : E → ℂ}
    (h : HasWeakDerivOn V vs f g) (hf : ∀ᵐ x, x ∈ V → f x = f' x)
    (hg : ∀ᵐ x, x ∈ V → g x = g' x) : HasWeakDerivOn V vs f' g' := by
  intro φ hφ
  rw [integral_mul_testFn_congr (hφ.iterDirDeriv vs) hf, h φ hφ,
    integral_mul_testFn_congr hφ hg]

/-- The order of the directions does not matter. -/
theorem HasWeakDerivOn.perm {V : Set E} {vs ws : List E} (hp : vs.Perm ws) {f g : E → ℂ}
    (h : HasWeakDerivOn V vs f g) : HasWeakDerivOn V ws f g := by
  intro φ hφ
  rw [← iterDirDeriv_perm hp hφ.smooth, h φ hφ, hp.length_eq]

/-- A weak derivative of a weak derivative is a weak derivative: if `g = ∂_{ws} f` and
`h = ∂_{vs} g` weakly on `V`, then `h = ∂_{vs ++ ws} f` weakly on `V`. -/
theorem HasWeakDerivOn.trans {V : Set E} {vs ws : List E} {f g h : E → ℂ}
    (hfg : HasWeakDerivOn V ws f g) (hgh : HasWeakDerivOn V vs g h) :
    HasWeakDerivOn V (vs ++ ws) f h := by
  intro φ hφ
  rw [iterDirDeriv_perm List.perm_append_comm hφ.smooth, iterDirDeriv_append,
    hfg _ (hφ.iterDirDeriv vs), hgh φ hφ, List.length_append, pow_add]
  ring

end NonUniqueEuler.Sob
