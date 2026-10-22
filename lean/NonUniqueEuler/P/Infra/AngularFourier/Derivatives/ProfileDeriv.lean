import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.H.Infra.AngularFourier.Derivatives.ProfileDeriv.Classical
import NonUniqueEuler.H.Infra.AngularFourier.Derivatives.ProfileDeriv.Polar

/-!
# Proof (step of `P/Infra/AngularFourier/Derivatives`): the weak derivative of a radial profile

Proof of `NonUniqueEuler/I/Infra/AngularFourier/Derivatives/ProfileDeriv.lean` (same declaration,
statement copied verbatim): for `g ∈ H^1` the profile `g_ℓ` has the weak derivative `(∂_r g)_ℓ`
on `(0, ∞)`.

Proof. Let `η` be a test function on `(0, ∞)` and
`f = fW ℓ η = e^{-iℓθ} η(|x|)/|x|²` (a test function on the plane, helper `Smooth`),
`Φ₁ = x₁ f`, `Φ₂ = x₂ f`.
1. `∂₁Φ₁ + ∂₂Φ₂ = e^{-iℓθ} η'(|x|)/|x| = W ℓ η'` (helper `Classical`, `div_fW_eq`).
2. Weak derivatives of `g` against `Φ₁`, `Φ₂` (`Sob.MemH.memLp_weakPartial`), and
   `∂₁g Φ₁ + ∂₂g Φ₂ = ∂_r g · W ℓ η` pointwise.
3. `∫ F · W ℓ ζ = 2π ∫ F_ℓ ζ dr` (helper `Polar`, `integral_mul_W`, Fubini in polar
   coordinates), for `(F, ζ) = (g, η')` and `(∂_r g, η)`.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Ang

namespace ProfileDerivAux

theorem hasWeakDerivOn_angularSector_aux {g : ℂ → ℂ} (hg : Sob.MemH 1 g) (ℓ : ℤ) :
    Sob.HasWeakDerivOn (Ioi 0) (Sob.derivList 1) (Polar.angularSector g ℓ)
      (Polar.angularSector (radDeriv g) ℓ) := by
  intro η hη
  have hlist : Sob.iterDirDeriv (Sob.derivList 1) η = Sob.dirDeriv 1 η := by
    simp [Sob.derivList]
  rw [hlist, Sob.derivList_length, pow_one]
  have hη' : Sob.IsTestFn (Ioi 0) (Sob.dirDeriv 1 η) := hη.dirDeriv 1
  obtain ⟨h10L, h10⟩ := hg.memLp_weakPartial (γ := (1, 0)) (Sob.mem_multiIdx.2 (by norm_num))
  obtain ⟨h01L, h01⟩ := hg.memLp_weakPartial (γ := (0, 1)) (Sob.mem_multiIdx.2 (by norm_num))
  have hgL : MemLp g 2 volume := (Sob.memH_iff.1 hg).1
  have hf := isTestFn_fW ℓ hη
  have hΦ₁ : Sob.IsTestFn univ (fun y => (y.re : ℂ) * fW ℓ η y) :=
    ⟨((Complex.ofRealCLM.comp Complex.reCLM).contDiff).mul hf.smooth, hf.compact.mul_left,
      subset_univ _⟩
  have hΦ₂ : Sob.IsTestFn univ (fun y => (y.im : ℂ) * fW ℓ η y) :=
    ⟨((Complex.ofRealCLM.comp Complex.imCLM).contDiff).mul hf.smooth, hf.compact.mul_left,
      subset_univ _⟩
  have e₁ := h10 _ hΦ₁
  have e₂ := h01 _ hΦ₂
  simp only [Sob.pdList, List.replicate_zero, List.replicate_one, List.nil_append,
    List.append_nil, Sob.iterDirDeriv_cons, Sob.iterDirDeriv_nil, List.length_singleton,
    pow_one, neg_one_mul] at e₁ e₂
  -- integrability
  have iA : Integrable (fun x => g x * W ℓ (Sob.dirDeriv 1 η) x) volume :=
    hgL.integrable_mul ((isTestFn_W ℓ hη').memLp 2 volume)
  have i₁ : Integrable (fun x => Sob.weakPartial (1, 0) g x * ((x.re : ℂ) * fW ℓ η x)) volume :=
    h10L.integrable_mul (hΦ₁.memLp 2 volume)
  have i₂ : Integrable (fun x => Sob.weakPartial (0, 1) g x * ((x.im : ℂ) * fW ℓ η x)) volume :=
    h01L.integrable_mul (hΦ₂.memLp 2 volume)
  have j₁ : Integrable
      (fun x => g x * Sob.dirDeriv 1 (fun y => (y.re : ℂ) * fW ℓ η y) x) volume :=
    hgL.integrable_mul ((hΦ₁.dirDeriv 1).memLp 2 volume)
  have j₂ : Integrable
      (fun x => g x * Sob.dirDeriv Complex.I (fun y => (y.im : ℂ) * fW ℓ η y) x) volume :=
    hgL.integrable_mul ((hΦ₂.dirDeriv Complex.I).memLp 2 volume)
  -- pointwise identities
  have C : (fun x => radDeriv g x * W ℓ η x) = fun x =>
      Sob.weakPartial (1, 0) g x * ((x.re : ℂ) * fW ℓ η x) +
        Sob.weakPartial (0, 1) g x * ((x.im : ℂ) * fW ℓ η x) := by
    funext x
    simp only [radDeriv, W, fW, Complex.ofReal_div]
    ring
  have B : (fun x => g x * W ℓ (Sob.dirDeriv 1 η) x) = fun x =>
      g x * Sob.dirDeriv 1 (fun y => (y.re : ℂ) * fW ℓ η y) x +
        g x * Sob.dirDeriv Complex.I (fun y => (y.im : ℂ) * fW ℓ η y) x := by
    funext x
    rw [← div_fW_eq ℓ hη x]
    ring
  have iB : Integrable (fun x => radDeriv g x * W ℓ η x) volume := by
    rw [C]
    exact i₁.add i₂
  -- polar coordinates
  have A1 := integral_mul_W hη' ℓ iA
  have A2 := integral_mul_W hη ℓ iB
  rw [B, integral_add j₁ j₂, e₁, e₂] at A1
  rw [C, integral_add i₁ i₂] at A2
  have hπ : (2 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  apply mul_left_cancel₀ hπ
  linear_combination (-1 : ℂ) * A1 - A2

end ProfileDerivAux

/-- The profile `g_ℓ` of `g ∈ H^1` has the weak derivative `(∂_r g)_ℓ` on `(0, ∞)`. -/
theorem hasWeakDerivOn_angularSector {g : ℂ → ℂ} (hg : Sob.MemH 1 g) (ℓ : ℤ) :
    Sob.HasWeakDerivOn (Ioi 0) (Sob.derivList 1) (Polar.angularSector g ℓ)
      (Polar.angularSector (radDeriv g) ℓ) := by
  exact ProfileDerivAux.hasWeakDerivOn_angularSector_aux hg ℓ

end NonUniqueEuler.Ang
