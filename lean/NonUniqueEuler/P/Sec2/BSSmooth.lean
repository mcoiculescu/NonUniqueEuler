import NonUniqueEuler.Defs.Sec2.BiotSavart
import Mathlib.Analysis.InnerProductSpace.Laplacian
import NonUniqueEuler.H.Sec2.BSSmooth.L2Identity
import NonUniqueEuler.H.Sec2.BSSmooth.Weak
import NonUniqueEuler.I.Infra.Sobolev.Smooth

/-!
# Proof: `lem:BS-basic`(d), the velocity of a smooth compactly supported vorticity

Proof of `I/Sec2/BSSmooth.lean` (`02_prelim.tex:160-169`, proof `02_prelim.tex:208-262`).
Helpers in `H/Sec2/BSSmooth/`:
* `Differentiate`: `u = K ⋆ g`, `ψ = (2π)⁻¹ log‖·‖ ⋆ g` as Mathlib convolutions; smoothness and
  `∂_{vs} u = K ⋆ ∂_{vs} g` (differentiation under the integral sign);
* `Stream`: `u = ∇^⊥ψ`, `Δψ = g`, `div u = 0`, `curl u = g` (R6: the weak derivative of
  `log‖·‖` and `∫ log‖y‖ Δh(y) dy = 2π h(0)` from `I/Infra/Polar/LogLaplacian.lean`);
* `Decay`: `D^q u = O(|x|^{-(q+1)})` (from `I/Infra/Multipole/CauchySmooth.lean`), hence
  `∂_v u ∈ L² ∩ L^∞`;
* `L2Identity`: `‖∂₁u‖² + ‖∂₂u‖² = ‖g‖²` (whole-plane integration by parts of `det ∇u`);
* `Weak`: weak derivatives of smooth functions are the classical ones (a.e.).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal ContDiff Laplacian

namespace NonUniqueEuler.BS

open BSSmoothH in
/-- `∂_{vs} (K ∗ g) ∈ L² ∩ L^∞` for every nonempty list of directions. -/
private theorem memLp_iterDirDeriv_velocity {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) {vs : List ℂ} (hvs : vs ≠ []) :
    MemLp (Sob.iterDirDeriv vs (velocity g)) 2 volume ∧
      MemLp (Sob.iterDirDeriv vs (velocity g)) ⊤ volume := by
  cases vs with
  | nil => exact absurd rfl hvs
  | cons v vs =>
    obtain ⟨h, hh, hhc, h1, -⟩ := iterDirDeriv_velocity vs hg hgc
    rw [Sob.iterDirDeriv_cons, h1]
    exact memLp_fderiv_velocity hh hhc v

/-! ### (d) Smooth compactly supported vorticities -/

/-- `lem:BS-basic`(d): for real `g ∈ C_c^∞`, `u = K ∗ g ∈ C^∞` and the stream function
`ψ = (2π)⁻¹ log|·| ∗ g ∈ C^∞`. -/
theorem contDiff_velocity_of_smooth {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ContDiff ℝ ∞ (velocity g) ∧ ContDiff ℝ ∞ (Multipole.logPotentialReal g) :=
  ⟨BSSmoothH.contDiff_velocity hg hgc, BSSmoothH.contDiff_logPotentialReal hg hgc⟩

/-- `lem:BS-basic`(d): `∂^γ (K ∗ g) = K ∗ ∂^γ g` for every multi-index `γ`. -/
theorem partialD_velocity_of_smooth {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (γ : ℕ × ℕ) : Sob.partialD γ (velocity g) = velocity (Prelim.partialDR γ g) := by
  obtain ⟨h, -, -, h1, h2⟩ := BSSmoothH.iterDirDeriv_velocity (Sob.pdList γ) hg hgc
  have e : Prelim.partialDR γ g = h := by
    funext x
    simp only [Prelim.partialDR, Sob.partialD, h2, Complex.ofReal_re]
  rw [e]
  exact h1

/-- `lem:BS-basic`(d): `u = ∇^⊥ψ` with `ψ(x) = (2π)⁻¹ ∫ log|x - y| g(y) dy`. -/
theorem velocity_eq_perpGrad_of_smooth {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) :
    velocity g = Prelim.perpGrad (Multipole.logPotentialReal g) :=
  BSSmoothH.velocity_eq_perpGrad hg hgc

/-- `lem:BS-basic`(d): `Δψ = g`. -/
theorem laplacian_logPotentialReal_of_smooth {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) : Δ (Multipole.logPotentialReal g) = g :=
  BSSmoothH.laplacian_logPotentialReal hg hgc

/-- `lem:BS-basic`(d): `div u = 0` and `∂₁u₂ - ∂₂u₁ = g` (classical derivatives, everywhere). -/
theorem divergence_curl_velocity_of_smooth {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) :
    (∀ x, Prelim.divergence (velocity g) x = 0) ∧ ∀ x, Prelim.curl (velocity g) x = g x :=
  ⟨BSSmoothH.divergence_velocity hg hgc, BSSmoothH.curl_velocity hg hgc⟩

/-- `lem:BS-basic`(d): `∂^γ u ∈ L² ∩ L^∞` for `|γ| ≥ 1`. -/
theorem memLp_partialD_velocity_of_smooth {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) {γ : ℕ × ℕ} (hγ : 1 ≤ γ.1 + γ.2) :
    MemLp (Sob.partialD γ (velocity g)) 2 volume ∧ MemLp (Sob.partialD γ (velocity g)) ⊤ volume := by
  have hne : Sob.pdList γ ≠ [] := by
    intro h
    have := Sob.pdList_length γ
    rw [h, List.length_nil] at this
    omega
  exact memLp_iterDirDeriv_velocity hg hgc hne

/-- `lem:BS-basic`(d): `Σ_{i,l=1}^2 ‖∂_l ∂^γ u_i‖²_{L²} = ‖∂^γ g‖²_{L²}` for every `γ` (the sum
over `i` is the complex modulus of `∂_l ∂^γ u`; each `∂_l ∂^γ u` lies in `L²`). -/
theorem sum_l2_pd_partialD_velocity_of_smooth {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (γ : ℕ × ℕ) :
    (∀ l : Fin 2, MemLp (Prelim.pd l (Sob.partialD γ (velocity g))) 2 volume) ∧
      ∑ l : Fin 2, Sob.l2 (Prelim.pd l (Sob.partialD γ (velocity g))) ^ 2 =
        Sob.l2 (Sob.partialD γ (fun y => (g y : ℂ))) ^ 2 := by
  obtain ⟨h, hh, hhc, h1, h2⟩ := BSSmoothH.iterDirDeriv_velocity (Sob.pdList γ) hg hgc
  have e1 : Sob.partialD γ (velocity g) = velocity h := h1
  have e2 : Sob.partialD γ (fun y => (g y : ℂ)) = fun y => (h y : ℂ) := h2
  rw [e1, e2]
  exact ⟨fun l => (BSSmoothH.memLp_fderiv_velocity hh hhc (Prelim.e2 l)).1,
    BSSmoothH.sum_l2_pd_velocity hh hhc⟩

/-- `lem:BS-basic`(d): `∇u ∈ H^k` and `‖∇u‖_{H^k} = ‖g‖_{H^k}` for every integer `k ≥ 0` (weak
derivatives). -/
theorem gradNormH_velocity_of_smooth {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (k : ℕ) :
    Prelim.HasGradH k (velocity g) ∧
      Prelim.gradNormH k (velocity g) = Sob.normH k (fun y => (g y : ℂ)) := by
  have hu : ContDiff ℝ ∞ (velocity g) := BSSmoothH.contDiff_velocity hg hgc
  constructor
  · refine ⟨fun l => ⟨Sob.iterDirDeriv [Prelim.e2 l] (velocity g), ?_,
      BSSmoothH.hasWeakDerivOn_univ_of_smooth hu _⟩⟩
    have hG := BSSmoothH.contDiff_iterDirDeriv hu [Prelim.e2 l]
    refine (Sob.memHOn_of_contDiffOn isOpen_univ
      (BSSmoothH.contDiffOn_nat_of_smooth hG k univ) fun γ _ => ?_).1
    rw [Measure.restrict_univ, Sob.partialD, ← Sob.iterDirDeriv_append]
    exact (memLp_iterDirDeriv_velocity hg hgc (by simp)).1
  · have hgC : ContDiff ℝ ∞ (fun y => (g y : ℂ)) := BSSmoothH.contDiff_ofReal_comp hg
    rw [(Sob.memH_of_contDiff_hasCompactSupport hgC
      (BSSmoothH.hasCompactSupport_ofReal_comp hgc) k).2.2, Prelim.gradNormH,
      BSSmoothH.normH_weakPartial_eq_of_smooth hu 0 Prelim.pdList_one_zero,
      BSSmoothH.normH_weakPartial_eq_of_smooth hu 1 Prelim.pdList_zero_one,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun γ _ => ?_
    have := (sum_l2_pd_partialD_velocity_of_smooth hg hgc γ).2
    rw [Fin.sum_univ_two] at this
    exact this

end NonUniqueEuler.BS
