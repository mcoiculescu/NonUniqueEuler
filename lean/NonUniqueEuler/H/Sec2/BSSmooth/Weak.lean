import NonUniqueEuler.Defs.Sec2.Conventions
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helper for `lem:BS-basic`(d): weak derivatives of smooth functions

Helper of `P/Sec2/BSSmooth.lean`. For `u ∈ C^∞(ℝ²; ℂ)` the chosen weak derivatives on the plane
are the classical ones a.e., also after an a.e. modification of `u`, and classical derivatives
in permuted directions agree a.e. (uniqueness of weak derivatives).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal

namespace NonUniqueEuler.BSSmoothH

theorem contDiff_iterDirDeriv {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u) (vs : List ℂ) :
    ContDiff ℝ ∞ (Sob.iterDirDeriv vs u) := by
  induction vs with
  | nil => simpa using hu
  | cons v vs ih =>
    rw [Sob.iterDirDeriv_cons]
    exact (ih.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

theorem contDiffOn_nat_of_smooth {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u) (n : ℕ) (V : Set ℂ) :
    ContDiffOn ℝ n u V :=
  (hu.of_le (by exact_mod_cast le_top)).contDiffOn

theorem locallyIntegrableOn_of_continuous {u : ℂ → ℂ} (hu : Continuous u) (V : Set ℂ) :
    LocallyIntegrableOn u V volume :=
  hu.locallyIntegrable.locallyIntegrableOn V

/-- Classical derivatives of a smooth function are weak derivatives on the plane. -/
theorem hasWeakDerivOn_univ_of_smooth {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u) (vs : List ℂ) :
    Sob.HasWeakDerivOn univ vs u (Sob.iterDirDeriv vs u) :=
  Sob.hasWeakDerivOn_of_contDiffOn isOpen_univ le_rfl (contDiffOn_nat_of_smooth hu _ _)

/-- Classical derivatives of a smooth function commute (a.e.). -/
theorem iterDirDeriv_perm_ae {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u) {vs ws : List ℂ}
    (hp : vs.Perm ws) : Sob.iterDirDeriv vs u =ᵐ[volume] Sob.iterDirDeriv ws u := by
  have h1 := hasWeakDerivOn_univ_of_smooth hu vs
  have h2 := (hasWeakDerivOn_univ_of_smooth hu ws).perm hp.symm
  have := Sob.HasWeakDerivOn.ae_eq isOpen_univ
    (locallyIntegrableOn_of_continuous (contDiff_iterDirDeriv hu vs).continuous _)
    (locallyIntegrableOn_of_continuous (contDiff_iterDirDeriv hu ws).continuous _) h1 h2
  filter_upwards [this] with x hx using hx (mem_univ x)

/-- The chosen weak derivative of an a.e. modification of a smooth `G` is the classical one. -/
theorem weakDerivOn_univ_ae_eq_of_ae_eq_smooth {W G : ℂ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hWG : W =ᵐ[volume] G) (vs : List ℂ) :
    Sob.weakDerivOn univ vs W =ᵐ[volume] Sob.iterDirDeriv vs G := by
  have h1 := hasWeakDerivOn_univ_of_smooth hG vs
  have h2 : Sob.HasWeakDerivOn univ vs W (Sob.iterDirDeriv vs G) := by
    refine h1.congr_ae ?_ (Eventually.of_forall fun x _ => rfl)
    filter_upwards [hWG] with x hx _ using hx.symm
  have := Sob.weakDerivOn_ae_eq isOpen_univ
    (locallyIntegrableOn_of_continuous (contDiff_iterDirDeriv hG vs).continuous _) h2
  filter_upwards [this] with x hx using hx (mem_univ x)

/-- `‖∂_l u‖_{H^k}` (weak derivatives) computed with classical derivatives of a smooth `u`:
`Σ_{|γ| ≤ k} ‖∂_l ∂^γ u‖²_{L²}`. -/
theorem normH_weakPartial_eq_of_smooth {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u) (l : Fin 2)
    {γ₀ : ℕ × ℕ} (hγ₀ : Sob.pdList γ₀ = [Prelim.e2 l]) (k : ℕ) :
    Sob.normH k (Sob.weakPartial γ₀ u) =
      Real.sqrt (∑ γ ∈ Sob.multiIdx k, Sob.l2 (Prelim.pd l (Sob.partialD γ u)) ^ 2) := by
  have hG : ContDiff ℝ ∞ (Sob.iterDirDeriv [Prelim.e2 l] u) := contDiff_iterDirDeriv hu _
  have hW : Sob.weakPartial γ₀ u =ᵐ[volume] Sob.iterDirDeriv [Prelim.e2 l] u := by
    have := weakDerivOn_univ_ae_eq_of_ae_eq_smooth hu (EventuallyEq.refl _ u) [Prelim.e2 l]
    simpa [Sob.weakPartial, Sob.weakPartialOn, hγ₀] using this
  rw [Sob.normH_eq]
  congr 1
  refine Finset.sum_congr rfl fun γ _ => ?_
  congr 1
  have h1 : Sob.weakPartial γ (Sob.weakPartial γ₀ u) =ᵐ[volume]
      Sob.iterDirDeriv (Sob.pdList γ) (Sob.iterDirDeriv [Prelim.e2 l] u) :=
    weakDerivOn_univ_ae_eq_of_ae_eq_smooth hG hW _
  rw [← Sob.iterDirDeriv_append] at h1
  have h2 := iterDirDeriv_perm_ae hu (List.perm_append_singleton (Prelim.e2 l) (Sob.pdList γ))
  have h3 := h1.trans h2
  unfold Sob.l2
  rw [eLpNorm_congr_ae h3]
  rfl

end NonUniqueEuler.BSSmoothH
