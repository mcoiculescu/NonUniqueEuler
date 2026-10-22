import NonUniqueEuler.Defs.Sec4.Bridge
import NonUniqueEuler.I.Sec4.RieszFixes
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Helper for `thm:evans-simple`: an abstract criterion for a simple isolated eigenvalue

Helper of `P/Sec4/EvansSimple.lean` (fully proved; manuscript-independent functional analysis).
Namespace `NonUniqueEuler.EvansSimpleAux`.

Restructured proof of `thm:evans-simple`(2) (deviation from the manuscript's contour-integral
computation): for a bounded operator `A` on a complex Banach space,
an eigenvector `g` (`A g = z₀ g`), a functional `f` with `f g = 1` and `f ∘ A = z₀ f`, a
one-dimensional eigenspace and the solvability `ran (A - z₀) ⊇ ker f`, the rank-one operator
`P = f(·) g` is the spectral projection at `z₀` in the Laurent form
`Dunford.IsSimpleSpectralProj`.

Proof. `B = A - P` commutes with `P`, and `z₀ - B = z₀ - A + P` is bijective (injective: apply
`f`, then use the eigenspace; surjective: `y - f(y) g ∈ ker f` is in the range of `z₀ - A`), hence
invertible (open mapping). For `w ∈ ρ(B)`, `w ≠ z₀`,
`(w - A)⁻¹ = (w - B)⁻¹(1 - P) + (w - z₀)⁻¹ P`, and `(w - B)⁻¹(1 - P)` is continuous at `z₀`.

* `isSimpleSpectralProj_of_range`, `isAlgSimpleEig_of_range`: the criterion;
* `not_isAlgSimpleEig_of_genEigen`: a generalized eigenvector `g₁`, `(A - z₀)g₁ = g_* ≠ 0`,
  `(A - z₀) g_* = 0`, excludes algebraic simplicity (`thm:evans-simple`(3), with
  `RieszFixes`).
-/

noncomputable section

open Filter Topology

namespace NonUniqueEuler.EvansSimpleAux

open Dunford

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem algebraMap_clm (w : ℂ) : algebraMap ℂ (X →L[ℂ] X) w = w • (1 : X →L[ℂ] X) :=
  Algebra.algebraMap_eq_smul_one w

/-- Algebraic identities for `P = f(·) g`, `B = A - P`. -/
theorem rankOne_facts {A : X →L[ℂ] X} {z₀ : ℂ} {f : X →L[ℂ] ℂ} {g : X}
    (hfg : f g = 1) (hAg : A g = z₀ • g) (hfA : ∀ x, f (A x) = z₀ * f x) :
    rankOneProj f g * rankOneProj f g = rankOneProj f g ∧
      A * rankOneProj f g = z₀ • rankOneProj f g ∧
      rankOneProj f g * A = z₀ • rankOneProj f g := by
  refine ⟨rankOneProj_mul_self hfg, mul_rankOneProj hAg, rankOneProj_mul ?_⟩
  ext x
  simp [hfA]

variable [CompleteSpace X]

/-- `z₀ - (A - P)` is invertible. -/
theorem isUnit_sub_deflate {A : X →L[ℂ] X} {z₀ : ℂ} {f : X →L[ℂ] ℂ} {g : X}
    (hfg : f g = 1) (hAg : A g = z₀ • g) (hfA : ∀ x, f (A x) = z₀ * f x)
    (hker : ∀ x, A x = z₀ • x → ∃ c : ℂ, x = c • g)
    (hrange : ∀ h, f h = 0 → ∃ x, A x - z₀ • x = h) :
    IsUnit (algebraMap ℂ (X →L[ℂ] X) z₀ - (A - rankOneProj f g)) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have happ : ∀ x, (algebraMap ℂ (X →L[ℂ] X) z₀ - (A - rankOneProj f g)) x =
      z₀ • x - A x + f x • g := by
    intro x
    rw [algebraMap_clm]
    simp only [sub_apply, smul_apply, one_apply_eq_self, rankOneProj_apply]
    abel
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [happ] at hx
    have h1 := congrArg f hx
    simp only [map_add, map_sub, map_smul, hfA, hfg, smul_eq_mul, mul_one, map_zero] at h1
    have hfx : f x = 0 := by linear_combination h1
    rw [hfx, zero_smul, add_zero, sub_eq_zero] at hx
    obtain ⟨c, rfl⟩ := hker x hx.symm
    simp only [map_smul, hfg, smul_eq_mul, mul_one] at hfx
    rw [hfx, zero_smul]
  · intro y
    have hh : f (y - f y • g) = 0 := by simp [hfg]
    obtain ⟨x, hx⟩ := hrange _ hh
    refine ⟨-x + (f x + f y) • g, ?_⟩
    rw [happ]
    have hfx' : f (-x + (f x + f y) • g) = f y := by simp [hfg]
    rw [hfx']
    simp only [smul_add, map_add, map_neg, map_smul, hAg, smul_neg, smul_smul]
    linear_combination (norm := module) hx

/-- **The criterion** (restructured `thm:evans-simple`(2)). -/
theorem isSimpleSpectralProj_of_range {A : X →L[ℂ] X} {z₀ : ℂ} {f : X →L[ℂ] ℂ} {g : X}
    (hfg : f g = 1) (hAg : A g = z₀ • g) (hfA : ∀ x, f (A x) = z₀ * f x)
    (hker : ∀ x, A x = z₀ • x → ∃ c : ℂ, x = c • g)
    (hrange : ∀ h, f h = 0 → ∃ x, A x - z₀ • x = h) :
    IsSimpleSpectralProj A (rankOneProj f g) z₀ := by
  obtain ⟨hPP, hAP, hPA⟩ := rankOne_facts hfg hAg hfA
  set P := rankOneProj f g with hPdef
  set B : X →L[ℂ] X := A - P with hBdef
  have hu : z₀ ∈ resolventSet ℂ B :=
    spectrum.mem_resolventSet_iff.2 (isUnit_sub_deflate hfg hAg hfA hker hrange)
  have hnhds : resolventSet ℂ B ∈ 𝓝 z₀ := (spectrum.isOpen_resolventSet B).mem_nhds hu
  -- `P` commutes with `w - B`
  have hcomm : ∀ w : ℂ, P * (algebraMap ℂ _ w - B) = (algebraMap ℂ _ w - B) * P := by
    intro w
    rw [algebraMap_clm, hBdef, mul_sub, sub_mul, mul_sub, sub_mul, hPA, hAP, hPP,
      mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  -- the key identity on `ρ(B) \ {z₀}`
  have hkey : ∀ w : ℂ, w ∈ resolventSet ℂ B → w ≠ z₀ →
      w ∈ resolventSet ℂ A ∧
        resolvent A w = resolvent B w * (1 - P) + (w - z₀)⁻¹ • P := by
    intro w hw hwz
    have hwu := spectrum.mem_resolventSet_iff.1 hw
    set Q := resolvent B w with hQdef
    have hQ1 : (algebraMap ℂ _ w - B) * Q = 1 := Ring.mul_inverse_cancel _ hwu
    have hQ2 : Q * (algebraMap ℂ _ w - B) = 1 := Ring.inverse_mul_cancel _ hwu
    have hPQ : P * Q = Q * P := by
      calc P * Q = Q * (algebraMap ℂ _ w - B) * P * Q := by rw [hQ2, one_mul]
        _ = Q * ((algebraMap ℂ _ w - B) * P) * Q := by rw [mul_assoc Q]
        _ = Q * (P * (algebraMap ℂ _ w - B)) * Q := by rw [hcomm]
        _ = Q * P * ((algebraMap ℂ _ w - B) * Q) := by simp only [mul_assoc]
        _ = Q * P := by rw [hQ1, mul_one]
    have hwA : algebraMap ℂ (X →L[ℂ] X) w - A = (algebraMap ℂ _ w - B) - P := by
      rw [hBdef]; abel
    have hne : w - z₀ ≠ 0 := sub_ne_zero.2 hwz
    have hAPw : (algebraMap ℂ (X →L[ℂ] X) w - A) * P = (w - z₀) • P := by
      rw [algebraMap_clm, sub_mul, hAP, smul_mul_assoc, one_mul, sub_smul]
    have hPAw : P * (algebraMap ℂ (X →L[ℂ] X) w - A) = (w - z₀) • P := by
      rw [algebraMap_clm, mul_sub, hPA, mul_smul_comm, mul_one, sub_smul]
    set T := Q * (1 - P) + (w - z₀)⁻¹ • P with hTdef
    have hT1 : (algebraMap ℂ (X →L[ℂ] X) w - A) * T = 1 := by
      rw [hTdef, mul_add, mul_smul_comm, hAPw, smul_smul, inv_mul_cancel₀ hne, one_smul, hwA,
        sub_mul, ← mul_assoc, hQ1, one_mul, ← mul_assoc, hPQ, mul_assoc, mul_sub, mul_one, hPP,
        sub_self, mul_zero, sub_zero, sub_add_cancel]
    have hT2 : T * (algebraMap ℂ (X →L[ℂ] X) w - A) = 1 := by
      have h1 : (1 - P) * (algebraMap ℂ (X →L[ℂ] X) w - A) =
          (algebraMap ℂ _ w - B) * (1 - P) := by
        rw [hwA]
        set wB := algebraMap ℂ (X →L[ℂ] X) w - B with hwB
        calc (1 - P) * (wB - P) = wB - P * wB - (P - P * P) := by noncomm_ring
          _ = wB - wB * P := by rw [hPP, sub_self, sub_zero, hcomm]
          _ = wB * (1 - P) := by noncomm_ring
      rw [hTdef, add_mul, smul_mul_assoc, hPAw, smul_smul, inv_mul_cancel₀ hne, one_smul,
        mul_assoc, h1, ← mul_assoc, hQ2, one_mul, sub_add_cancel]
    let u : (X →L[ℂ] X)ˣ := ⟨algebraMap ℂ _ w - A, T, hT1, hT2⟩
    refine ⟨spectrum.mem_resolventSet_iff.2 ⟨u, rfl⟩, ?_⟩
    rw [resolvent, show algebraMap ℂ (X →L[ℂ] X) w - A = (u : X →L[ℂ] X) from rfl,
      Ring.inverse_unit]
    rfl
  refine ⟨hPP, hAP, hPA, ?_, ?_⟩
  · filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with w hw hwz
    exact (hkey w hw hwz).1
  · refine ⟨resolvent B z₀ * (1 - P), ?_⟩
    have hcont : ContinuousAt (fun w => resolvent B w * (1 - P)) z₀ := by
      obtain ⟨u, hu'⟩ := spectrum.mem_resolventSet_iff.1 hu
      have h1 : ContinuousAt (fun w : ℂ => algebraMap ℂ (X →L[ℂ] X) w - B) z₀ := by
        simp only [algebraMap_clm]
        fun_prop
      have h2 : ContinuousAt (fun w => resolvent B w) z₀ := by
        have h3 : ContinuousAt Ring.inverse (algebraMap ℂ (X →L[ℂ] X) z₀ - B) := by
          rw [← hu']
          exact NormedRing.inverse_continuousAt u
        exact ContinuousAt.comp (g := Ring.inverse)
          (f := fun w : ℂ => algebraMap ℂ (X →L[ℂ] X) w - B) h3 h1
      exact h2.mul continuousAt_const
    refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with w hw hwz
    rw [(hkey w hw hwz).2]
    abel

/-- The criterion, as algebraic simplicity. -/
theorem isAlgSimpleEig_of_range {A : X →L[ℂ] X} {z₀ : ℂ} {f : X →L[ℂ] ℂ} {g : X}
    (hfg : f g = 1) (hAg : A g = z₀ • g) (hfA : ∀ x, f (A x) = z₀ * f x)
    (hker : ∀ x, A x = z₀ • x → ∃ c : ℂ, x = c • g)
    (hrange : ∀ h, f h = 0 → ∃ x, A x - z₀ • x = h) :
    IsAlgSimpleEig A z₀ :=
  ⟨f, g, hfg, isSimpleSpectralProj_of_range hfg hAg hfA hker hrange⟩

omit [CompleteSpace X] in
/-- A generalized eigenvector excludes algebraic simplicity (`thm:evans-simple`(3),
`04_ring.tex:556-560`). -/
theorem not_isAlgSimpleEig_of_genEigen {A : X →L[ℂ] X} {z₀ : ℂ} {g₁ gs : X} (hgs : gs ≠ 0)
    (hAgs : A gs = z₀ • gs) (h₁ : A g₁ - z₀ • g₁ = gs) : ¬ IsAlgSimpleEig A z₀ := by
  rintro ⟨f, g, hfg, hP⟩
  have hsq : ((A - z₀ • (1 : X →L[ℂ] X)) ^ 2) g₁ = 0 := by
    rw [pow_two, mul_apply_eq_comp]
    have : (A - z₀ • (1 : X →L[ℂ] X)) g₁ = gs := by simpa using h₁
    rw [this]
    simp [hAgs]
  have hfix := hP.apply_eq_self_of_pow_apply_eq_zero hsq
  rw [rankOneProj_apply] at hfix
  have hAg : A g = z₀ • g := by
    have h1 := congrArg (fun T : X →L[ℂ] X => T g) hP.mul_proj
    simpa [hfg] using h1
  apply hgs
  rw [← h₁, ← hfix, map_smul, hAg, smul_comm, sub_self]

end NonUniqueEuler.EvansSimpleAux
