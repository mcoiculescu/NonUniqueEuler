import NonUniqueEuler.Defs.Sec3.Auxiliary
import NonUniqueEuler.Defs.Infra.Sobolev
import NonUniqueEuler.Defs.Sec2.Conventions

/-!
# Section 3: divergence-free Sobolev fields and the commutator `C_ε[u, w]`

Manuscript sources: the commutator and eq:comm-formula (`03_compactness.tex:342-363`),
`lem:commutator` (`03_compactness.tex:365-372`), `lem:transport` (`03_compactness.tex:463-478`),
and the convention for `W^{1,a}` in time-dependent spaces (`02_prelim.tex:109-113`: "a space
with `W^{1,a}(Ω)` in place of `L^b(Ω)` consists of the `w` for which `w` and its distributional
gradient in `x` lie in the corresponding space with `L^a(Ω)`").

Exponents (R7, D9): only `a = 2` is formalized; `W^{1,2}(B_R) = H¹(B_R)` is the I-HK predicate
`Sob.MemHOn 1 (ball 0 R)` applied to the field `w t : ℂ → ℂ` (a real vector field written in
`ℂ`), with norm `Sob.normHOn 1 (ball 0 R) (w t)`; `div w = 0` is `Prelim.IsWeaklyDivFree`.

* `IsLocH1DivFreeField I w`: `w ∈ L¹_loc(I; W^{1,2}_loc(ℝ²; ℝ²))` and `div w = 0`
  (`lem:commutator`, `a = 2`).
* `IsBddH1DivFreeField I w`: `w ∈ L^∞(I; W^{1,2}_loc)` and `div w = 0` (`lem:transport`, `a = 2`).
  `IsBddH1DivFreeField.isLocH1DivFreeField` (proved) gives the first from the second.
* `dotGradMollify ρ ε u w t x = w(t,x) · ∇(u(t) ⋆ ρ_ε)(x)`, written as the integral
  `∫ u(t,y) w(t,x) · ∇ρ_ε(x - y) dy` (`03_compactness.tex:349-351`);
  `mollifyDiv ρ ε u w t x = (div(wu)) ⋆ ρ_ε (t,x) = ∫ (wu)(t,y) · ∇ρ_ε(x - y) dy`
  (`03_compactness.tex:348`); `commEps ρ ε u w = dotGradMollify - mollifyDiv`
  (`03_compactness.tex:346`).

The commutator is defined for any kernel `ρ` (use `rho`, or any `ρ` with `IsMollifier ρ`), with
`ρ_ε = scaled ρ ε`. Defining the first term by its integral formula (rather than as
`fderiv ℝ (mollify ρ ε (u t)) x (w t x)`) is the manuscript's own rewriting
(`03_compactness.tex:349-351`); the two agree wherever differentiation under the integral sign
is justified (`u(t) ∈ L¹_loc`), which is a lemma for the interface layer.

All lemmas in this file are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak

/-- `w ∈ L¹_loc(I; W^{1,2}_loc(ℝ²; ℝ²))` with `div w = 0` (the field of `lem:commutator` with
`a = 2`, `03_compactness.tex:368-369`, and `02_prelim.tex:109-113`): `w` is measurable on
`I × ℝ²`; for every `R > 0` and a.e. `t ∈ I`, `w(t) ∈ H¹(B_R)`; `t ↦ ‖w(t)‖_{H¹(B_R)}` is
integrable on every compact `J ⊆ I`; and `div w(t) = 0` in `𝒟'(ℝ²)` for a.e. `t ∈ I`. -/
structure IsLocH1DivFreeField (I : Set ℝ) (w : ℝ → ℂ → ℂ) : Prop where
  aestronglyMeasurable : AEStronglyMeasurable (Function.uncurry w) (volume.restrict (I ×ˢ univ))
  memHOn : ∀ R : ℝ, 0 < R → ∀ᵐ t ∂(volume.restrict I), Sob.MemHOn 1 (ball (0 : ℂ) R) (w t)
  integrableOn_normHOn : ∀ R : ℝ, 0 < R → ∀ J ⊆ I, IsCompact J →
    IntegrableOn (fun t => Sob.normHOn 1 (ball (0 : ℂ) R) (w t)) J
  divFree : ∀ᵐ t ∂(volume.restrict I), Prelim.IsWeaklyDivFree (w t)

/-- `w ∈ L^∞(I; W^{1,2}_loc(ℝ²; ℝ²))` with `div w = 0` (the field of `lem:transport` with
`a = 2`, `03_compactness.tex:466-467`): `w` is measurable on `I × ℝ²`; for every `R > 0`,
`t ↦ ‖w(t)‖_{H¹(B_R)}` is measurable and, for a.e. `t ∈ I`, `w(t) ∈ H¹(B_R)` with
`‖w(t)‖_{H¹(B_R)} ≤ M_R`; and `div w(t) = 0` for a.e. `t ∈ I`. -/
structure IsBddH1DivFreeField (I : Set ℝ) (w : ℝ → ℂ → ℂ) : Prop where
  aestronglyMeasurable : AEStronglyMeasurable (Function.uncurry w) (volume.restrict (I ×ˢ univ))
  aestronglyMeasurable_normHOn : ∀ R : ℝ, 0 < R →
    AEStronglyMeasurable (fun t => Sob.normHOn 1 (ball (0 : ℂ) R) (w t)) (volume.restrict I)
  bound : ∀ R : ℝ, 0 < R → ∃ M : ℝ, ∀ᵐ t ∂(volume.restrict I),
    Sob.MemHOn 1 (ball (0 : ℂ) R) (w t) ∧ Sob.normHOn 1 (ball (0 : ℂ) R) (w t) ≤ M
  divFree : ∀ᵐ t ∂(volume.restrict I), Prelim.IsWeaklyDivFree (w t)

theorem IsBddH1DivFreeField.integrableOn_normHOn {I : Set ℝ} {w : ℝ → ℂ → ℂ}
    (h : IsBddH1DivFreeField I w) {R : ℝ} (hR : 0 < R) {J : Set ℝ} (hJI : J ⊆ I)
    (hJ : IsCompact J) : IntegrableOn (fun t => Sob.normHOn 1 (ball (0 : ℂ) R) (w t)) J := by
  obtain ⟨M, hM⟩ := h.bound R hR
  have : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.2 hJ.measure_lt_top.ne
  refine Integrable.of_bound ((h.aestronglyMeasurable_normHOn R hR).mono_measure
    (Measure.restrict_mono hJI le_rfl)) M ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hJI hM] with t ht
  rw [Real.norm_of_nonneg (Sob.normHOn_nonneg _ _ _)]
  exact ht.2

/-- `L^∞(I; W^{1,2}_loc) ⊆ L¹_loc(I; W^{1,2}_loc)`. -/
theorem IsBddH1DivFreeField.isLocH1DivFreeField {I : Set ℝ} {w : ℝ → ℂ → ℂ}
    (h : IsBddH1DivFreeField I w) : IsLocH1DivFreeField I w where
  aestronglyMeasurable := h.aestronglyMeasurable
  memHOn R hR := by
    obtain ⟨M, hM⟩ := h.bound R hR
    exact hM.mono fun t ht => ht.1
  integrableOn_normHOn R hR _ hJI hJ := h.integrableOn_normHOn hR hJI hJ
  divFree := h.divFree

/-- `w · ∇(u ⋆ ρ_ε)(t, x) = ∫ u(t,y) w(t,x) · ∇ρ_ε(x - y) dy` (`03_compactness.tex:349-351`). -/
def dotGradMollify (ρ : ℂ → ℝ) (ε : ℝ) (u : ℝ → ℂ → ℝ) (w : ℝ → ℂ → ℂ) (t : ℝ) (x : ℂ) : ℝ :=
  ∫ y, u t y * fderiv ℝ (scaled ρ ε) (x - y) (w t x)

/-- `(div(wu)) ⋆ ρ_ε (t, x) = ∫ (wu)(t,y) · ∇ρ_ε(x - y) dy` (`03_compactness.tex:348`). -/
def mollifyDiv (ρ : ℂ → ℝ) (ε : ℝ) (u : ℝ → ℂ → ℝ) (w : ℝ → ℂ → ℂ) (t : ℝ) (x : ℂ) : ℝ :=
  ∫ y, u t y * fderiv ℝ (scaled ρ ε) (x - y) (w t y)

/-- The commutator `C_ε[u, w] = w · ∇(u ⋆ ρ_ε) - (div(wu)) ⋆ ρ_ε` (`03_compactness.tex:342-348`),
for a kernel `ρ` (the manuscript's `ρ`: any `ρ` with `IsMollifier ρ`, e.g. `rho`). -/
def commEps (ρ : ℂ → ℝ) (ε : ℝ) (u : ℝ → ℂ → ℝ) (w : ℝ → ℂ → ℂ) (t : ℝ) (x : ℂ) : ℝ :=
  dotGradMollify ρ ε u w t x - mollifyDiv ρ ε u w t x

end NonUniqueEuler.Weak
