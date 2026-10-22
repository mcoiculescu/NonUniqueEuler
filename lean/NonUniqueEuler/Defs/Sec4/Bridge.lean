import NonUniqueEuler.Defs.Infra.SectorSpace
import NonUniqueEuler.Defs.Infra.Dunford

/-!
# Section 4: generic bridges used by the linear theory (definitions)

Small manuscript-independent helpers that the Section 4 objects need and that the libraries
I-SECT (`Defs/Infra/SectorSpace.lean`) and I-DUNF (`Defs/Infra/Dunford.lean`) do not provide.
They are declared in those libraries' namespaces (new names only; nothing is redefined):

* `Sect.toY s K f : Y s K`: the element of `Y^s(K)` whose function is `f` (chosen, `0` if `f`
  is not the function of an element, i.e. unless `f ∈ H^s` vanishes a.e. off `K`);
* `Sect.toYsec s K ℓ f : Ysec s K ℓ`: the same in the sector space `Y^s_ℓ(K)`;
* `Sect.Y.IsReal w`, `Sect.Ysec.IsReal g`: the function is real valued almost everywhere
  (the manuscript's "real-valued `w`", e.g. `prop:semigroup`, `lem:duhamel`);
* `Dunford.IsAlgSimpleEig A z₀`: `z₀` is an algebraically simple eigenvalue of the bounded
  operator `A`, in the form of restructuring R2: its spectral
  projection is a rank-one projection `x ↦ f(x) g` with `f g = 1`, given in the Laurent form
  `IsSimpleSpectralProj`. Manuscript: the definition of algebraic multiplicity by the rank of the
  Riesz projection (`04_ring.tex:355-364`). For an isolated point `z₀` of the spectrum this is
  equivalent to "the Riesz projection at `z₀` has rank one": on a punctured disk the resolvent
  minus `(z - z₀)⁻¹ P` is holomorphic and bounded, so its singularity is removable and the Riesz
  projection `(2πi)⁻¹ ∮ (z - A)⁻¹ dz` equals `P`.

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler

namespace Sect

open Classical in
/-- The element of `Y^s(K)` with function `f` (chosen; `0` if there is none). -/
def toY (s : ℕ) (K : Set ℂ) (f : ℂ → ℂ) : Y s K :=
  if h : ∃ w : Y s K, w.fn =ᵐ[volume] f then h.choose else 0

open Classical in
/-- The element of the sector space `Y^s_ℓ(K)` with function `f` (chosen; `0` if there is
none). -/
def toYsec (s : ℕ) (K : Set ℂ) (ℓ : ℤ) (f : ℂ → ℂ) : Ysec s K ℓ :=
  if h : ∃ g : Ysec s K ℓ, g.fn =ᵐ[volume] f then h.choose else 0

/-- `w ∈ Y^s(K)` is real valued (almost everywhere). -/
def Y.IsReal {s : ℕ} {K : Set ℂ} (w : Y s K) : Prop :=
  ∀ᵐ x ∂(volume : Measure ℂ), (w.fn x).im = 0

/-- `g ∈ Y^s_ℓ(K)` is real valued (almost everywhere); only `g = 0` qualifies when `ℓ ≠ 0`. -/
def Ysec.IsReal {s : ℕ} {K : Set ℂ} {ℓ : ℤ} (g : Ysec s K ℓ) : Prop :=
  ∀ᵐ x ∂(volume : Measure ℂ), (g.fn x).im = 0

theorem toY_spec {s : ℕ} {K : Set ℂ} {f : ℂ → ℂ} (h : ∃ w : Y s K, w.fn =ᵐ[volume] f) :
    (toY s K f).fn =ᵐ[volume] f := by
  classical
  rw [toY, dite_eq_left h]
  exact h.choose_spec

theorem toYsec_spec {s : ℕ} {K : Set ℂ} {ℓ : ℤ} {f : ℂ → ℂ}
    (h : ∃ g : Ysec s K ℓ, g.fn =ᵐ[volume] f) : (toYsec s K ℓ f).fn =ᵐ[volume] f := by
  classical
  rw [toYsec, dite_eq_left h]
  exact h.choose_spec

end Sect

namespace Dunford

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- `z₀` is an algebraically simple eigenvalue of `A` (restructuring R2): there are `f : X →L ℂ`
and `g : X` with `f g = 1` such that the rank-one projection `x ↦ f(x) g` is the spectral
projection of `A` at `z₀` in the Laurent form `IsSimpleSpectralProj` (`04_ring.tex:355-364`,
`thm:evans-simple`(2), `04_ring.tex:462-469`). -/
def IsAlgSimpleEig (A : X →L[ℂ] X) (z₀ : ℂ) : Prop :=
  ∃ (f : X →L[ℂ] ℂ) (g : X), f g = 1 ∧ IsSimpleSpectralProj A (rankOneProj f g) z₀

/-- An algebraically simple eigenvalue is an eigenvalue: `A g = z₀ g` with `g ≠ 0`. -/
theorem IsAlgSimpleEig.exists_eigenvector {A : X →L[ℂ] X} {z₀ : ℂ}
    (h : IsAlgSimpleEig A z₀) : ∃ g : X, g ≠ 0 ∧ A g = z₀ • g := by
  obtain ⟨f, g, hfg, hP⟩ := h
  refine ⟨g, ?_, ?_⟩
  · rintro rfl
    simp at hfg
  · have h1 := congrArg (fun T : X →L[ℂ] X => T g) hP.mul_proj
    simpa [hfg] using h1

end Dunford

end NonUniqueEuler
