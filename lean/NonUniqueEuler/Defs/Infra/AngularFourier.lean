import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import NonUniqueEuler.Defs.Infra.Polar
import NonUniqueEuler.Defs.Infra.SobolevOneD

/-!
# Angular Fourier decomposition on the plane (definitions; library I-ANG)

Manuscript-independent infrastructure (library I-ANG). Manuscript: `02_prelim.tex:26-35` (angular
sectors, `g = ∑ g_ℓ e^{iℓθ}` in `L²`, `m`-fold symmetry iff `g_ℓ = 0` for `ℓ ∉ mℤ`) and
`04_ring.tex:174-185` (sector profiles, `P_ℓ w = (2π)⁻¹ ∫₀^{2π} e^{-iℓφ} w ∘ O_φ dφ`).

The angular sector `g_ℓ(r) = (2π)⁻¹ ∫₀^{2π} g(re^{iθ}) e^{-iℓθ} dθ` is `Polar.angularSector`
(library I-POLAR, `Defs/Infra/Polar.lean`); it is not redefined here.

Definitions (namespace `NonUniqueEuler.Ang`).
* `angPhase ℓ x = (x/|x|)^ℓ`, i.e. `e^{iℓθ}` at `x = re^{iθ}` (value `0^ℓ` at `x = 0`);
* `ofProfile ℓ h x = h(|x|) e^{iℓθ}`: the sector function with radial profile `h : ℝ → ℂ`;
* `sectorProj ℓ g x = (2π)⁻¹ ∫₀^{2π} e^{-iℓφ} g(O_φ x) dφ`: the sector projection `P_ℓ`
  (pointwise, by rotations; `= g_ℓ(|x|) e^{iℓθ}` for `x ≠ 0`, `I/Infra/AngularFourier/Sector`);
* `IsSectorFn ℓ g`: `g ∘ O_θ = e^{iℓθ} g` a.e., for every `θ` (the functions `g_ℓ(r)e^{iℓθ}`);
* `IsMFoldSymmetricC m g`: complex-valued version of the statement layer's
  `IsMFoldSymmetric` (`isMFoldSymmetric_iff_C` relates them);
* `thetaDeriv g = -x₂ ∂₁g + x₁ ∂₂g` (weak `∂_θ`) and `radDeriv g = cos θ ∂₁g + sin θ ∂₂g`
  (weak `∂_r`), `04_ring.tex:851-853`;
* `rotLp θ`: `g ↦ g ∘ O_θ` on `L²(ℂ)`, a linear isometry (`Lp.compMeasurePreservingₗᵢ`);
* `sectorProjL ℓ`: `P_ℓ` as a continuous linear map on `L²(ℂ)`, chosen; its specification
  `sectorProjL_spec` is in `I/Infra/AngularFourier/Sector.lean`.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang

/-- `e^{iℓθ}` at `x = r e^{iθ}`, written `(x/|x|)^ℓ`. -/
def angPhase (ℓ : ℤ) (x : ℂ) : ℂ :=
  (x / (‖x‖ : ℂ)) ^ ℓ

/-- The sector function `h(|x|) e^{iℓθ}` with radial profile `h`. -/
def ofProfile (ℓ : ℤ) (h : ℝ → ℂ) (x : ℂ) : ℂ :=
  h ‖x‖ * angPhase ℓ x

/-- The sector projection `P_ℓ g (x) = (2π)⁻¹ ∫₀^{2π} e^{-iℓφ} g(O_φ x) dφ`
(`04_ring.tex:181`). -/
def sectorProj (ℓ : ℤ) (g : ℂ → ℂ) (x : ℂ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..2 * π,
    Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * g (rot φ x)

/-- `g` is a sector-`ℓ` function: `g ∘ O_θ = e^{iℓθ} g` almost everywhere, for every `θ`. -/
def IsSectorFn (ℓ : ℤ) (g : ℂ → ℂ) : Prop :=
  ∀ θ : ℝ, (fun x => g (rot θ x)) =ᵐ[volume] fun x => Complex.exp ((ℓ : ℂ) * θ * Complex.I) * g x

/-- `m`-fold symmetry of a complex-valued function: `g ∘ O_{2π/m} = g` almost everywhere. -/
def IsMFoldSymmetricC (m : ℕ) (g : ℂ → ℂ) : Prop :=
  (fun x => g (rot (2 * π / m) x)) =ᵐ[volume] g

/-- The weak angular derivative `∂_θ g = -x₂ ∂₁g + x₁ ∂₂g`. -/
def thetaDeriv (g : ℂ → ℂ) (x : ℂ) : ℂ :=
  (x.re : ℂ) * Sob.weakPartial (0, 1) g x - (x.im : ℂ) * Sob.weakPartial (1, 0) g x

/-- The weak radial derivative `∂_r g = cos θ ∂₁g + sin θ ∂₂g` (for `x ≠ 0`). -/
def radDeriv (g : ℂ → ℂ) (x : ℂ) : ℂ :=
  ((x.re / ‖x‖ : ℝ) : ℂ) * Sob.weakPartial (1, 0) g x +
    ((x.im / ‖x‖ : ℝ) : ℂ) * Sob.weakPartial (0, 1) g x

/-- The rotation `g ↦ g ∘ O_θ` on `L²(ℂ)`. -/
def rotLp (θ : ℝ) : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (rot θ) (Polar.measurePreserving_rot θ)).toContinuousLinearMap

open Classical in
/-- `P_ℓ` as a continuous linear map on `L²(ℂ)` (chosen; `0` if no such map existed — it does,
`sectorProjL_spec`). -/
def sectorProjL (ℓ : ℤ) : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  if h : ∃ P : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ),
      ∀ f, (P f : ℂ → ℂ) =ᵐ[volume] sectorProj ℓ f then h.choose else 0

/-! ### Basic lemmas (fully proved) -/

@[simp] theorem angPhase_zero (x : ℂ) : angPhase 0 x = 1 := by
  simp [angPhase]

theorem norm_angPhase {x : ℂ} (hx : x ≠ 0) (ℓ : ℤ) : ‖angPhase ℓ x‖ = 1 := by
  have h1 : ‖x / (‖x‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hx)]
  rw [angPhase, norm_zpow, h1, one_zpow]

theorem rotLp_coeFn (θ : ℝ) (f : Lp ℂ 2 (volume : Measure ℂ)) :
    (rotLp θ f : ℂ → ℂ) =ᵐ[volume] fun x => f (rot θ x) :=
  Lp.coeFn_compMeasurePreserving f (Polar.measurePreserving_rot θ)

theorem norm_rotLp_apply (θ : ℝ) (f : Lp ℂ 2 (volume : Measure ℂ)) : ‖rotLp θ f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (Polar.measurePreserving_rot θ)

theorem isMFoldSymmetric_iff_C (m : ℕ) (g : ℂ → ℝ) :
    IsMFoldSymmetric m g ↔ IsMFoldSymmetricC m (fun x => (g x : ℂ)) := by
  constructor
  · intro h
    filter_upwards [h] with x hx
    simp [hx]
  · intro h
    filter_upwards [h] with x hx
    exact_mod_cast hx

@[simp] theorem ofProfile_zero_profile (ℓ : ℤ) : ofProfile ℓ (fun _ => 0) = fun _ => 0 := by
  funext x
  simp [ofProfile]

end NonUniqueEuler.Ang
