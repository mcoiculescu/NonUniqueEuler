import NonUniqueEuler.Statement.Plane
import NonUniqueEuler.Defs.Infra.Polar
import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.Defs.Infra.SectorSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Part I Section 4.2: the sector setting (definitions)

Manuscript Part I Definition 4.3 (`def:sector-setting`)
(`def:sector-setting`), with the later objects that live in every sector setting:
`Z_ℓ` of Part I Lemma 4.10 (`lem:edge`), the dilated setting of the retained dilation identities
(the retained general dilation identities; the ring specialization is the scaling argument for Part I Equation 13 (`eq:evans-units`)), the sector norms `‖g‖_{k,ℓ}` (the mode norms preceding Part I Lemma 4.12 (`lem:norm-equiv`)), the transport
part and the coupling operator `𝒦` of Part I Lemma 4.14 (`lem:semigroup-construct`), and the
retained general-mode multipole field (the mode-3 case precedes Part I Definition 4.20,
`def:eigendata`).

**Data and validity are separate.** `SectorSetting` holds the data `(ω̄, r₁, r₂, ρ₋, ρ₊)` only,
and `SectorSetting.Valid S` is the list of conditions of `def:sector-setting`. Every object is
defined for all data (junk values where the conditions fail), and the theorems about a setting
take `hS : S.Valid`. The two settings of the ring (`Defs/Sec4/RingSetting.lean`) are thus plain
definitions; their validity is a theorem (a consequence of `lem:ring-facts`). The number `G` of
the manuscript's setting is not a field: as in the manuscript's notation `Ω(r;G)`, `L_ℓ(G)`,
`E_ℓ(λ;G)`, it is an argument of the objects.

**Function-level objects.** Radial profiles are functions `g : ℝ → ℂ` of `r` (only `r > 0`
matters); plane functions are `w : ℂ → ℂ`; `ℓ : ℤ` for sector objects and `ℓ : ℕ` (`ℓ ≥ 1`)
for the Riccati coefficient, as in the statement layer's `riccatiCoeff`. The typed operators on
the sector spaces `Y^s_ℓ` are in `Defs/Sec4/Operators.lean`.

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ContDiff

namespace NonUniqueEuler

/-- The data of a **sector setting** (Part I Definition 4.3 (`def:sector-setting`)): the radial
profile `ω̄` (a function on the plane), the numbers `r₁ ≤ r₂` with `supp ω̄' ⊆ [r₁, r₂]`, and the
radii `ρ₋ < r₁`, `r₂ < ρ₊` of the annulus `N_* = {ρ₋ ≤ |x| ≤ ρ₊}`. The conditions are
`SectorSetting.Valid`. -/
structure SectorSetting where
  /-- `ω̄ : ℝ² → ℝ`, a real radial function in `C_c^∞(ℝ²)`. -/
  om : ℂ → ℝ
  /-- `r₁ > 0`, with `supp ω̄' ⊆ [r₁, r₂]`. -/
  r₁ : ℝ
  /-- `r₂ ≥ r₁`. -/
  r₂ : ℝ
  /-- `ρ₋ ∈ (0, r₁)`, the inner radius of `N_*`. -/
  ρm : ℝ
  /-- `ρ₊ > r₂`, the outer radius of `N_*`. -/
  ρp : ℝ

namespace SectorSetting

/-- `ω̄` written as a function of `r = |x|` (Part I Definition 4.3 (`def:sector-setting`)): `r ↦ ω̄(r)`, `r` real. -/
def omR (S : SectorSetting) (r : ℝ) : ℝ := S.om (r : ℂ)

/-- `ω̄'(r)`, the radial derivative of the profile (Part I Definition 4.3 (`def:sector-setting`)). -/
def dom (S : SectorSetting) (r : ℝ) : ℝ := deriv S.omR r

/-- The conditions of Part I Definition 4.3 (`def:sector-setting`): `ω̄ ∈ C_c^∞(ℝ²)` real and
radial; `0 < r₁ ≤ r₂` with `supp ω̄' ⊆ [r₁, r₂]` (on `r > 0`); `0 < ρ₋ < r₁` and `r₂ < ρ₊`. -/
structure Valid (S : SectorSetting) : Prop where
  contDiff : ContDiff ℝ ∞ S.om
  hasCompactSupport : HasCompactSupport S.om
  radial : IsRadialPointwise S.om
  r₁_pos : 0 < S.r₁
  r₁_le_r₂ : S.r₁ ≤ S.r₂
  dom_eq_zero : ∀ r : ℝ, 0 < r → r ∉ Icc S.r₁ S.r₂ → S.dom r = 0
  ρm_pos : 0 < S.ρm
  ρm_lt_r₁ : S.ρm < S.r₁
  r₂_lt_ρp : S.r₂ < S.ρp

/-- `ξ₁ = log r₁` (Part I Definition 4.3 (`def:sector-setting`)). -/
def ξ₁ (S : SectorSetting) : ℝ := Real.log S.r₁

/-- `ξ₂ = log r₂` (Part I Definition 4.3 (`def:sector-setting`)). -/
def ξ₂ (S : SectorSetting) : ℝ := Real.log S.r₂

/-- The annulus `N_* = {ρ₋ ≤ |x| ≤ ρ₊}` (Part I Definition 4.3 (`def:sector-setting`)). The spaces `Y^s`, `Y^s_ℓ` of the
setting are `Sect.Y s S.Nstar`, `Sect.Ysec s S.Nstar ℓ` (Part I Definition 4.3 (`def:sector-setting`)). -/
def Nstar (S : SectorSetting) : Set ℂ := Sect.closedAnnulus S.ρm S.ρp

/-- The angular velocity `Ω(r;G) = r⁻² (Circ_ω̄(r)/(2π) + G)` (Part I Definition 4.3 (`def:sector-setting`)), with
`Circ_ω̄(r) = ∫_{B_r} ω̄` (`Polar.circ`, Part I Definition 4.3 (`def:sector-setting`)). -/
def Omega (S : SectorSetting) (G r : ℝ) : ℝ :=
  (r ^ 2)⁻¹ * (Polar.circ S.om r / (2 * π) + G)

/-- `k_ℓ(r) = iℓ ω̄'(r)/r` (Part I Definition 4.3 (`def:sector-setting`)). -/
def kcoef (S : SectorSetting) (ℓ : ℤ) (r : ℝ) : ℂ :=
  Complex.I * (ℓ : ℂ) * ((S.dom r : ℝ) : ℂ) / (r : ℂ)

/-- The sector Green operator
`(𝒢_ℓ g)(r) = -(2|ℓ|)⁻¹ ∫_0^∞ (min(r,ρ)/max(r,ρ))^{|ℓ|} g(ρ) ρ dρ` (Part I Definition 4.3 (`def:sector-setting`)), for
`ℓ ≠ 0` (the value `0` for `ℓ = 0` is a junk value). It does not depend on the setting. -/
def green (ℓ : ℤ) (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  -((((2 * |(ℓ : ℝ)|)⁻¹ : ℝ)) : ℂ) *
    ∫ ρ in Ioi (0 : ℝ), (((min r ρ / max r ρ) ^ ℓ.natAbs : ℝ) : ℂ) * g ρ * (ρ : ℂ)

/-- `f_ξ(ξ) = r ω̄'(r)` at `r = e^ξ` (Part I Definition 4.3 (`def:sector-setting`)). -/
def fxi (S : SectorSetting) (ξ : ℝ) : ℝ := Real.exp ξ * S.dom (Real.exp ξ)

/-- The **Riccati coefficient**
`V_ℓ(ξ;λ,G) = ℓ² + iℓ f_ξ(ξ) / (λ + iℓ Ω(e^ξ;G))` (Part I Definition 4.3 (`def:sector-setting`)), for `ℓ ≥ 1` and
`Re λ > 0` (junk otherwise). Written as the statement layer's `riccatiCoeff`. -/
def Vric (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) : ℂ :=
  (ℓ : ℂ) ^ 2 + Complex.I * (ℓ : ℂ) * ((S.fxi ξ : ℝ) : ℂ) /
    (z + Complex.I * (ℓ : ℂ) * ((S.Omega G (Real.exp ξ) : ℝ) : ℂ))

/-- `M_λ(r) = (λ + iℓΩ(r;G))⁻¹` (Part I Definition 4.3 (`def:sector-setting`); the manuscript suppresses `ℓ`). -/
def Mres (S : SectorSetting) (ℓ : ℤ) (z : ℂ) (G r : ℝ) : ℂ :=
  (z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ))⁻¹

/-- The coupling operator on sector profiles, `g ↦ k_ℓ 𝒢_ℓ g` (Part I Definition 4.3 (`def:sector-setting`); it is `𝒦` on
the sector `ℓ`, `lem:sector`(2), `cor:K-bound`). -/
def KsecFn (S : SectorSetting) (ℓ : ℤ) (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  S.kcoef ℓ r * green ℓ g r

/-- The **sector operator** on profiles, `L_ℓ(G) g = -iℓΩ g + k_ℓ 𝒢_ℓ g` (Part I Definition 4.3 (`def:sector-setting`)).
For `ℓ = 0` it is `0`, as in the manuscript (`LsecFn_zero`). -/
def LsecFn (S : SectorSetting) (ℓ : ℤ) (G : ℝ) (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  -(Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)) * g r + S.KsecFn ℓ g r

/-- The coupling term `𝒦w = -(K_BS * w)·∇ω̄` (Part I Definition 4.3 (`def:sector-setting`), Part I Lemma 4.14 (`lem:semigroup-construct`)) for complex `w`:
`(𝒦w)(x) = -∫ (K_BS(x-y)·∇ω̄(x)) w(y) dy`, the dot product being `Dω̄(x)(K_BS(x-y))`
(decision D2). -/
def couplingFn (S : SectorSetting) (w : ℂ → ℂ) (x : ℂ) : ℂ :=
  -∫ y, ((fderiv ℝ S.om x (biotSavartKernel (x - y)) : ℝ) : ℂ) * w y

/-- The transport part `L^tr w = -Ω(|x|;G) ∂_θ w` (Part I Definition 4.3 (`def:sector-setting`), Part I Lemma 4.14 (`lem:semigroup-construct`)), with the weak
angular derivative `Ang.thetaDeriv`. -/
def transportPartFn (S : SectorSetting) (G : ℝ) (w : ℂ → ℂ) (x : ℂ) : ℂ :=
  -((S.Omega G ‖x‖ : ℝ) : ℂ) * Ang.thetaDeriv w x

/-- The **linearization** at `(ω̄, G)`: `L(G)w = -Ω(·;G) ∂_θ w - (K_BS * w)·∇ω̄`
(Part I Definition 4.3 (`def:sector-setting`)), as a function on the plane. -/
def linFn (S : SectorSetting) (G : ℝ) (w : ℂ → ℂ) (x : ℂ) : ℂ :=
  S.transportPartFn G w x + S.couplingFn w x

/-- The transport group `(e^{tL^tr} w)(r, θ) = w(r, θ - Ω(r;G)t)` (`lem:semigroup-construct`(1),
Part I Lemma 4.14 (`lem:semigroup-construct`)), as a function on the plane. -/
def transportFn (S : SectorSetting) (G t : ℝ) (w : ℂ → ℂ) (x : ℂ) : ℂ :=
  w (rot (-(S.Omega G ‖x‖ * t)) x)

/-- The manuscript's sector norm `‖g‖²_{k,ℓ} = ∑_{j ≤ k} (1+ℓ²)^{k-j} ‖∂_r^j g‖²_{L²([ρ₋,ρ₊], r dr)}`
(the mode norms preceding Part I Lemma 4.12 (`lem:norm-equiv`)). The version on an interval `I` is `Sob.secNormSq k ℓ I g`. -/
def secNormSq (S : SectorSetting) (k : ℕ) (ℓ : ℤ) (g : ℝ → ℂ) : ℝ :=
  Sob.secNormSq k ℓ (Icc S.ρm S.ρp) g

/-! ### Part I Lemma 4.10 (`lem:edge`) -/

/-- The hypothesis of Part I Lemma 4.10 (`lem:edge`): with `𝒰₊ = {ω̄' > 0}` and
`𝒰₋ = {ω̄' < 0}` (in `r > 0`), `r < ρ` for all `r ∈ 𝒰₊`, `ρ ∈ 𝒰₋`. -/
def EdgeSplit (S : SectorSetting) : Prop :=
  ∀ r ρ : ℝ, 0 < r → 0 < ρ → 0 < S.dom r → S.dom ρ < 0 → r < ρ

/-- `Z_ℓ = ∫_{𝒰₊} ∫_{𝒰₋} (r/ρ)^{2ℓ} |ω̄'(r)| |ω̄'(ρ)| dρ dr` (Part I Lemma 4.10 (`lem:edge`)). -/
def Zedge (S : SectorSetting) (ℓ : ℕ) : ℝ :=
  ∫ r in {r : ℝ | 0 < r ∧ 0 < S.dom r}, ∫ ρ in {ρ : ℝ | 0 < ρ ∧ S.dom ρ < 0},
    (r / ρ) ^ (2 * ℓ) * |S.dom r| * |S.dom ρ|

/-! ### the retained dilation identities (the retained general dilation identities; the ring specialization is the scaling argument for Part I Equation 13 (`eq:evans-units`)) -/

/-- The dilated setting: `ω̄_R(y) = ω̄(Ry)`, radii divided by `R` (the retained general dilation identities; the ring specialization is the scaling argument for Part I Equation 13 (`eq:evans-units`); so
`ξ_i` becomes `ξ_i - log R`, the retained general dilation identities; the ring specialization is the scaling argument for Part I Equation 13 (`eq:evans-units`)). -/
def dilate (S : SectorSetting) (R : ℝ) : SectorSetting where
  om := fun y => S.om ((R : ℂ) * y)
  r₁ := S.r₁ / R
  r₂ := S.r₂ / R
  ρm := S.ρm / R
  ρp := S.ρp / R

/-! ### The general-mode multipole field (mode-3 case before Part I Definition 4.20) -/

/-- `∇^⊥ψ = (-∂₂ψ, ∂₁ψ)` of a real function `ψ` on the plane, as the complex number
`i(∂₁ψ + i∂₂ψ)` (decision D1, `x^⊥ = i x`). -/
def perpGrad (ψ : ℂ → ℝ) (x : ℂ) : ℂ :=
  Complex.I * (((fderiv ℝ ψ x 1 : ℝ) : ℂ) + Complex.I * ((fderiv ℝ ψ x Complex.I : ℝ) : ℂ))

/-- The real stream function `-(m/(2ℓ)) r^{-ℓ} e^{iℓθ} + c.c.`; its mode-3 case appears
before Part I Definition 4.20 (`def:eigendata`). -/
def multipoleStream (ℓ : ℕ) (m : ℂ) (x : ℂ) : ℝ :=
  2 * (-(m / (2 * (ℓ : ℂ))) * (((‖x‖ : ℝ) : ℂ) ^ (-(ℓ : ℤ)) * Ang.angPhase ℓ x)).re

/-- The retained general-mode field `h = ∇^⊥(-(m/(2ℓ)) r^{-ℓ} e^{iℓθ} + c.c.)`,
extending the mode-3 calculation before Part I Definition 4.20 (`def:eigendata`). -/
def multipoleField (ℓ : ℕ) (m : ℂ) : ℂ → ℂ :=
  perpGrad (multipoleStream ℓ m)

/-! ### Basic lemmas (fully proved) -/

theorem Valid.ρm_lt_ρp {S : SectorSetting} (hS : S.Valid) : S.ρm < S.ρp :=
  (hS.ρm_lt_r₁.trans_le hS.r₁_le_r₂).trans hS.r₂_lt_ρp

theorem Valid.r₂_pos {S : SectorSetting} (hS : S.Valid) : 0 < S.r₂ :=
  hS.r₁_pos.trans_le hS.r₁_le_r₂

theorem Valid.ξ₁_le_ξ₂ {S : SectorSetting} (hS : S.Valid) : S.ξ₁ ≤ S.ξ₂ :=
  Real.log_le_log hS.r₁_pos hS.r₁_le_r₂

theorem isRotInvariant_Nstar (S : SectorSetting) : Sect.IsRotInvariant S.Nstar :=
  Sect.isRotInvariant_closedAnnulus _ _

theorem isCompact_Nstar (S : SectorSetting) : IsCompact S.Nstar :=
  Sect.isCompact_closedAnnulus _ _

theorem mem_Nstar {S : SectorSetting} {x : ℂ} : x ∈ S.Nstar ↔ S.ρm ≤ ‖x‖ ∧ ‖x‖ ≤ S.ρp :=
  Iff.rfl

/-- `Ω(r;G) = Ω(r;0) + G r⁻²` (used in `prop:semigroup`: `L_ℓ(G) = L_ℓ(0) - iℓG r⁻²`). -/
theorem Omega_eq_add (S : SectorSetting) (G r : ℝ) :
    S.Omega G r = S.Omega 0 r + G * (r ^ 2)⁻¹ := by
  simp only [Omega]
  ring

@[simp] theorem kcoef_zero (S : SectorSetting) (r : ℝ) : S.kcoef 0 r = 0 := by
  simp [kcoef]

@[simp] theorem green_zero (g : ℝ → ℂ) (r : ℝ) : green 0 g r = 0 := by
  simp [green]

/-- `L_0 = 0` (Part I Definition 4.3 (`def:sector-setting`)). -/
theorem LsecFn_zero (S : SectorSetting) (G : ℝ) (g : ℝ → ℂ) : S.LsecFn 0 G g = 0 := by
  funext r
  simp [LsecFn, KsecFn]

theorem LsecFn_eq (S : SectorSetting) (ℓ : ℤ) (G : ℝ) (g : ℝ → ℂ) (r : ℝ) :
    S.LsecFn ℓ G g r =
      -(Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)) * g r + S.kcoef ℓ r * green ℓ g r :=
  rfl

theorem dilate_om (S : SectorSetting) (R : ℝ) (y : ℂ) :
    (S.dilate R).om y = S.om ((R : ℂ) * y) := rfl

theorem dilate_Nstar (S : SectorSetting) (R : ℝ) :
    (S.dilate R).Nstar = Sect.closedAnnulus (S.ρm / R) (S.ρp / R) := rfl

theorem dilate_ξ₁ (S : SectorSetting) {R : ℝ} (hr : S.r₁ ≠ 0) (hR : R ≠ 0) :
    (S.dilate R).ξ₁ = S.ξ₁ - Real.log R := by
  simp only [ξ₁, dilate]
  exact Real.log_div hr hR

theorem dilate_ξ₂ (S : SectorSetting) {R : ℝ} (hr : S.r₂ ≠ 0) (hR : R ≠ 0) :
    (S.dilate R).ξ₂ = S.ξ₂ - Real.log R := by
  simp only [ξ₂, dilate]
  exact Real.log_div hr hR

end SectorSetting

end NonUniqueEuler
