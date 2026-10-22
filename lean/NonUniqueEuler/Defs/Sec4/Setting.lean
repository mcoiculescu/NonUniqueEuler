import NonUniqueEuler.Statement.Plane
import NonUniqueEuler.Defs.Infra.Polar
import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.Defs.Infra.SectorSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Section 4.2: the sector setting (definitions)

Manuscript `04_ring.tex:134-185`
(`def:sector-setting`), with the later objects that live in every sector setting:
`Z_ℓ` of `lem:edge` (`04_ring.tex:718-729`), the dilated setting of `lem:dilation`
(`04_ring.tex:653-671`), the sector norms `‖g‖_{k,ℓ}` (`04_ring.tex:836-841`), the transport
part and the coupling operator `𝒦` of `lem:semigroup-construct` (`04_ring.tex:926-933`), and the
multipole field of `lem:adjoint`(4) (`04_ring.tex:595-599`).

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

/-- The data of a **sector setting** (`def:sector-setting`, `04_ring.tex:140-146`): the radial
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

/-- `ω̄` written as a function of `r = |x|` (`04_ring.tex:143`): `r ↦ ω̄(r)`, `r` real. -/
def omR (S : SectorSetting) (r : ℝ) : ℝ := S.om (r : ℂ)

/-- `ω̄'(r)`, the radial derivative of the profile (`04_ring.tex:144`). -/
def dom (S : SectorSetting) (r : ℝ) : ℝ := deriv S.omR r

/-- The conditions of `def:sector-setting` (`04_ring.tex:142-146`): `ω̄ ∈ C_c^∞(ℝ²)` real and
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

/-- `ξ₁ = log r₁` (`04_ring.tex:144`). -/
def ξ₁ (S : SectorSetting) : ℝ := Real.log S.r₁

/-- `ξ₂ = log r₂` (`04_ring.tex:145`). -/
def ξ₂ (S : SectorSetting) : ℝ := Real.log S.r₂

/-- The annulus `N_* = {ρ₋ ≤ |x| ≤ ρ₊}` (`04_ring.tex:145`). The spaces `Y^s`, `Y^s_ℓ` of the
setting are `Sect.Y s S.Nstar`, `Sect.Ysec s S.Nstar ℓ` (`04_ring.tex:155-160`). -/
def Nstar (S : SectorSetting) : Set ℂ := Sect.closedAnnulus S.ρm S.ρp

/-- The angular velocity `Ω(r;G) = r⁻² (Circ_ω̄(r)/(2π) + G)` (`04_ring.tex:150`), with
`Circ_ω̄(r) = ∫_{B_r} ω̄` (`Polar.circ`, `04_ring.tex:175`). -/
def Omega (S : SectorSetting) (G r : ℝ) : ℝ :=
  (r ^ 2)⁻¹ * (Polar.circ S.om r / (2 * π) + G)

/-- `k_ℓ(r) = iℓ ω̄'(r)/r` (`04_ring.tex:151`). -/
def kcoef (S : SectorSetting) (ℓ : ℤ) (r : ℝ) : ℂ :=
  Complex.I * (ℓ : ℂ) * ((S.dom r : ℝ) : ℂ) / (r : ℂ)

/-- The sector Green operator
`(𝒢_ℓ g)(r) = -(2|ℓ|)⁻¹ ∫_0^∞ (min(r,ρ)/max(r,ρ))^{|ℓ|} g(ρ) ρ dρ` (`04_ring.tex:152`), for
`ℓ ≠ 0` (the value `0` for `ℓ = 0` is a junk value). It does not depend on the setting. -/
def green (ℓ : ℤ) (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  -((((2 * |(ℓ : ℝ)|)⁻¹ : ℝ)) : ℂ) *
    ∫ ρ in Ioi (0 : ℝ), (((min r ρ / max r ρ) ^ ℓ.natAbs : ℝ) : ℂ) * g ρ * (ρ : ℂ)

/-- `f_ξ(ξ) = r ω̄'(r)` at `r = e^ξ` (`04_ring.tex:170`). -/
def fxi (S : SectorSetting) (ξ : ℝ) : ℝ := Real.exp ξ * S.dom (Real.exp ξ)

/-- The **Riccati coefficient**
`V_ℓ(ξ;λ,G) = ℓ² + iℓ f_ξ(ξ) / (λ + iℓ Ω(e^ξ;G))` (`04_ring.tex:166-171`), for `ℓ ≥ 1` and
`Re λ > 0` (junk otherwise). Written as the statement layer's `riccatiCoeff`. -/
def Vric (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) : ℂ :=
  (ℓ : ℂ) ^ 2 + Complex.I * (ℓ : ℂ) * ((S.fxi ξ : ℝ) : ℂ) /
    (z + Complex.I * (ℓ : ℂ) * ((S.Omega G (Real.exp ξ) : ℝ) : ℂ))

/-- `M_λ(r) = (λ + iℓΩ(r;G))⁻¹` (`04_ring.tex:172`; the manuscript suppresses `ℓ`). -/
def Mres (S : SectorSetting) (ℓ : ℤ) (z : ℂ) (G r : ℝ) : ℂ :=
  (z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ))⁻¹

/-- The coupling operator on sector profiles, `g ↦ k_ℓ 𝒢_ℓ g` (`04_ring.tex:165`; it is `𝒦` on
the sector `ℓ`, `lem:sector`(2), `cor:K-bound`). -/
def KsecFn (S : SectorSetting) (ℓ : ℤ) (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  S.kcoef ℓ r * green ℓ g r

/-- The **sector operator** on profiles, `L_ℓ(G) g = -iℓΩ g + k_ℓ 𝒢_ℓ g` (`04_ring.tex:165-166`).
For `ℓ = 0` it is `0`, as in the manuscript (`LsecFn_zero`). -/
def LsecFn (S : SectorSetting) (ℓ : ℤ) (G : ℝ) (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  -(Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)) * g r + S.KsecFn ℓ g r

/-- The coupling term `𝒦w = -(K_BS * w)·∇ω̄` (`04_ring.tex:163`, `:927`) for complex `w`:
`(𝒦w)(x) = -∫ (K_BS(x-y)·∇ω̄(x)) w(y) dy`, the dot product being `Dω̄(x)(K_BS(x-y))`
(decision D2). -/
def couplingFn (S : SectorSetting) (w : ℂ → ℂ) (x : ℂ) : ℂ :=
  -∫ y, ((fderiv ℝ S.om x (biotSavartKernel (x - y)) : ℝ) : ℂ) * w y

/-- The transport part `L^tr w = -Ω(|x|;G) ∂_θ w` (`04_ring.tex:163`, `:927`), with the weak
angular derivative `Ang.thetaDeriv`. -/
def transportPartFn (S : SectorSetting) (G : ℝ) (w : ℂ → ℂ) (x : ℂ) : ℂ :=
  -((S.Omega G ‖x‖ : ℝ) : ℂ) * Ang.thetaDeriv w x

/-- The **linearization** at `(ω̄, G)`: `L(G)w = -Ω(·;G) ∂_θ w - (K_BS * w)·∇ω̄`
(`04_ring.tex:161-164`), as a function on the plane. -/
def linFn (S : SectorSetting) (G : ℝ) (w : ℂ → ℂ) (x : ℂ) : ℂ :=
  S.transportPartFn G w x + S.couplingFn w x

/-- The transport group `(e^{tL^tr} w)(r, θ) = w(r, θ - Ω(r;G)t)` (`lem:semigroup-construct`(1),
`04_ring.tex:929`), as a function on the plane. -/
def transportFn (S : SectorSetting) (G t : ℝ) (w : ℂ → ℂ) (x : ℂ) : ℂ :=
  w (rot (-(S.Omega G ‖x‖ * t)) x)

/-- The manuscript's sector norm `‖g‖²_{k,ℓ} = ∑_{j ≤ k} (1+ℓ²)^{k-j} ‖∂_r^j g‖²_{L²([ρ₋,ρ₊], r dr)}`
(`04_ring.tex:836-841`). The version on an interval `I` is `Sob.secNormSq k ℓ I g`. -/
def secNormSq (S : SectorSetting) (k : ℕ) (ℓ : ℤ) (g : ℝ → ℂ) : ℝ :=
  Sob.secNormSq k ℓ (Icc S.ρm S.ρp) g

/-! ### `lem:edge` (`04_ring.tex:718-729`) -/

/-- The hypothesis of `lem:edge` (`04_ring.tex:720-722`): with `𝒰₊ = {ω̄' > 0}` and
`𝒰₋ = {ω̄' < 0}` (in `r > 0`), `r < ρ` for all `r ∈ 𝒰₊`, `ρ ∈ 𝒰₋`. -/
def EdgeSplit (S : SectorSetting) : Prop :=
  ∀ r ρ : ℝ, 0 < r → 0 < ρ → 0 < S.dom r → S.dom ρ < 0 → r < ρ

/-- `Z_ℓ = ∫_{𝒰₊} ∫_{𝒰₋} (r/ρ)^{2ℓ} |ω̄'(r)| |ω̄'(ρ)| dρ dr` (`04_ring.tex:723-725`). -/
def Zedge (S : SectorSetting) (ℓ : ℕ) : ℝ :=
  ∫ r in {r : ℝ | 0 < r ∧ 0 < S.dom r}, ∫ ρ in {ρ : ℝ | 0 < ρ ∧ S.dom ρ < 0},
    (r / ρ) ^ (2 * ℓ) * |S.dom r| * |S.dom ρ|

/-! ### `lem:dilation` (`04_ring.tex:653-671`) -/

/-- The dilated setting: `ω̄_R(y) = ω̄(Ry)`, radii divided by `R` (`04_ring.tex:655-656`; so
`ξ_i` becomes `ξ_i - log R`, `04_ring.tex:663`). -/
def dilate (S : SectorSetting) (R : ℝ) : SectorSetting where
  om := fun y => S.om ((R : ℂ) * y)
  r₁ := S.r₁ / R
  r₂ := S.r₂ / R
  ρm := S.ρm / R
  ρp := S.ρp / R

/-! ### The multipole field of `lem:adjoint`(4) (`04_ring.tex:595-599`) -/

/-- `∇^⊥ψ = (-∂₂ψ, ∂₁ψ)` of a real function `ψ` on the plane, as the complex number
`i(∂₁ψ + i∂₂ψ)` (decision D1, `x^⊥ = i x`). -/
def perpGrad (ψ : ℂ → ℝ) (x : ℂ) : ℂ :=
  Complex.I * (((fderiv ℝ ψ x 1 : ℝ) : ℂ) + Complex.I * ((fderiv ℝ ψ x Complex.I : ℝ) : ℂ))

/-- The real stream function `-(m/(2ℓ)) r^{-ℓ} e^{iℓθ} + c.c.` (`04_ring.tex:597`). -/
def multipoleStream (ℓ : ℕ) (m : ℂ) (x : ℂ) : ℝ :=
  2 * (-(m / (2 * (ℓ : ℂ))) * (((‖x‖ : ℝ) : ℂ) ^ (-(ℓ : ℤ)) * Ang.angPhase ℓ x)).re

/-- The real field `h = ∇^⊥(-(m/(2ℓ)) r^{-ℓ} e^{iℓθ} + c.c.)` of `lem:adjoint`(4)
(`04_ring.tex:597-599`). -/
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

/-- `L_0 = 0` (`04_ring.tex:166`). -/
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
