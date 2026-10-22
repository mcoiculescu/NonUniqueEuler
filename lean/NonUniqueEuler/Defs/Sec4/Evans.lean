import NonUniqueEuler.Defs.Sec4.Operators
import NonUniqueEuler.Defs.Infra.ODE

/-!
# Section 4.2: the Evans function, the resolvent and the eigendata of a sector setting
(definitions)

Manuscript `04_ring.tex`:
`def:evans` (`:187-198`), `lem:evans-basic` (`:285-303`: `ψ_L`, `ψ_R`, the Wronskian),
`lem:resolvent` (`:366-389`: the resolvent formula, the eigenfunction `g_λ`),
`thm:evans-simple` (`:450-477`: `ψ_*`, `g_*`, `J`, `ℓ_*`, the projection `P g = ℓ_*(g) g_*`),
`lem:adjoint` (`:575-601`: `pout_*`, `pin_*`, `b`, `β`).

These are the objects of an arbitrary sector setting `S` (the statement-layer `evans` is the
Evans function of the ring in reference units; `lem:evans-basic`, last assertion, says that it is
`(ringRefSetting χ).evans`, and `eq:evans-units` relates it to the ring units). The eigenvalue
`λ_*` of `thm:evans-simple` is an explicit argument `z`: the objects are meaningful when `z` is a
zero of `S.evans ℓ · G` with `Re z > 0`. The sector index is `ℓ : ℕ` (`ℓ ≥ 1`); the sector
`-ℓ` is reached by complex conjugation (`lem:resolvent`, last assertion), see `ellStarBar`,
`gStarBarY`, `rieszSecBar`.

**The solution `ψ_ℓ`.** `def:evans` solves `ψ'' = V_ℓ ψ` on all of `ℝ`
(`04_ring.tex:189-191`); we take the global solution `LinODE.sol` of I-ODE with data
`(ψ, ψ')(ξ₁) = (1, ℓ)` (it exists and is unique since `V_ℓ` is continuous for `Re λ > 0`,
`lem:sector`(3)). `psi` and `dpsi` are `ψ_ℓ` and `ψ_ℓ'`.

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set ComplexConjugate

namespace NonUniqueEuler

namespace SectorSetting

open Sect

/-! ### `def:evans` and `lem:evans-basic` -/

/-- The pair `(ψ_ℓ, ψ_ℓ')(·;λ,G)`: the global solution of `ψ'' = V_ℓ(·;λ,G) ψ` with
`ψ(ξ₁) = 1`, `ψ'(ξ₁) = ℓ` (`def:evans`, `04_ring.tex:189-191`). -/
def psiPair (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) : ℝ → ℂ × ℂ :=
  LinODE.sol (S.Vric ℓ z G) S.ξ₁ (1, (ℓ : ℂ))

/-- `ψ_ℓ(ξ;λ,G)` (`04_ring.tex:190`). -/
def psi (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) : ℂ := (S.psiPair ℓ z G ξ).1

/-- `ψ_ℓ'(ξ;λ,G)`. -/
def dpsi (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) : ℂ := (S.psiPair ℓ z G ξ).2

/-- **The Evans function** `E_ℓ(λ;G) = e^{-ℓ(ξ₂-ξ₁)} (ψ_ℓ'(ξ₂) + ℓ ψ_ℓ(ξ₂))` of the setting
(`def:evans`, `04_ring.tex:193-195`). -/
def evans (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) : ℂ :=
  ((Real.exp (-(ℓ : ℝ) * (S.ξ₂ - S.ξ₁)) : ℝ) : ℂ) *
    (S.dpsi ℓ z G S.ξ₂ + (ℓ : ℂ) * S.psi ℓ z G S.ξ₂)

/-- `ψ_L = e^{ℓξ₁} ψ_ℓ`, so that `ψ_L(ξ) = e^{ℓξ}` for `ξ ≤ ξ₁` (`lem:evans-basic`(3),
`04_ring.tex:294-295`). -/
def psiL (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) : ℂ :=
  ((Real.exp (ℓ * S.ξ₁) : ℝ) : ℂ) * S.psi ℓ z G ξ

/-- `ψ_L'`. -/
def dpsiL (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) : ℂ :=
  ((Real.exp (ℓ * S.ξ₁) : ℝ) : ℂ) * S.dpsi ℓ z G ξ

/-- The pair `(ψ_R, ψ_R')`: the global solution of `ψ'' = V_ℓ ψ` with `ψ_R(ξ) = e^{-ℓξ}` for
`ξ ≥ ξ₂`, i.e. with data `(e^{-ℓξ₂}, -ℓe^{-ℓξ₂})` at `ξ₂` (`04_ring.tex:295-296`). -/
def psiRPair (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) : ℝ → ℂ × ℂ :=
  LinODE.sol (S.Vric ℓ z G) S.ξ₂
    (((Real.exp (-(ℓ : ℝ) * S.ξ₂) : ℝ) : ℂ), -(ℓ : ℂ) * ((Real.exp (-(ℓ : ℝ) * S.ξ₂) : ℝ) : ℂ))

/-- `ψ_R`. -/
def psiR (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) : ℂ := (S.psiRPair ℓ z G ξ).1

/-- `ψ_R'`. -/
def dpsiR (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) : ℂ := (S.psiRPair ℓ z G ξ).2

/-- The Wronskian `W = ψ_L ψ_R' - ψ_L' ψ_R` as a function of `ξ` (`04_ring.tex:297`; it is
constant and equal to `-E_ℓ(λ;G)`, `lem:evans-basic`(3)). -/
def wrFn (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) : ℂ :=
  LinODE.wronskian (S.psiL ℓ z G) (S.dpsiL ℓ z G) (S.psiR ℓ z G) (S.dpsiR ℓ z G) ξ

/-- The Wronskian `W(λ)`, evaluated at `ξ₂` (`04_ring.tex:297-298`). -/
def wr (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) : ℂ := S.wrFn ℓ z G S.ξ₂

/-! ### `lem:resolvent` (`04_ring.tex:366-389`) -/

/-- `F(ξ) = e^{2ξ} (M_λ g)(e^ξ)` (`04_ring.tex:378`). -/
def Fres (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) (g : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ((Real.exp (2 * ξ) : ℝ) : ℂ) * (S.Mres ℓ z G (Real.exp ξ) * g (Real.exp ξ))

/-- `ψ_g(ξ) = W⁻¹ [ψ_R(ξ) ∫_{-∞}^ξ ψ_L F + ψ_L(ξ) ∫_ξ^∞ ψ_R F]` (`04_ring.tex:375`). -/
def psiG (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) (g : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  (S.wr ℓ z G)⁻¹ *
    (S.psiR ℓ z G ξ * (∫ η in Iic ξ, S.psiL ℓ z G η * S.Fres ℓ z G g η) +
      S.psiL ℓ z G ξ * ∫ η in Ioi ξ, S.psiR ℓ z G η * S.Fres ℓ z G g η)

/-- The resolvent formula `(λ - L_ℓ)⁻¹ g = M_λ (g + k_ℓ ψ_g)`, `ψ_g` read at `ξ = log r`
(`lem:resolvent`(1), `04_ring.tex:374-379`). -/
def resolventFn (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  S.Mres ℓ z G r * (g r + S.kcoef ℓ r * S.psiG ℓ z G g (Real.log r))

/-! ### `thm:evans-simple` and `lem:adjoint` -/

/-- The eigenprofile `g_λ = M_λ k_ℓ ψ_ℓ(log r;λ,G)` (`lem:resolvent`(2), `04_ring.tex:383`);
at a zero `λ_*` it is `g_*` of `thm:evans-simple` (`04_ring.tex:454`). -/
def gStar (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G r : ℝ) : ℂ :=
  S.Mres ℓ z G r * S.kcoef ℓ r * S.psi ℓ z G (Real.log r)

/-- `J = ∫_0^∞ g_*(r) ψ_*(log r) M_{λ_*}(r) r dr` (`04_ring.tex:456`). -/
def J (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), S.gStar ℓ z G r * S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ)

/-- The functional `ℓ_*(g) = J⁻¹ ∫_0^∞ g(r) ψ_*(log r) M_{λ_*}(r) r dr` on sector profiles
(`thm:evans-simple`(2), `04_ring.tex:467`). -/
def ellStar (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) (g : ℝ → ℂ) : ℂ :=
  (S.J ℓ z G)⁻¹ *
    ∫ r in Ioi (0 : ℝ), g r * S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ)

/-- The adjoint eigenprofile `conj(ψ_*(log r) M_{λ_*}(r))` (`lem:adjoint`(1),
`04_ring.tex:585-586`). -/
def adjEig (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G r : ℝ) : ℂ :=
  conj (S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r)

/-- `pout_* = ∫_0^∞ ρ^{ℓ+1} g_*(ρ) dρ` (`04_ring.tex:579`). -/
def poutStar (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) : ℂ :=
  ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (ℓ + 1) * S.gStar ℓ z G ρ

/-- `pin_* = ∫_0^∞ ρ^{1-ℓ} g_*(ρ) dρ` (`04_ring.tex:580`). -/
def pinStar (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) : ℂ :=
  ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ ((1 : ℤ) - ℓ) * S.gStar ℓ z G ρ

/-- `b(r) = -(i/2) r^{-ℓ-1} ω̄'(r)` (`lem:adjoint`(4), `04_ring.tex:595`). -/
def bfun (S : SectorSetting) (ℓ : ℕ) (r : ℝ) : ℂ :=
  -(Complex.I / 2) * (r : ℂ) ^ (-(ℓ : ℤ) - 1) * ((S.dom r : ℝ) : ℂ)

/-- `β = ℓ_*(b)` (`lem:adjoint`(4), `04_ring.tex:595`). -/
def betaStar (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) : ℂ :=
  S.ellStar ℓ z G (S.bfun ℓ)

/-- The functional of the conjugate sector `-ℓ`: `h ↦ conj(ℓ_*(conj h))` (the Riesz projection of
`L_{-ℓ}` at `conj λ_*` is `h ↦ conj(ℓ_*(conj h)) conj(g_*)`, by `lem:resolvent`, last assertion
and `lem:sector`(2): `L_{-ℓ} conj g = conj(L_ℓ g)`). -/
def ellStarBar (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) (h : ℝ → ℂ) : ℂ :=
  conj (S.ellStar ℓ z G fun r => conj (h r))

/-! ### Typed versions on the sector spaces -/

/-- `g_* e^{iℓθ}` as an element of `Y^s_ℓ` (`toYsec`; it lies in every `Y^s_ℓ` at a zero,
`lem:resolvent`(2)). -/
def gStarY (S : SectorSetting) (s : ℕ) (ℓ : ℕ) (z : ℂ) (G : ℝ) : Ysec s S.Nstar ℓ :=
  toYsec s S.Nstar ℓ (Ang.ofProfile ℓ (S.gStar ℓ z G))

open Classical in
/-- `ℓ_*` as a continuous functional on `Y^s_ℓ`, `g ↦ ℓ_*(g_ℓ)` (chosen). -/
def ellStarY (S : SectorSetting) (s : ℕ) (ℓ : ℕ) (z : ℂ) (G : ℝ) : Ysec s S.Nstar ℓ →L[ℂ] ℂ :=
  if h : ∃ T : Ysec s S.Nstar ℓ →L[ℂ] ℂ, ∀ g : Ysec s S.Nstar ℓ,
      T g = S.ellStar ℓ z G (Polar.angularSector g.fn ℓ)
  then h.choose else 0

/-- The rank-one projection `P g = ℓ_*(g) g_*` on `Y^s_ℓ`: the Riesz projection of `L_ℓ(G)` at
`λ_*` (`thm:evans-simple`(2), `04_ring.tex:462-469`; restructuring R2, `Dunford.rankOneProj`). -/
def rieszSec (S : SectorSetting) (s : ℕ) (ℓ : ℕ) (z : ℂ) (G : ℝ) :
    Ysec s S.Nstar ℓ →L[ℂ] Ysec s S.Nstar ℓ :=
  Dunford.rankOneProj (S.ellStarY s ℓ z G) (S.gStarY s ℓ z G)

/-- `conj(g_*) e^{-iℓθ} = conj(g_* e^{iℓθ})` as an element of `Y^s_{-ℓ}`. -/
def gStarBarY (S : SectorSetting) (s : ℕ) (ℓ : ℕ) (z : ℂ) (G : ℝ) : Ysec s S.Nstar (-(ℓ : ℤ)) :=
  toYsec s S.Nstar (-(ℓ : ℤ)) (Ang.ofProfile (-(ℓ : ℤ)) fun r => conj (S.gStar ℓ z G r))

open Classical in
/-- `h ↦ conj(ℓ_*(conj h_{-ℓ}))` as a continuous functional on `Y^s_{-ℓ}` (chosen). -/
def ellStarBarY (S : SectorSetting) (s : ℕ) (ℓ : ℕ) (z : ℂ) (G : ℝ) :
    Ysec s S.Nstar (-(ℓ : ℤ)) →L[ℂ] ℂ :=
  if h : ∃ T : Ysec s S.Nstar (-(ℓ : ℤ)) →L[ℂ] ℂ, ∀ g : Ysec s S.Nstar (-(ℓ : ℤ)),
      T g = S.ellStarBar ℓ z G (Polar.angularSector g.fn (-(ℓ : ℤ)))
  then h.choose else 0

/-- The Riesz projection of `L_{-ℓ}(G)` at `conj λ_*`, `h ↦ conj(ℓ_*(conj h)) conj(g_*)`, on
`Y^s_{-ℓ}` (`prop:SU`, `04_ring.tex:1263-1266`). -/
def rieszSecBar (S : SectorSetting) (s : ℕ) (ℓ : ℕ) (z : ℂ) (G : ℝ) :
    Ysec s S.Nstar (-(ℓ : ℤ)) →L[ℂ] Ysec s S.Nstar (-(ℓ : ℤ)) :=
  Dunford.rankOneProj (S.ellStarBarY s ℓ z G) (S.gStarBarY s ℓ z G)

/-! ### Basic lemmas (fully proved) -/

theorem evans_def (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) :
    S.evans ℓ z G = ((Real.exp (-(ℓ : ℝ) * (S.ξ₂ - S.ξ₁)) : ℝ) : ℂ) *
      (S.dpsi ℓ z G S.ξ₂ + (ℓ : ℂ) * S.psi ℓ z G S.ξ₂) := rfl

theorem ellStarY_spec_of_exists (S : SectorSetting) (s ℓ : ℕ) (z : ℂ) (G : ℝ)
    (h : ∃ T : Ysec s S.Nstar ℓ →L[ℂ] ℂ, ∀ g : Ysec s S.Nstar ℓ,
      T g = S.ellStar ℓ z G (Polar.angularSector g.fn ℓ))
    (g : Ysec s S.Nstar ℓ) :
    S.ellStarY s ℓ z G g = S.ellStar ℓ z G (Polar.angularSector g.fn ℓ) := by
  classical
  rw [ellStarY, dite_eq_left h]
  exact h.choose_spec g

theorem ellStarBarY_spec_of_exists (S : SectorSetting) (s ℓ : ℕ) (z : ℂ) (G : ℝ)
    (h : ∃ T : Ysec s S.Nstar (-(ℓ : ℤ)) →L[ℂ] ℂ, ∀ g : Ysec s S.Nstar (-(ℓ : ℤ)),
      T g = S.ellStarBar ℓ z G (Polar.angularSector g.fn (-(ℓ : ℤ))))
    (g : Ysec s S.Nstar (-(ℓ : ℤ))) :
    S.ellStarBarY s ℓ z G g = S.ellStarBar ℓ z G (Polar.angularSector g.fn (-(ℓ : ℤ))) := by
  classical
  rw [ellStarBarY, dite_eq_left h]
  exact h.choose_spec g

theorem rieszSec_apply (S : SectorSetting) (s ℓ : ℕ) (z : ℂ) (G : ℝ) (g : Ysec s S.Nstar ℓ) :
    S.rieszSec s ℓ z G g = S.ellStarY s ℓ z G g • S.gStarY s ℓ z G := rfl

theorem rieszSecBar_apply (S : SectorSetting) (s ℓ : ℕ) (z : ℂ) (G : ℝ)
    (g : Ysec s S.Nstar (-(ℓ : ℤ))) :
    S.rieszSecBar s ℓ z G g = S.ellStarBarY s ℓ z G g • S.gStarBarY s ℓ z G := rfl

/-- `ℓ_*(g_*) = J/J = 1` when `J ≠ 0` (`04_ring.tex:529`, `lem:adjoint`(2), `04_ring.tex:614`). -/
theorem ellStar_gStar (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) (hJ : S.J ℓ z G ≠ 0) :
    S.ellStar ℓ z G (S.gStar ℓ z G) = 1 := by
  rw [ellStar, ← J]
  exact inv_mul_cancel₀ hJ

end SectorSetting

end NonUniqueEuler
