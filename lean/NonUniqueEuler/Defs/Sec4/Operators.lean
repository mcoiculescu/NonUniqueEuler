import NonUniqueEuler.Defs.Sec4.Setting
import NonUniqueEuler.Defs.Sec4.Bridge

/-!
# Section 4: the operators of a sector setting on the sector spaces (definitions)

Manuscript `04_ring.tex:155-185`
(spaces), `:161-166` (`L(G)`, `L_ℓ(G)`), `:924-1012` (`lem:semigroup-construct`), with
decision D8 and restructuring R1 (see `FORMALIZATION_NOTES.md`): the linear evolution
`e^{tL(G)}` on `Y^s` is **defined** sector-wise as `⊕_ℓ exp(t L_ℓ(G))`
(`Sect.sectorExp`, I-SECT), the manuscript's `lem:semigroup-construct`(3).

The spaces of a setting `S` are those of I-SECT on `N_* = S.Nstar`:
`Y^s = Sect.Y s S.Nstar`, `Y^s_ℓ = Sect.Ysec s S.Nstar ℓ`, `Y^s_𝒵 = Sect.YZ s S.Nstar 𝒵`.
An element `g : Ysec s S.Nstar ℓ` is the plane function `g.fn = g_ℓ(r) e^{iℓθ}`; its profile
(the manuscript's element of `Y^s_ℓ`) is `Polar.angularSector g.fn ℓ`. The norm of `Ysec` is the
`H^s` norm of `g_ℓ(r)e^{iℓθ}`, as in the manuscript (`04_ring.tex:157-158`); the profile norm
`‖g_ℓ‖_{s,ℓ}` is `S.secNormY s g`.

Operators (all ℂ-linear and continuous; the chosen ones are `if h : ∃ T, spec T then h.choose
else 0`, so they are the right operators once the interface files prove the existence):
* `S.transSec s ℓ G`: multiplication by `-iℓΩ(r;G)` on `Y^s_ℓ` (`Sect.radialMul`);
* `S.Ksec s ℓ`: `k_ℓ 𝒢_ℓ` on `Y^s_ℓ` (chosen; `𝒦` on the sector `ℓ`, `cor:K-bound`);
* `S.Lsec s ℓ G = S.transSec s ℓ G + S.Ksec s ℓ`: the sector operator `L_ℓ(G)` on `Y^s_ℓ`;
* `S.semigroup s G t = ⊕_ℓ exp(t L_ℓ(G))` on `Y^s` (D8, R1);
* `S.transportY s G t = ⊕_ℓ exp(t(-iℓΩ))`: the transport group `e^{tL^tr}` on `Y^s`;
* `S.KY s`: `𝒦 = -(K_BS * ·)·∇ω̄` on `Y^s` (chosen);
* `S.LinY s G : Y^{s+1} → Y^s`: the linearization `L(G)` (chosen, from `S.linFn`).

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace SectorSetting

open Sect

/-- Multiplication by `-iℓΩ(r;G)` on `Y^s_ℓ`: the transport part of `L_ℓ(G)`
(`04_ring.tex:165`), and the generator of `e^{tL^tr}` on the sector `ℓ` (`04_ring.tex:949-950`). -/
def transSec (S : SectorSetting) (s : ℕ) (ℓ : ℤ) (G : ℝ) :
    Ysec s S.Nstar ℓ →L[ℂ] Ysec s S.Nstar ℓ :=
  radialMul s S.Nstar ℓ fun r => -(Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ))

open Classical in
/-- The coupling operator `k_ℓ 𝒢_ℓ` on `Y^s_ℓ` (`04_ring.tex:165`; `cor:K-bound`,
`04_ring.tex:900-907`). Chosen: the continuous linear map whose value has profile
`k_ℓ 𝒢_ℓ g_ℓ` (`0` if there is none). -/
def Ksec (S : SectorSetting) (s : ℕ) (ℓ : ℤ) : Ysec s S.Nstar ℓ →L[ℂ] Ysec s S.Nstar ℓ :=
  if h : ∃ T : Ysec s S.Nstar ℓ →L[ℂ] Ysec s S.Nstar ℓ, ∀ g : Ysec s S.Nstar ℓ,
      (T g).fn =ᵐ[volume] Ang.ofProfile ℓ (S.KsecFn ℓ (Polar.angularSector g.fn ℓ))
  then h.choose else 0

/-- The **sector operator** `L_ℓ(G) = -iℓΩ + k_ℓ 𝒢_ℓ` on `Y^s_ℓ` (`04_ring.tex:165-166`; bounded
by `lem:sector`(4) and the remark after `lem:semigroup-construct`, `04_ring.tex:944-947`). For
`ℓ = 0` both summands are `0` (this follows from the specifications). -/
def Lsec (S : SectorSetting) (s : ℕ) (ℓ : ℤ) (G : ℝ) : Ysec s S.Nstar ℓ →L[ℂ] Ysec s S.Nstar ℓ :=
  S.transSec s ℓ G + S.Ksec s ℓ

/-- The **linear evolution** `e^{tL(G)}` on `Y^s`, defined sector-wise as
`⊕_ℓ exp(t L_ℓ(G))` (decision D8, restructuring R1; this is `lem:semigroup-construct`(3),
`04_ring.tex:940-941`). -/
def semigroup (S : SectorSetting) (s : ℕ) (G t : ℝ) : Y s S.Nstar →L[ℂ] Y s S.Nstar :=
  sectorExp s S.Nstar (fun ℓ => S.Lsec s ℓ G) t

/-- The transport group `e^{tL^tr}` on `Y^s`, sector-wise `exp(t(-iℓΩ))`
(`lem:semigroup-construct`(1), `04_ring.tex:929-933`). -/
def transportY (S : SectorSetting) (s : ℕ) (G t : ℝ) : Y s S.Nstar →L[ℂ] Y s S.Nstar :=
  sectorExp s S.Nstar (fun ℓ => S.transSec s ℓ G) t

open Classical in
/-- The coupling operator `𝒦w = -(K_BS * w)·∇ω̄` on `Y^s` (`04_ring.tex:927`; bounded by
`lem:semigroup-construct`(1)). Chosen from `S.couplingFn`. -/
def KY (S : SectorSetting) (s : ℕ) : Y s S.Nstar →L[ℂ] Y s S.Nstar :=
  if h : ∃ T : Y s S.Nstar →L[ℂ] Y s S.Nstar, ∀ w : Y s S.Nstar,
      (T w).fn =ᵐ[volume] S.couplingFn w.fn
  then h.choose else 0

open Classical in
/-- The **linearization** `L(G) : Y^{s+1} → Y^s` (`04_ring.tex:161-164`;
`‖L(G)w‖_{Y^s} ≤ C‖w‖_{Y^{s+1}}`, `lem:semigroup-construct`(2)). Chosen from `S.linFn`. -/
def LinY (S : SectorSetting) (s : ℕ) (G : ℝ) : Y (s + 1) S.Nstar →L[ℂ] Y s S.Nstar :=
  if h : ∃ T : Y (s + 1) S.Nstar →L[ℂ] Y s S.Nstar, ∀ w : Y (s + 1) S.Nstar,
      (T w).fn =ᵐ[volume] S.linFn G w.fn
  then h.choose else 0

/-- The manuscript's profile norm `‖g_ℓ‖_{s,ℓ}` of `g ∈ Y^s_ℓ` (`04_ring.tex:836-841`). It is
equivalent to `‖g‖` uniformly in `ℓ` (`Sect.exists_norm_Ysec_equiv`). -/
def secNormY (S : SectorSetting) (s : ℕ) {ℓ : ℤ} (g : Ysec s S.Nstar ℓ) : ℝ :=
  Sob.secNorm s ℓ (Icc S.ρm S.ρp) (Polar.angularSector g.fn ℓ)

/-! ### Specifications of the chosen operators, given existence (fully proved) -/

theorem Lsec_def (S : SectorSetting) (s : ℕ) (ℓ : ℤ) (G : ℝ) :
    S.Lsec s ℓ G = S.transSec s ℓ G + S.Ksec s ℓ := rfl

theorem semigroup_def (S : SectorSetting) (s : ℕ) (G t : ℝ) :
    S.semigroup s G t = sectorExp s S.Nstar (fun ℓ => S.Lsec s ℓ G) t := rfl

theorem Ksec_spec_of_exists (S : SectorSetting) (s : ℕ) (ℓ : ℤ)
    (h : ∃ T : Ysec s S.Nstar ℓ →L[ℂ] Ysec s S.Nstar ℓ, ∀ g : Ysec s S.Nstar ℓ,
      (T g).fn =ᵐ[volume] Ang.ofProfile ℓ (S.KsecFn ℓ (Polar.angularSector g.fn ℓ)))
    (g : Ysec s S.Nstar ℓ) :
    (S.Ksec s ℓ g).fn =ᵐ[volume] Ang.ofProfile ℓ (S.KsecFn ℓ (Polar.angularSector g.fn ℓ)) := by
  classical
  rw [Ksec, dite_eq_left h]
  exact h.choose_spec g

theorem KY_spec_of_exists (S : SectorSetting) (s : ℕ)
    (h : ∃ T : Y s S.Nstar →L[ℂ] Y s S.Nstar, ∀ w : Y s S.Nstar,
      (T w).fn =ᵐ[volume] S.couplingFn w.fn)
    (w : Y s S.Nstar) : (S.KY s w).fn =ᵐ[volume] S.couplingFn w.fn := by
  classical
  rw [KY, dite_eq_left h]
  exact h.choose_spec w

theorem LinY_spec_of_exists (S : SectorSetting) (s : ℕ) (G : ℝ)
    (h : ∃ T : Y (s + 1) S.Nstar →L[ℂ] Y s S.Nstar, ∀ w : Y (s + 1) S.Nstar,
      (T w).fn =ᵐ[volume] S.linFn G w.fn)
    (w : Y (s + 1) S.Nstar) : (S.LinY s G w).fn =ᵐ[volume] S.linFn G w.fn := by
  classical
  rw [LinY, dite_eq_left h]
  exact h.choose_spec w

end SectorSetting

end NonUniqueEuler
