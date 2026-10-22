import NonUniqueEuler.Defs.Sec4.Operators
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.Defs.Infra.Multipole
import NonUniqueEuler.H.Sec4.Sector.GreenSol
import NonUniqueEuler.H.Sec4.Sector.GreenGrowth
import NonUniqueEuler.H.Sec4.Sector.GreenUnique
import NonUniqueEuler.H.Sec4.Sector.Riccati
import NonUniqueEuler.H.Sec4.Sector.Ksec0
import NonUniqueEuler.H.Sec4.Sector.Transport
import NonUniqueEuler.H.Sec4.Sector.Coupling
import NonUniqueEuler.H.Sec4.Sector.LogPot
import NonUniqueEuler.I.Sec4.Sector.LogPotReal
import NonUniqueEuler.I.Sec4.Sector.CouplingProj
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives
import NonUniqueEuler.I.Infra.AngularFourier.Sector

/-!
# Proof of `lem:sector` (`I/Sec4/Sector.lean`)

Manuscript `04_ring.tex:200-221` (statement), proof `:222-283`.

* Part (1). `green_spec`: the kernel computation of `H/Sec4/Sector/GreenSol.lean` (Fubini and
  the two FTCs for the kernel `(min/max)ⁿρ`, whose `r`-derivative jumps by `-2n` on the diagonal)
  and the growth `H/Sec4/Sector/GreenGrowth.lean`. `green_unique`: `H/Sec4/Sector/GreenUnique.lean`
  (two first integrals of the homogeneous equation instead of "`ψ₁ - ψ₂ = Arⁿ + Br⁻ⁿ`").
  `green_eq_logPotential`: the rotation reduction `H/Sec4/Sector/LogPot.lean` and the value on the
  real axis `I/Sec4/Sector/LogPotReal.lean` (a direct polar-coordinate computation, instead of
  Liouville plus density). `green_bound`: `norm_green_le` (kernel `≤ 1`, Cauchy–Schwarz).
* Part (2). `couplingFn_sector`: `I/Sec4/Sector/CouplingProj.lean` (`𝒦` commutes with `P_ℓ`) and
  `I/Sec4/Sector/CouplingOfProfile.lean` (`𝒦` on a sector function), assembled in
  `H/Sec4/Sector/Coupling.lean`. `linFn_sector`: `P_ℓ` of the transport part by
  `sectorProj_thetaDeriv` (`P_ℓ ∂_θ = iℓ P_ℓ`), linearity of the pointwise rotation average on
  `L¹_loc` (`H/Sec4/Sector/Transport.lean`). `linFn_real`, `linFn_rot`: weak derivatives of real
  functions are real, the weak chain rule for rotations, and `couplingFn_rot`.
* Parts (3), (4): `H/Sec4/Sector/Riccati.lean`, `H/Sec4/Sector/Ksec0.lean`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Asymptotics ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler

namespace SectorSetting

open Sect

/-! ### Part (1): the Green operator -/

/-- `lem:sector`(1): for `ℓ ≠ 0` and `g ∈ Y^0_ℓ`, `𝒢_ℓ g` solves
`ψ'' + ψ'/r - ℓ²ψ/r² = g` on `(0,∞)`, with `ψ = O(r^{|ℓ|})` as `r → 0` and `ψ = O(r^{-|ℓ|})`
as `r → ∞`. -/
theorem green_spec (S : SectorSetting) (hS : S.Valid) {ℓ : ℤ} (hℓ : ℓ ≠ 0) {g : ℝ → ℂ}
    (hg : S.IsProfileL2 g) :
    IsRadialPoissonSol ℓ g (green ℓ g) ∧
      (green ℓ g =O[𝓝[>] 0] fun r : ℝ => r ^ ℓ.natAbs) ∧
      (green ℓ g =O[atTop] fun r : ℝ => r ^ (-(ℓ.natAbs : ℤ))) := by
  have h := SectorH.prof_of_isProfileL2 hS hg
  exact ⟨SectorH.isRadialPoissonSol_green h hℓ, SectorH.green_isBigO_zero h ℓ,
    SectorH.green_isBigO_atTop h ℓ⟩

/-- `lem:sector`(1), uniqueness: any solution of `ψ'' + ψ'/r - ℓ²ψ/r² = g` on `(0,∞)` that is
`O(r^{|ℓ|})` at `0` and `O(r^{-|ℓ|})` at `∞` equals `𝒢_ℓ g` on `(0,∞)`. -/
theorem green_unique (S : SectorSetting) (hS : S.Valid) {ℓ : ℤ} (hℓ : ℓ ≠ 0) {g : ℝ → ℂ}
    (hg : S.IsProfileL2 g) {ψ : ℝ → ℂ} (hψ : IsRadialPoissonSol ℓ g ψ)
    (h0 : ψ =O[𝓝[>] 0] fun r : ℝ => r ^ ℓ.natAbs)
    (hinf : ψ =O[atTop] fun r : ℝ => r ^ (-(ℓ.natAbs : ℤ))) :
    EqOn ψ (green ℓ g) (Ioi 0) := by
  have h := SectorH.prof_of_isProfileL2 hS hg
  obtain ⟨hG, hG0, hGinf⟩ := green_spec S hS hℓ hg
  exact SectorH.eqOn_of_isRadialPoissonSol hℓ (fun a' b' ha' hb' => h.intervalIntegrable ha' hb')
    hψ hG (h0.sub hG0) (hinf.sub hGinf)

/-- `lem:sector`(1), equivalently: `(𝒢_ℓ g)(r) e^{iℓθ} = Δ⁻¹(g(r)e^{iℓθ})`, the convolution
with `(2π)⁻¹ log|x|` (equality in `L²_loc`, i.e. almost everywhere). -/
theorem green_eq_logPotential (S : SectorSetting) (hS : S.Valid) {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    {g : ℝ → ℂ} (hg : S.IsProfileL2 g) :
    Ang.ofProfile ℓ (green ℓ g) =ᵐ[volume] Multipole.logPotential (Ang.ofProfile ℓ g) := by
  have h0 : ∀ᵐ x : ℂ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [h0] with x hx
  rw [SectorH.logPotential_ofProfile_rot ℓ g hx,
    logPotential_ofProfile_ofReal S hS hℓ hg (norm_pos_iff.2 hx), Ang.ofProfile]
  ring

/-- `lem:sector`(1), last assertion: `𝒢_ℓ` is bounded from `Y^0_ℓ` to `C([ρ₋,ρ₊])`; precisely
`𝒢_ℓ g` is continuous on `(0,∞)` and `|𝒢_ℓ g(r)| ≤ (ρ₊/(2|ℓ|)) ‖g‖_{L²((0,∞), r dr)}` for all
`r > 0` (`04_ring.tex:228-231`). -/
theorem green_bound (S : SectorSetting) (hS : S.Valid) {ℓ : ℤ} (hℓ : ℓ ≠ 0) {g : ℝ → ℂ}
    (hg : S.IsProfileL2 g) :
    ContinuousOn (green ℓ g) (Ioi 0) ∧
      ∀ r : ℝ, 0 < r →
        ‖green ℓ g r‖ ≤ S.ρp / (2 * |(ℓ : ℝ)|) *
          Real.sqrt (∫ ρ in Ioi (0 : ℝ), ‖g ρ‖ ^ 2 * ρ) :=
  ⟨SectorH.continuousOn_green hS hg ℓ, fun _ hr =>
    SectorH.norm_green_le (SectorH.prof_of_isProfileL2 hS hg) hg.1 hℓ hr.le⟩

/-! ### Part (2): sector invariance -/

/-- `lem:sector`(2): `L(G)` preserves angular sectors: for `w ∈ Y^{s+1}`,
`P_ℓ L(G)w = (L_ℓ(G) g_ℓ)(r) e^{iℓθ}` for every `ℓ` (`g_ℓ` the sector profiles of `w`). -/
theorem linFn_sector (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ)
    (w : Y (s + 1) S.Nstar) (ℓ : ℤ) :
    Ang.sectorProj ℓ (S.linFn G w.fn) =ᵐ[volume]
      Ang.ofProfile ℓ (S.LsecFn ℓ G (Polar.angularSector w.fn ℓ)) := by
  have hw := (SectorH.y_memH w).1
  have hw1 : Sob.MemH 1 w.fn := SectorH.MemH.mono hw (by omega)
  have hsupp := SectorH.y_supp w
  have hL : S.linFn G w.fn = fun y => (fun r : ℝ => -((S.Omega G r : ℝ) : ℂ)) ‖y‖ *
      Ang.thetaDeriv w.fn y + S.couplingFn w.fn y := rfl
  -- local integrability of the two parts
  have h10 : ((1, 0) : ℕ × ℕ) ∈ Sob.multiIdx 1 := by decide
  have h01 : ((0, 1) : ℕ × ℕ) ∈ Sob.multiIdx 1 := by decide
  have hloc1 : LocallyIntegrable (Ang.thetaDeriv w.fn) volume := by
    have a1 := ((hw1.memLp_weakPartial h01).1.locallyIntegrable (by norm_num)).continuous_mul
      (Complex.continuous_ofReal.comp Complex.continuous_re)
    have a2 := ((hw1.memLp_weakPartial h10).1.locallyIntegrable (by norm_num)).continuous_mul
      (Complex.continuous_ofReal.comp Complex.continuous_im)
    exact a1.sub a2
  have hloc2 : LocallyIntegrable (S.couplingFn w.fn) volume :=
    (SectorH.memLp_couplingFn hS (SectorH.memLp_of_memH hw) hsupp).locallyIntegrable
      (by norm_num)
  have hlin := SectorH.sectorProj_radial_mul_add_ae ℓ (fun r : ℝ => -((S.Omega G r : ℝ) : ℂ))
    hloc1 hloc2
  have hth := Ang.sectorProj_thetaDeriv hw1 ℓ
  have hcp := SectorH.couplingFn_sector_fn S hS hw hsupp ℓ
  have h0 : ∀ᵐ x : ℂ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  rw [hL]
  filter_upwards [hlin, hth, hcp, h0] with x h1 h2 h3 hx
  rw [h1, h2, h3, Ang.sectorProj_eq_angularSector ℓ w.fn hx]
  simp only [Ang.ofProfile, LsecFn]
  ring

/-- `lem:sector`(2), the coupling term, for every `w ∈ Y^0`:
`P_ℓ(-(K_BS * w)·∇ω̄) = (k_ℓ 𝒢_ℓ g_ℓ)(r) e^{iℓθ}`. -/
theorem couplingFn_sector (S : SectorSetting) (hS : S.Valid) (w : Y 0 S.Nstar) (ℓ : ℤ) :
    Ang.sectorProj ℓ (S.couplingFn w.fn) =ᵐ[volume]
      Ang.ofProfile ℓ (S.KsecFn ℓ (Polar.angularSector w.fn ℓ)) :=
  SectorH.couplingFn_sector_fn S hS (SectorH.y_memH w).1 (SectorH.y_supp w) ℓ

/-- `lem:sector`(2): `L_{-ℓ}(G) ḡ = conj(L_ℓ(G) g)` (pointwise; `Ω`, `ω̄'` and the kernel of
`𝒢_ℓ = 𝒢_{-ℓ}` are real). -/
theorem LsecFn_neg_conj (S : SectorSetting) (ℓ : ℤ) (G : ℝ) (g : ℝ → ℂ) (r : ℝ) :
    S.LsecFn (-ℓ) G (fun ρ => conj (g ρ)) r = conj (S.LsecFn ℓ G g r) :=
  SectorH.LsecFn_neg_conj' S ℓ G g r

/-- `lem:sector`(2): `L(G)` maps real functions to real functions. -/
theorem linFn_real (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ) (w : Y (s + 1) S.Nstar)
    (hw : w.IsReal) : ∀ᵐ x ∂(volume : Measure ℂ), (S.linFn G w.fn x).im = 0 := by
  have hw1 : Sob.MemH 1 w.fn := SectorH.MemH.mono (SectorH.y_memH w).1 (by omega)
  filter_upwards [SectorH.thetaDeriv_im_eq_zero hw1 hw] with x hx
  simp only [linFn, transportPartFn, Complex.add_im, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, hx, SectorH.couplingFn_im_eq_zero S hw x]
  ring

/-- `lem:sector`(2): `L(G)` commutes with rotations of `ℝ²`. -/
theorem linFn_rot (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ) (w : Y (s + 1) S.Nstar)
    (φ : ℝ) :
    S.linFn G (fun x => w.fn (rot φ x)) =ᵐ[volume] fun x => S.linFn G w.fn (rot φ x) := by
  have hw1 : Sob.MemH 1 w.fn := SectorH.MemH.mono (SectorH.y_memH w).1 (by omega)
  filter_upwards [SectorH.thetaDeriv_comp_rot hw1 φ] with x hx
  simp only [linFn, transportPartFn, hx, Polar.norm_rot, couplingFn_rot S hS w.fn φ x]

/-! ### Part (3): the Riccati coefficient -/

/-- `lem:sector`(3): for `ℓ ≥ 1` and `Re λ > 0`, `|λ + iℓΩ(r;G)| ≥ Re λ` for every `r > 0`;
`V_ℓ(·;λ,G)` is smooth in `ξ`, holomorphic in `λ` on `{Re λ > 0}` (and jointly continuous in
`(ξ, λ)`), and equal to `ℓ²` outside `[ξ₁, ξ₂]`. -/
theorem sector_riccati (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (G : ℝ) :
    (∀ z : ℂ, 0 < z.re → ∀ r : ℝ, 0 < r →
        z.re ≤ ‖z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)‖) ∧
      (∀ z : ℂ, 0 < z.re → ContDiff ℝ ∞ (fun ξ => S.Vric ℓ z G ξ)) ∧
      (∀ ξ : ℝ, DifferentiableOn ℂ (fun z => S.Vric ℓ z G ξ) {z : ℂ | 0 < z.re}) ∧
      ContinuousOn (fun p : ℝ × ℂ => S.Vric ℓ p.2 G p.1) (univ ×ˢ {z : ℂ | 0 < z.re}) ∧
      (∀ (z : ℂ) (ξ : ℝ), ξ ∉ Icc S.ξ₁ S.ξ₂ → S.Vric ℓ z G ξ = (ℓ : ℂ) ^ 2) :=
  SectorH.sector_riccati' S hS ℓ G

/-! ### Part (4): `L_ℓ(G)` is bounded on `Y^0_ℓ` -/

/-- `lem:sector`(4): the sector operator `L_ℓ(G)` is a bounded operator on `Y^0_ℓ`: the chosen
continuous operator `S.Lsec 0 ℓ G` acts on sector profiles as `L_ℓ(G)`. -/
theorem Lsec_zero_spec (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) (G : ℝ)
    (g : Ysec 0 S.Nstar ℓ) :
    (S.Lsec 0 ℓ G g).fn =ᵐ[volume]
      Ang.ofProfile ℓ (S.LsecFn ℓ G (Polar.angularSector g.fn ℓ)) :=
  SectorH.Lsec_zero_spec' S hS ℓ G g

end SectorSetting

end NonUniqueEuler
