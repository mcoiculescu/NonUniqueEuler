import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.H.Sec4.EvansSimple.Deriv
import NonUniqueEuler.H.Sec4.EvansSimple.Conj
import NonUniqueEuler.H.Sec4.EvansSimple.Lift
import NonUniqueEuler.I.Sec4.EvansSimple.Range
import NonUniqueEuler.I.Sec4.EvansSimple.GenEigen
import NonUniqueEuler.I.Sec4.Resolvent
import NonUniqueEuler.I.Infra.AngularFourier.Symmetry

/-!
# Proof of `thm:evans-simple` (`I/Sec4/EvansSimple.lean`)

Manuscript `04_ring.tex:450-563`. Same declarations as the interface file, proved.

* `evansSimple_J_eq`: substitution `r = e^ξ` (`H/Sec4/EvansSimple/Deriv.lean`);
* `evansSimple_deriv` (part (1)): the variational equation of `∂_λψ` and the integrated
  Wronskian identity (`H/Sec4/EvansSimple/Deriv.lean`);
* `evansSimple_riesz` (part (2), R2): **restructured.** Instead of computing the Riesz projection
  by a contour integral and the residue theorem (`04_ring.tex:498-534`), the Laurent form
  `Dunford.IsSimpleSpectralProj` is derived from the abstract criterion
  `EvansSimpleAux.isSimpleSpectralProj_of_range` (`H/Sec4/EvansSimple/Abstract.lean`): eigenvector
  `g_*` (`lem:resolvent`(2)), one-dimensional eigenspace (`lem:resolvent`(2)), the functional
  `ℓ_*` bounded on `Y^s_ℓ` (`H/Sec4/EvansSimple/Functional.lean`) with `ℓ_*(g_*) = 1` and
  `ℓ_* ∘ L_ℓ = λ_* ℓ_*` (the adjoint eigenfunction, `lem:adjoint`(1) in weak form), and the
  solvability `ran(L_ℓ - λ_*) ⊇ ker ℓ_*` (`I/Sec4/EvansSimple/Range.lean`);
* `evansSimple_riesz_conj`: transport by the conjugation `C` of `exists_conj_Ysec`
  (`H/Sec4/EvansSimple/Conj.lean`);
* `evansSimple_not_simple` (part (3)): the generalized eigenprofile (`I/Sec4/EvansSimple/GenEigen`),
  lifted to `Y^s_ℓ` (`H/Sec4/EvansSimple/Lift.lean`), and `I/Sec4/RieszFixes.lean`;
* `evansSimple_J_eq_zero_of_genEigen`: the unnormalized functional annihilates
  `ran(L_ℓ - λ_*)` and equals `J` at `g_*` (restructured, `H/Sec4/EvansSimple/Lift.lean`);
* `evansSimple_iff` (part (4)): combination.
-/

noncomputable section

open MeasureTheory Set ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler

namespace EvansSimpleAux

open SectorSetting Sect

theorem exp_ne_zero' (x : ℝ) : ((Real.exp x : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.exp_pos x).ne'

/-- The hypotheses of the criterion `isSimpleSpectralProj_of_range` for `L_ℓ(G)` on `Y^s_ℓ` at a
zero `λ_*` with `J ≠ 0`. -/
theorem riesz_hyps (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) (hJ : S.J ℓ z G ≠ 0) (s : ℕ) :
    (∀ g : Ysec s S.Nstar ℓ,
        S.ellStarY s ℓ z G g = S.ellStar ℓ z G (Polar.angularSector g.fn ℓ)) ∧
      S.ellStarY s ℓ z G (S.gStarY s ℓ z G) = 1 ∧
      S.Lsec s ℓ G (S.gStarY s ℓ z G) = z • S.gStarY s ℓ z G ∧
      (∀ g, S.ellStarY s ℓ z G (S.Lsec s ℓ G g) = z * S.ellStarY s ℓ z G g) ∧
      (∀ η : Ysec s S.Nstar ℓ, S.Lsec s ℓ G η = z • η → ∃ c : ℂ, η = c • S.gStarY s ℓ z G) ∧
      ∀ h : Ysec s S.Nstar ℓ, S.ellStarY s ℓ z G h = 0 →
        ∃ x : Ysec s S.Nstar ℓ, S.Lsec s ℓ G x - z • x = h := by
  have hspec := ellStarY_spec S hS s ℓ hℓ hz G
  have heig := (eigen_of_evans_eq_zero S hS ℓ hℓ z hz G hE).2.2.2.2 s
  refine ⟨hspec, ellStarY_gStarY S hS s ℓ hℓ hz G hE hJ, heig.2.2.1,
    ellStarY_Lsec S hS s ℓ hℓ hz G hE, heig.2.2.2, fun h hh => ?_⟩
  rw [hspec, ellStar, mul_eq_zero] at hh
  exact evansSimple_range S hS ℓ hℓ z hz G hE s h (hh.resolve_left (inv_ne_zero hJ))

end EvansSimpleAux

namespace SectorSetting

open Sect

/-- `thm:evans-simple`, the two expressions of `J` (`04_ring.tex:455-457`):
`J = ∫_0^∞ g_* ψ_*(log r) M_* r dr = iℓ ∫_ℝ f_ξ ψ_*² / (λ_* + iℓΩ(e^ξ;G))² dξ`. -/
theorem evansSimple_J_eq (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) :
    S.J ℓ z G = Complex.I * (ℓ : ℂ) *
      ∫ ξ : ℝ, ((S.fxi ξ : ℝ) : ℂ) * S.psi ℓ z G ξ ^ 2 /
        (z + Complex.I * (ℓ : ℂ) * ((S.Omega G (Real.exp ξ) : ℝ) : ℂ)) ^ 2 := by
  exact EvansSimpleAux.J_eq_integral S ℓ z G

/-- `thm:evans-simple`(1): `ψ_*(ξ₂) ≠ 0` and
`e^{ℓ(ξ₂-ξ₁)} ψ_*(ξ₂) ∂_λE_ℓ(λ_*;G) = -J`. -/
theorem evansSimple_deriv (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) :
    S.psi ℓ z G S.ξ₂ ≠ 0 ∧
      ((Real.exp (ℓ * (S.ξ₂ - S.ξ₁)) : ℝ) : ℂ) * S.psi ℓ z G S.ξ₂ *
          deriv (fun w => S.evans ℓ w G) z = -S.J ℓ z G := by
  exact EvansSimpleAux.evans_deriv_identity S hS ℓ hℓ z hz G hE

/-- `thm:evans-simple`(2), restructured (R2): if `∂_λE_ℓ(λ_*;G) ≠ 0`, then `J ≠ 0`, and on every
`Y^s_ℓ`: `ℓ_*` is a bounded functional acting on profiles by the formula of `S.ellStar`,
`ℓ_*(g_*) = 1`, `P g = ℓ_*(g)g_*` is the spectral (Riesz) projection of `L_ℓ(G)` at `λ_*`
(Laurent form), and `λ_*` is an algebraically simple eigenvalue. -/
theorem evansSimple_riesz (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0)
    (hE' : deriv (fun w => S.evans ℓ w G) z ≠ 0) :
    S.J ℓ z G ≠ 0 ∧
      ∀ s : ℕ,
        (∀ g : Ysec s S.Nstar ℓ,
            S.ellStarY s ℓ z G g = S.ellStar ℓ z G (Polar.angularSector g.fn ℓ)) ∧
          S.ellStarY s ℓ z G (S.gStarY s ℓ z G) = 1 ∧
          Dunford.IsSimpleSpectralProj (S.Lsec s ℓ G) (S.rieszSec s ℓ z G) z ∧
          Dunford.IsAlgSimpleEig (S.Lsec s ℓ G) z := by
  obtain ⟨hψ, hid⟩ := evansSimple_deriv S hS ℓ hℓ z hz G hE
  have hJ : S.J ℓ z G ≠ 0 := by
    intro hJ0
    rw [hJ0, neg_zero] at hid
    exact hE' ((mul_eq_zero.1 hid).resolve_left (mul_ne_zero (EvansSimpleAux.exp_ne_zero' _) hψ))
  refine ⟨hJ, fun s => ?_⟩
  obtain ⟨hspec, h1, hAg, hfA, hker, hrange⟩ :=
    EvansSimpleAux.riesz_hyps S hS ℓ hℓ hz G hE hJ s
  have hP : Dunford.IsSimpleSpectralProj (S.Lsec s ℓ G) (S.rieszSec s ℓ z G) z :=
    EvansSimpleAux.isSimpleSpectralProj_of_range h1 hAg hfA hker hrange
  exact ⟨hspec, h1, hP, ⟨_, _, h1, hP⟩⟩

/-- `thm:evans-simple`(2) in the conjugate sector `-ℓ` (R2; `lem:resolvent`, last assertion;
`prop:SU`, `04_ring.tex:1263-1266`): if `∂_λE_ℓ(λ_*;G) ≠ 0`, then on every `Y^s_{-ℓ}`:
`h ↦ conj(ℓ_*(conj h))` is a bounded functional acting on profiles by `S.ellStarBar`,
`conj(g_*)e^{-iℓθ}` is an eigenvector of `L_{-ℓ}(G)` for `conj λ_*` on which this functional is `1`,
`P̄ h = conj(ℓ_*(conj h)) conj g_*` is the spectral (Riesz) projection of `L_{-ℓ}(G)` at `conj λ_*`
(Laurent form), and `conj λ_*` is an algebraically simple eigenvalue of `L_{-ℓ}(G)`. -/
theorem evansSimple_riesz_conj (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0)
    (hE' : deriv (fun w => S.evans ℓ w G) z ≠ 0) :
    ∀ s : ℕ,
      (∀ g : Ysec s S.Nstar (-(ℓ : ℤ)),
          S.ellStarBarY s ℓ z G g = S.ellStarBar ℓ z G (Polar.angularSector g.fn (-(ℓ : ℤ)))) ∧
        (S.gStarBarY s ℓ z G).fn =ᵐ[volume]
          Ang.ofProfile (-(ℓ : ℤ)) (fun r => conj (S.gStar ℓ z G r)) ∧
        S.gStarBarY s ℓ z G ≠ 0 ∧
        S.Lsec s (-(ℓ : ℤ)) G (S.gStarBarY s ℓ z G) = conj z • S.gStarBarY s ℓ z G ∧
        S.ellStarBarY s ℓ z G (S.gStarBarY s ℓ z G) = 1 ∧
        Dunford.IsSimpleSpectralProj (S.Lsec s (-(ℓ : ℤ)) G) (S.rieszSecBar s ℓ z G) (conj z) ∧
        Dunford.IsAlgSimpleEig (S.Lsec s (-(ℓ : ℤ)) G) (conj z) := by
  intro s
  obtain ⟨hψ, hid⟩ := evansSimple_deriv S hS ℓ hℓ z hz G hE
  have hJ : S.J ℓ z G ≠ 0 := (evansSimple_riesz S hS ℓ hℓ z hz G hE hE').1
  obtain ⟨hspec, h1, hAg, hfA, hker, hrange⟩ :=
    EvansSimpleAux.riesz_hyps S hS ℓ hℓ hz G hE hJ s
  obtain ⟨C, hC1, hC2, hC3⟩ := exists_conj_Ysec S hS s (ℓ : ℤ) G
  obtain ⟨f', hf'⟩ := EvansSimpleAux.exists_conj_functional C hC2 (S.ellStarY s ℓ z G)
  have hf'spec : ∀ y : Ysec s S.Nstar (-(ℓ : ℤ)),
      f' y = S.ellStarBar ℓ z G (Polar.angularSector y.fn (-(ℓ : ℤ))) := by
    intro y
    rw [hf', hspec, ellStarBar]
    congr 1
    apply EvansSimpleAux.ellStar_congr_ae
    have hy : (C.symm y).fn =ᵐ[volume] fun x => conj (y.fn x) := by
      have h := hC1 (C.symm y)
      rw [C.apply_symm_apply] at h
      filter_upwards [h] with x hx
      rw [hx, Complex.conj_conj]
    filter_upwards [EvansSimpleAux.angularSector_congr_ae hy (ℓ : ℤ)] with r hr
    have h := Ang.angularSector_conj y.fn (-(ℓ : ℤ)) r
    rw [neg_neg] at h
    exact hr.trans h
  have hbarY : ∀ y, S.ellStarBarY s ℓ z G y = f' y := fun y =>
    (ellStarBarY_spec_of_exists S s ℓ z G ⟨f', hf'spec⟩ y).trans (hf'spec y).symm
  have hbarY' : S.ellStarBarY s ℓ z G = f' := ContinuousLinearMap.ext hbarY
  have heig := (eigen_of_evans_eq_zero S hS ℓ hℓ z hz G hE).2.2.2.2 s
  have hCg : (C (S.gStarY s ℓ z G)).fn =ᵐ[volume]
      Ang.ofProfile (-(ℓ : ℤ)) (fun r => conj (S.gStar ℓ z G r)) := by
    filter_upwards [hC1 (S.gStarY s ℓ z G), heig.1] with x hx1 hx2
    rw [hx1, hx2, EvansSimpleAux.ofProfile_neg_conj]
  have hbarfn : (S.gStarBarY s ℓ z G).fn =ᵐ[volume]
      Ang.ofProfile (-(ℓ : ℤ)) (fun r => conj (S.gStar ℓ z G r)) :=
    toYsec_spec ⟨_, hCg⟩
  have hbarC : S.gStarBarY s ℓ z G = C (S.gStarY s ℓ z G) :=
    EvansSimpleAux.Ysec_ext_fn (hbarfn.trans hCg.symm)
  obtain ⟨h1', h2', hP'⟩ := EvansSimpleAux.conj_transport C hC2 (A := S.Lsec s ℓ G)
    (A' := S.Lsec s (-(ℓ : ℤ)) G) hC3 h1 hAg hfA hker hrange hf'
  refine ⟨fun g => (hbarY g).trans (hf'spec g), hbarfn, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbarC]
    intro h0
    apply heig.2.1
    apply C.injective
    rw [h0, map_zero]
  · rw [hbarC]
    exact h2'
  · rw [hbarY', hbarC]
    exact h1'
  · rw [rieszSecBar, hbarY', hbarC]
    exact hP'
  · exact ⟨f', C (S.gStarY s ℓ z G), h1', hP'⟩

/-- `thm:evans-simple`(3), first half (low priority, R13): if `J = 0`, there is a profile
`g₁`, smooth on `(0,∞)` and supported in `[r₁,r₂]`, with `g₁e^{iℓθ} ∈ Y^s_ℓ` and
`(L_ℓ(G) - λ_*)g₁ = g_*` on every `Y^s_ℓ`; so `λ_*` is not algebraically simple. -/
theorem evansSimple_not_simple (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) (hJ : S.J ℓ z G = 0) :
    (∃ g₁ : ℝ → ℂ, ContDiffOn ℝ ∞ g₁ (Ioi 0) ∧
        (∀ r : ℝ, 0 < r → r ∉ Icc S.r₁ S.r₂ → g₁ r = 0) ∧
        ∀ s : ℕ, ∃ h : Ysec s S.Nstar ℓ, h.fn =ᵐ[volume] Ang.ofProfile ℓ g₁ ∧
          S.Lsec s ℓ G h - z • h = S.gStarY s ℓ z G) ∧
      ∀ s : ℕ, ¬ Dunford.IsAlgSimpleEig (S.Lsec s ℓ G) z := by
  obtain ⟨g₁, hg₁, hsupp, heq⟩ := evansSimple_genEigen S hS ℓ hℓ z hz G hE hJ
  refine ⟨⟨g₁, hg₁, hsupp, fun s =>
    EvansSimpleAux.exists_Ysec_genEigen S hS ℓ hℓ hz G hE hg₁ hsupp heq s⟩, fun s => ?_⟩
  obtain ⟨h, -, hh⟩ := EvansSimpleAux.exists_Ysec_genEigen S hS ℓ hℓ hz G hE hg₁ hsupp heq s
  have heig := (eigen_of_evans_eq_zero S hS ℓ hℓ z hz G hE).2.2.2.2 s
  exact EvansSimpleAux.not_isAlgSimpleEig_of_genEigen heig.2.1 heig.2.2.1 hh

/-- `thm:evans-simple`(3), converse (low priority, R13): if some `g₁ ∈ Y^0_ℓ` satisfies
`(L_ℓ(G) - λ_*)g₁ = g_*`, then `J = 0`. -/
theorem evansSimple_J_eq_zero_of_genEigen (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (z : ℂ) (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0)
    (h₁ : ∃ h : Ysec 0 S.Nstar ℓ, S.Lsec 0 ℓ G h - z • h = S.gStarY 0 ℓ z G) :
    S.J ℓ z G = 0 := by
  obtain ⟨h, hh⟩ := h₁
  exact EvansSimpleAux.J_eq_zero_of_genEigen S hS ℓ hℓ hz G hE 0 h hh

/-- `thm:evans-simple`(4) (the implications other than "simple zero ⟹ algebraically simple" are
low priority, R13): on every `Y^s_ℓ`, `λ_*` is an algebraically simple eigenvalue of `L_ℓ(G)` iff
`J ≠ 0`, iff `λ_*` is a simple zero of `E_ℓ(·;G)`. -/
theorem evansSimple_iff (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) (s : ℕ) :
    (Dunford.IsAlgSimpleEig (S.Lsec s ℓ G) z ↔ S.J ℓ z G ≠ 0) ∧
      (S.J ℓ z G ≠ 0 ↔ deriv (fun w => S.evans ℓ w G) z ≠ 0) := by
  obtain ⟨hψ, hid⟩ := evansSimple_deriv S hS ℓ hℓ z hz G hE
  have hJd : S.J ℓ z G ≠ 0 ↔ deriv (fun w => S.evans ℓ w G) z ≠ 0 := by
    constructor
    · intro hJ hd
      apply hJ
      rw [hd, mul_zero] at hid
      exact neg_eq_zero.1 hid.symm
    · intro hd hJ
      rw [hJ, neg_zero] at hid
      exact hd ((mul_eq_zero.1 hid).resolve_left
        (mul_ne_zero (EvansSimpleAux.exp_ne_zero' _) hψ))
  refine ⟨⟨fun hs hJ => ?_, fun hJ => ?_⟩, hJd⟩
  · exact (evansSimple_not_simple S hS ℓ hℓ z hz G hE hJ).2 s hs
  · exact ((evansSimple_riesz S hS ℓ hℓ z hz G hE (hJd.1 hJ)).2 s).2.2.2

end SectorSetting

end NonUniqueEuler
