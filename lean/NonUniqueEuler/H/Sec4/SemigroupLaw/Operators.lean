import NonUniqueEuler.H.Sec4.SemigroupLaw.Basic
import NonUniqueEuler.H.Sec4.SemigroupLaw.Profile
import NonUniqueEuler.H.Sec4.SemigroupLaw.Conj
import NonUniqueEuler.Defs.Sec4.Operators
import NonUniqueEuler.I.Sec4.SemigroupConstruct
import NonUniqueEuler.I.Sec4.Sector
import NonUniqueEuler.I.Infra.SectorSpace.Lower
import NonUniqueEuler.I.Infra.SectorSpace.Projection
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.I.Infra.AngularFourier.Symmetry

/-!
# Helpers for `P/Sec4/SemigroupLaw`: the sector operators `L_ℓ(G)` on `Y^s_ℓ`

* `Lsec_lowerSec`, `exp_Lsec_lowerSec`: `L_ℓ(G)` and `exp(tL_ℓ(G))` commute with the inclusions
  `Y^{s'}_ℓ → Y^s_ℓ` (both act on profiles by `LsecFn`, `semigroupConstruct_Lsec`);
* `secProj_LinY`: `P_ℓ L(G) w = L_ℓ(G) P_ℓ w` for `w ∈ Y^{s+1}` (`lem:sector`(2),
  `linFn_sector`);
* `Lsec_conjSec`, `exp_Lsec_conjSec`: `L_{-ℓ}(G) conj = conj L_ℓ(G)` (`LsecFn_neg_conj`) and the
  same for the exponentials (real `t`);
* `Lsec_exp_comm`: a bounded operator commutes with its exponential.
-/

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

namespace NonUniqueEuler

namespace SectorSetting

open Sect

/-- `L_ℓ(G)` commutes with the inclusion `Y^{s'}_ℓ → Y^s_ℓ`. -/
theorem SgLaw_Lsec_lowerSec (S : SectorSetting) (hS : S.Valid) {s s' : ℕ} (h : s ≤ s') (ℓ : ℤ)
    (G : ℝ) (g : Ysec s' S.Nstar ℓ) :
    S.Lsec s ℓ G (lowerSec s s' S.Nstar ℓ g) = lowerSec s s' S.Nstar ℓ (S.Lsec s' ℓ G g) := by
  refine SgLawH.Ysec.ext_fn ?_
  have h1 := semigroupConstruct_Lsec S hS s ℓ G (lowerSec s s' S.Nstar ℓ g)
  have h2 := (lowerSec_spec h S.Nstar ℓ).1 (S.Lsec s' ℓ G g)
  have h3 := semigroupConstruct_Lsec S hS s' ℓ G g
  have h4 := SgLawH.ofProfile_LsecFn_congr S ℓ G ((lowerSec_spec h S.Nstar ℓ).1 g)
  exact h1.trans (h4.trans (h3.symm.trans h2.symm))

/-- `exp(tL_ℓ(G))` commutes with the inclusion `Y^{s'}_ℓ → Y^s_ℓ`. -/
theorem SgLaw_exp_Lsec_lowerSec (S : SectorSetting) (hS : S.Valid) {s s' : ℕ} (h : s ≤ s')
    (ℓ : ℤ) (G t : ℝ) (g : Ysec s' S.Nstar ℓ) :
    NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G) (lowerSec s s' S.Nstar ℓ g) =
      lowerSec s s' S.Nstar ℓ (NormedSpace.exp ((t : ℂ) • S.Lsec s' ℓ G) g) := by
  have := SgLawH.exp_smul_apply_intertwine (S.Lsec s' ℓ G) (S.Lsec s ℓ G)
    (lowerSec s s' S.Nstar ℓ : Ysec s' S.Nstar ℓ →+ Ysec s S.Nstar ℓ)
    (lowerSec s s' S.Nstar ℓ).continuous
    (fun r x => (lowerSec s s' S.Nstar ℓ).map_smul (r : ℂ) x)
    (fun x => (SgLaw_Lsec_lowerSec S hS h ℓ G x).symm) t g
  exact this.symm

/-- `lem:sector`(2) on `Y^{s+1}`: `P_ℓ L(G) w = L_ℓ(G) P_ℓ w`. -/
theorem SgLaw_secProj_LinY (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ)
    (u : Y (s + 1) S.Nstar) (ℓ : ℤ) :
    secProj s S.Nstar ℓ (S.LinY s G u) =
      S.Lsec s ℓ G (secProj s S.Nstar ℓ (lowerY s (s + 1) S.Nstar u)) := by
  have hK := S.isRotInvariant_Nstar
  refine SgLawH.Ysec.ext_fn ?_
  have h1 := (secProj_spec (s := s) hK ℓ).1 (S.LinY s G u)
  have h2 := Ang.sectorProj_congr_ae ℓ
    (LinY_spec_of_exists S s G (semigroupConstruct_LinY S hS s G) u)
  have h3 := linFn_sector S hS s G u ℓ
  have h4 := semigroupConstruct_Lsec S hS s ℓ G
    (secProj s S.Nstar ℓ (lowerY s (s + 1) S.Nstar u))
  have h5 : (secProj s S.Nstar ℓ (lowerY s (s + 1) S.Nstar u)).fn =ᵐ[volume]
      Ang.sectorProj ℓ u.fn :=
    ((secProj_spec hK ℓ).1 _).trans
      (Ang.sectorProj_congr_ae ℓ ((lowerY_spec (Nat.le_succ s) S.Nstar).1 u))
  have h6 := SgLawH.ofProfile_LsecFn_congr_sectorProj S ℓ G h5
  exact h1.trans (h2.trans (h3.trans (h4.trans h6).symm))

/-- `angPhase (-ℓ) = conj ∘ angPhase ℓ`. -/
theorem SgLaw_angPhase_neg (ℓ : ℤ) (x : ℂ) : Ang.angPhase (-ℓ) x = conj (Ang.angPhase ℓ x) := by
  unfold Ang.angPhase
  rw [map_zpow₀, zpow_neg, ← inv_zpow]
  congr 1
  by_cases hx : x = 0
  · subst hx
    simp
  · have hn : ‖x / (‖x‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (norm_ne_zero_iff.2 hx)]
    exact Complex.inv_eq_conj hn

/-- `ofProfile (-ℓ) (conj ∘ h) = conj ∘ ofProfile ℓ h`. -/
theorem SgLaw_ofProfile_neg_conj (ℓ : ℤ) (h : ℝ → ℂ) (x : ℂ) :
    Ang.ofProfile (-ℓ) (fun r => conj (h r)) x = conj (Ang.ofProfile ℓ h x) := by
  unfold Ang.ofProfile
  rw [SgLaw_angPhase_neg, map_mul]

/-- `L_{-ℓ}(G) conj g = conj (L_ℓ(G) g)` on `Y^s_ℓ`. -/
theorem SgLaw_Lsec_conjSec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ) (G : ℝ)
    (g : Ysec s S.Nstar ℓ) :
    SgLawH.conjSec s S.Nstar ℓ (S.Lsec s ℓ G g) =
      S.Lsec s (-ℓ) G (SgLawH.conjSec s S.Nstar ℓ g) := by
  refine SgLawH.Ysec.ext_fn ?_
  have h1 := SgLawH.conjSec_fn (S.Lsec s ℓ G g)
  have h2 := semigroupConstruct_Lsec S hS s ℓ G g
  have h3 := semigroupConstruct_Lsec S hS s (-ℓ) G (SgLawH.conjSec s S.Nstar ℓ g)
  have h4 := SgLawH.ofProfile_LsecFn_congr S (-ℓ) G (SgLawH.conjSec_fn g)
  have h5 : Ang.ofProfile (-ℓ) (S.LsecFn (-ℓ) G
      (Polar.angularSector (fun x => conj (g.fn x)) (-ℓ))) =
      fun x => conj (Ang.ofProfile ℓ (S.LsecFn ℓ G (Polar.angularSector g.fn ℓ)) x) := by
    funext x
    have hA : Polar.angularSector (fun x => conj (g.fn x)) (-ℓ) =
        fun r => conj (Polar.angularSector g.fn ℓ r) := by
      funext r
      exact Ang.angularSector_conj g.fn ℓ r
    have hL : S.LsecFn (-ℓ) G (fun r => conj (Polar.angularSector g.fn ℓ r)) =
        fun r => conj (S.LsecFn ℓ G (Polar.angularSector g.fn ℓ) r) := by
      funext r
      exact S.LsecFn_neg_conj ℓ G _ r
    rw [hA, hL, SgLaw_ofProfile_neg_conj]
  have h6 : (fun x => conj ((S.Lsec s ℓ G g).fn x)) =ᵐ[volume]
      fun x => conj (Ang.ofProfile ℓ (S.LsecFn ℓ G (Polar.angularSector g.fn ℓ)) x) := by
    filter_upwards [h2] with x hx
    rw [hx]
  rw [h5] at h4
  exact h1.trans (h6.trans (h3.trans h4).symm)

/-- `exp(tL_{-ℓ}(G)) conj g = conj (exp(tL_ℓ(G)) g)` for real `t`. -/
theorem SgLaw_exp_Lsec_conjSec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ) (G t : ℝ)
    (g : Ysec s S.Nstar ℓ) :
    SgLawH.conjSec s S.Nstar ℓ (NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G) g) =
      NormedSpace.exp ((t : ℂ) • S.Lsec s (-ℓ) G) (SgLawH.conjSec s S.Nstar ℓ g) :=
  SgLawH.exp_smul_apply_intertwine (S.Lsec s ℓ G) (S.Lsec s (-ℓ) G)
    (SgLawH.conjSecHom s S.Nstar ℓ) (SgLawH.continuous_conjSecHom ℓ)
    (fun r x => SgLawH.conjSec_smul_real r x) (fun x => SgLaw_Lsec_conjSec S hS s ℓ G x) t g

/-- A bounded operator commutes with its exponential. -/
theorem SgLaw_exp_comm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (t : ℝ) (x : E) :
    A (NormedSpace.exp ((t : ℂ) • A) x) = NormedSpace.exp ((t : ℂ) • A) (A x) := by
  have h : Commute A (NormedSpace.exp ((t : ℂ) • A)) :=
    ((Commute.refl A).smul_right (t : ℂ)).exp_right
  have h2 := congrArg (fun T : E →L[ℂ] E => T x) h.eq
  simpa only [mul_apply_eq_comp] using h2

end SectorSetting

end NonUniqueEuler
