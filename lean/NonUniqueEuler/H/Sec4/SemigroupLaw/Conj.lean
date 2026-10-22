import NonUniqueEuler.H.Sec4.SemigroupLaw.Basic
import NonUniqueEuler.Defs.Sec4.Bridge
import NonUniqueEuler.I.Infra.Sobolev.Symmetry
import NonUniqueEuler.I.Infra.SectorSpace.Projection
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.I.Infra.AngularFourier.Symmetry

/-!
# Helpers for `P/Sec4/SemigroupLaw`: complex conjugation on the sector spaces

* `exists_Y_conj`, `exists_Ysec_conj`: `conj w` lies in `Y^s(K)`, and `conj g ∈ Y^s_{-ℓ}(K)`
  for `g ∈ Y^s_ℓ(K)` (`Sob.MemH.conj`);
* `conjSec : Y^s_ℓ → Y^s_{-ℓ}`, an additive, real-homogeneous isometry (`conjSecHom`,
  `continuous_conjSec`);
* `secProj_neg_of_isReal`: for real `w`, `P_{-ℓ} w = conj(P_ℓ w)` (`Ang.sectorProj_conj`);
* `isReal_of_secProj_neg`: conversely, if `P_{-ℓ} w = conj(P_ℓ w)` for every `ℓ`, then `w` is
  real (on an annulus, where `w` is determined by its sectors).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal ComplexConjugate

namespace NonUniqueEuler.Sect.SgLawH

open Sob Ang

variable {s : ℕ} {K : Set ℂ}

/-- `conj w ∈ Y^s(K)` for `w ∈ Y^s(K)`. -/
theorem exists_Y_conj (w : Y s K) :
    ∃ w' : Y s K, w'.fn =ᵐ[volume] fun x => conj (w.fn x) := by
  obtain ⟨hmem, -⟩ := (Y.memH_fn w).conj
  obtain ⟨F, hF⟩ := memH_iff_exists_Hk.1 hmem
  have hY : (F : SobTuple s) ∈ YSub s K := by
    rw [mem_YSub_iff]
    refine ⟨F.2, ?_⟩
    filter_upwards [hF, Y.supp w] with x hx hsupp hxK
    change F.fn x = 0
    rw [hx, hsupp hxK, map_zero]
  exact ⟨⟨F, hY⟩, hF⟩

/-- `conj g ∈ Y^s_{-ℓ}(K)` for `g ∈ Y^s_ℓ(K)`. -/
theorem exists_Ysec_conj {ℓ : ℤ} (g : Ysec s K ℓ) :
    ∃ g' : Ysec s K (-ℓ), g'.fn =ᵐ[volume] fun x => conj (g.fn x) := by
  obtain ⟨w', hw'⟩ := exists_Y_conj (inclSec s K ℓ g)
  have hsec : IsSectorFn (-ℓ) w'.fn := by
    intro θ
    have h1 := Ysec.isSectorFn g θ
    have h2 : (fun x => w'.fn (rot θ x)) =ᵐ[volume] fun x => conj (g.fn (rot θ x)) :=
      (Polar.measurePreserving_rot θ).quasiMeasurePreserving.ae_eq_comp hw'
    filter_upwards [h1, h2, hw'] with x h1x h2x hwx
    rw [h2x, h1x, map_mul, hwx, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, Int.cast_neg]
    ring
  have hmem : (w' : SobTuple s) ∈ YsecSub s K (-ℓ) := (mem_YsecSub_iff' _ _).2 ⟨w'.2, hsec⟩
  exact ⟨⟨w', hmem⟩, hw'⟩

/-- Complex conjugation `Y^s_ℓ(K) → Y^s_{-ℓ}(K)`. -/
def conjSec (s : ℕ) (K : Set ℂ) (ℓ : ℤ) (g : Ysec s K ℓ) : Ysec s K (-ℓ) :=
  toYsec s K (-ℓ) fun x => conj (g.fn x)

theorem conjSec_fn {ℓ : ℤ} (g : Ysec s K ℓ) :
    (conjSec s K ℓ g).fn =ᵐ[volume] fun x => conj (g.fn x) :=
  toYsec_spec (exists_Ysec_conj g)

theorem conjSec_add {ℓ : ℤ} (g h : Ysec s K ℓ) :
    conjSec s K ℓ (g + h) = conjSec s K ℓ g + conjSec s K ℓ h := by
  refine Ysec.ext_fn ?_
  filter_upwards [conjSec_fn (g + h), Ysec.fn_add g h, conjSec_fn g, conjSec_fn h,
    Ysec.fn_add (conjSec s K ℓ g) (conjSec s K ℓ h)] with x h1 h2 h3 h4 h5
  rw [h1, h5, h2, Pi.add_apply, map_add, Pi.add_apply, h3, h4]

theorem conjSec_smul_real {ℓ : ℤ} (r : ℝ) (g : Ysec s K ℓ) :
    conjSec s K ℓ ((r : ℂ) • g) = (r : ℂ) • conjSec s K ℓ g := by
  refine Ysec.ext_fn ?_
  filter_upwards [conjSec_fn ((r : ℂ) • g), Ysec.fn_smul (r : ℂ) g, conjSec_fn g,
    Ysec.fn_smul (r : ℂ) (conjSec s K ℓ g)] with x h1 h2 h3 h4
  rw [h1, h4, h2, Pi.smul_apply, Pi.smul_apply, h3, smul_eq_mul, smul_eq_mul, map_mul,
    Complex.conj_ofReal]

theorem norm_conjSec {ℓ : ℤ} (g : Ysec s K ℓ) : ‖conjSec s K ℓ g‖ = ‖g‖ := by
  obtain ⟨hmem, hnorm⟩ := (Ysec.memH_fn g).conj
  rw [Ysec.norm_eq_normH_of_ae hmem (conjSec_fn g), hnorm,
    ← Ysec.norm_eq_normH_of_ae (Ysec.memH_fn g) (Filter.EventuallyEq.refl _ _)]

/-- `conjSec` as an additive map. -/
def conjSecHom (s : ℕ) (K : Set ℂ) (ℓ : ℤ) : Ysec s K ℓ →+ Ysec s K (-ℓ) :=
  AddMonoidHom.mk' (conjSec s K ℓ) conjSec_add

@[simp] theorem conjSecHom_apply {ℓ : ℤ} (g : Ysec s K ℓ) :
    conjSecHom s K ℓ g = conjSec s K ℓ g := rfl

theorem continuous_conjSecHom (ℓ : ℤ) : Continuous (conjSecHom s K ℓ) :=
  AddMonoidHomClass.continuous_of_bound (conjSecHom s K ℓ) 1 fun g => by
    rw [conjSecHom_apply, norm_conjSec, one_mul]

/-! ### Real functions and sectors -/

theorem secProj_neg_of_isReal (hK : IsRotInvariant K) {w : Y s K} (hw : w.IsReal) (ℓ : ℤ) :
    secProj s K (-ℓ) w = conjSec s K ℓ (secProj s K ℓ w) := by
  have hwc : w.fn =ᵐ[volume] fun x => conj (w.fn x) := by
    filter_upwards [hw] with x hx
    exact (Complex.conj_eq_iff_im.2 hx).symm
  refine Ysec.ext_fn ?_
  have h1 := (secProj_spec (s := s) hK (-ℓ)).1 w
  have h2 := sectorProj_congr_ae (-ℓ) hwc
  have h3 := (secProj_spec (s := s) hK ℓ).1 w
  filter_upwards [h1, h2, h3, conjSec_fn (secProj s K ℓ w)] with x h1x h2x h3x h4x
  rw [h1x, h2x, sectorProj_conj, h4x, h3x]

theorem isReal_of_secProj_neg {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    {u : Y s (closedAnnulus ρm ρp)}
    (h : ∀ ℓ, secProj s _ (-ℓ) u = conjSec s _ ℓ (secProj s _ ℓ u)) : u.IsReal := by
  have hK := isRotInvariant_closedAnnulus ρm ρp
  obtain ⟨u', hu'⟩ := exists_Y_conj u
  have heq : u' = u := by
    refine Y_ext_of_secProj hρm hρ fun ℓ => Ysec.ext_fn ?_
    have h1 := (secProj_spec (s := s) hK ℓ).1 u'
    have h2 := sectorProj_congr_ae ℓ hu'
    have h3 := (secProj_spec (s := s) hK (-ℓ)).1 u
    have h4 := conjSec_fn (secProj s _ ℓ u)
    rw [← h ℓ] at h4
    have h5 : sectorProj ℓ (fun x => conj (u.fn x)) = fun x => conj (sectorProj (-ℓ) u.fn x) := by
      funext x
      have := sectorProj_conj u.fn (-ℓ) x
      rwa [neg_neg] at this
    filter_upwards [h1, h2, h3, h4] with x h1x h2x h3x h4x
    rw [h1x, h2x, h5]
    simp only
    rw [← h3x, h4x, Complex.conj_conj]
  rw [heq] at hu'
  filter_upwards [hu'] with x hx
  exact Complex.conj_eq_iff_im.1 hx.symm

end NonUniqueEuler.Sect.SgLawH
