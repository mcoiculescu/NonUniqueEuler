import NonUniqueEuler.Defs.Infra.SectorSpace
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives
import NonUniqueEuler.I.Infra.AngularFourier.Symmetry
import NonUniqueEuler.H.Infra.SectorSpace.Projection.Basic

/-!
# Proof: the sector projections on `Y^s(K)` (library I-SECT)

Proof of `I/Infra/SectorSpace/Projection.lean` (`04_ring.tex:181-185`, with the norm bound
corrected to `2^s`, see `I/Infra/Sobolev/Symmetry.lean`).

The operator `w ↦ toHk s (P_ℓ w.fn)` lands in `Y^s_ℓ(K)` (`Sob.MemH.sectorProj`,
`Ang.sectorProj_eq_zero_outside`, `Ang.sectorProj_rot`), is linear (a.e. linearity of `P_ℓ` on
`L²`, from the linear map `Ang.sectorProjL`) and bounded by `2^s` (`Sob.norm_toHk`). Elements of
`Y^s_ℓ(K)` are determined by their functions (`Sob.Hk.ext_fn`), so the chosen `secProj` is this
operator. The remaining items follow from `Ang.sectorProj_sectorProj`, `Ang.isSectorFn_iff` and
`Ang.isMFoldSymmetricC_iff`, through the function-level membership criteria of
`H/Infra/SectorSpace/Projection/Basic.lean`.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Sect

open Sob Ang

namespace ProjP

open ProjH

variable {s : ℕ} {K : Set ℂ}

/-- `P_ℓ` is additive a.e. on `L²` functions (through the linear map `sectorProjL ℓ`). -/
theorem sectorProj_add_ae (ℓ : ℤ) (F G : SobTuple s) :
    sectorProj ℓ (tupleFn F + tupleFn G) =ᵐ[volume]
      sectorProj ℓ (tupleFn F) + sectorProj ℓ (tupleFn G) := by
  have h1 : sectorProj ℓ (tupleFn F + tupleFn G) =ᵐ[volume]
      sectorProj ℓ (proj0 s F + proj0 s G : Lp ℂ 2 (volume : Measure ℂ)) :=
    sectorProj_congr_ae ℓ (Lp.coeFn_add (proj0 s F) (proj0 s G)).symm
  have h2 := sectorProjL_spec ℓ (proj0 s F + proj0 s G)
  have h3 := sectorProjL_spec ℓ (proj0 s F)
  have h4 := sectorProjL_spec ℓ (proj0 s G)
  rw [map_add] at h2
  filter_upwards [h1, h2, h3, h4,
    Lp.coeFn_add (sectorProjL ℓ (proj0 s F)) (sectorProjL ℓ (proj0 s G))] with x h1x h2x h3x h4x h5x
  rw [h1x, ← h2x, h5x, Pi.add_apply, Pi.add_apply, h3x, h4x]
  rfl

/-- `P_ℓ` commutes with scalars (pointwise). -/
theorem sectorProj_smul (ℓ : ℤ) (c : ℂ) (g : ℂ → ℂ) :
    sectorProj ℓ (c • g) = c • sectorProj ℓ g := by
  funext x
  simp only [sectorProj, Pi.smul_apply, smul_eq_mul]
  rw [show (fun φ : ℝ => Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * (c * g (rot φ x))) =
      fun φ : ℝ => c * (Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * g (rot φ x)) from
    funext fun φ => by ring, intervalIntegral.integral_const_mul]
  ring

theorem memH_sectorProj (w : Y s K) (ℓ : ℤ) : MemH s (sectorProj ℓ w.fn) :=
  (MemH.sectorProj (Y.memH_fn w) ℓ).1

theorem toHk_sectorProj_fn (w : Y s K) (ℓ : ℤ) :
    tupleFn ((toHk s (sectorProj ℓ w.fn) : Hk s) : SobTuple s) =ᵐ[volume] sectorProj ℓ w.fn :=
  toHk_fn (memH_sectorProj w ℓ)

/-- `toHk s (P_ℓ w)` lies in `Y^s_ℓ(K)`. -/
theorem toHk_sectorProj_mem (hK : IsRotInvariant K) (ℓ : ℤ) (w : Y s K) :
    ((toHk s (sectorProj ℓ w.fn) : Hk s) : SobTuple s) ∈ YsecSub s K ℓ := by
  rw [mem_YsecSub_iff', mem_YSub_iff]
  have hfn := toHk_sectorProj_fn w ℓ
  refine ⟨⟨(toHk s (sectorProj ℓ w.fn)).2, ?_⟩, ?_⟩
  · filter_upwards [hfn, sectorProj_eq_zero_outside hK (Y.supp w) ℓ] with x hx h0 hxK
    rw [hx]
    exact h0 hxK
  · intro θ
    have hrot := (Polar.measurePreserving_rot θ).quasiMeasurePreserving.ae_eq_comp hfn
    filter_upwards [hrot, hfn] with x h1 h2
    simp only [Function.comp_apply] at h1
    rw [h1, h2, sectorProj_rot]

/-- The sector projection exists as a bounded operator `Y^s(K) → Y^s_ℓ(K)` of norm `≤ 2^s`. -/
theorem exists_secProj (hK : IsRotInvariant K) (ℓ : ℤ) :
    ∃ P : Y s K →L[ℂ] Ysec s K ℓ, (∀ w, (P w).fn =ᵐ[volume] sectorProj ℓ w.fn) ∧
      ∀ w, ‖P w‖ ≤ 2 ^ s * ‖w‖ := by
  let e : Y s K → Ysec s K ℓ := fun w =>
    ⟨((toHk s (sectorProj ℓ w.fn) : Hk s) : SobTuple s), toHk_sectorProj_mem hK ℓ w⟩
  have he : ∀ w, (e w).fn =ᵐ[volume] sectorProj ℓ w.fn := fun w => toHk_sectorProj_fn w ℓ
  have hadd : ∀ w v, e (w + v) = e w + e v := by
    intro w v
    apply Ysec.ext_fn
    filter_upwards [he (w + v), he w, he v, Ysec.fn_add (e w) (e v),
      sectorProj_congr_ae ℓ (Y.fn_add w v),
      sectorProj_add_ae ℓ (w : SobTuple s) (v : SobTuple s)] with x h1 h2 h3 h4 h5 h6
    rw [h1, h4, h5, Pi.add_apply, h2, h3]
    exact h6
  have hsmul : ∀ (c : ℂ) w, e (c • w) = c • e w := by
    intro c w
    apply Ysec.ext_fn
    filter_upwards [he (c • w), he w, Ysec.fn_smul c (e w),
      sectorProj_congr_ae ℓ (Y.fn_smul c w)] with x h1 h2 h3 h4
    rw [h1, h3, h4, sectorProj_smul, Pi.smul_apply, Pi.smul_apply, h2]
  have hbound : ∀ w, ‖e w‖ ≤ 2 ^ s * ‖w‖ := by
    intro w
    have h1 : ‖e w‖ = ‖toHk s (sectorProj ℓ w.fn)‖ := rfl
    rw [h1, norm_toHk (memH_sectorProj w ℓ), ← Y.normH_fn w]
    exact (MemH.sectorProj (Y.memH_fn w) ℓ).2
  exact ⟨LinearMap.mkContinuous ⟨⟨e, hadd⟩, hsmul⟩ (2 ^ s) hbound, he, hbound⟩

end ProjP

open ProjH ProjP

/-- The chosen `secProj` is the sector projection, with norm at most `2^s`. -/
theorem secProj_spec {s : ℕ} {K : Set ℂ} (hK : IsRotInvariant K) (ℓ : ℤ) :
    (∀ w : Y s K, (secProj s K ℓ w).fn =ᵐ[volume] sectorProj ℓ w.fn) ∧
      ‖secProj s K ℓ‖ ≤ 2 ^ s := by
  obtain ⟨P, hP, hPb⟩ := exists_secProj (s := s) hK ℓ
  have hex : ∃ P : Y s K →L[ℂ] Ysec s K ℓ, ∀ w, (P w).fn =ᵐ[volume] sectorProj ℓ w.fn :=
    ⟨P, hP⟩
  have hspec : ∀ w : Y s K, (secProj s K ℓ w).fn =ᵐ[volume] sectorProj ℓ w.fn := by
    rw [secProj, dite_eq_left_of_eq_true (eq_true hex)]
    exact hex.choose_spec
  have heq : secProj s K ℓ = P := by
    ext1 w
    exact Ysec.ext_fn ((hspec w).trans (hP w).symm)
  refine ⟨hspec, ?_⟩
  rw [heq]
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) hPb

/-- `P_ℓ` is the identity on `Y^s_ℓ`, and `P_m` vanishes on it for `m ≠ ℓ`. -/
theorem secProj_inclSec {s : ℕ} {K : Set ℂ} (hK : IsRotInvariant K) (ℓ m : ℤ)
    (g : Ysec s K ℓ) :
    ((secProj s K m (inclSec s K ℓ g) : Ysec s K m) : SobTuple s) =
      if m = ℓ then (g : SobTuple s) else 0 := by
  have hspec := (secProj_spec hK m).1 (inclSec s K ℓ g)
  have hg : g.fn =ᵐ[volume] sectorProj ℓ g.fn :=
    (isSectorFn_iff (g := g.fn) (memLp_tupleFn _)).1.1 (Ysec.isSectorFn g)
  have h2 : sectorProj m g.fn =ᵐ[volume] sectorProj m (sectorProj ℓ g.fn) :=
    sectorProj_congr_ae m hg
  rw [sectorProj_sectorProj] at h2
  split_ifs with hm
  · subst hm
    exact congrArg Subtype.val
      (Ysec.ext_fn (g := secProj s K m (inclSec s K m g)) (h := g) (hspec.trans hg.symm))
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)] at h2
    have h0 := Ysec.ext_fn (g := secProj s K m (inclSec s K ℓ g)) (h := 0)
      (hspec.trans (h2.trans Ysec.fn_zero.symm))
    rw [h0]
    rfl

/-- `w ∈ Y^s_ℓ` iff `w ∈ Y^s` is fixed by `P_ℓ`. -/
theorem mem_YsecSub_iff {s : ℕ} {K : Set ℂ} (hK : IsRotInvariant K) (ℓ : ℤ) (w : Y s K) :
    (w : SobTuple s) ∈ YsecSub s K ℓ ↔ inclSec s K ℓ (secProj s K ℓ w) = w := by
  constructor
  · intro h
    have h1 := secProj_inclSec hK ℓ ℓ ⟨(w : SobTuple s), h⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_self ℓ)] at h1
    have hw : inclSec s K ℓ ⟨(w : SobTuple s), h⟩ = w := Subtype.ext rfl
    rw [hw] at h1
    exact Subtype.ext h1
  · intro h
    rw [← h, inclSec_apply_coe]
    exact (secProj s K ℓ w).2

/-- `w ∈ Y^s_𝒵` iff `P_ℓ w = 0` for all `ℓ ∉ Z`. -/
theorem mem_YZSub_iff {s : ℕ} {K : Set ℂ} (hK : IsRotInvariant K) (Z : Set ℤ) (w : Y s K) :
    (w : SobTuple s) ∈ YZSub s K Z ↔ ∀ ℓ ∉ Z, secProj s K ℓ w = 0 := by
  rw [mem_YZSub_iff']
  have hw : (w : SobTuple s) ∈ YSub s K := w.2
  simp only [hw, true_and]
  refine forall₂_congr fun ℓ _ => ?_
  have hspec := (secProj_spec hK ℓ).1 w
  constructor
  · intro h
    exact Ysec.ext_fn (hspec.trans (h.trans Ysec.fn_zero.symm))
  · intro h
    rw [h] at hspec
    exact hspec.symm.trans Ysec.fn_zero

-- `hK` is part of the interface statement; it is not needed for this item.
set_option linter.unusedVariables false in
/-- The `m`-fold symmetric part of `Y^s(K)` is `Y^s_{mℤ}(K)`. -/
theorem YsymSub_eq_YZSub {s : ℕ} {K : Set ℂ} (hK : IsRotInvariant K) {m : ℕ} (hm : 0 < m) :
    YsymSub s K m = YZSub s K {ℓ | (m : ℤ) ∣ ℓ} := by
  ext F
  rw [mem_YsymSub_iff', mem_YZSub_iff']
  refine and_congr_right fun _ => ?_
  rw [isMFoldSymmetricC_iff hm (memLp_tupleFn F)]
  rfl

end NonUniqueEuler.Sect
