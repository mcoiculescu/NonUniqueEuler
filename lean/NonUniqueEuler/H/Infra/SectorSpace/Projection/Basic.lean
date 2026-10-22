import NonUniqueEuler.Defs.Infra.SectorSpace
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2

/-!
# Helpers for `P/Infra/SectorSpace/Projection`: membership in the sector spaces

Function-level characterisations of the closed submodules `YSub`, `YsecSub`, `YZSub` and
`YsymSub` of `SobTuple s` (`Defs/Infra/SectorSpace.lean`), and extensionality: an element of
`Y s K` or `Ysec s K ℓ` is determined by its function (`Sob.Hk.ext_fn`).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Sect.ProjH

open Sob Ang

variable {s : ℕ} {K : Set ℂ}

theorem proj0_apply (F : SobTuple s) : proj0 s F = F.ofLp (idx0 s) := rfl

theorem coeFn_proj0 (F : SobTuple s) : (proj0 s F : ℂ → ℂ) = tupleFn F := rfl

theorem tupleFn_add (F G : SobTuple s) :
    tupleFn (F + G) =ᵐ[volume] tupleFn F + tupleFn G :=
  Lp.coeFn_add (F.ofLp (idx0 s)) (G.ofLp (idx0 s))

theorem tupleFn_smul (c : ℂ) (F : SobTuple s) :
    tupleFn (c • F) =ᵐ[volume] c • tupleFn F :=
  Lp.coeFn_smul c (F.ofLp (idx0 s))

theorem tupleFn_zero : tupleFn (0 : SobTuple s) =ᵐ[volume] 0 :=
  Lp.coeFn_zero ℂ 2 volume

theorem memLp_tupleFn (F : SobTuple s) : MemLp (tupleFn F) 2 volume :=
  Lp.memLp _

theorem stronglyMeasurable_tupleFn (F : SobTuple s) : StronglyMeasurable (tupleFn F) :=
  Lp.stronglyMeasurable _

/-- Two elements of `H^s` with a.e. equal functions are equal (as tuples). -/
theorem tuple_ext {F G : SobTuple s} (hF : F ∈ HkSub s) (hG : G ∈ HkSub s)
    (h : tupleFn F =ᵐ[volume] tupleFn G) : F = G := by
  have := Hk.ext_fn (F := (⟨F, hF⟩ : Hk s)) (G := ⟨G, hG⟩) h
  exact congrArg Subtype.val this

/-! ### The support condition -/

theorem suppCLM_eq_zero_iff (F : SobTuple s) :
    suppCLM s K F = 0 ↔ ∀ᵐ x ∂volume, x ∉ K → tupleFn F x = 0 := by
  have hc := LpToLpRestrictCLM_coeFn ℂ (μ := (volume : Measure ℂ)) (p := 2) Kᶜ (proj0 s F)
  have hmeas : MeasurableSet {x | tupleFn F x = 0} :=
    (stronglyMeasurable_tupleFn F).measurable (measurableSet_singleton 0)
  rw [suppCLM, ContinuousLinearMap.comp_apply, Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h
    have h2 : tupleFn F =ᵐ[volume.restrict Kᶜ] 0 := hc.symm.trans h
    exact (ae_restrict_iff hmeas).1 h2
  · intro h
    have h2 : ∀ᵐ x ∂volume.restrict Kᶜ, tupleFn F x = 0 := (ae_restrict_iff hmeas).2 h
    filter_upwards [hc, h2] with x hx h2x
    rw [hx]
    exact h2x

theorem mem_YSub_iff (F : SobTuple s) :
    F ∈ YSub s K ↔ F ∈ HkSub s ∧ ∀ᵐ x ∂volume, x ∉ K → tupleFn F x = 0 := by
  rw [YSub, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    suppCLM_eq_zero_iff]

/-! ### The sector condition -/

theorem sectorDefect_eq_zero_iff (ℓ : ℤ) (θ : ℝ) (F : SobTuple s) :
    sectorDefect s ℓ θ F = 0 ↔
      (fun x => tupleFn F (rot θ x)) =ᵐ[volume]
        fun x => Complex.exp ((ℓ : ℂ) * θ * Complex.I) * tupleFn F x := by
  have hr : (rotLp θ (proj0 s F) : ℂ → ℂ) =ᵐ[volume] fun x => tupleFn F (rot θ x) :=
    rotLp_coeFn θ (proj0 s F)
  have hs : ((Complex.exp ((ℓ : ℂ) * θ * Complex.I) • proj0 s F : Lp ℂ 2 volume) : ℂ → ℂ)
      =ᵐ[volume] Complex.exp ((ℓ : ℂ) * θ * Complex.I) • tupleFn F :=
    Lp.coeFn_smul (Complex.exp ((ℓ : ℂ) * θ * Complex.I)) (proj0 s F)
  rw [sectorDefect, ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, sub_eq_zero, Lp.ext_iff]
  constructor
  · intro h
    filter_upwards [hr, hs, h] with x hrx hsx hx
    rw [← hrx, hx, hsx]
    rfl
  · intro h
    filter_upwards [hr, hs, h] with x hrx hsx hx
    rw [hrx, hsx]
    exact hx

theorem mem_YsecSub_iff' (ℓ : ℤ) (F : SobTuple s) :
    F ∈ YsecSub s K ℓ ↔ F ∈ YSub s K ∧ IsSectorFn ℓ (tupleFn F) := by
  rw [YsecSub, Submodule.mem_inf, Submodule.mem_iInf]
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sectorDefect_eq_zero_iff]
  rfl

/-! ### The `Y^s_𝒵` condition -/

theorem sectorProjL_proj0_eq_zero_iff (ℓ : ℤ) (F : SobTuple s) :
    (sectorProjL ℓ) (proj0 s F) = 0 ↔ sectorProj ℓ (tupleFn F) =ᵐ[volume] 0 := by
  have hspec := sectorProjL_spec ℓ (proj0 s F)
  rw [Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h
    exact hspec.symm.trans h
  · intro h
    exact hspec.trans h

theorem mem_YZSub_iff' (Z : Set ℤ) (F : SobTuple s) :
    F ∈ YZSub s K Z ↔ F ∈ YSub s K ∧ ∀ ℓ ∉ Z, sectorProj ℓ (tupleFn F) =ᵐ[volume] 0 := by
  rw [YZSub, Submodule.mem_inf, Submodule.mem_iInf]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, sectorProjL_proj0_eq_zero_iff]

/-! ### The `m`-fold symmetry condition -/

theorem mem_YsymSub_iff' (m : ℕ) (F : SobTuple s) :
    F ∈ YsymSub s K m ↔ F ∈ YSub s K ∧ IsMFoldSymmetricC m (tupleFn F) := by
  have hr : (rotLp (2 * π / m) (proj0 s F) : ℂ → ℂ) =ᵐ[volume]
      fun x => tupleFn F (rot (2 * π / m) x) :=
    rotLp_coeFn (2 * π / m) (proj0 s F)
  rw [YsymSub, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply,
    sub_eq_zero, Lp.ext_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    filter_upwards [hr, h] with x hrx hx
    rw [← hrx, hx]
    rfl
  · intro h
    filter_upwards [hr, h] with x hrx hx
    rw [hrx]
    exact hx

/-! ### Elements of `Y s K` and `Ysec s K ℓ` -/

theorem Y.memH_fn (w : Y s K) : MemH s w.fn := (Hk.memH_fn w.toHk).1

theorem Y.normH_fn (w : Y s K) : normH s w.fn = ‖w‖ := (Hk.memH_fn w.toHk).2

theorem Y.ext_fn {w v : Y s K} (h : w.fn =ᵐ[volume] v.fn) : w = v :=
  Subtype.ext (tuple_ext (YSub_le_HkSub s K w.2) (YSub_le_HkSub s K v.2) h)

theorem Ysec.ext_fn {ℓ : ℤ} {g h : Ysec s K ℓ} (hgh : g.fn =ᵐ[volume] h.fn) : g = h :=
  Subtype.ext (tuple_ext (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ g.2))
    (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ h.2)) hgh)

theorem Y.supp (w : Y s K) : ∀ᵐ x ∂volume, x ∉ K → w.fn x = 0 :=
  ((mem_YSub_iff (w : SobTuple s)).1 w.2).2

theorem Ysec.isSectorFn {ℓ : ℤ} (g : Ysec s K ℓ) : IsSectorFn ℓ g.fn :=
  ((mem_YsecSub_iff' ℓ (g : SobTuple s)).1 g.2).2

theorem Y.fn_add (w v : Y s K) : (w + v).fn =ᵐ[volume] w.fn + v.fn :=
  tupleFn_add (w : SobTuple s) v

theorem Y.fn_smul (c : ℂ) (w : Y s K) : (c • w).fn =ᵐ[volume] c • w.fn :=
  tupleFn_smul c (w : SobTuple s)

theorem Ysec.fn_add {ℓ : ℤ} (g h : Ysec s K ℓ) : (g + h).fn =ᵐ[volume] g.fn + h.fn :=
  tupleFn_add (g : SobTuple s) h

theorem Ysec.fn_smul {ℓ : ℤ} (c : ℂ) (g : Ysec s K ℓ) : (c • g).fn =ᵐ[volume] c • g.fn :=
  tupleFn_smul c (g : SobTuple s)

theorem Ysec.fn_zero {ℓ : ℤ} : (0 : Ysec s K ℓ).fn =ᵐ[volume] 0 :=
  tupleFn_zero

theorem Ysec.norm_eq {ℓ : ℤ} (g : Ysec s K ℓ) :
    ‖g‖ = ‖(⟨(g : SobTuple s), YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ g.2)⟩ : Hk s)‖ := rfl

end NonUniqueEuler.Sect.ProjH
