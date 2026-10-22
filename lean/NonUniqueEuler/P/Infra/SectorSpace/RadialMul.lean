import NonUniqueEuler.Defs.Infra.SectorSpace
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Leibniz
import NonUniqueEuler.H.Infra.SectorSpace.RadialMul.Radial

/-!
# Proof: radial multipliers on the sector spaces (library I-SECT)

Proof of `I/Infra/SectorSpace/RadialMul.lean` (used by `def:sector-setting` / `lem:sector`(4),
`04_ring.tex:945-947`).

For `χ ∈ C^s(K)` (`K` closed) invariant under rotations, `g ↦ toHk s (χ g)` maps `Y^s_ℓ(K)`
to itself (`Sob.MemH.mul_of_memCk`: `χ g ∈ H^s` with
`‖χ g‖_{H^s} ≤ (s+1) 2^s ‖χ‖_{C^s(K)} ‖g‖_{H^s}`; the support and sector conditions are
pointwise), is linear and bounded. For `χ = a(|·|)` on the annulus the `C^s` norm of `χ` is
controlled by `‖a‖_{C^s([ρ₋,ρ₊])}` (`RadMulH.exists_memCk_radial`). Elements of `Y^s_ℓ` are
determined by their functions (`Sob.Hk.ext_fn`), so the chosen `radialMul` is this operator;
linearity in `a` and the constant case follow from the same uniqueness.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sect

open Sob Ang

namespace RadMulP

variable {s : ℕ} {K : Set ℂ} {ℓ : ℤ}

/-! ### Membership in the sector spaces (function level) -/

theorem tupleFn_add (F G : SobTuple s) :
    tupleFn (F + G) =ᵐ[volume] tupleFn F + tupleFn G :=
  Lp.coeFn_add (F.ofLp (idx0 s)) (G.ofLp (idx0 s))

theorem tupleFn_smul (c : ℂ) (F : SobTuple s) :
    tupleFn (c • F) =ᵐ[volume] c • tupleFn F :=
  Lp.coeFn_smul c (F.ofLp (idx0 s))

theorem stronglyMeasurable_tupleFn (F : SobTuple s) : StronglyMeasurable (tupleFn F) :=
  Lp.stronglyMeasurable _

/-- Two elements of `H^s` with a.e. equal functions are equal (as tuples). -/
theorem tuple_ext {F G : SobTuple s} (hF : F ∈ HkSub s) (hG : G ∈ HkSub s)
    (h : tupleFn F =ᵐ[volume] tupleFn G) : F = G := by
  have := Hk.ext_fn (F := (⟨F, hF⟩ : Hk s)) (G := ⟨G, hG⟩) h
  exact congrArg Subtype.val this

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

theorem sectorDefect_eq_zero_iff (θ : ℝ) (F : SobTuple s) :
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

theorem mem_YsecSub_iff' (F : SobTuple s) :
    F ∈ YsecSub s K ℓ ↔ F ∈ YSub s K ∧ IsSectorFn ℓ (tupleFn F) := by
  rw [YsecSub, Submodule.mem_inf, Submodule.mem_iInf]
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sectorDefect_eq_zero_iff]
  rfl

/-- `g ∈ Y^s_ℓ(K)` as an element of `H^s`. -/
def Ysec.toHk (g : Ysec s K ℓ) : Hk s :=
  ⟨(g : SobTuple s), YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ g.2)⟩

theorem Ysec.memH_fn (g : Ysec s K ℓ) : MemH s g.fn ∧ normH s g.fn = ‖g‖ :=
  Hk.memH_fn (Ysec.toHk g)

theorem Ysec.ext_fn {g h : Ysec s K ℓ} (hgh : g.fn =ᵐ[volume] h.fn) : g = h :=
  Subtype.ext (tuple_ext (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ g.2))
    (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ h.2)) hgh)

theorem Ysec.supp (g : Ysec s K ℓ) : ∀ᵐ x ∂volume, x ∉ K → g.fn x = 0 :=
  ((mem_YSub_iff (K := K) (g : SobTuple s)).1 (YsecSub_le_YSub s K ℓ g.2)).2

theorem Ysec.isSectorFn (g : Ysec s K ℓ) : IsSectorFn ℓ g.fn :=
  ((mem_YsecSub_iff' (K := K) (g : SobTuple s)).1 g.2).2

theorem Ysec.fn_add (g h : Ysec s K ℓ) : (g + h).fn =ᵐ[volume] g.fn + h.fn :=
  tupleFn_add (g : SobTuple s) h

theorem Ysec.fn_smul (c : ℂ) (g : Ysec s K ℓ) : (c • g).fn =ᵐ[volume] c • g.fn :=
  tupleFn_smul c (g : SobTuple s)

/-! ### Multiplication by a rotation-invariant `C^s(K)` function -/

/-- The tuple of `χ g` in `H^s`. -/
def mulTuple (χ : ℂ → ℂ) (g : Ysec s K ℓ) : SobTuple s :=
  ((toHk s (fun x => χ x * g.fn x) : Hk s) : SobTuple s)

theorem memH_mul {χ : ℂ → ℂ} (hK : IsClosed K) (hχ : MemCk s K χ) (g : Ysec s K ℓ) :
    MemH s (fun x => χ x * g.fn x) ∧
      normH s (fun x => χ x * g.fn x) ≤ (s + 1) * 2 ^ s * normCk s K χ * ‖g‖ := by
  obtain ⟨hm, hn⟩ := (Ysec.memH_fn g)
  have h := MemH.mul_of_memCk hK hm (Ysec.supp g) hχ
  rw [hn] at h
  exact h

theorem mulTuple_fn {χ : ℂ → ℂ} (hK : IsClosed K) (hχ : MemCk s K χ) (g : Ysec s K ℓ) :
    tupleFn (mulTuple χ g) =ᵐ[volume] fun x => χ x * g.fn x :=
  toHk_fn (memH_mul hK hχ g).1

theorem mulTuple_mem {χ : ℂ → ℂ} (hK : IsClosed K) (hχ : MemCk s K χ)
    (hrot : ∀ θ x, χ (rot θ x) = χ x) (g : Ysec s K ℓ) :
    mulTuple χ g ∈ YsecSub s K ℓ := by
  rw [mem_YsecSub_iff', mem_YSub_iff]
  have hfn := mulTuple_fn hK hχ g
  refine ⟨⟨(toHk s (fun x => χ x * g.fn x)).2, ?_⟩, ?_⟩
  · filter_upwards [hfn, Ysec.supp g] with x hx h0 hxK
    rw [hx, h0 hxK, mul_zero]
  · intro θ
    have hrotae := (Polar.measurePreserving_rot θ).quasiMeasurePreserving.ae_eq_comp hfn
    filter_upwards [hrotae, hfn, Ysec.isSectorFn g θ] with x h1 h2 h3
    simp only [Function.comp_apply] at h1
    rw [h1, h2, hrot, h3]
    ring

/-- Multiplication by a rotation-invariant `χ ∈ C^s(K)` (`K` closed) is a bounded operator on
`Y^s_ℓ(K)` of norm `≤ (s+1) 2^s ‖χ‖_{C^s(K)}`. -/
theorem exists_mul_op {χ : ℂ → ℂ} (hK : IsClosed K) (hχ : MemCk s K χ)
    (hrot : ∀ θ x, χ (rot θ x) = χ x) (ℓ : ℤ) :
    ∃ T : Ysec s K ℓ →L[ℂ] Ysec s K ℓ, (∀ g, (T g).fn =ᵐ[volume] fun x => χ x * g.fn x) ∧
      ∀ g, ‖T g‖ ≤ (s + 1) * 2 ^ s * normCk s K χ * ‖g‖ := by
  let e : Ysec s K ℓ → Ysec s K ℓ := fun g => ⟨mulTuple χ g, mulTuple_mem hK hχ hrot g⟩
  have he : ∀ g, (e g).fn =ᵐ[volume] fun x => χ x * g.fn x := fun g => mulTuple_fn hK hχ g
  have hadd : ∀ g h, e (g + h) = e g + e h := by
    intro g h
    apply Ysec.ext_fn
    filter_upwards [he (g + h), he g, he h, Ysec.fn_add (e g) (e h), Ysec.fn_add g h]
      with x h1 h2 h3 h4 h5
    rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply, mul_add]
  have hsmul : ∀ (c : ℂ) g, e (c • g) = c • e g := by
    intro c g
    apply Ysec.ext_fn
    filter_upwards [he (c • g), he g, Ysec.fn_smul c (e g), Ysec.fn_smul c g]
      with x h1 h2 h3 h4
    rw [h1, h3, Pi.smul_apply, h2, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  have hbound : ∀ g, ‖e g‖ ≤ (s + 1) * 2 ^ s * normCk s K χ * ‖g‖ := by
    intro g
    have h1 : ‖e g‖ = ‖toHk s (fun x => χ x * g.fn x)‖ := rfl
    rw [h1, norm_toHk (memH_mul hK hχ g).1]
    exact (memH_mul hK hχ g).2
  exact ⟨LinearMap.mkContinuous ⟨⟨e, hadd⟩, hsmul⟩ _ hbound, he, hbound⟩

/-- The chosen `radialMul` is any operator meeting its specification. -/
theorem radialMul_eq {a : ℝ → ℂ} (T : Ysec s K ℓ →L[ℂ] Ysec s K ℓ)
    (hT : ∀ g, (T g).fn =ᵐ[volume] fun x => a ‖x‖ * g.fn x) : radialMul s K ℓ a = T := by
  have hex : ∃ T : Ysec s K ℓ →L[ℂ] Ysec s K ℓ,
      ∀ g, (T g).fn =ᵐ[volume] fun x => a ‖x‖ * g.fn x := ⟨T, hT⟩
  have hspec : ∀ g, (radialMul s K ℓ a g).fn =ᵐ[volume] fun x => a ‖x‖ * g.fn x := by
    rw [radialMul, dite_eq_left_of_eq_true (eq_true hex)]
    exact hex.choose_spec
  ext1 g
  exact Ysec.ext_fn ((hspec g).trans (hT g).symm)

end RadMulP

open RadMulP

theorem exists_radialMul_spec (s : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℤ) (a : ℝ → ℂ), MemCk s (Icc ρm ρp) a →
      (∀ g : Ysec s (closedAnnulus ρm ρp) ℓ,
          (radialMul s _ ℓ a g).fn =ᵐ[volume] fun x => a ‖x‖ * g.fn x) ∧
        ‖radialMul s (closedAnnulus ρm ρp) ℓ a‖ ≤ C * normCk s (Icc ρm ρp) a := by
  have _hρ := hρ
  obtain ⟨C', hC', hrad⟩ := RadMulH.exists_memCk_radial s (ρp := ρp) hρm
  have hpos : 0 < ((s : ℝ) + 1) * 2 ^ s * C' := mul_pos (by positivity) hC'
  refine ⟨((s : ℝ) + 1) * 2 ^ s * C', hpos, fun ℓ a ha => ?_⟩
  obtain ⟨hχ, hχb⟩ := hrad a ha
  obtain ⟨T, hT, hTb⟩ := exists_mul_op (isClosed_closedAnnulus ρm ρp) hχ
    (fun θ x => by simp) ℓ
  rw [radialMul_eq T hT]
  refine ⟨hT, ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hpos.le (normCk_nonneg _ _ _)) fun g => ?_⟩
  calc ‖T g‖ ≤ ((s : ℝ) + 1) * 2 ^ s *
        normCk s (closedAnnulus ρm ρp) (fun x : ℂ => a ‖x‖) * ‖g‖ := hTb g
    _ ≤ ((s : ℝ) + 1) * 2 ^ s * (C' * normCk s (Icc ρm ρp) a) * ‖g‖ := by gcongr
    _ = ((s : ℝ) + 1) * 2 ^ s * C' * normCk s (Icc ρm ρp) a * ‖g‖ := by ring

theorem radialMul_add {s : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) (ℓ : ℤ) {a b : ℝ → ℂ}
    (ha : MemCk s (Icc ρm ρp) a) (hb : MemCk s (Icc ρm ρp) b) (c : ℂ) :
    radialMul s (closedAnnulus ρm ρp) ℓ (fun r => a r + c * b r) =
      radialMul s _ ℓ a + c • radialMul s _ ℓ b := by
  obtain ⟨C, _, hC⟩ := exists_radialMul_spec s hρm hρ
  have hA := (hC ℓ a ha).1
  have hB := (hC ℓ b hb).1
  refine radialMul_eq _ fun g => ?_
  filter_upwards [hA g, hB g, Ysec.fn_add (radialMul s _ ℓ a g) (c • radialMul s _ ℓ b g),
    Ysec.fn_smul c (radialMul s _ ℓ b g)] with x h1 h2 h3 h4
  rw [add_apply, smul_apply, h3, Pi.add_apply, h4,
    Pi.smul_apply, h1, h2, smul_eq_mul]
  ring

/-- Multiplication by the constant `c` is `c • id`. -/
theorem radialMul_const {s : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) (ℓ : ℤ) (c : ℂ) :
    radialMul s (closedAnnulus ρm ρp) ℓ (fun _ => c) = c • ContinuousLinearMap.id ℂ _ := by
  have _h := hρm
  have _h' := hρ
  refine radialMul_eq _ fun g => ?_
  filter_upwards [Ysec.fn_smul c g] with x h1
  rw [smul_apply, ContinuousLinearMap.id_apply, h1, Pi.smul_apply,
    smul_eq_mul]

end NonUniqueEuler.Sect
