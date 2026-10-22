import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import NonUniqueEuler.Defs.Infra.SobolevSpace
import NonUniqueEuler.Defs.Infra.AngularFourier

/-!
# Sector spaces `Y^s`, `Y^s_ℓ`, `Y^s_𝒵` and sector-wise operators (definitions; library I-SECT)

Manuscript-independent infrastructure (library I-SECT, decisions D8, D14
and restructuring R1). Manuscript: `04_ring.tex:155-185`
(`Y^s`, `Y^s_ℓ`, sector profiles), `04_ring.tex:1042-1045` (`Y^s_𝒵`), and the sector-wise
semigroup `e^{tL} = ⊕_ℓ exp(t L_ℓ)` of `lem:semigroup-construct`(3) (R1).

All spaces are closed submodules of the tuple space `Sob.SobTuple s` (`Defs/Infra/SobolevSpace`),
defined as intersections of kernels of continuous linear maps, so they are complete with no
further proof. For a set `K ⊆ ℂ` (in practice the closed annulus `N_* = closedAnnulus ρ₋ ρ₊`):
* `YSub s K`, `Y s K`: `{w ∈ H^s : w = 0 a.e. outside K}` (`04_ring.tex:155-156`);
* `YsecSub s K ℓ`, `Ysec s K ℓ`: its sector-`ℓ` part, `w ∘ O_θ = e^{iℓθ} w` for all `θ`
  (the manuscript's `Y^s_ℓ`, identified with `P_ℓ Y^s` through `g ↦ g(r)e^{iℓθ}`,
  `04_ring.tex:944-945`);
* `YZSub s K Z`, `YZ s K Z`: the `w ∈ Y^s` with `P_ℓ w = 0` for `ℓ ∉ Z` (`04_ring.tex:1042`);
* `YsymSub s K m`, `Ysym s K m`: the `m`-fold symmetric `w ∈ Y^s` (the space `X^s` of the
  manuscript is `Ysym s N_* 3` in ring units; equal to `YZ s K (3ℤ)` by
  `I/Infra/SectorSpace/Projection.lean`).

Operators (all chosen with the `if h : ∃ … then h.choose else 0` pattern; their
specifications are the interface theorems):
* `inclSec`, `inclZ`, `inclSym`: the inclusions into `Y s K` (genuine definitions);
* `secProj s K ℓ : Y s K →L[ℂ] Ysec s K ℓ`, the sector projection `P_ℓ`;
* `sectorSum s K A : Y s K →L[ℂ] Y s K`, the direct sum `⊕_ℓ A_ℓ` of uniformly bounded sector
  operators `A ℓ : Ysec s K ℓ →L[ℂ] Ysec s K ℓ`: `(⊕A) w = ∑_ℓ A_ℓ (P_ℓ w)`;
* `lowerY s s' K`, `lowerSec s s' K ℓ`: the inclusions `Y^{s'} → Y^s`, `Y^{s'}_ℓ → Y^s_ℓ`
  for `s ≤ s'`;
* `sectorExp s K L t = ⊕_ℓ exp(t L_ℓ)` (decision D8: the linear evolution is *defined* this
  way), with `NormedSpace.exp` the Banach-algebra exponential in `Ysec s K ℓ →L[ℂ] Ysec s K ℓ`;
* `radialMul s K ℓ a : Ysec s K ℓ →L[ℂ] Ysec s K ℓ`, multiplication by the radial function
  `a(|x|)`.

Also: `closedAnnulus ρ₋ ρ₊`, the predicate `IsRotInvariant K`, and `ExpBounded s K L`
(uniform bounds of `exp(t L_ℓ)` on compact time sets).

Accessors: `Y.fn w`, `Ysec.fn g`, `YZ.fn`, `Ysym.fn` are the underlying functions `w_0 : ℂ → ℂ`.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Sect

open Sob Ang

/-- The closed annulus `{ρ₋ ≤ |x| ≤ ρ₊}` (the manuscript's `N_*`). -/
def closedAnnulus (ρm ρp : ℝ) : Set ℂ :=
  {x | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp}

/-- The projection `F ↦ F_0` of a tuple onto its function. -/
def proj0 (s : ℕ) : SobTuple s →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  PiLp.proj 2 (fun _ : SobIdx s => Lp ℂ 2 (volume : Measure ℂ)) (idx0 s)

/-- `F ↦ F_0|_{Kᶜ}`; its kernel is "`F_0 = 0` a.e. outside `K`". -/
def suppCLM (s : ℕ) (K : Set ℂ) : SobTuple s →L[ℂ] Lp ℂ 2 ((volume : Measure ℂ).restrict Kᶜ) :=
  (LpToLpRestrictCLM ℂ ℂ ℂ (volume : Measure ℂ) 2 Kᶜ).comp (proj0 s)

/-- `Y^s(K) = {w ∈ H^s : w = 0 a.e. outside K}`. -/
def YSub (s : ℕ) (K : Set ℂ) : Submodule ℂ (SobTuple s) :=
  HkSub s ⊓ LinearMap.ker
    (suppCLM s K : SobTuple s →ₗ[ℂ] Lp ℂ 2 ((volume : Measure ℂ).restrict Kᶜ))

/-- The type of `Y^s(K)`. -/
abbrev Y (s : ℕ) (K : Set ℂ) : Type := ↥(YSub s K)

/-- `F ↦ F_0 ∘ O_θ - e^{iℓθ} F_0`. -/
def sectorDefect (s : ℕ) (ℓ : ℤ) (θ : ℝ) : SobTuple s →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  (rotLp θ - Complex.exp ((ℓ : ℂ) * θ * Complex.I) • ContinuousLinearMap.id ℂ _).comp (proj0 s)

/-- The sector space `Y^s_ℓ(K)`: the `w ∈ Y^s(K)` with `w ∘ O_θ = e^{iℓθ} w` for all `θ`. -/
def YsecSub (s : ℕ) (K : Set ℂ) (ℓ : ℤ) : Submodule ℂ (SobTuple s) :=
  YSub s K ⊓ ⨅ θ : ℝ,
    LinearMap.ker (sectorDefect s ℓ θ : SobTuple s →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℂ))

/-- The type of `Y^s_ℓ(K)`. -/
abbrev Ysec (s : ℕ) (K : Set ℂ) (ℓ : ℤ) : Type := ↥(YsecSub s K ℓ)

/-- `Y^s_𝒵(K)`: the `w ∈ Y^s(K)` whose sector projections vanish for `ℓ ∉ Z`. -/
def YZSub (s : ℕ) (K : Set ℂ) (Z : Set ℤ) : Submodule ℂ (SobTuple s) :=
  YSub s K ⊓ ⨅ (ℓ : ℤ) (_ : ℓ ∉ Z),
    LinearMap.ker ((sectorProjL ℓ).comp (proj0 s) : SobTuple s →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℂ))

/-- The type of `Y^s_𝒵(K)`. -/
abbrev YZ (s : ℕ) (K : Set ℂ) (Z : Set ℤ) : Type := ↥(YZSub s K Z)

/-- The `m`-fold symmetric part of `Y^s(K)`: `w ∘ O_{2π/m} = w`. -/
def YsymSub (s : ℕ) (K : Set ℂ) (m : ℕ) : Submodule ℂ (SobTuple s) :=
  YSub s K ⊓
    LinearMap.ker ((rotLp (2 * π / m) - ContinuousLinearMap.id ℂ _).comp (proj0 s) :
      SobTuple s →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℂ))

/-- The type of the `m`-fold symmetric part of `Y^s(K)`. -/
abbrev Ysym (s : ℕ) (K : Set ℂ) (m : ℕ) : Type := ↥(YsymSub s K m)

/-! ### Closedness and completeness (fully proved) -/

theorem isClosed_YSub (s : ℕ) (K : Set ℂ) : IsClosed (YSub s K : Set (SobTuple s)) := by
  rw [YSub, Submodule.coe_inf]
  exact (isClosed_HkSub s).inter (suppCLM s K).isClosed_ker

theorem isClosed_YsecSub (s : ℕ) (K : Set ℂ) (ℓ : ℤ) :
    IsClosed (YsecSub s K ℓ : Set (SobTuple s)) := by
  rw [YsecSub, Submodule.coe_inf, Submodule.coe_iInf]
  exact (isClosed_YSub s K).inter (isClosed_iInter fun θ => (sectorDefect s ℓ θ).isClosed_ker)

theorem isClosed_YZSub (s : ℕ) (K : Set ℂ) (Z : Set ℤ) :
    IsClosed (YZSub s K Z : Set (SobTuple s)) := by
  rw [YZSub, Submodule.coe_inf, Submodule.coe_iInf]
  refine (isClosed_YSub s K).inter (isClosed_iInter fun ℓ => ?_)
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun _ => ((sectorProjL ℓ).comp (proj0 s)).isClosed_ker

theorem isClosed_YsymSub (s : ℕ) (K : Set ℂ) (m : ℕ) :
    IsClosed (YsymSub s K m : Set (SobTuple s)) := by
  rw [YsymSub, Submodule.coe_inf]
  exact (isClosed_YSub s K).inter
    ((rotLp (2 * π / m) - ContinuousLinearMap.id ℂ _).comp (proj0 s)).isClosed_ker

instance (s : ℕ) (K : Set ℂ) : CompleteSpace (Y s K) :=
  haveI := isClosed_YSub s K
  IsClosed.completeSpace_coe

instance (s : ℕ) (K : Set ℂ) (ℓ : ℤ) : CompleteSpace (Ysec s K ℓ) :=
  haveI := isClosed_YsecSub s K ℓ
  IsClosed.completeSpace_coe

instance (s : ℕ) (K : Set ℂ) (Z : Set ℤ) : CompleteSpace (YZ s K Z) :=
  haveI := isClosed_YZSub s K Z
  IsClosed.completeSpace_coe

instance (s : ℕ) (K : Set ℂ) (m : ℕ) : CompleteSpace (Ysym s K m) :=
  haveI := isClosed_YsymSub s K m
  IsClosed.completeSpace_coe

/-! Mathlib's instance search does not find `IsTopologicalRing` for operator algebras on
submodule types (an instance-transparency mismatch between the subspace topology and the norm
topology); we provide it from the seminormed ring structure. It is needed by `NormedSpace.exp`. -/

instance (s : ℕ) (K : Set ℂ) : IsTopologicalRing (Y s K →L[ℂ] Y s K) :=
  NonUnitalSeminormedRing.toIsTopologicalRing (α := Y s K →L[ℂ] Y s K)

instance (s : ℕ) (K : Set ℂ) (ℓ : ℤ) : IsTopologicalRing (Ysec s K ℓ →L[ℂ] Ysec s K ℓ) :=
  NonUnitalSeminormedRing.toIsTopologicalRing (α := Ysec s K ℓ →L[ℂ] Ysec s K ℓ)

instance (s : ℕ) (K : Set ℂ) (Z : Set ℤ) : IsTopologicalRing (YZ s K Z →L[ℂ] YZ s K Z) :=
  NonUnitalSeminormedRing.toIsTopologicalRing (α := YZ s K Z →L[ℂ] YZ s K Z)

instance (s : ℕ) (K : Set ℂ) (m : ℕ) : IsTopologicalRing (Ysym s K m →L[ℂ] Ysym s K m) :=
  NonUnitalSeminormedRing.toIsTopologicalRing (α := Ysym s K m →L[ℂ] Ysym s K m)

theorem YSub_le_HkSub (s : ℕ) (K : Set ℂ) : YSub s K ≤ HkSub s := inf_le_left

theorem YsecSub_le_YSub (s : ℕ) (K : Set ℂ) (ℓ : ℤ) : YsecSub s K ℓ ≤ YSub s K := inf_le_left

theorem YZSub_le_YSub (s : ℕ) (K : Set ℂ) (Z : Set ℤ) : YZSub s K Z ≤ YSub s K := inf_le_left

theorem YsymSub_le_YSub (s : ℕ) (K : Set ℂ) (m : ℕ) : YsymSub s K m ≤ YSub s K := inf_le_left

/-! ### Accessors and inclusions -/

/-- The function `w_0` of `w ∈ Y^s(K)`. -/
def Y.fn {s : ℕ} {K : Set ℂ} (w : Y s K) : ℂ → ℂ := tupleFn (w : SobTuple s)

/-- The function of `g ∈ Y^s_ℓ(K)`. -/
def Ysec.fn {s : ℕ} {K : Set ℂ} {ℓ : ℤ} (g : Ysec s K ℓ) : ℂ → ℂ := tupleFn (g : SobTuple s)

/-- The function of `w ∈ Y^s_𝒵(K)`. -/
def YZ.fn {s : ℕ} {K : Set ℂ} {Z : Set ℤ} (w : YZ s K Z) : ℂ → ℂ := tupleFn (w : SobTuple s)

/-- The function of `w` in the `m`-fold symmetric part. -/
def Ysym.fn {s : ℕ} {K : Set ℂ} {m : ℕ} (w : Ysym s K m) : ℂ → ℂ := tupleFn (w : SobTuple s)

/-- `w ∈ Y^s(K)` as an element of `H^s`. -/
def Y.toHk {s : ℕ} {K : Set ℂ} (w : Y s K) : Hk s := ⟨w, YSub_le_HkSub s K w.2⟩

/-- The inclusion `Y^s_ℓ(K) → Y^s(K)`. -/
def inclSec (s : ℕ) (K : Set ℂ) (ℓ : ℤ) : Ysec s K ℓ →L[ℂ] Y s K :=
  (YsecSub s K ℓ).subtypeL.codRestrict (YSub s K) fun g => YsecSub_le_YSub s K ℓ g.2

/-- The inclusion `Y^s_𝒵(K) → Y^s(K)`. -/
def inclZ (s : ℕ) (K : Set ℂ) (Z : Set ℤ) : YZ s K Z →L[ℂ] Y s K :=
  (YZSub s K Z).subtypeL.codRestrict (YSub s K) fun g => YZSub_le_YSub s K Z g.2

/-- The inclusion of the `m`-fold symmetric part into `Y^s(K)`. -/
def inclSym (s : ℕ) (K : Set ℂ) (m : ℕ) : Ysym s K m →L[ℂ] Y s K :=
  (YsymSub s K m).subtypeL.codRestrict (YSub s K) fun g => YsymSub_le_YSub s K m g.2

/-! ### Chosen operators -/

open Classical in
/-- The sector projection `P_ℓ : Y^s(K) → Y^s_ℓ(K)` (chosen; its specification
`secProj_spec` holds for rotation-invariant `K`, `I/Infra/SectorSpace/Projection.lean`). -/
def secProj (s : ℕ) (K : Set ℂ) (ℓ : ℤ) : Y s K →L[ℂ] Ysec s K ℓ :=
  if h : ∃ P : Y s K →L[ℂ] Ysec s K ℓ, ∀ w, (P w).fn =ᵐ[volume] sectorProj ℓ w.fn then h.choose
  else 0

open Classical in
/-- The direct sum `⊕_ℓ A_ℓ : Y^s(K) → Y^s(K)`, `(⊕A) w = ∑_ℓ A_ℓ (P_ℓ w)` (chosen; the
specification `sectorSum_spec`, for uniformly bounded `A`, is in
`I/Infra/SectorSpace/DirectSum.lean`). -/
def sectorSum (s : ℕ) (K : Set ℂ) (A : ∀ ℓ : ℤ, Ysec s K ℓ →L[ℂ] Ysec s K ℓ) :
    Y s K →L[ℂ] Y s K :=
  if h : ∃ T : Y s K →L[ℂ] Y s K,
      ∀ w, HasSum (fun ℓ : ℤ => inclSec s K ℓ (A ℓ (secProj s K ℓ w))) (T w) then h.choose
  else 0

/-- The sector-wise exponential `e^{tL} = ⊕_ℓ exp(t L_ℓ)` (decision D8, restructuring R1). -/
def sectorExp (s : ℕ) (K : Set ℂ) (L : ∀ ℓ : ℤ, Ysec s K ℓ →L[ℂ] Ysec s K ℓ) (t : ℝ) :
    Y s K →L[ℂ] Y s K :=
  sectorSum s K fun ℓ => NormedSpace.exp ((t : ℂ) • L ℓ)

open Classical in
/-- The continuous inclusion `Y^{s'}(K) → Y^s(K)` for `s ≤ s'` (forget the derivatives of order
`> s`; chosen, specification `lowerY_spec` in `I/Infra/SectorSpace/Lower.lean`). -/
def lowerY (s s' : ℕ) (K : Set ℂ) : Y s' K →L[ℂ] Y s K :=
  if h : ∃ T : Y s' K →L[ℂ] Y s K, ∀ w, (T w).fn =ᵐ[volume] w.fn then h.choose else 0

open Classical in
/-- The continuous inclusion `Y^{s'}_ℓ(K) → Y^s_ℓ(K)` for `s ≤ s'` (chosen). -/
def lowerSec (s s' : ℕ) (K : Set ℂ) (ℓ : ℤ) : Ysec s' K ℓ →L[ℂ] Ysec s K ℓ :=
  if h : ∃ T : Ysec s' K ℓ →L[ℂ] Ysec s K ℓ, ∀ g, (T g).fn =ᵐ[volume] g.fn then h.choose else 0

/-- The sector exponentials `exp(t L_ℓ)` are bounded uniformly in `ℓ` and in `t` on compact time
sets `[0, T]` (the hypothesis under which `sectorExp` is a strongly continuous semigroup,
`I/Infra/SectorSpace/Semigroup.lean`). -/
def ExpBounded (s : ℕ) (K : Set ℂ) (L : ∀ ℓ : ℤ, Ysec s K ℓ →L[ℂ] Ysec s K ℓ) : Prop :=
  ∀ T : ℝ, ∃ M : ℝ, ∀ t ∈ Icc 0 T, ∀ ℓ : ℤ, ‖NormedSpace.exp ((t : ℂ) • L ℓ)‖ ≤ M

open Classical in
/-- Multiplication by the radial function `a(|x|)` on `Y^s_ℓ(K)` (chosen; specification
`radialMul_spec` in `I/Infra/SectorSpace/RadialMul.lean`). -/
def radialMul (s : ℕ) (K : Set ℂ) (ℓ : ℤ) (a : ℝ → ℂ) : Ysec s K ℓ →L[ℂ] Ysec s K ℓ :=
  if h : ∃ T : Ysec s K ℓ →L[ℂ] Ysec s K ℓ,
      ∀ g, (T g).fn =ᵐ[volume] fun x => a ‖x‖ * g.fn x then h.choose
  else 0

/-- `K` is invariant under all rotations. -/
def IsRotInvariant (K : Set ℂ) : Prop :=
  ∀ θ x, rot θ x ∈ K ↔ x ∈ K

/-! ### Basic lemmas (fully proved) -/

theorem mem_closedAnnulus {ρm ρp : ℝ} {x : ℂ} :
    x ∈ closedAnnulus ρm ρp ↔ ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp := Iff.rfl

theorem isClosed_closedAnnulus (ρm ρp : ℝ) : IsClosed (closedAnnulus ρm ρp) :=
  (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)

theorem isCompact_closedAnnulus (ρm ρp : ℝ) : IsCompact (closedAnnulus ρm ρp) :=
  (isCompact_closedBall (0 : ℂ) ρp).of_isClosed_subset (isClosed_closedAnnulus ρm ρp)
    fun x hx => by simpa using hx.2

@[simp] theorem rot_mem_closedAnnulus {ρm ρp θ : ℝ} {x : ℂ} :
    rot θ x ∈ closedAnnulus ρm ρp ↔ x ∈ closedAnnulus ρm ρp := by
  simp [closedAnnulus]

theorem isRotInvariant_closedAnnulus (ρm ρp : ℝ) : IsRotInvariant (closedAnnulus ρm ρp) :=
  fun _ _ => rot_mem_closedAnnulus

@[simp] theorem inclSec_apply_coe {s : ℕ} {K : Set ℂ} {ℓ : ℤ} (g : Ysec s K ℓ) :
    ((inclSec s K ℓ g : Y s K) : SobTuple s) = (g : SobTuple s) := rfl

@[simp] theorem inclZ_apply_coe {s : ℕ} {K : Set ℂ} {Z : Set ℤ} (g : YZ s K Z) :
    ((inclZ s K Z g : Y s K) : SobTuple s) = (g : SobTuple s) := rfl

@[simp] theorem inclSym_apply_coe {s : ℕ} {K : Set ℂ} {m : ℕ} (g : Ysym s K m) :
    ((inclSym s K m g : Y s K) : SobTuple s) = (g : SobTuple s) := rfl

theorem Y.fn_inclSec {s : ℕ} {K : Set ℂ} {ℓ : ℤ} (g : Ysec s K ℓ) :
    (inclSec s K ℓ g).fn = g.fn := rfl

end NonUniqueEuler.Sect
