import NonUniqueEuler.Defs.Infra.SectorSpace
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.SectorSpace.Projection
import NonUniqueEuler.I.Infra.SectorSpace.DirectSum
import NonUniqueEuler.I.Infra.SectorSpace.RadialMul

/-!
# Proof: the inclusions `Y^{s'} ⊂ Y^s` for `s ≤ s'` (library I-SECT)

Proof of `I/Infra/SectorSpace/Lower.lean` (statements copied verbatim).

Construction. For `s ≤ s'` the index map `restrIdx h : {|γ| ≤ s} → {|γ| ≤ s'}` is injective, so
forgetting the entries of order `> s` is a continuous linear map
`restrCLM h : SobTuple s' →L[ℂ] SobTuple s` of norm `≤ 1` (`PiLp.norm_eq_of_L2`, fewer
nonnegative terms: `Finset.sum_le_sum_of_injOn`). It keeps the entry `F_0`, so it maps `HkSub s'`
into `HkSub s` (`mem_HkSub_iff`: the conditions for `|γ| ≤ s` are among those for `|γ| ≤ s'`)
and preserves the support and sector conditions (which only involve `F_0` through `proj0`).
This gives the explicit operators `lowY h K`, `lowSec h K ℓ`, whose functions are *equal* to the
input functions. Elements of `Y^s(K)`, `Y^s_ℓ(K)` are determined by their functions
(`Sob.Hk.ext_fn`), so the chosen `lowerY`, `lowerSec` coincide with them (`lowerY_eq`,
`lowerSec_eq`), which gives the norm bound and injectivity. The commutation statements are
proved by comparing functions, using `secProj_spec`, `exists_sectorSum_spec` (uniqueness of the
limit of the sector series) and `exists_radialMul_spec`.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Sect

open Sob Ang

namespace LowerP

variable {s s' : ℕ}

/-- The inclusion of multi-indices `{|γ| ≤ s} → {|γ| ≤ s'}`. -/
def restrIdx (h : s ≤ s') (γ : SobIdx s) : SobIdx s' :=
  ⟨γ.1, multiIdx_mono h γ.2⟩

theorem restrIdx_injective (h : s ≤ s') : Function.Injective (restrIdx h) := by
  intro a b hab
  exact Subtype.ext (congrArg (fun x : SobIdx s' => (x : ℕ × ℕ)) hab)

/-- Forget the entries `F_γ` with `|γ| > s`. -/
def restrLin (h : s ≤ s') : SobTuple s' →ₗ[ℂ] SobTuple s where
  toFun F := WithLp.toLp 2 (fun γ => F.ofLp (restrIdx h γ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem norm_restrLin_le (h : s ≤ s') (F : SobTuple s') : ‖restrLin h F‖ ≤ ‖F‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  classical
  exact Finset.sum_le_sum_of_injOn (restrIdx h) (restrIdx_injective h).injOn
    (Finset.subset_univ _) (fun _ _ => le_rfl) (fun _ _ _ => sq_nonneg _)

/-- The truncation `SobTuple s' → SobTuple s`, of norm `≤ 1`. -/
def restrCLM (h : s ≤ s') : SobTuple s' →L[ℂ] SobTuple s :=
  (restrLin h).mkContinuous 1 fun F => by
    rw [one_mul]
    exact norm_restrLin_le h F

theorem restrCLM_apply_ofLp (h : s ≤ s') (F : SobTuple s') (γ : SobIdx s) :
    (restrCLM h F).ofLp γ = F.ofLp (restrIdx h γ) := rfl

theorem norm_restrCLM_apply_le (h : s ≤ s') (F : SobTuple s') : ‖restrCLM h F‖ ≤ ‖F‖ :=
  norm_restrLin_le h F

theorem proj0_restrCLM (h : s ≤ s') (F : SobTuple s') : proj0 s (restrCLM h F) = proj0 s' F :=
  rfl

theorem suppCLM_restrCLM (h : s ≤ s') (K : Set ℂ) (F : SobTuple s') :
    suppCLM s K (restrCLM h F) = suppCLM s' K F := rfl

theorem sectorDefect_restrCLM (h : s ≤ s') (ℓ : ℤ) (θ : ℝ) (F : SobTuple s') :
    sectorDefect s ℓ θ (restrCLM h F) = sectorDefect s' ℓ θ F := rfl

theorem restrCLM_mem_HkSub (h : s ≤ s') {F : SobTuple s'} (hF : F ∈ HkSub s') :
    restrCLM h F ∈ HkSub s := by
  rw [mem_HkSub_iff] at hF ⊢
  intro γ
  exact hF (restrIdx h γ)

theorem restrCLM_mem_YSub (h : s ≤ s') {K : Set ℂ} {F : SobTuple s'} (hF : F ∈ YSub s' K) :
    restrCLM h F ∈ YSub s K := by
  rw [YSub, Submodule.mem_inf, LinearMap.mem_ker] at hF ⊢
  refine ⟨restrCLM_mem_HkSub h hF.1, ?_⟩
  rw [ContinuousLinearMap.coe_coe] at hF ⊢
  rw [suppCLM_restrCLM]
  exact hF.2

theorem restrCLM_mem_YsecSub (h : s ≤ s') {K : Set ℂ} {ℓ : ℤ} {F : SobTuple s'}
    (hF : F ∈ YsecSub s' K ℓ) : restrCLM h F ∈ YsecSub s K ℓ := by
  rw [YsecSub, Submodule.mem_inf, Submodule.mem_iInf] at hF ⊢
  refine ⟨restrCLM_mem_YSub h hF.1, fun θ => ?_⟩
  have h2 := hF.2 θ
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at h2 ⊢
  rw [sectorDefect_restrCLM]
  exact h2

/-- The explicit inclusion `Y^{s'}(K) → Y^s(K)`. -/
def lowY (h : s ≤ s') (K : Set ℂ) : Y s' K →L[ℂ] Y s K :=
  ((restrCLM h).comp (YSub s' K).subtypeL).codRestrict (YSub s K) fun w =>
    restrCLM_mem_YSub h w.2

/-- The explicit inclusion `Y^{s'}_ℓ(K) → Y^s_ℓ(K)`. -/
def lowSec (h : s ≤ s') (K : Set ℂ) (ℓ : ℤ) : Ysec s' K ℓ →L[ℂ] Ysec s K ℓ :=
  ((restrCLM h).comp (YsecSub s' K ℓ).subtypeL).codRestrict (YsecSub s K ℓ) fun g =>
    restrCLM_mem_YsecSub h g.2

theorem lowY_coe (h : s ≤ s') (K : Set ℂ) (w : Y s' K) :
    ((lowY h K w : Y s K) : SobTuple s) = restrCLM h (w : SobTuple s') := rfl

theorem lowSec_coe (h : s ≤ s') (K : Set ℂ) (ℓ : ℤ) (g : Ysec s' K ℓ) :
    ((lowSec h K ℓ g : Ysec s K ℓ) : SobTuple s) = restrCLM h (g : SobTuple s') := rfl

theorem lowY_fn (h : s ≤ s') (K : Set ℂ) (w : Y s' K) : (lowY h K w).fn = w.fn := rfl

theorem lowSec_fn (h : s ≤ s') (K : Set ℂ) (ℓ : ℤ) (g : Ysec s' K ℓ) :
    (lowSec h K ℓ g).fn = g.fn := rfl

theorem norm_lowY_le (h : s ≤ s') (K : Set ℂ) : ‖lowY h K‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [one_mul]
    exact norm_restrCLM_apply_le h (w : SobTuple s')

theorem norm_lowSec_le (h : s ≤ s') (K : Set ℂ) (ℓ : ℤ) : ‖lowSec h K ℓ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
    rw [one_mul]
    exact norm_restrCLM_apply_le h (g : SobTuple s')

/-! ### Extensionality: elements are determined by their functions -/

theorem Y_ext {K : Set ℂ} {w v : Y s K} (hwv : w.fn =ᵐ[volume] v.fn) : w = v := by
  have := Hk.ext_fn (F := (⟨w, YSub_le_HkSub s K w.2⟩ : Hk s))
    (G := ⟨v, YSub_le_HkSub s K v.2⟩) hwv
  exact Subtype.ext (congrArg (fun x : Hk s => (x : SobTuple s)) this)

theorem Ysec_ext {K : Set ℂ} {ℓ : ℤ} {g g' : Ysec s K ℓ} (hgg : g.fn =ᵐ[volume] g'.fn) :
    g = g' := by
  have := Hk.ext_fn (F := (⟨g, YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ g.2)⟩ : Hk s))
    (G := ⟨g', YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ g'.2)⟩) hgg
  exact Subtype.ext (congrArg (fun x : Hk s => (x : SobTuple s)) this)

/-! ### The chosen inclusions are the explicit ones -/

theorem lowerY_eq (h : s ≤ s') (K : Set ℂ) : lowerY s s' K = lowY h K := by
  have hex : ∃ T : Y s' K →L[ℂ] Y s K, ∀ w, (T w).fn =ᵐ[volume] w.fn :=
    ⟨lowY h K, fun _ => Filter.EventuallyEq.rfl⟩
  have hspec : ∀ w, (lowerY s s' K w).fn =ᵐ[volume] w.fn := by
    rw [lowerY, dite_eq_left_of_eq_true (eq_true hex)]
    exact hex.choose_spec
  ext1 w
  exact Y_ext ((hspec w).trans (Filter.EventuallyEq.of_eq (lowY_fn h K w).symm))

theorem lowerSec_eq (h : s ≤ s') (K : Set ℂ) (ℓ : ℤ) : lowerSec s s' K ℓ = lowSec h K ℓ := by
  have hex : ∃ T : Ysec s' K ℓ →L[ℂ] Ysec s K ℓ, ∀ g, (T g).fn =ᵐ[volume] g.fn :=
    ⟨lowSec h K ℓ, fun _ => Filter.EventuallyEq.rfl⟩
  have hspec : ∀ g, (lowerSec s s' K ℓ g).fn =ᵐ[volume] g.fn := by
    rw [lowerSec, dite_eq_left_of_eq_true (eq_true hex)]
    exact hex.choose_spec
  ext1 g
  exact Ysec_ext ((hspec g).trans (Filter.EventuallyEq.of_eq (lowSec_fn h K ℓ g).symm))

end LowerP

open LowerP

theorem lowerY_spec {s s' : ℕ} (h : s ≤ s') (K : Set ℂ) :
    (∀ w : Y s' K, (lowerY s s' K w).fn =ᵐ[volume] w.fn) ∧ ‖lowerY s s' K‖ ≤ 1 ∧
      Function.Injective (lowerY s s' K) := by
  rw [lowerY_eq h K]
  refine ⟨fun w => Filter.EventuallyEq.of_eq (lowY_fn h K w), norm_lowY_le h K,
    fun w v hwv => ?_⟩
  apply Y_ext
  have := congrArg Y.fn hwv
  rw [lowY_fn, lowY_fn] at this
  exact Filter.EventuallyEq.of_eq this

theorem lowerSec_spec {s s' : ℕ} (h : s ≤ s') (K : Set ℂ) (ℓ : ℤ) :
    (∀ g : Ysec s' K ℓ, (lowerSec s s' K ℓ g).fn =ᵐ[volume] g.fn) ∧ ‖lowerSec s s' K ℓ‖ ≤ 1 ∧
      Function.Injective (lowerSec s s' K ℓ) := by
  rw [lowerSec_eq h K ℓ]
  refine ⟨fun g => Filter.EventuallyEq.of_eq (lowSec_fn h K ℓ g), norm_lowSec_le h K ℓ,
    fun g g' hgg => ?_⟩
  apply Ysec_ext
  have := congrArg Ysec.fn hgg
  rw [lowSec_fn, lowSec_fn] at this
  exact Filter.EventuallyEq.of_eq this

theorem lowerY_inclSec {s s' : ℕ} (h : s ≤ s') (K : Set ℂ) (ℓ : ℤ) (g : Ysec s' K ℓ) :
    lowerY s s' K (inclSec s' K ℓ g) = inclSec s K ℓ (lowerSec s s' K ℓ g) := by
  rw [lowerY_eq h K, lowerSec_eq h K ℓ]
  exact Subtype.ext rfl

theorem secProj_lowerY {s s' : ℕ} (h : s ≤ s') {K : Set ℂ} (hK : IsRotInvariant K) (ℓ : ℤ)
    (w : Y s' K) :
    secProj s K ℓ (lowerY s s' K w) = lowerSec s s' K ℓ (secProj s' K ℓ w) := by
  rw [lowerY_eq h K, lowerSec_eq h K ℓ]
  apply Ysec_ext
  have e1 := (secProj_spec (s := s) hK ℓ).1 (lowY h K w)
  have e2 := (secProj_spec (s := s') hK ℓ).1 w
  rw [lowY_fn] at e1
  rw [lowSec_fn]
  exact e1.trans e2.symm

/-- Direct sums commute with the inclusions when the sector operators do. -/
theorem sectorSum_lowerY {s s' : ℕ} (h : s ≤ s') {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    {A : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s (closedAnnulus ρm ρp) ℓ}
    {A' : ∀ ℓ : ℤ, Ysec s' (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s' (closedAnnulus ρm ρp) ℓ}
    {M M' : ℝ} (hA : ∀ ℓ, ‖A ℓ‖ ≤ M) (hA' : ∀ ℓ, ‖A' ℓ‖ ≤ M')
    (hcomm : ∀ ℓ g, A ℓ (lowerSec s s' _ ℓ g) = lowerSec s s' _ ℓ (A' ℓ g))
    (w : Y s' (closedAnnulus ρm ρp)) :
    sectorSum s _ A (lowerY s s' _ w) = lowerY s s' _ (sectorSum s' _ A' w) := by
  have hK := isRotInvariant_closedAnnulus ρm ρp
  obtain ⟨B, -, hB⟩ := exists_sectorSum_spec s hρm hρ
  obtain ⟨B', -, hB'⟩ := exists_sectorSum_spec s' hρm hρ
  have h1 := (hB A M hA).1 (lowerY s s' _ w)
  have h2 := (lowerY s s' (closedAnnulus ρm ρp)).hasSum ((hB' A' M' hA').1 w)
  have hterm : ∀ ℓ : ℤ, lowerY s s' _ (inclSec s' _ ℓ (A' ℓ (secProj s' _ ℓ w))) =
      inclSec s _ ℓ (A ℓ (secProj s _ ℓ (lowerY s s' _ w))) := by
    intro ℓ
    rw [lowerY_inclSec h, ← hcomm, secProj_lowerY h hK]
  simp only [hterm] at h2
  exact h1.unique h2

theorem radialMul_lowerSec {s s' : ℕ} (h : s ≤ s') {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    (ℓ : ℤ) {a : ℝ → ℂ} (ha : MemCk s' (Icc ρm ρp) a) (g : Ysec s' (closedAnnulus ρm ρp) ℓ) :
    radialMul s _ ℓ a (lowerSec s s' _ ℓ g) = lowerSec s s' _ ℓ (radialMul s' _ ℓ a g) := by
  obtain ⟨C, -, hC⟩ := exists_radialMul_spec s hρm hρ
  obtain ⟨C', -, hC'⟩ := exists_radialMul_spec s' hρm hρ
  rw [lowerSec_eq h _ ℓ]
  apply Ysec_ext
  have e1 := (hC ℓ a (ha.mono_order h)).1 (lowSec h _ ℓ g)
  have e2 := (hC' ℓ a ha).1 g
  rw [lowSec_fn] at e1
  rw [lowSec_fn]
  exact e1.trans e2.symm

end NonUniqueEuler.Sect
