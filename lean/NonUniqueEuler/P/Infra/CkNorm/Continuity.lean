import NonUniqueEuler.Defs.Infra.CkNorm
import NonUniqueEuler.I.Infra.CkNorm.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Module.Multilinear.Topology

/-!
# Proof: continuity in time of `C^k(U)` norms (library I-CK)

Proof of `NonUniqueEuler/I/Infra/CkNorm/Continuity.lean` (same declarations, statements copied
verbatim). Uses `I/Infra/CkNorm/Basic.lean` (`IsCkNear.memCk_of_isCompact`, `MemCk.add`,
`MemCk.sub`) as a black box.

Write `f = uncurry h`. Steps (helpers in the namespace `NonUniqueEuler.CkNormContinuity`):
* `iteratedFDeriv_slice_eq`: for `(t, x) ∈ W` and `q ≤ k`,
  `D^q (h t) x = (D^q f (t, x)).compContinuousLinearMap (fun _ => inr)`. Proof: `h t = g ∘ inr`
  with `g = f (· + (t, 0))`, then `ContinuousLinearMap.iteratedFDerivWithin_comp_right` on the
  open set `(· + (t,0))⁻¹' W`, `iteratedFDerivWithin_of_isOpen` and
  `iteratedFDeriv_comp_add_right`.
* `continuousOn_sliceDeriv`: the right side is continuous on `W`.
* `eventually_forall_norm_sub_lt`: for `Φ` continuous on the open `W ⊇ {t₀} × U`, `U` compact,
  `‖Φ (t, x) - Φ (t₀, x)‖ < ε` for all `x ∈ U` and `t` near `t₀`
  (`IsCompact.eventually_forall_of_forall_eventually`).
* Then `iteratedFDeriv_sub_apply` and `normCk_le_of_bound`.
-/

noncomputable section

open scoped ENNReal ContDiff Topology
open Set Filter

namespace NonUniqueEuler

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

namespace CkNormContinuity

omit [NormedSpace ℝ E] in
theorem isOpen_slice {W : Set (ℝ × E)} (hW : IsOpen W) (t : ℝ) :
    IsOpen {x : E | (t, x) ∈ W} :=
  hW.preimage (Continuous.prodMk_right t)

theorem contDiffOn_slice {k : ℕ} {h : ℝ → E → F} {W : Set (ℝ × E)}
    (hh : ContDiffOn ℝ k (fun p : ℝ × E => h p.1 p.2) W) (t : ℝ) :
    ContDiffOn ℝ k (h t) {x : E | (t, x) ∈ W} :=
  hh.comp (contDiff_prodMk_right t).contDiffOn (fun _ hx => hx)

/-- The `x`-derivatives of a slice are the joint derivatives restricted to the `x`-directions. -/
theorem iteratedFDeriv_slice_eq {k : ℕ} {h : ℝ → E → F} {W : Set (ℝ × E)} (hW : IsOpen W)
    (hh : ContDiffOn ℝ k (fun p : ℝ × E => h p.1 p.2) W) {t : ℝ} {x : E} (hx : (t, x) ∈ W)
    {q : ℕ} (hq : q ≤ k) :
    iteratedFDeriv ℝ q (h t) x =
      (iteratedFDeriv ℝ q (fun p : ℝ × E => h p.1 p.2) (t, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ E) := by
  set f : ℝ × E → F := fun p => h p.1 p.2 with hf
  set a : ℝ × E := (t, 0) with ha
  set g : ℝ × E → F := fun p => f (p + a) with hg_def
  set S : Set (ℝ × E) := (fun p => p + a) ⁻¹' W with hS_def
  have hS : IsOpen S := hW.preimage (continuous_add_const a)
  have hg : ContDiffOn ℝ k g S :=
    hh.comp ((contDiff_id.add contDiff_const).contDiffOn) (fun _ hp => hp)
  have hcomp : h t = g ∘ ContinuousLinearMap.inr ℝ ℝ E := by
    funext y
    simp [g, f, a]
  have hpre : IsOpen ((ContinuousLinearMap.inr ℝ ℝ E) ⁻¹' S) :=
    hS.preimage (ContinuousLinearMap.continuous _)
  have hxS : ContinuousLinearMap.inr ℝ ℝ E x ∈ S := by
    simpa [S, a] using hx
  rw [hcomp, ← iteratedFDerivWithin_of_isOpen q hpre hxS,
    ContinuousLinearMap.iteratedFDerivWithin_comp_right _ hg hS.uniqueDiffOn hpre.uniqueDiffOn
      hxS (by exact_mod_cast hq),
    iteratedFDerivWithin_of_isOpen q hS hxS, iteratedFDeriv_comp_add_right]
  simp [a]

/-- The restricted joint derivative is continuous on `W`. -/
theorem continuousOn_sliceDeriv {k : ℕ} {h : ℝ → E → F} {W : Set (ℝ × E)} (hW : IsOpen W)
    (hh : ContDiffOn ℝ k (fun p : ℝ × E => h p.1 p.2) W) {q : ℕ} (hq : q ≤ k) :
    ContinuousOn (fun p : ℝ × E =>
      (iteratedFDeriv ℝ q (fun p : ℝ × E => h p.1 p.2) p).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ E)) W := by
  have h1 : ContinuousOn (iteratedFDeriv ℝ q (fun p : ℝ × E => h p.1 p.2)) W :=
    (hh.continuousOn_iteratedFDerivWithin (by exact_mod_cast hq) hW.uniqueDiffOn).congr
      (fun p hp => (iteratedFDerivWithin_of_isOpen q hW hp).symm)
  exact (ContinuousMultilinearMap.continuous_precomp _).comp_continuousOn h1

omit [NormedSpace ℝ E] in
/-- Uniform closeness on a compact slice (tube lemma). -/
theorem eventually_forall_norm_sub_lt {G : Type*} [NormedAddCommGroup G] {Φ : ℝ × E → G}
    {W : Set (ℝ × E)} (hW : IsOpen W) (hΦ : ContinuousOn Φ W) {U : Set E} (hU : IsCompact U)
    {t₀ : ℝ} (hU₀ : ∀ x ∈ U, (t₀, x) ∈ W) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∀ x ∈ U, (t, x) ∈ W ∧ ‖Φ (t, x) - Φ (t₀, x)‖ < ε := by
  apply hU.eventually_forall_of_forall_eventually
  intro y hy
  have hWy : W ∈ 𝓝 (t₀, y) := hW.mem_nhds (hU₀ y hy)
  have h1 : ContinuousAt Φ (t₀, y) := hΦ.continuousAt hWy
  have h2 : ContinuousAt (fun z : ℝ × E => Φ (t₀, z.2)) (t₀, y) := by
    have : ContinuousAt (fun z : ℝ × E => (t₀, z.2)) (t₀, y) :=
      (continuous_const.prodMk continuous_snd).continuousAt
    exact ContinuousAt.comp (f := fun z : ℝ × E => (t₀, z.2)) (g := Φ) h1 this
  have hc : ContinuousAt (fun z : ℝ × E => ‖Φ z - Φ (t₀, z.2)‖) (t₀, y) := (h1.sub h2).norm
  have h0 : (fun z : ℝ × E => ‖Φ z - Φ (t₀, z.2)‖) (t₀, y) < ε := by simpa using hε
  have hlt : ∀ᶠ z in 𝓝 (t₀, y), ‖Φ z - Φ (t₀, z.2)‖ < ε := Tendsto.eventually_lt_const h0 hc
  filter_upwards [hWy, hlt] with z hz1 hz2
  exact ⟨hz1, hz2⟩

end CkNormContinuity

open CkNormContinuity

/-- Slices of a jointly `C^k` family are `C^k` near `U`. -/
theorem memCk_slice_of_contDiffOn {k : ℕ} {U : Set E} (hU : IsCompact U) {J : Set ℝ}
    {h : ℝ → E → F} {W : Set (ℝ × E)} (hW : IsOpen W) (hJU : J ×ˢ U ⊆ W)
    (hh : ContDiffOn ℝ k (fun p : ℝ × E => h p.1 p.2) W) {t : ℝ} (ht : t ∈ J) :
    MemCk k U (h t) := by
  exact IsCkNear.memCk_of_isCompact
    ⟨_, isOpen_slice hW t, fun x hx => hJU ⟨ht, hx⟩, contDiffOn_slice hh t⟩ hU

/-- `t ↦ h t` is continuous into `C^k(U)`. -/
theorem tendsto_normCk_sub_of_contDiffOn {k : ℕ} {U : Set E} (hU : IsCompact U) {J : Set ℝ}
    {h : ℝ → E → F} {W : Set (ℝ × E)} (hW : IsOpen W) (hJU : J ×ˢ U ⊆ W)
    (hh : ContDiffOn ℝ k (fun p : ℝ × E => h p.1 p.2) W) {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    Tendsto (fun t => normCk k U (h t - h t₀)) (𝓝[J] t₀) (𝓝 0) := by
  have hU₀ : ∀ x ∈ U, (t₀, x) ∈ W := fun x hx => hJU ⟨ht₀, hx⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / (2 * ((k : ℝ) + 1)) with hδ_def
  have hδ : 0 < δ := by positivity
  have hev : ∀ᶠ t in 𝓝 t₀, ∀ q ∈ Finset.range (k + 1), ∀ x ∈ U, (t, x) ∈ W ∧
      ‖(iteratedFDeriv ℝ q (fun p : ℝ × E => h p.1 p.2) (t, x)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ E) -
        (iteratedFDeriv ℝ q (fun p : ℝ × E => h p.1 p.2) (t₀, x)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ E)‖ < δ := by
    rw [Filter.eventually_all_finset]
    intro q hq
    exact eventually_forall_norm_sub_lt hW
      (continuousOn_sliceDeriv hW hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq))) hU hU₀ hδ
  filter_upwards [nhdsWithin_le_nhds hev] with t ht
  have hbound : ∀ q ≤ k, ∀ x ∈ U, ‖iteratedFDeriv ℝ q (h t - h t₀) x‖ ≤ δ := by
    intro q hq x hx
    obtain ⟨hxt, hlt⟩ := ht q (Finset.mem_range.2 (Nat.lt_succ_of_le hq)) x hx
    have hq' : ((q : ℕ) : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hq
    have hd1 : ContDiffAt ℝ q (h t) x :=
      ((contDiffOn_slice hh t).contDiffAt ((isOpen_slice hW t).mem_nhds hxt)).of_le hq'
    have hd2 : ContDiffAt ℝ q (h t₀) x :=
      ((contDiffOn_slice hh t₀).contDiffAt ((isOpen_slice hW t₀).mem_nhds (hU₀ x hx))).of_le hq'
    rw [iteratedFDeriv_sub_apply hd1 hd2, iteratedFDeriv_slice_eq hW hh hxt hq,
      iteratedFDeriv_slice_eq hW hh (hU₀ x hx) hq]
    exact hlt.le
  have hle := normCk_le_of_bound (k := k) (U := U) (h := h t - h t₀) (fun _ => δ)
    (fun _ => hδ.le) hbound
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
  have hval : ((k + 1 : ℕ) : ℝ) * δ = ε / 2 := by
    rw [hδ_def]
    push_cast
    field_simp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (normCk_nonneg _ _ _)]
  linarith

/-- `t ↦ ‖h t‖_{C^k(U)}` is continuous on `J`. -/
theorem continuousOn_normCk_of_contDiffOn {k : ℕ} {U : Set E} (hU : IsCompact U) {J : Set ℝ}
    {h : ℝ → E → F} {W : Set (ℝ × E)} (hW : IsOpen W) (hJU : J ×ˢ U ⊆ W)
    (hh : ContDiffOn ℝ k (fun p : ℝ × E => h p.1 p.2) W) :
    ContinuousOn (fun t => normCk k U (h t)) J := by
  intro t₀ ht₀
  have hlim := tendsto_normCk_sub_of_contDiffOn hU hW hJU hh ht₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have m := memCk_slice_of_contDiffOn hU hW hJU hh ht
  have m0 := memCk_slice_of_contDiffOn hU hW hJU hh ht₀
  have hs := MemCk.sub m m0
  have h1 := (MemCk.add hs.1 m0).2
  have h2 := (MemCk.sub m hs.1).2
  rw [sub_add_cancel] at h1
  rw [sub_sub_cancel] at h2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- Uniform bound on a compact time set. -/
theorem exists_bound_normCk_of_contDiffOn {k : ℕ} {U : Set E} (hU : IsCompact U) {J : Set ℝ}
    (hJ : IsCompact J) {h : ℝ → E → F} {W : Set (ℝ × E)} (hW : IsOpen W) (hJU : J ×ˢ U ⊆ W)
    (hh : ContDiffOn ℝ k (fun p : ℝ × E => h p.1 p.2) W) :
    ∃ M : ℝ, ∀ t ∈ J, normCk k U (h t) ≤ M := by
  obtain ⟨M, hM⟩ := hJ.bddAbove_image (continuousOn_normCk_of_contDiffOn hU hW hJU hh)
  exact ⟨M, fun t ht => hM ⟨t, ht, rfl⟩⟩

end NonUniqueEuler
