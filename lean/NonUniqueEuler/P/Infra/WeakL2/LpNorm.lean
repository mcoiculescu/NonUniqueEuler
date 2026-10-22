import NonUniqueEuler.Defs.Infra.WeakL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Proof of the interface `I/Infra/WeakL2/LpNorm.lean` (I-WEAKL2)

Lower semicontinuity of `L^q` norms (`q ∈ [1, ∞]`) under weak convergence in `L²(μ)`.

Restructured proof (instead of the duality against simple test functions sketched in the
interface docstring, we use Mazur's argument):
* `WeakTendsto.mem_of_frequently`: in a real Hilbert space a weak limit of a family that is
  frequently in a closed convex set `C` lies in `C` (Hahn–Banach `geometric_hahn_banach_point_closed`
  and the Riesz representation `InnerProductSpace.toDual`).
* `convex_setOf_eLpNorm_le`: for `1 ≤ q` the sublevel set `{f ∈ L² : ‖f‖_q ≤ c}` is convex
  (Minkowski `eLpNorm_add_le`).
* `isClosed_setOf_eLpNorm_le`: it is closed in `L²` (an `L²`-convergent sequence has an a.e.
  convergent subsequence, then Fatou `eLpNorm_le_of_ae_tendsto`).
Hence `c < ‖x‖_q` forces `c < ‖u i‖_q` eventually, which gives the `liminf` inequality.

The σ-finiteness hypothesis of the interface is not needed.
-/

noncomputable section

open Filter Topology Set MeasureTheory
open scoped InnerProductSpace ENNReal

namespace NonUniqueEuler.WeakL2

section Mazur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Mazur.** A weak limit of a family that is frequently in a closed convex set lies in it. -/
theorem WeakTendsto.mem_of_frequently {ι : Type*} {l : Filter ι} {u : ι → E} {x : E}
    {C : Set E} (hC : Convex ℝ C) (hCc : IsClosed C) (h : WeakTendsto u l x)
    (hu : ∃ᶠ i in l, u i ∈ C) : x ∈ C := by
  by_contra hx
  obtain ⟨f, c, hfx, hfC⟩ := geometric_hahn_banach_point_closed hC hCc hx
  set y : E := (InnerProductSpace.toDual ℝ E).symm f
  have hy : ∀ v : E, ⟪v, y⟫_ℝ = f v := fun v => by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have ht := h y
  rw [hy] at ht
  have hlt : ∀ᶠ i in l, ⟪u i, y⟫_ℝ < c := ht.eventually (gt_mem_nhds hfx)
  obtain ⟨i, hi1, hi2⟩ := (hu.and_eventually hlt).exists
  have h1 := hfC _ hi1
  rw [hy] at hi2
  linarith

end Mazur

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- For `1 ≤ q`, the `L^q` sublevel sets in `L²` are convex. -/
theorem convex_setOf_eLpNorm_le {q : ℝ≥0∞} (hq : 1 ≤ q) (c : ℝ≥0∞) :
    Convex ℝ {f : Lp ℝ 2 μ | eLpNorm f q μ ≤ c} := by
  intro f hf g hg a b ha hb hab
  change eLpNorm f q μ ≤ c at hf
  change eLpNorm g q μ ≤ c at hg
  change eLpNorm (a • f + b • g : Lp ℝ 2 μ) q μ ≤ c
  have hae : ((a • f + b • g : Lp ℝ 2 μ) : α → ℝ) =ᵐ[μ]
      a • (f : α → ℝ) + b • (g : α → ℝ) := by
    filter_upwards [Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f, Lp.coeFn_smul b g]
      with z h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
    rfl
  rw [eLpNorm_congr_ae hae]
  have hab' : ‖a‖ₑ + ‖b‖ₑ = 1 := by
    rw [Real.enorm_of_nonneg ha, Real.enorm_of_nonneg hb, ← ENNReal.ofReal_add ha hb, hab,
      ENNReal.ofReal_one]
  calc eLpNorm (a • (f : α → ℝ) + b • (g : α → ℝ)) q μ
      ≤ eLpNorm (a • (f : α → ℝ)) q μ + eLpNorm (b • (g : α → ℝ)) q μ :=
        eLpNorm_add_le ((Lp.aestronglyMeasurable f).const_smul a)
          ((Lp.aestronglyMeasurable g).const_smul b) hq
    _ = ‖a‖ₑ * eLpNorm f q μ + ‖b‖ₑ * eLpNorm g q μ := by
        rw [eLpNorm_const_smul, eLpNorm_const_smul]
    _ ≤ ‖a‖ₑ * c + ‖b‖ₑ * c := by gcongr
    _ = c := by rw [← add_mul, hab', one_mul]

/-- The `L^q` sublevel sets are closed in `L²` (Fatou along an a.e. convergent subsequence). -/
theorem isClosed_setOf_eLpNorm_le (q : ℝ≥0∞) (c : ℝ≥0∞) :
    IsClosed {f : Lp ℝ 2 μ | eLpNorm f q μ ≤ c} := by
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨g, hg, hgf⟩ := mem_closure_iff_seq_limit.mp hf
  have hm := tendstoInMeasure_of_tendsto_Lp hgf
  obtain ⟨ns, -, hns⟩ := hm.exists_seq_tendsto_ae
  exact Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (Eventually.of_forall fun n => hg (ns n))
    (fun n => Lp.aestronglyMeasurable _) hns

section Eventually

variable {ι : Type*} {l : Filter ι} {u : ι → Lp ℝ 2 μ} {x : Lp ℝ 2 μ}

/-- If `c < ‖x‖_q` and `u i ⇀ x` in `L²`, then eventually `c < ‖u i‖_q`. -/
theorem eventually_lt_eLpNorm_of_weakTendsto {q : ℝ≥0∞} (hq : 1 ≤ q)
    (h : WeakTendsto u l x) {c : ℝ≥0∞} (hc : c < eLpNorm x q μ) :
    ∀ᶠ i in l, c < eLpNorm (u i) q μ := by
  by_contra hne
  rw [not_eventually] at hne
  simp only [not_lt] at hne
  have hx : x ∈ {f : Lp ℝ 2 μ | eLpNorm f q μ ≤ c} :=
    h.mem_of_frequently (convex_setOf_eLpNorm_le hq c) (isClosed_setOf_eLpNorm_le q c) hne
  exact absurd hx (not_le.mpr hc)

end Eventually

/-! ### The interface statements (variables in the order of the interface file) -/

variable [SigmaFinite μ]
variable {ι : Type*} {l : Filter ι} {u : ι → Lp ℝ 2 μ} {x : Lp ℝ 2 μ}

/-- **Weak lower semicontinuity of `L^q` norms** under weak convergence in `L²`, for every
`q ∈ [1, ∞]`. -/
theorem eLpNorm_le_liminf_of_weakTendsto {q : ℝ≥0∞} (hq : 1 ≤ q) (h : WeakTendsto u l x) :
    eLpNorm x q μ ≤ liminf (fun i => eLpNorm (u i) q μ) l := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  exact le_liminf_of_le (by isBoundedDefault)
    ((eventually_lt_eLpNorm_of_weakTendsto hq h hc).mono fun _ hi => hi.le)

/-- A uniform `L^q` bound passes to weak `L²` limits (`q ∈ [1, ∞]`). -/
theorem eLpNorm_le_of_weakTendsto [l.NeBot] {q : ℝ≥0∞} (hq : 1 ≤ q) (h : WeakTendsto u l x)
    {M : ℝ≥0∞} (hM : ∀ᶠ i in l, eLpNorm (u i) q μ ≤ M) : eLpNorm x q μ ≤ M := by
  have hx : x ∈ {f : Lp ℝ 2 μ | eLpNorm f q μ ≤ M} :=
    h.mem_of_frequently (convex_setOf_eLpNorm_le hq M) (isClosed_setOf_eLpNorm_le q M)
      hM.frequently
  exact hx

/-- A uniform bound on `‖·‖_p + ‖·‖_q` passes to weak `L²` limits (`p, q ∈ [1, ∞]`). -/
theorem eLpNorm_add_eLpNorm_le_of_weakTendsto [l.NeBot] {p q : ℝ≥0∞} (hp : 1 ≤ p)
    (hq : 1 ≤ q) (h : WeakTendsto u l x) {M : ℝ≥0∞}
    (hM : ∀ᶠ i in l, eLpNorm (u i) p μ + eLpNorm (u i) q μ ≤ M) :
    eLpNorm x p μ + eLpNorm x q μ ≤ M := by
  rcases eq_or_ne (eLpNorm x p μ) 0 with hA | hA
  · rw [hA, zero_add]
    exact eLpNorm_le_of_weakTendsto hq h (hM.mono fun _ hi => le_add_self.trans hi)
  rcases eq_or_ne (eLpNorm x q μ) 0 with hB | hB
  · rw [hB, add_zero]
    exact eLpNorm_le_of_weakTendsto hp h (hM.mono fun _ hi => le_self_add.trans hi)
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨a, ha, b, hb, hab⟩ := ENNReal.exists_lt_add_of_lt_add hlt hA hB
  obtain ⟨i, hi1, hi2, hi3⟩ := ((eventually_lt_eLpNorm_of_weakTendsto hp h ha).and
    ((eventually_lt_eLpNorm_of_weakTendsto hq h hb).and hM)).exists
  exact absurd (hab.trans_le ((add_le_add hi1.le hi2.le).trans hi3)) (lt_irrefl M)

/-- A weak `L²` limit of a family bounded in `L^q` lies in `L^q` (`q ∈ [1, ∞]`). -/
theorem memLp_of_weakTendsto [l.NeBot] {q : ℝ≥0∞} (hq : 1 ≤ q) (h : WeakTendsto u l x)
    {M : ℝ≥0∞} (hM : ∀ᶠ i in l, eLpNorm (u i) q μ ≤ M) (hMfin : M ≠ ∞) :
    MemLp x q μ :=
  ⟨Lp.aestronglyMeasurable x, (eLpNorm_le_of_weakTendsto hq h hM).trans_lt hMfin.lt_top⟩

/-- Weak `L²` convergence gives convergence of the integrals over sets of finite measure. -/
theorem setIntegral_tendsto_of_weakTendsto (h : WeakTendsto u l x) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    Tendsto (fun i => ∫ a in s, u i a ∂μ) l (𝓝 (∫ a in s, x a ∂μ)) := by
  have hψ : MemLp (s.indicator fun _ => (1 : ℝ)) 2 μ := memLp_indicator_const 2 hs 1 (Or.inr hμs)
  have key : ∀ f : Lp ℝ 2 μ,
      ∫ a, f a * s.indicator (fun _ => (1 : ℝ)) a ∂μ = ∫ a in s, f a ∂μ := fun f => by
    rw [← integral_indicator hs]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    by_cases ha : a ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, ha]
  have := h.integral_mul_tendsto hψ
  simpa only [key] using this

end NonUniqueEuler.WeakL2
