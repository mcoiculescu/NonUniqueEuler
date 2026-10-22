import NonUniqueEuler.H.Sec3.Criterion.Basic
import NonUniqueEuler.I.Sec3.RenormAllT
import NonUniqueEuler.I.Sec3.RR
import NonUniqueEuler.I.Infra.Equimeasurable.Norms
import NonUniqueEuler.I.Infra.LpInterp.Tendsto
import NonUniqueEuler.I.Infra.LpInterp.Interp

/-!
# Helper for `P/Sec3/Criterion`: items (ii) and (iii) of `thm:criterion`

Manuscript: proof of `thm:criterion`, paragraph "We next prove (ii) and (iii)",
`03_compactness.tex:996-1021`.

For a renormalized weak solution `ω` on `[0, T₀)` with datum `f` (exponent `2`), weakly
continuous into `L²` on `[0, T₀)`:
* (ii) `ω(t)` is equimeasurable with `f` (`lem:renorm-all-t` on `[0, T₁)`, `T₁ ∈ (t, T₀)`), hence
  has the `L^p` norms of `f`, is `≥ 0` if `f ≥ 0`, and is a renormalized weak solution in
  `X_q(T')` whenever `f ∈ L^q` (`renormalized_q_of_equimeasurable`; the identities do not involve
  `q`);
* (iii) `ω ∈ C([0, T₀); L^q)`: `q ∈ [1, 2)` by `lem:renorm-all-t`, `q = 2` by weak continuity,
  constant norm and `lem:RR` (`continuousIntoLpOn_two`), `q ∈ (2, r)` with `f ∈ L^r` by
  interpolation (R8, `continuousIntoLpOn_of_interp`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.CriterionAux

open Weak

variable {T₀ : ℝ≥0∞} {f : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}

/-- (ii): `ω(t)` is equimeasurable with `f` for every `t ∈ [0, T₀)`. -/
theorem equimeasurable_of_renormalized (hren : IsRenormalizedWeakSolutionUpTo 2 T₀ f ω)
    (hwc : IsWeakContL2On (timeInterval T₀) ω) :
    ∀ t ∈ timeInterval T₀, Equimeasurable (ω t) f := by
  intro t ht
  obtain ⟨T₁, htT₁, hT₁⟩ := exists_lt_of_mem_timeInterval ht
  exact renormAllT_equimeasurable (hren T₁ (ht.1.trans_lt htT₁) hT₁)
    (hwc.mono (Icc_subset_timeInterval hT₁)) t ⟨ht.1, htT₁⟩

/-- (ii): `‖ω(t)‖_{L^p} = ‖f‖_{L^p}`. -/
theorem eLpNorm_eq_of_equimeasurable (heq : ∀ t ∈ timeInterval T₀, Equimeasurable (ω t) f) :
    ∀ t ∈ timeInterval T₀, ∀ p : ℝ≥0∞, 1 ≤ p →
      eLpNorm (ω t) p volume = eLpNorm f p volume :=
  fun t ht p _ => (heq t ht).eLpNorm_eq p

/-- (ii): `ω ≥ 0` if `f ≥ 0`. -/
theorem nonneg_of_equimeasurable (heq : ∀ t ∈ timeInterval T₀, Equimeasurable (ω t) f) :
    0 ≤ᵐ[volume] f → ∀ t ∈ timeInterval T₀, 0 ≤ᵐ[volume] ω t :=
  fun hf t ht => (heq t ht).symm.nonneg hf

/-- (ii): change of exponent. A renormalized weak solution in `X₂(T')` whose slices have, for
every `t ∈ (0, T')`, the `L¹` and `L^q` norms of the datum `f ∈ L^q`, is a renormalized weak
solution in `X_q(T')` (the identities eq:weak, eq:renorm do not involve the exponent). -/
theorem renormalized_q_of_eLpNorm_eq {T' q : ℝ} (hren : IsRenormalizedWeakSolution 2 T' f ω)
    (hq : 4 / 3 < q) (hfq : MemLp f (ENNReal.ofReal q) volume)
    (hmem : ∀ t ∈ Ioo 0 T', MemLp (ω t) (ENNReal.ofReal q) volume)
    (h1 : ∀ t ∈ Ioo 0 T', eLpNorm (ω t) 1 volume = eLpNorm f 1 volume)
    (hqn : ∀ t ∈ Ioo 0 T',
      eLpNorm (ω t) (ENNReal.ofReal q) volume = eLpNorm f (ENNReal.ofReal q) volume) :
    IsRenormalizedWeakSolution q T' f ω := by
  have hX : MemX q T' ω := by
    refine ⟨hren.memX.aestronglyMeasurable, ⟨(eLpNorm f 1 volume).toReal +
      (eLpNorm f (ENNReal.ofReal q) volume).toReal, ?_⟩⟩
    refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_
    have hm1 : MemLp (ω t) 1 volume := by
      refine ⟨(hmem t ht).aestronglyMeasurable, ?_⟩
      rw [h1 t ht]
      exact hren.datum_memLp_one.eLpNorm_lt_top
    exact ⟨hm1, hmem t ht, by rw [h1 t ht, hqn t ht]⟩
  exact
    { q_gt := hq
      T_pos := hren.T_pos
      datum_memLp_one := hren.datum_memLp_one
      datum_memLp_q := hfq
      memX := hX
      velocity_convergent := hren.velocity_convergent
      weak := hren.weak
      renormalized := hren.renormalized }

/-- (ii): `ω` is a renormalized weak solution in `X_q(T')`, `T' < T₀`, `q ∈ (4/3, ∞)`, `f ∈ L^q`. -/
theorem renormalized_q_of_equimeasurable (hren : IsRenormalizedWeakSolutionUpTo 2 T₀ f ω)
    (heq : ∀ t ∈ timeInterval T₀, Equimeasurable (ω t) f) :
    ∀ T' : ℝ, 0 < T' → ENNReal.ofReal T' < T₀ → ∀ q : ℝ, 4 / 3 < q →
      MemLp f (ENNReal.ofReal q) volume → IsRenormalizedWeakSolution q T' f ω := by
  intro T' hT' hT'T₀ q hq hfq
  have hsub : Ioo 0 T' ⊆ timeInterval T₀ :=
    Ioo_subset_Icc_self.trans (Icc_subset_timeInterval hT'T₀)
  refine renormalized_q_of_eLpNorm_eq (hren T' hT' hT'T₀) hq hfq
    (fun t ht => ((heq t (hsub ht)).memLp_iff _).2 hfq)
    (fun t ht => (heq t (hsub ht)).eLpNorm_eq 1)
    (fun t ht => (heq t (hsub ht)).eLpNorm_eq _)

/-- (iii), `q ∈ [1, 2)`: `lem:renorm-all-t` on every `[0, T₁)`, `T₁ < T₀`. -/
theorem continuousIntoLpOn_lt_two (hren : IsRenormalizedWeakSolutionUpTo 2 T₀ f ω)
    (hwc : IsWeakContL2On (timeInterval T₀) ω) :
    ∀ q : ℝ, 1 ≤ q → q < 2 → ContinuousIntoLpOn (ENNReal.ofReal q) (timeInterval T₀) ω :=
  fun q hq1 hq2 => continuousIntoLpOn_timeInterval_of_Ico fun T₁ hT₁ hT₁T₀ =>
    renormAllT_continuousIntoLpOn (hren T₁ hT₁ hT₁T₀)
      (hwc.mono (Icc_subset_timeInterval hT₁T₀)) q hq1 hq2

/-- The path `ω`, replaced by `0` outside `s` (so that every slice is in `L²`). -/
def cutPath (s : Set ℝ) (ω : ℝ → ℂ → ℝ) (t : ℝ) : ℂ → ℝ :=
  by classical exact if t ∈ s then ω t else 0

theorem cutPath_eventuallyEq {s : Set ℝ} (ω : ℝ → ℂ → ℝ) (t₀ : ℝ) :
    ∀ᶠ t in 𝓝[s] t₀, cutPath s ω t = ω t :=
  eventually_mem_nhdsWithin.mono fun t ht => by simp [cutPath, ht]

theorem memLp_cutPath {s : Set ℝ} {ω : ℝ → ℂ → ℝ} {p : ℝ≥0∞}
    (h : ∀ t ∈ s, MemLp (ω t) p volume) (t : ℝ) : MemLp (cutPath s ω t) p volume := by
  by_cases ht : t ∈ s
  · simpa [cutPath, ht] using h t ht
  · simp [cutPath, ht]

/-- (iii), `q = 2`: weak continuity, constant `L²` norm and `lem:RR`. -/
theorem continuousIntoLpOn_two {s : Set ℝ} (hwc : IsWeakContL2On s ω)
    (hnorm : ∀ t ∈ s, eLpNorm (ω t) 2 volume = eLpNorm f 2 volume) :
    ContinuousIntoLpOn 2 s ω := by
  refine ⟨hwc.memLp, fun t₀ ht₀ => ?_⟩
  have hev := cutPath_eventuallyEq (s := s) ω t₀
  have hw : ∀ ψ : ℂ → ℝ, MemLp ψ 2 volume →
      Tendsto (fun t => ∫ x, cutPath s ω t x * ψ x) (𝓝[s] t₀) (𝓝 (∫ x, ω t₀ x * ψ x)) := by
    intro ψ hψ
    refine ((hwc.continuousOn ψ hψ) t₀ ht₀).congr' ?_
    filter_upwards [hev] with t ht
    rw [ht]
  have hn : Tendsto (fun t => eLpNorm (cutPath s ω t) 2 volume) (𝓝[s] t₀)
      (𝓝 (eLpNorm (ω t₀) 2 volume)) := by
    rw [hnorm t₀ ht₀]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev, self_mem_nhdsWithin] with t ht hts
    rw [ht, hnorm t hts]
  refine (radonRiesz_filter (memLp_cutPath hwc.memLp) (hwc.memLp t₀ ht₀) hw hn).congr' ?_
  filter_upwards [hev] with t ht
  rw [ht]

/-- (iii), `q ∈ (2, r)` with `f ∈ L^r` (R8): interpolation between continuity in `L²` and the
uniform bound `‖ω(t)‖_{L^r} = ‖f‖_{L^r}`. -/
theorem continuousIntoLpOn_of_interp {s : Set ℝ} (hc2 : ContinuousIntoLpOn 2 s ω)
    {q r : ℝ} (hq : 2 < q) (hqr : q < r) (hfr : MemLp f (ENNReal.ofReal r) volume)
    (hmem : ∀ t ∈ s, MemLp (ω t) (ENNReal.ofReal q) volume)
    (hnorm : ∀ t ∈ s, eLpNorm (ω t) (ENNReal.ofReal r) volume = eLpNorm f (ENNReal.ofReal r) volume) :
    ContinuousIntoLpOn (ENNReal.ofReal q) s ω := by
  refine ⟨hmem, fun t₀ ht₀ => ?_⟩
  have hev := cutPath_eventuallyEq (s := s) ω t₀
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hmeas : ∀ t, AEStronglyMeasurable (cutPath s ω t - ω t₀) volume := fun t =>
    (memLp_cutPath hc2.1 t).aestronglyMeasurable.sub (hc2.1 t₀ ht₀).aestronglyMeasurable
  have h2q : (2 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_ofNat 2]; exact ENNReal.ofReal_le_ofReal hq.le
  have hqr' : ENNReal.ofReal q < ENNReal.ofReal r :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hqr
  have hC : eLpNorm f (ENNReal.ofReal r) volume + eLpNorm f (ENNReal.ofReal r) volume ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hfr.eLpNorm_ne_top, hfr.eLpNorm_ne_top⟩
  have hbound : ∀ᶠ t in 𝓝[s] t₀, eLpNorm (cutPath s ω t - ω t₀) (ENNReal.ofReal r) volume ≤
      eLpNorm f (ENNReal.ofReal r) volume + eLpNorm f (ENNReal.ofReal r) volume := by
    filter_upwards [hev, self_mem_nhdsWithin] with t ht hts
    rw [ht]
    refine (eLpNorm_sub_le (hc2.1 t hts).aestronglyMeasurable
      (hc2.1 t₀ ht₀).aestronglyMeasurable hr1).trans ?_
    rw [hnorm t hts, hnorm t₀ ht₀]
  have hlim : Tendsto (fun t => eLpNorm (cutPath s ω t - ω t₀) 2 volume) (𝓝[s] t₀) (𝓝 0) := by
    refine (hc2.2 t₀ ht₀).congr' ?_
    filter_upwards [hev] with t ht
    rw [ht]
  refine (LpInterp.tendsto_eLpNorm_of_interp hmeas (by norm_num) h2q hqr' hC hbound hlim).congr' ?_
  filter_upwards [hev] with t ht
  rw [ht]

end NonUniqueEuler.Compact.CriterionAux
