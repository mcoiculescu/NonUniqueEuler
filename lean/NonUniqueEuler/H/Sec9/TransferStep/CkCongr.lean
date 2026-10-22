import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Infra.CkNorm.Basic

/-!
# Helper for `lem:transfer-step`: `C^k(N')` norms of fields that agree on `N'`

Helper of `P/Sec9/TransferStep.lean` (`09_relay.tex:185-225`). The norm `normCk k U h` uses the
global derivatives of `h` at the points of `U`, so it depends on the germ of `h` near `U`. The
identities that the proof of `lem:transfer-step` combines (`inner_field_eq`,
`transfer_outer_sum_eq`) hold on `N'` only. Since `N' ⊂ closure (interior N')` and the derivatives of
order `≤ k` of a function that is `C^k` near `N'` are continuous there, two such functions that
agree on `N'` have the same derivatives of order `≤ k` on `N'`, hence the same `C^k(N')` norm.

* `iteratedFDeriv_eq_of_eqOn_closure`, `normCkE_congr_of_eqOn_closure`,
  `normCk_congr_of_eqOn_closure`: the congruence;
* `annN'_subset_closure_interior`: `N' ⊂ closure (interior N')`;
* `memCk_finsetSum`: the triangle inequality for a finite sum of `C^k(U)` fields.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.Relay.TransferStepAux

open RingData

/-- Two functions that are `C^k` near `U` and agree on `U ⊂ closure (interior U)` have the same
derivatives of order `q ≤ k` at every point of `U`. -/
theorem iteratedFDeriv_eq_of_eqOn_closure {k : ℕ} {U : Set ℂ} {f g : ℂ → ℂ}
    (hU : U ⊆ closure (interior U)) (hf : IsCkNear k U f) (hg : IsCkNear k U g)
    (hfg : EqOn f g U) {q : ℕ} (hq : q ≤ k) :
    EqOn (iteratedFDeriv ℝ q f) (iteratedFDeriv ℝ q g) U := by
  obtain ⟨Vf, hVf, hUVf, hcf⟩ := hf
  obtain ⟨Vg, hVg, hUVg, hcg⟩ := hg
  have hW : IsOpen (Vf ∩ Vg) := hVf.inter hVg
  have hUW : U ⊆ Vf ∩ Vg := subset_inter hUVf hUVg
  have hqk : ((q : ℕ) : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hq
  have hcont : ∀ {h : ℂ → ℂ}, ContDiffOn ℝ k h (Vf ∩ Vg) →
      ContinuousOn (iteratedFDeriv ℝ q h) (Vf ∩ Vg) := by
    intro h hh
    exact (hh.continuousOn_iteratedFDerivWithin hqk hW.uniqueDiffOn).congr
      fun x hx => (iteratedFDerivWithin_of_isOpen q hW hx).symm
  have hcf' := hcont (hcf.mono inter_subset_left)
  have hcg' := hcont (hcg.mono inter_subset_right)
  have hint : EqOn (iteratedFDeriv ℝ q f) (iteratedFDeriv ℝ q g) (interior U) := by
    intro z hz
    have h : f =ᶠ[𝓝 z] g :=
      Filter.eventually_of_mem (mem_interior_iff_mem_nhds.mp hz) fun y hy => hfg hy
    exact (h.iteratedFDeriv ℝ q).eq_of_nhds
  exact hint.of_subset_closure (hcf'.mono hUW) (hcg'.mono hUW) interior_subset hU

/-- The `C^k(U)` norms (in `[0, ∞]`) of two functions that are `C^k` near `U` and agree on
`U ⊂ closure (interior U)` are equal. -/
theorem normCkE_congr_of_eqOn_closure {k : ℕ} {U : Set ℂ} {f g : ℂ → ℂ}
    (hU : U ⊆ closure (interior U)) (hf : IsCkNear k U f) (hg : IsCkNear k U g)
    (hfg : EqOn f g U) : normCkE k U f = normCkE k U g := by
  unfold normCkE supIterDerivE
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqk : q ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  refine iSup_congr fun x => iSup_congr fun hx => ?_
  rw [iteratedFDeriv_eq_of_eqOn_closure hU hf hg hfg hqk hx]

/-- The real `C^k(U)` norms of two functions that are `C^k` near `U` and agree on
`U ⊂ closure (interior U)` are equal. -/
theorem normCk_congr_of_eqOn_closure {k : ℕ} {U : Set ℂ} {f g : ℂ → ℂ}
    (hU : U ⊆ closure (interior U)) (hf : IsCkNear k U f) (hg : IsCkNear k U g)
    (hfg : EqOn f g U) : normCk k U f = normCk k U g := by
  unfold normCk
  rw [normCkE_congr_of_eqOn_closure hU hf hg hfg]

/-- `N' = {a/4 ≤ |y| ≤ 3}` is contained in the closure of its interior. -/
theorem annN'_subset_closure_interior : annN' ⊆ closure (interior annN') := by
  intro x hx
  have ha := Relay.zero_lt_a
  have ha1 := Relay.a_lt_one
  have hx1 : a / 4 ≤ ‖x‖ := hx.1
  have hx2 : ‖x‖ ≤ 3 := hx.2
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (by positivity) hx1
  -- the open annulus is inside `interior N'`
  have hopen : {y : ℂ | a / 4 < ‖y‖ ∧ ‖y‖ < 3} ⊆ interior annN' := by
    refine interior_maximal (fun y hy => ⟨hy.1.le, hy.2.le⟩) ?_
    exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  -- the segment `c ↦ c x`
  set lo : ℝ := a / 4 / ‖x‖
  set hi : ℝ := 3 / ‖x‖
  have hlo : 0 < lo := by positivity
  have hlohi : lo < hi := div_lt_div_of_pos_right (by linarith) hxpos
  have h1 : (1 : ℝ) ∈ closure (Ioo lo hi) := by
    rw [closure_Ioo hlohi.ne]
    exact ⟨(div_le_one hxpos).mpr hx1, (one_le_div hxpos).mpr hx2⟩
  have hφ : Continuous fun c : ℝ => (c : ℂ) * x := Complex.continuous_ofReal.mul continuous_const
  have himg : (fun c : ℝ => (c : ℂ) * x) '' Ioo lo hi ⊆ interior annN' := by
    rintro _ ⟨c, hc, rfl⟩
    apply hopen
    have hc0 : 0 < c := hlo.trans hc.1
    have hn : ‖(c : ℂ) * x‖ = c * ‖x‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    show a / 4 < ‖(c : ℂ) * x‖ ∧ ‖(c : ℂ) * x‖ < 3
    rw [hn]
    constructor
    · have := hc.1
      rwa [div_lt_iff₀ hxpos] at this
    · have := hc.2
      rwa [lt_div_iff₀ hxpos] at this
  have hmem := image_closure_subset_closure_image hφ ⟨1, h1, rfl⟩
  simp only [Complex.ofReal_one, one_mul] at hmem
  exact closure_mono himg hmem

/-- The triangle inequality for a finite sum of `C^k(U)` fields (`U` nonempty). -/
theorem memCk_finsetSum {k : ℕ} {U : Set ℂ} (hU : U.Nonempty) {ι : Type*} (s : Finset ι)
    (f : ι → ℂ → ℂ) (hf : ∀ i ∈ s, MemCk k U (f i)) :
    MemCk k U (fun y => ∑ i ∈ s, f i y) ∧
      normCk k U (fun y => ∑ i ∈ s, f i y) ≤ ∑ i ∈ s, normCk k U (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := memCk_const_and_normCk k hU (0 : ℂ)
    simp only [Finset.sum_empty]
    refine ⟨h.1, ?_⟩
    rw [h.2, norm_zero]
  | insert a s ha ih =>
    have ih' := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a s)
    have hfun : (fun y => ∑ i ∈ insert a s, f i y) = f a + fun y => ∑ i ∈ s, f i y := by
      funext y
      rw [Finset.sum_insert ha, Pi.add_apply]
    rw [hfun, Finset.sum_insert ha]
    have hadd := hfa.add ih'.1
    exact ⟨hadd.1, hadd.2.trans (by linarith [ih'.2])⟩

/-- `N'` is nonempty. -/
theorem annN'_nonempty : annN'.Nonempty := by
  have ha := Relay.zero_lt_a
  have ha1 := Relay.a_lt_one
  refine ⟨(1 : ℂ), ?_⟩
  show a / 4 ≤ ‖(1 : ℂ)‖ ∧ ‖(1 : ℂ)‖ ≤ 3
  rw [norm_one]
  constructor <;> linarith

end NonUniqueEuler.Relay.TransferStepAux
