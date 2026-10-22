import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Geometry.Manifold.PartitionOfUnity
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `P/Infra/Sobolev/Leibniz`: cutoffs, germs and `C^k(K)` under linear maps

* `exists_cutoff`: for a closed `K` inside an open `V`, a smooth `ζ : ℂ → ℝ` with
  `tsupport ζ ⊆ V` and `ζ = 1` on an open `W ⊇ K` (smooth Urysohn,
  `exists_contMDiffMap_one_nhds_of_subset_interior`).
* `contDiff_cutoff_mul`: `ζ χ` is globally `C^k` when `χ` is `C^k` on `V`.
* `iterDirDeriv_eqOn`: iterated directional derivatives only depend on the function on an
  open set.
* `MemCk.clm_comp`: `C^k(K)` is stable under a continuous linear map of norm `≤ 1`
  (used for `Re` and `Im`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology Manifold

namespace NonUniqueEuler.Sob.LeibnizAux

/-- A smooth cutoff equal to `1` near the closed set `K` and supported in the open `V ⊇ K`. -/
theorem exists_cutoff {K V : Set ℂ} (hK : IsClosed K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ ζ : ℂ → ℝ, ContDiff ℝ ∞ ζ ∧ tsupport ζ ⊆ V ∧
      ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ EqOn ζ 1 W := by
  obtain ⟨U, hUo, hKU, hUV⟩ := normal_exists_closure_subset hK hV hKV
  have hd : K ⊆ interior (closure U) := hKU.trans (interior_maximal subset_closure hUo)
  obtain ⟨f, h1, h0, -⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, ℂ) (n := ⊤) hK hd
  refine ⟨f, f.contMDiff.contDiff, ?_, ?_⟩
  · have hs : Function.support f ⊆ closure U := fun x hx => by
      by_contra h
      exact hx (h0 x h)
    exact (closure_minimal hs isClosed_closure).trans hUV
  · obtain ⟨W, hWo, hKW, hW⟩ := mem_nhdsSet_iff_exists.1 h1
    exact ⟨W, hWo, hKW, fun x hx => hW hx⟩

/-- `ζ χ` is globally `C^k` if `χ` is `C^k` on the open set `V ⊇ tsupport ζ`. -/
theorem contDiff_cutoff_mul {k : ℕ} {V : Set ℂ} (hV : IsOpen V) {ζ : ℂ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζV : tsupport ζ ⊆ V) {χ : ℂ → ℂ} (hχ : ContDiffOn ℝ k χ V) :
    ContDiff ℝ k (fun x => (ζ x : ℂ) * χ x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ V
  · have h1 : ContDiffAt ℝ k (fun x => (ζ x : ℂ)) x :=
      (Complex.ofRealCLM.contDiff.comp (hζ.of_le (by exact_mod_cast le_top))).contDiffAt
    exact h1.mul (hχ.contDiffAt (hV.mem_nhds hx))
  · have hxs : x ∉ tsupport ζ := fun h => hx (hζV h)
    have hev : ζ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hxs
    refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    simp [hy]

/-- Iterated directional derivatives only depend on the function on an open set. -/
theorem iterDirDeriv_eqOn {W : Set ℂ} (hW : IsOpen W) {f g : ℂ → ℂ} (hfg : EqOn f g W)
    (vs : List ℂ) : EqOn (iterDirDeriv vs f) (iterDirDeriv vs g) W := by
  induction vs with
  | nil => simpa using hfg
  | cons v vs ih =>
    intro x hx
    simp only [iterDirDeriv_cons, dirDeriv]
    rw [Filter.EventuallyEq.fderiv_eq (ih.eventuallyEq_of_mem (hW.mem_nhds hx))]

theorem partialD_eqOn {W : Set ℂ} (hW : IsOpen W) {f g : ℂ → ℂ} (hfg : EqOn f g W)
    (β : ℕ × ℕ) : EqOn (partialD β f) (partialD β g) W :=
  iterDirDeriv_eqOn hW hfg _

/-- `C^k(K)` is stable under a continuous linear map of norm `≤ 1`. -/
theorem MemCk.clm_comp {k : ℕ} {K : Set ℂ} {h : ℂ → ℂ} (hh : MemCk k K h) (L : ℂ →L[ℝ] ℂ)
    (hL : ‖L‖ ≤ 1) :
    MemCk k K (fun x => L (h x)) ∧ normCk k K (fun x => L (h x)) ≤ normCk k K h := by
  obtain ⟨V, hVo, hKV, hcd⟩ := hh.near
  have hpt : ∀ q ≤ k, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ q (fun x => L (h x)) x‖ ≤ ‖iteratedFDeriv ℝ q h x‖ := by
    intro q hq x hx
    have hxV := hKV hx
    have hat : ContDiffAt ℝ k h x := hcd.contDiffAt (hVo.mem_nhds hxV)
    have := L.norm_iteratedFDeriv_comp_left (n := q) hat (by exact_mod_cast hq)
    calc ‖iteratedFDeriv ℝ q (fun x => L (h x)) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ q h x‖ := this
      _ ≤ 1 * ‖iteratedFDeriv ℝ q h x‖ := by gcongr
      _ = _ := one_mul _
  have hle : normCkE k K (fun x => L (h x)) ≤ normCkE k K h := by
    refine Finset.sum_le_sum fun q hq => ?_
    have hq' : q ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
    refine iSup₂_le fun x hx => ?_
    refine le_trans ?_ (enorm_iteratedFDeriv_le_supIterDerivE h hx)
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hpt q hq' x hx)
  refine ⟨⟨⟨V, hVo, hKV, L.contDiff.comp_contDiffOn hcd⟩, ne_top_of_le_ne_top hh.finite hle⟩, ?_⟩
  exact ENNReal.toReal_mono hh.finite hle

end NonUniqueEuler.Sob.LeibnizAux
