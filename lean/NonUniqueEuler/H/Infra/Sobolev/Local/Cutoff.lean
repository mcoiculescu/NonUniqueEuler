import Mathlib.Geometry.Manifold.PartitionOfUnity
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `P/Infra/Sobolev/Local`: smooth cutoffs and locality of derivatives

* `LocalAux.exists_cutoff`: for a compact `K` inside an open `V ⊆ ℂ`, a test function `ζ`
  supported in `V`, with `‖ζ‖ ≤ 1`, equal to `1` on an open neighbourhood `W` of `K`
  (from Mathlib's `exists_contMDiffMap_one_nhds_of_subset_interior` and
  `exists_compact_between`).
* `LocalAux.iterDirDeriv_eqOn`: classical derivatives are local: two functions that agree on an
  open set have the same iterated directional derivatives there.
* `LocalAux.isTestFn_mul`: a smooth function times a test function supported in `V` is a test
  function supported in `V`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold

namespace NonUniqueEuler.Sob.LocalAux

/-- A smooth cutoff equal to `1` near the compact set `K ⊆ V` and supported in `V`. -/
theorem exists_cutoff {K V : Set ℂ} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ ζ : ℂ → ℂ, IsTestFn V ζ ∧ (∀ x, ‖ζ x‖ ≤ 1) ∧
      ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ ∀ x ∈ W, ζ x = 1 := by
  obtain ⟨L, hL, hKL, hLV⟩ := exists_compact_between hK hV hKV
  obtain ⟨f, h1, h0, hrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, ℂ) (n := ⊤) hK.isClosed hKL
  obtain ⟨W, hW, hKW, hfW⟩ := eventually_nhdsSet_iff_exists.1 h1
  have hfs : ContDiff ℝ ∞ (f : ℂ → ℝ) := contMDiff_iff_contDiff.1 f.contMDiff
  have hsupp : Function.support (f : ℂ → ℝ) ⊆ L := fun x hx => by
    by_contra h
    exact hx (h0 x h)
  have hts : tsupport (f : ℂ → ℝ) ⊆ L := closure_minimal hsupp hL.isClosed
  refine ⟨fun x => ((f x : ℝ) : ℂ), ⟨?_, ?_, ?_⟩, ?_, W, hW, hKW, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp hfs
  · exact (HasCompactSupport.intro hL h0).comp_left Complex.ofReal_zero
  · exact (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero _).trans
      (hts.trans hLV)
  · intro x
    have := hrange x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [this.1], this.2⟩
  · intro x hx
    simp [hfW x hx]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Locality of classical derivatives: if `F = G` on the open set `W`, then all iterated
directional derivatives agree on `W`. -/
theorem iterDirDeriv_eqOn {F G : E → ℂ} {W : Set E} (hW : IsOpen W) (h : EqOn F G W)
    (vs : List E) : EqOn (iterDirDeriv vs F) (iterDirDeriv vs G) W := by
  induction vs with
  | nil => simpa using h
  | cons v vs ih =>
    intro x hx
    simp only [iterDirDeriv_cons, dirDeriv]
    have hev : iterDirDeriv vs F =ᶠ[𝓝 x] iterDirDeriv vs G :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hx) ih
    rw [hev.fderiv_eq]

/-- A smooth function times a test function supported in `V` is a test function supported
in `V`. -/
theorem isTestFn_mul {V : Set E} {χ φ : E → ℂ} (hχ : ContDiff ℝ ∞ χ) (hφ : IsTestFn V φ) :
    IsTestFn V (fun x => χ x * φ x) :=
  ⟨hχ.mul hφ.smooth, hφ.compact.mul_left, tsupport_mul_subset_right.trans hφ.subset⟩

end NonUniqueEuler.Sob.LocalAux
