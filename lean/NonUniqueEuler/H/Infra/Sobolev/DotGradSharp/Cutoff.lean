import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Geometry.Manifold.PartitionOfUnity
import NonUniqueEuler.Defs.Infra.Sobolev
import NonUniqueEuler.I.Infra.Sobolev.Smooth

/-!
# Helper for `P/Infra/Sobolev/DotGradSharp`: the cutoff `h̃ = ζ h` (step 1 of `04_ring.tex:1558`)

* `exists_cutoff_compact`: for a compact `K` inside an open `V`, a smooth compactly supported
  `ζ : ℂ → ℝ` with `tsupport ζ ⊆ V` and `ζ = 1` on an open `W ⊇ K`;
* `contDiff_cutoff_mul`: `ζ χ` is globally `C^k` when `χ` is `C^k` on `V ⊇ tsupport ζ`;
* `memCk_univ_of_contDiff`: a compactly supported `C^k` function lies in `C^k(ℝ²)`;
* `partialD_eqOn`: classical derivatives only depend on the function on an open set;
* `partialD_clm_comp`: `∂^β (L ∘ f) = L ∘ ∂^β f` for a continuous `ℝ`-linear `L` (used for
  `Re` and `Im`).

(`contDiff_cutoff_mul` and `partialD_eqOn` follow the helpers of the same names in
`H/Infra/Sobolev/Leibniz/Cutoff.lean`.)
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology Manifold

namespace NonUniqueEuler.Sob.DotGradSharpAux

/-- A smooth compactly supported cutoff equal to `1` near the compact set `K` and supported in
the open `V ⊇ K`. -/
theorem exists_cutoff_compact {K V : Set ℂ} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ ζ : ℂ → ℝ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ V ∧
      ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ EqOn ζ 1 W := by
  obtain ⟨U, hUo, hKU, hUV, hUc⟩ := exists_open_between_and_isCompact_closure hK hV hKV
  have hd : K ⊆ interior (closure U) := hKU.trans (interior_maximal subset_closure hUo)
  obtain ⟨f, h1, h0, -⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, ℂ) (n := ⊤) hK.isClosed hd
  have hs : tsupport f ⊆ closure U := by
    have hs : Function.support f ⊆ closure U := fun x hx => by
      by_contra h
      exact hx (h0 x h)
    exact closure_minimal hs isClosed_closure
  refine ⟨f, f.contMDiff.contDiff, hUc.of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans hUV, ?_⟩
  obtain ⟨W, hWo, hKW, hW⟩ := mem_nhdsSet_iff_exists.1 h1
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

/-- A compactly supported `C^k` function lies in `C^k(ℝ²)` (its derivatives are bounded). -/
theorem memCk_univ_of_contDiff {k : ℕ} {f : ℂ → ℂ} (hf : ContDiff ℝ k f)
    (hc : HasCompactSupport f) : MemCk k univ f := by
  refine ⟨⟨univ, isOpen_univ, subset_rfl, hf.contDiffOn⟩, ?_⟩
  have hb : ∀ q : ℕ, ∃ C : ℝ, q ≤ k → ∀ x ∈ (univ : Set ℂ),
      ‖iteratedFDeriv ℝ q f x‖ ≤ C := by
    intro q
    by_cases hq : q ≤ k
    · obtain ⟨C, hC⟩ := (hf.continuous_iteratedFDeriv (by exact_mod_cast hq)).bounded_above_of_compact_support
        (hc.iteratedFDeriv q)
      exact ⟨C, fun _ x _ => hC x⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose M hM using hb
  exact normCkE_ne_top_of_bound M fun q hq => hM q hq

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

/-- `∂^β (L ∘ f) = L (∂^β f)` for a continuous `ℝ`-linear map `L` and `f ∈ C^{|β|}`. -/
theorem partialD_clm_comp {n : ℕ} {f : ℂ → ℂ} (hf : ContDiff ℝ n f) (L : ℂ →L[ℝ] ℂ)
    {β : ℕ × ℕ} (hβ : β.1 + β.2 ≤ n) (x : ℂ) :
    partialD β (fun y => L (f y)) x = L (partialD β f x) := by
  have hfx : ContDiffAt ℝ (β.1 + β.2) f x :=
    (hf.of_le (by exact_mod_cast hβ)).contDiffAt
  have hLfx : ContDiffAt ℝ (β.1 + β.2) (fun y => L (f y)) x :=
    (L.contDiff.comp (hf.of_le (by exact_mod_cast hβ))).contDiffAt
  rw [partialD_eq_iteratedFDeriv hLfx, partialD_eq_iteratedFDeriv hfx]
  have h := L.iteratedFDeriv_comp_left hfx (i := β.1 + β.2) le_rfl
  have h' : iteratedFDeriv ℝ (β.1 + β.2) (fun y => L (f y)) x =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ (β.1 + β.2) f x) := h
  rw [h']
  rfl

end NonUniqueEuler.Sob.DotGradSharpAux
