import NonUniqueEuler.H.Sec3.Stable.EveryTime
import NonUniqueEuler.I.Sec3.Stable.RenormLimit

/-!
# Proof: `prop:stable`, stability of renormalized solutions under strong convergence of data

Proof of `I/Sec3/Stable.lean` (manuscript `03_compactness.tex:716-827`).

Structure (following the manuscript proof):
1. Bounded renormalizations converge strongly (`03_compactness.tex:739-789`):
   `StableAux.stable_bddRenorm` (`H/Sec3/Stable/BddRenorm.lean`), from the weak limits of
   `stable_weakLimit` (`I/Sec3/Stable/WeakLimit.lean`) and `lem:transport`(i), (iii).
2. Strong convergence in space–time (`03_compactness.tex:791-800`):
   `StableAux.stable_tendsto_slab` (`H/Sec3/Stable/SpaceTime.lean`). Deviation: a
   sub-subsequence argument replaces the diagonal subsequence, so the whole sequence converges.
3. The limit is renormalized (`03_compactness.tex:802-815`): `stable_renormalized`
   (`I/Sec3/Stable/RenormLimit.lean`).
4. Convergence at every time (`03_compactness.tex:817-827`): `StableAux.stable_tendsto_time`
   (`H/Sec3/Stable/EveryTime.lean`).

Since steps 2-4 hold for the whole sequence, the subsequence of the statement is `φ = id`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact

open Weak

/-- **`prop:stable`** (`03_compactness.tex:716-723`): in the setting of `prop:compact`
(`IsCompactSeq T M gs g ωs` and its conclusions `IsCompactLimit T g ωs ω`), if moreover
`gₙ → g` in `L¹ ∩ L²` and every `ωₙ` is renormalized, then `ω` is renormalized and, along a
further subsequence `φ`, `ω_{φ n}(t) → ω(t)` in `L^q` for every `t ∈ [0, T)` and `q ∈ [1, 2]`. -/
theorem stable {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}
    {ω : ℝ → ℂ → ℝ} (hseq : IsCompactSeq T M gs g ωs) (hlim : IsCompactLimit T g ωs ω)
    (hstrong : Tendsto (fun n => normL1LpE 2 (gs n - g)) atTop (𝓝 0))
    (hren : ∀ n, IsRenormalizedWeakSolution 2 T (gs n) (ωs n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ IsRenormalizedWeakSolution 2 T g ω ∧
      ∀ t ∈ Ico 0 T, ∀ q : ℝ, 1 ≤ q → q ≤ 2 →
        Tendsto (fun n => eLpNorm (ωs (φ n) t - ω t) (ENNReal.ofReal q) volume) atTop (𝓝 0) := by
  have hL1 := StableAux.stable_tendsto_slab hseq hlim hstrong hren
  have hω := stable_renormalized hseq hlim hstrong hren hL1
  exact ⟨id, strictMono_id, hω, StableAux.stable_tendsto_time hseq hlim hstrong hren hω⟩

end NonUniqueEuler.Compact
