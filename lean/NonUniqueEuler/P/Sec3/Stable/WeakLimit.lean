import NonUniqueEuler.Defs.Sec3.Compact
import NonUniqueEuler.Defs.Sec3.Transport
import NonUniqueEuler.H.Sec3.Stable.WeakLimit.Limit
import NonUniqueEuler.H.Sec3.Stable.WeakLimit.Flux

/-!
# Proof of `I/Sec3/Stable/WeakLimit.lean`: `prop:stable`, step 1a

Manuscript: proof of `prop:stable`, second and third paragraphs (`03_compactness.tex:739-785`).

Helpers (`H/Sec3/Stable/WeakLimit/*`, namespace `NonUniqueEuler.Compact.WeakLimitAux`):
* `Basic`: test functions, `Lip₀` (`isLipO_sq`: `β² ∈ Lip₀`), Tonelli on `I × Ω`;
* `Weak`: weak `L²` extraction with a bounded measurable limit (`exists_subseq_weak_bdd`),
  passage of `L^q` and `∫_S |·|` bounds to weak limits;
* `Bounds`: `γ(ωₙ)` bounded in `L²((0,T) × ℝ²)` (R5), `exists_weak_limit` (extraction with the
  slice bound `‖G(t)‖_{L¹} ≤ C M`), `memLinfLp_of_slice`;
* `Flux`: `integrable_smul_velocityField` (`∫|ū(t)||v(t)| ≤ ‖ω(t)‖₁(B + LM/(2π))`, Tonelli,
  `|K|` even, `lem:BS-basic`(b));
* `TE`, `Limit`: `solvesTE_of_weak` (passage to the limit in `(te)`).

The proof extracts twice (first for `β(ωₙ)`, then for `β(ωₙ)²` along the first subsequence),
with `γ = β` (`|β(s)| ≤ L|s|`, `|β| ≤ B`) and `γ = β²` (`|β(s)²| ≤ BL|s|`, `|β²| ≤ B²`).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact

open Weak

/-- **`prop:stable`, step 1a** (`03_compactness.tex:739-785`): for bounded `β ∈ Lip₀`, along a
subsequence, `β(ωₙ)` and `β(ωₙ)²` converge weakly in `L²((0,T) × ℝ²)` to `ū`, `z̄`, which are
bounded (`|ū| ≤ B`), lie in `L^∞(0,T; L¹ ∩ L²)`, have integrable fluxes `ū v`, `z̄ v`, and satisfy
(te) on `[0,T)` with field `v = K ∗ ω` and data `β(g)`, `β(g)²`. -/
theorem stable_weakLimit {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}
    {ω : ℝ → ℂ → ℝ} (hseq : IsCompactSeq T M gs g ωs) (hlim : IsCompactLimit T g ωs ω)
    (hstrong : Tendsto (fun n => normL1LpE 2 (gs n - g)) atTop (𝓝 0))
    (hren : ∀ n, IsRenormalizedWeakSolution 2 T (gs n) (ωs n))
    {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β) {B : ℝ} (hB : ∀ s, |β s| ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ub zb : ℝ → ℂ → ℝ,
      (∀ Φ : ℝ × ℂ → ℝ, MemLp Φ 2 (volume.restrict (slab T)) →
        Tendsto (fun n => ∫ p in slab T, β (ωs (φ n) p.1 p.2) * Φ p) atTop
          (𝓝 (∫ p in slab T, ub p.1 p.2 * Φ p))) ∧
      (∀ Φ : ℝ × ℂ → ℝ, MemLp Φ 2 (volume.restrict (slab T)) →
        Tendsto (fun n => ∫ p in slab T, β (ωs (φ n) p.1 p.2) ^ 2 * Φ p) atTop
          (𝓝 (∫ p in slab T, zb p.1 p.2 * Φ p))) ∧
      (∀ᵐ p ∂(volume.restrict (slab T)), |ub p.1 p.2| ≤ B) ∧
      Prelim.MemLinfLp (Ioo 0 T) univ 1 ub ∧ Prelim.MemLinfLp (Ioo 0 T) univ 2 ub ∧
      Prelim.MemLinfLp (Ioo 0 T) univ 1 zb ∧ Prelim.MemLinfLp (Ioo 0 T) univ 2 zb ∧
      Integrable (fun p : ℝ × ℂ => ub p.1 p.2 • velocityField ω p.1 p.2)
        (volume.restrict (slab T)) ∧
      Integrable (fun p : ℝ × ℂ => zb p.1 p.2 • velocityField ω p.1 p.2)
        (volume.restrict (slab T)) ∧
      SolvesTE 0 T ub (velocityField ω) (fun x => β (g x)) ∧
      SolvesTE 0 T zb (velocityField ω) (fun x => β (g x) ^ 2) := by
  obtain ⟨L, hL0, hLs, -⟩ := WeakLimitAux.isLipO_exists_abs_le hβ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hβc : Continuous β := WeakLimitAux.isLipO_continuous hβ
  -- the bounded renormalization `β²`
  have hβ2 : Equimeas.IsLipO (fun s => β s ^ 2) := WeakLimitAux.isLipO_sq hβ hB
  have hβ2c : Continuous (fun s => β s ^ 2) := hβc.pow 2
  have hβ2C : ∀ s, |β s ^ 2| ≤ B * L * |s| := fun s => by
    rw [abs_pow, sq]
    calc |β s| * |β s| ≤ B * (L * |s|) := mul_le_mul (hB s) (hLs s) (abs_nonneg _) hB0
      _ = B * L * |s| := by ring
  have hβ2B : ∀ s, |β s ^ 2| ≤ B ^ 2 := fun s => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hB s) 2
  -- the two extractions
  obtain ⟨φ₁, hφ₁, G, hGm, hGB, hG2, hwG, hGC⟩ :=
    WeakLimitAux.exists_weak_limit hseq hβc hL0 hB0 hLs hB
  obtain ⟨φ₂, hφ₂, Z, hZm, hZB, hZ2, hwZ, hZC⟩ :=
    WeakLimitAux.exists_weak_limit (hseq.subseq hφ₁) hβ2c (mul_nonneg hB0 hL0) (sq_nonneg B)
      hβ2C hβ2B
  have hφ : StrictMono (φ₁ ∘ φ₂) := hφ₁.comp hφ₂
  have hwG' : ∀ Φ : ℝ × ℂ → ℝ, MemLp Φ 2 (volume.restrict (slab T)) →
      Tendsto (fun n => ∫ p in slab T, β (ωs ((φ₁ ∘ φ₂) n) p.1 p.2) * Φ p) atTop
        (𝓝 (∫ p in slab T, G p * Φ p)) :=
    fun Φ hΦ => (hwG Φ hΦ).comp hφ₂.tendsto_atTop
  have hwZ' : ∀ Φ : ℝ × ℂ → ℝ, MemLp Φ 2 (volume.restrict (slab T)) →
      Tendsto (fun n => ∫ p in slab T, β (ωs ((φ₁ ∘ φ₂) n) p.1 p.2) ^ 2 * Φ p) atTop
        (𝓝 (∫ p in slab T, Z p * Φ p)) := hwZ
  -- the `L^∞(0,T; L¹ ∩ L²)` bounds
  have hGL := WeakLimitAux.memLinfLp_of_slice hGm hGB hGC
  have hZL := WeakLimitAux.memLinfLp_of_slice hZm hZB hZC
  have hGC' : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∫⁻ x, ‖G (t, x)‖ₑ ≤
      ENNReal.ofReal (max (L * M) 0) :=
    hGC.mono fun t ht => ht.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hZC' : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∫⁻ x, ‖Z (t, x)‖ₑ ≤
      ENNReal.ofReal (max (B * L * M) 0) :=
    hZC.mono fun t ht => ht.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- the subsequence data
  have hseqφ := hseq.subseq hφ
  have hlimφ := hlim.subseq hφ
  have hstrongφ : Tendsto (fun n => normL1LpE 2 (gs ((φ₁ ∘ φ₂) n) - g)) atTop (𝓝 0) :=
    hstrong.comp hφ.tendsto_atTop
  refine ⟨φ₁ ∘ φ₂, hφ, fun t x => G (t, x), fun t x => Z (t, x), hwG', hwZ',
    Eventually.of_forall fun p => hGB _, hGL.1, hGL.2, hZL.1, hZL.2, ?_, ?_, ?_, ?_⟩
  · exact WeakLimitAux.integrable_smul_velocityField hlim.weakSolution.memX hGm hB0
      (le_max_right _ _) hGB hGC'
  · exact WeakLimitAux.integrable_smul_velocityField hlim.weakSolution.memX hZm (sq_nonneg B)
      (le_max_right _ _) hZB hZC'
  · exact WeakLimitAux.solvesTE_of_weak hseqφ hlimφ hstrongφ (fun n => hren _) hβ hB hG2 hwG'
  · exact WeakLimitAux.solvesTE_of_weak hseqφ hlimφ hstrongφ (fun n => hren _) hβ2 hβ2B hZ2
      hwZ'

end NonUniqueEuler.Compact
