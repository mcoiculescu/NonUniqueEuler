import NonUniqueEuler.Defs.Sec2.Spaces
import NonUniqueEuler.Defs.Sec3.Paths
import NonUniqueEuler.I.Infra.WeakL2.Norm

/-!
# Proof: `lem:RR`, the Radon–Riesz property (exponent `2`)

Proof of `NonUniqueEuler/I/Sec3/RR.lean` (manuscript `lem:RR`, `03_compactness.tex:691-714`,
restructuring R8: `p = 2` only).

Pass to the classes `(hgs i).toLp (gs i)` in the Hilbert space `L²(ℂ)`. Weak convergence of
the classes is `WeakL2.weakTendsto_toLp_iff`; `‖toLp f‖ = (eLpNorm f 2).toReal`
(`Lp.norm_toLp`), so the norms converge; Radon–Riesz in Hilbert space
(`WeakL2.WeakTendsto.tendsto_of_tendsto_norm`, I-WEAKL2) gives strong convergence of the
classes, and `eLpNorm (gs i - g) 2 = edist (toLp (gs i)) (toLp g)` (`Lp.edist_toLp_toLp`).
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact

/-- **`lem:RR`** with `p = 2`, along an arbitrary filter: if `gᵢ, g ∈ L²`, `∫ gᵢ ψ → ∫ g ψ` for
every `ψ ∈ L²` and `‖gᵢ‖_{L²} → ‖g‖_{L²}`, then `gᵢ → g` in `L²`. -/
theorem radonRiesz_filter {ι : Type*} {l : Filter ι} {gs : ι → ℂ → ℝ} {g : ℂ → ℝ}
    (hgs : ∀ i, MemLp (gs i) 2 volume) (hg : MemLp g 2 volume)
    (hw : ∀ ψ : ℂ → ℝ, MemLp ψ 2 volume →
      Tendsto (fun i => ∫ x, gs i x * ψ x) l (𝓝 (∫ x, g x * ψ x)))
    (hn : Tendsto (fun i => eLpNorm (gs i) 2 volume) l (𝓝 (eLpNorm g 2 volume))) :
    Tendsto (fun i => eLpNorm (gs i - g) 2 volume) l (𝓝 0) := by
  have hweak : WeakL2.WeakTendsto (fun i => (hgs i).toLp (gs i)) l (hg.toLp g) :=
    (WeakL2.weakTendsto_toLp_iff hgs hg).2 hw
  have hnorm : Tendsto (fun i => ‖(hgs i).toLp (gs i)‖) l (𝓝 ‖hg.toLp g‖) := by
    simp only [Lp.norm_toLp]
    exact (ENNReal.tendsto_toReal hg.2.ne).comp hn
  have hstrong := hweak.tendsto_of_tendsto_norm hnorm
  have hed := (tendsto_iff_edist_tendsto_0 (α := Lp ℝ 2 (volume : Measure ℂ))).1 hstrong
  simpa only [Lp.edist_toLp_toLp] using hed

/-- **`lem:RR`** with `p = 2` (`03_compactness.tex:691-696`, R8): if real `gₙ ⇀ g` weakly in `L²`
and `‖gₙ‖_{L²} → ‖g‖_{L²}`, then `gₙ → g` in `L²`. -/
theorem radonRiesz {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} (hw : Prelim.WeakTendstoLp 2 gs g)
    (hn : Tendsto (fun n => eLpNorm (gs n) 2 volume) atTop (𝓝 (eLpNorm g 2 volume))) :
    Tendsto (fun n => eLpNorm (gs n - g) 2 volume) atTop (𝓝 0) := by
  obtain ⟨hgs, hg, hψ⟩ := Weak.weakTendstoLp_two_iff.1 hw
  exact radonRiesz_filter hgs hg hψ hn

end NonUniqueEuler.Compact
