import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Infra.Sobolev.EmbedLinf
import Mathlib.Analysis.Convolution

/-!
# Helper for `lem:bilinear`(4): continuity of `K_BS * v` (`05_single_ring.tex:240-243`, `:262-266`)

Helper of `P/Sec5/Bilinear.lean`. Item (4) applies `lem:embed`(E2) to `χ_B K_BS * v`, which needs
a pointwise (not only a.e.) bound, hence the continuity of `K_BS * v`. For `v ∈ H^2` vanishing
a.e. outside a compact set `K`, the continuous representative `v'` of (E2)
(`I/Infra/Sobolev/EmbedLinf.lean`: `Sob.Linf_le_H2`) vanishes on the open set `ℂ ∖ K`, so it is
continuous with compact support; `K_BS * v = K_BS * v'` (the integral sees only the a.e. class),
and the convolution of a continuous compactly supported function with the locally integrable
kernel is continuous (Mathlib `HasCompactSupport.continuous_convolution_left`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff Convolution

namespace NonUniqueEuler

namespace OneRing

namespace BilinearH

/-- The Biot–Savart kernel is locally integrable (`lem:BS-basic`(a)). -/
theorem locallyIntegrable_biotSavartKernel' : LocallyIntegrable biotSavartKernel volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨r, hr, hkr⟩ := hk.isBounded.subset_ball_lt 0 0
  exact (BS.integral_norm_biotSavartKernel_ball hr).1.mono_set hkr

/-- `K_BS * g` is continuous for a continuous compactly supported real `g`. -/
theorem continuous_velocity_of_continuous {g : ℂ → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) : Continuous (velocity g) := by
  rw [Conv.velocity_eq_convolution]
  have hc' : HasCompactSupport (fun y => (g y : ℂ)) := hc.comp_left Complex.ofReal_zero
  exact hc'.continuous_convolution_left _ (Complex.continuous_ofReal.comp hg)
    locallyIntegrable_biotSavartKernel'

/-- The velocity only depends on the a.e. class of the vorticity. -/
theorem velocity_congr_ae {g g' : ℂ → ℝ} (h : g =ᵐ[volume] g') : velocity g = velocity g' := by
  funext x
  unfold velocity
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

/-- For `v ∈ H^2` vanishing a.e. outside a compact set, the two real velocity fields
`K_BS * Re v`, `K_BS * Im v` are continuous. -/
theorem continuous_velocity_of_memH {v : ℂ → ℂ} (hv : Sob.MemH 2 v) {K : Set ℂ}
    (hK : IsCompact K) (hvK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → v x = 0) :
    Continuous (BS.velocityRe v) ∧ Continuous (BS.velocityIm v) := by
  obtain ⟨g, hgc, hvg, -, -⟩ := Sob.Linf_le_H2 hv
  have hopen : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hae : g =ᵐ[volume.restrict Kᶜ] (fun _ => (0 : ℂ)) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hopen.measurableSet]
    filter_upwards [hvg, hvK] with x hx1 hx2 hx3
    rw [← hx1]
    exact hx2 hx3
  have heq : EqOn g (fun _ => (0 : ℂ)) Kᶜ :=
    Measure.eqOn_open_of_ae_eq hae hopen hgc.continuousOn continuousOn_const
  have hzero : ∀ x, x ∉ K → g x = 0 := fun x hx => heq hx
  refine ⟨?_, ?_⟩
  · have h1 : BS.velocityRe v = velocity (fun y => (g y).re) := by
      unfold BS.velocityRe
      refine velocity_congr_ae ?_
      filter_upwards [hvg] with y hy
      rw [hy]
    rw [h1]
    exact continuous_velocity_of_continuous (Complex.continuous_re.comp hgc)
      (HasCompactSupport.intro hK fun x hx => by simp [hzero x hx])
  · have h1 : BS.velocityIm v = velocity (fun y => (g y).im) := by
      unfold BS.velocityIm
      refine velocity_congr_ae ?_
      filter_upwards [hvg] with y hy
      rw [hy]
    rw [h1]
    exact continuous_velocity_of_continuous (Complex.continuous_im.comp hgc)
      (HasCompactSupport.intro hK fun x hx => by simp [hzero x hx])

end BilinearH

end OneRing

end NonUniqueEuler
