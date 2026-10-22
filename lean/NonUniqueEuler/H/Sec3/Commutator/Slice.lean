import NonUniqueEuler.H.Sec3.Commutator.Basic
import NonUniqueEuler.I.Sec3.Commutator.SliceBound
import NonUniqueEuler.I.Sec3.Commutator.SliceSmooth
import NonUniqueEuler.I.Sec3.Commutator.SmoothApprox

/-!
# Helper for `P/Sec3/Commutator.lean`: the commutator lemma at a fixed time

At a fixed time `t` with `u(t) ∈ L²_loc`, `w(t) ∈ H¹_loc` and `div w(t) = 0`,
`C_ε[u,w](t) → 0` in `L¹(B_R)` as `ε → 0⁺` (`03_compactness.tex:440-461`, at fixed `t`).

Proof (the manuscript's density step, slice-wise): choose smooth divergence-free `g_n` with
`‖w(t) - g_n‖_{H¹(B_{R+1})} → 0` (`exists_smooth_divFree_approx`); by bilinearity
(`commEps_sub`) `C_ε[u,w] = C_ε[u,w-g_n] + C_ε[u,g_n]`; the first term is bounded uniformly in
`ε ∈ (0,1]` by `C ‖u(t)‖_{L²(B_{R+1})} ‖w(t) - g_n‖_{H¹(B_{R+1})}`
(`exists_lintegral_commEps_ball_le`, eq:comm-bound), and the second tends to `0`
(`tendsto_lintegral_commEps_ball_of_contDiff`).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Weak.CommutatorH

/-- The commutator lemma at a fixed time. -/
theorem tendsto_lintegral_commEps_ball_slice {ρ : ℂ → ℝ} (hρ : IsMollifier ρ)
    {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {t : ℝ}
    (hu : ∀ r : ℝ, 0 < r → MemLp (u t) 2 (volume.restrict (ball (0 : ℂ) r)))
    (hw : ∀ r : ℝ, 0 < r → Sob.MemHOn 1 (ball (0 : ℂ) r) (w t))
    (hdiv : Prelim.IsWeaklyDivFree (w t)) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => ∫⁻ x in ball (0 : ℂ) R, ‖commEps ρ ε u w t x‖ₑ) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, -, hC⟩ := exists_lintegral_commEps_ball_le hρ
  obtain ⟨g, hgs, hgdiv, hgH, hgt⟩ :=
    exists_smooth_divFree_approx hw hdiv (R := R + 1) (by linarith)
  have hul : LocallyIntegrable (u t) volume := locallyIntegrable_of_memLp_two hu
  have hwL2 : ∀ r : ℝ, 0 < r → MemLp (w t) 2 (volume.restrict (ball (0 : ℂ) r)) :=
    fun r hr => (hw r hr).memLp
  have huw : LocallyIntegrable (fun y => u t y • w t y) volume :=
    locallyIntegrable_smul_of_memLp_two hu hwL2
  have hgc : ∀ n, Continuous (g n) := fun n => (hgs n).continuous
  -- the two fields of the decomposition
  set W : ℕ → ℝ → ℂ → ℂ := fun n s y => w s y - g n y with hW
  set G : ℕ → ℝ → ℂ → ℂ := fun n _ => g n with hG
  have hug : ∀ n, LocallyIntegrable (fun y => u t y • g n y) volume := fun n =>
    locallyIntegrable_smul_of_continuous hul (hgc n)
  have huW : ∀ n, LocallyIntegrable (fun y => u t y • W n t y) volume := by
    intro n
    have : (fun y => u t y • W n t y) = (fun y => u t y • w t y) - (fun y => u t y • g n y) := by
      funext y
      simp [hW, smul_sub]
    rw [this]
    exact huw.sub (hug n)
  have hWm : ∀ n, AEStronglyMeasurable (W n t) volume := fun n =>
    (locallyIntegrable_of_memLp_two hwL2).aestronglyMeasurable.sub (hgc n).aestronglyMeasurable
  -- decomposition `C_ε[u,w] = C_ε[u,w - g_n] + C_ε[u,g_n]`
  have hdec : ∀ n, ∀ ε : ℝ, 0 < ε → ∀ x,
      commEps ρ ε u w t x = commEps ρ ε u (W n) t x + commEps ρ ε u (G n) t x := by
    intro n ε hε x
    have h := commEps_sub hρ hε (w₁ := w) (w₂ := W n) hul huw (huW n) x
    have hfun : (fun s y => w s y - W n s y) = G n := by
      funext s y
      simp [hW, hG]
    rw [hfun] at h
    rw [h]
    ring
  -- the bound for the rough part tends to `0` in `n`
  have hfin : ENNReal.ofReal C * eLpNorm (u t) 2 (volume.restrict (ball (0 : ℂ) (R + 1))) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hu (R + 1) (by linarith)).eLpNorm_ne_top
  have hA : Tendsto (fun n => ENNReal.ofReal C *
      eLpNorm (u t) 2 (volume.restrict (ball (0 : ℂ) (R + 1))) *
        ENNReal.ofReal (Sob.normHOn 1 (ball (0 : ℂ) (R + 1)) (W n t))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ENNReal.ofReal (Sob.normHOn 1 (ball (0 : ℂ) (R + 1)) (W n t)))
        atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal hgt
      rwa [ENNReal.ofReal_zero] at this
    have := ENNReal.Tendsto.const_mul h1 (Or.inr hfin)
    rwa [mul_zero] at this
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hA).2 (η / 2) hη2).exists
  have hsm := tendsto_lintegral_commEps_ball_of_contDiff hρ ((hgs n).of_le (by simp))
    (hgdiv n) hul hR (u := u) (t := t)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫⁻ x in ball (0 : ℂ) R, ‖commEps ρ ε u (fun _ => g n) t x‖ₑ < η / 2 :=
    (tendsto_order.1 hsm).2 (η / 2) hη2
  filter_upwards [hev, Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε hε1
  obtain ⟨hε0, hε1⟩ := hε1
  have hmeas : AEMeasurable (fun x => ‖commEps ρ ε u (W n) t x‖ₑ)
      (volume.restrict (ball (0 : ℂ) R)) :=
    ((aestronglyMeasurable_commEps hρ hε0 hul (huW n) (hWm n)).enorm).restrict
  calc ∫⁻ x in ball (0 : ℂ) R, ‖commEps ρ ε u w t x‖ₑ
      ≤ ∫⁻ x in ball (0 : ℂ) R,
          (‖commEps ρ ε u (W n) t x‖ₑ + ‖commEps ρ ε u (G n) t x‖ₑ) := by
        refine lintegral_mono fun x => ?_
        rw [hdec n ε hε0 x]
        exact enorm_add_le _ _
    _ = (∫⁻ x in ball (0 : ℂ) R, ‖commEps ρ ε u (W n) t x‖ₑ) +
          ∫⁻ x in ball (0 : ℂ) R, ‖commEps ρ ε u (G n) t x‖ₑ := lintegral_add_left' hmeas _
    _ ≤ η / 2 + η / 2 := by
        gcongr
        exact (hC u (W n) t hu (hgH n) ε hε0 hε1 R hR).trans hn.le
    _ = η := ENNReal.add_halves η

end NonUniqueEuler.Weak.CommutatorH
