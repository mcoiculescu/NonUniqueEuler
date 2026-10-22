import NonUniqueEuler.Defs.Sec3.Commutator
import NonUniqueEuler.Defs.Sec2.Spaces
import NonUniqueEuler.H.Sec3.Commutator.Slice
import NonUniqueEuler.I.Sec3.Commutator.SliceBound
import NonUniqueEuler.I.Infra.Sobolev.Local
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Proof: `lem:commutator` (DiPerna–Lions commutator lemma), `a = b = 2`

Proof of `NonUniqueEuler/I/Sec3/Commutator.lean` (`03_compactness.tex:365-461`).

**Structure (restructured proof).** The
manuscript proves the uniform bound eq:comm-bound, the smooth case with dominated convergence on
`J`, and the density step in `L¹(J; L²(B_{R+2}))`. Here the density step is done at a fixed time
(`CommutatorH.tendsto_lintegral_commEps_ball_slice`, `H/Sec3/Commutator/Slice.lean`), and the
time integration is a single dominated convergence:
* for a.e. `t ∈ J`, `u(t) ∈ L²(B_r)`, `w(t) ∈ H¹(B_r)` for every `r`, and `div w(t) = 0`;
* for such `t`, `F_ε(t) = ‖C_ε[u,w](t)‖_{L¹(B_R)} → 0` (fixed-time lemma), and for
  `ε ∈ (0,1]`, `F_ε(t) ≤ C M ‖w(t)‖_{H¹(B_{R+1})}` (eq:comm-bound,
  `exists_lintegral_commEps_ball_le`, and `‖u(t)‖_{L²(B_{R+1})} ≤ M`), which is integrable on `J`;
* `‖C_ε‖_{L¹(J×B_R)} ≤ ∫_J F_ε(t) dt` (`lintegral_prod_le`, valid without measurability);
* dominated convergence for the lower integral: replace `F_ε` by a measurable minorant with the
  same integral (`exists_measurable_le_lintegral_eq`).
No joint measurability of `C_ε[u,w]` in `(t,x)` is needed.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Weak

/-- `lem:commutator` with `a = b = 2` (`03_compactness.tex:365-372`): for an open interval `I`,
a field `w ∈ L¹_loc(I; W^{1,2}_loc)` with `div w = 0`, and `u ∈ L^∞_loc(I; L²_loc)`,
`C_ε[u,w] → 0` in `L¹(J × B_R)` as `ε → 0⁺`, for every compact `J ⊆ I` and every `R > 0`. -/
theorem commutator_tendsto {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {I : Set ℝ} (hI : IsOpen I)
    (hIc : I.OrdConnected) {w : ℝ → ℂ → ℂ} (hw : IsLocH1DivFreeField I w) {u : ℝ → ℂ → ℝ}
    (hu : ∀ J ⊆ I, IsCompact J → ∀ R : ℝ, 0 < R → Prelim.MemLinfLp J (ball (0 : ℂ) R) 2 u) :
    ∀ J ⊆ I, IsCompact J → ∀ R : ℝ, 0 < R →
      Tendsto (fun ε : ℝ => ∫⁻ p in J ×ˢ ball (0 : ℂ) R, ‖commEps ρ ε u w p.1 p.2‖ₑ)
        (𝓝[>] 0) (𝓝 0) := by
  intro J hJI hJ R hR
  obtain ⟨C, -, hC⟩ := exists_lintegral_commEps_ball_le hρ
  have hR1 : (0 : ℝ) < R + 1 := by linarith
  -- a.e. good times in `J`
  have hun : ∀ᵐ t ∂(volume.restrict J), ∀ n : ℕ,
      MemLp (u t) 2 (volume.restrict (ball (0 : ℂ) ((n : ℝ) + 1))) := by
    rw [ae_all_iff]
    intro n
    obtain ⟨M, hM⟩ := (hu J hJI hJ ((n : ℝ) + 1) (by positivity)).essBounded
    exact hM.mono fun t ht => ht.1
  have hwn : ∀ᵐ t ∂(volume.restrict J), ∀ n : ℕ,
      Sob.MemHOn 1 (ball (0 : ℂ) ((n : ℝ) + 1)) (w t) := by
    rw [ae_all_iff]
    intro n
    exact ae_restrict_of_ae_restrict_of_subset hJI (hw.memHOn ((n : ℝ) + 1) (by positivity))
  have hdivJ : ∀ᵐ t ∂(volume.restrict J), Prelim.IsWeaklyDivFree (w t) :=
    ae_restrict_of_ae_restrict_of_subset hJI hw.divFree
  have hgood : ∀ᵐ t ∂(volume.restrict J),
      (∀ r : ℝ, 0 < r → MemLp (u t) 2 (volume.restrict (ball (0 : ℂ) r))) ∧
      (∀ r : ℝ, 0 < r → Sob.MemHOn 1 (ball (0 : ℂ) r) (w t)) ∧
      Prelim.IsWeaklyDivFree (w t) := by
    filter_upwards [hun, hwn, hdivJ] with t hut hwt hdt
    refine ⟨fun r hr => ?_, fun r hr => ?_, hdt⟩
    · obtain ⟨n, hn⟩ := exists_nat_ge r
      exact (hut n).mono_measure
        (Measure.restrict_mono (ball_subset_ball (by linarith)) le_rfl)
    · obtain ⟨n, hn⟩ := exists_nat_ge r
      exact (Sob.MemHOn.mono_set isOpen_ball isOpen_ball (ball_subset_ball (by linarith))
        (hwt n)).1
  -- the bound on `‖u(t)‖_{L²(B_{R+1})}`
  obtain ⟨M, hM⟩ := (hu J hJI hJ (R + 1) hR1).essBounded
  -- the slice integrals and their measurable minorants
  set F : ℝ → ℝ → ℝ≥0∞ := fun ε t => ∫⁻ x in ball (0 : ℂ) R, ‖commEps ρ ε u w t x‖ₑ with hF
  set bound : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal C * ENNReal.ofReal M *
    ENNReal.ofReal (Sob.normHOn 1 (ball (0 : ℂ) (R + 1)) (w t)) with hbound
  choose G hGm hGle hGeq using fun ε => exists_measurable_le_lintegral_eq (volume.restrict J) (F ε)
  -- domination
  have h_bound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ t ∂(volume.restrict J), G ε t ≤ bound t := by
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    filter_upwards [hgood, hM] with t ht htM
    refine (hGle ε t).trans ?_
    refine (hC u w t ht.1 ht.2.1 ε hε.1 hε.2 R hR).trans ?_
    have hle : eLpNorm (u t) 2 (volume.restrict (ball (0 : ℂ) (R + 1))) ≤ ENNReal.ofReal M := by
      rw [← ENNReal.ofReal_toReal htM.1.eLpNorm_ne_top]
      exact ENNReal.ofReal_le_ofReal htM.2
    simp only [hbound]
    gcongr
  -- integrability of the bound
  have h_fin : ∫⁻ t, bound t ∂(volume.restrict J) ≠ ∞ := by
    simp only [hbound]
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (hw.integrableOn_normHOn (R + 1) hR1 J hJI hJ).lintegral_lt_top.ne
  -- pointwise convergence of the minorants
  have h_lim : ∀ᵐ t ∂(volume.restrict J),
      Tendsto (fun ε => G ε t) (𝓝[>] (0 : ℝ)) (𝓝 ((fun _ => (0 : ℝ≥0∞)) t)) := by
    filter_upwards [hgood] with t ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (CommutatorH.tendsto_lintegral_commEps_ball_slice hρ ht.1 ht.2.1 ht.2.2 hR)
      (fun _ => zero_le) (fun ε => hGle ε t)
  have hGt : Tendsto (fun ε => ∫⁻ t, G ε t ∂(volume.restrict J)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := tendsto_lintegral_filter_of_dominated_convergence (μ := volume.restrict J)
      bound (Eventually.of_forall hGm) h_bound h_fin h_lim
    simpa using this
  -- the space-time integral is bounded by the iterated one
  have hle : ∀ ε : ℝ, ∫⁻ p in J ×ˢ ball (0 : ℂ) R, ‖commEps ρ ε u w p.1 p.2‖ₑ ≤
      ∫⁻ t, G ε t ∂(volume.restrict J) := by
    intro ε
    rw [← hGeq ε, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact lintegral_prod_le _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGt (fun _ => zero_le) hle

end NonUniqueEuler.Weak
