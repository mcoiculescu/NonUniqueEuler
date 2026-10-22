import NonUniqueEuler.Defs.Sec3.Commutator
import NonUniqueEuler.H.Sec3.Commutator.SmoothApprox.Deriv
import NonUniqueEuler.H.Sec3.Commutator.SmoothApprox.Sobolev

/-!
# Proof: smooth divergence-free approximation of an `H¹_loc` divergence-free field

Proof of `I/Sec3/Commutator/SmoothApprox.lean` (`03_compactness.tex:440-447`, inside the proof
of `lem:commutator`, "We now remove the smoothness").

`g_n = ρ_n ⋆ f` with `ρ_n` the normed bump of outer radius `δ_n = (1/2)/(n+1)`
(`SmoothApproxAux.bump`); the manuscript's `w_δ = w ⋆ ρ_δ`.
1. `g_n` is `C^∞` (`contDiff_conv`).
2. `div g_n = 0` (`divFree_conv`: test `div f = 0` against `y ↦ ρ_n(x - y)`).
3. `f - g_n ∈ H¹(B_r)` for every `r` (`memHOn_sub`, `memHOn_ball_of_contDiff`).
4. For `|γ| ≤ 1` let `G` be an `L²(B_{R+2})` weak derivative `∂^γ f` on `B_{R+2}`, extended by
   `0`. For `x ∈ B_R`, `∂^γ g_n(x) = (ρ_n ⋆ G)(x)` (`iterDirDeriv_conv_eq_conv`, since
   `closedBall x δ_n ⊆ B_{R+2}`), so the weak `∂^γ(f - g_n)` on `B_R` is `G - ρ_n ⋆ G`, which
   tends to `0` in `L²` (`tendsto_l2On_weakDerivOn_sub_conv`). Hence
   `‖f - g_n‖_{H¹(B_R)} → 0`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Weak

open SmoothApproxAux in
/-- `03_compactness.tex:440-447`: an `H¹_loc` field with `div f = 0` is the `H¹(B_R)`-limit of
smooth fields `g_n` with `div g_n = 0`, and `f - g_n ∈ H¹_loc`. -/
theorem exists_smooth_divFree_approx {f : ℂ → ℂ}
    (hf : ∀ r : ℝ, 0 < r → Sob.MemHOn 1 (ball (0 : ℂ) r) f) (hdiv : Prelim.IsWeaklyDivFree f)
    {R : ℝ} (hR : 0 < R) :
    ∃ g : ℕ → ℂ → ℂ, (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g n)) ∧
      (∀ n x, (fderiv ℝ (g n) x 1).re + (fderiv ℝ (g n) x Complex.I).im = 0) ∧
      (∀ n, ∀ r : ℝ, 0 < r → Sob.MemHOn 1 (ball (0 : ℂ) r) (fun x => f x - g n x)) ∧
      Tendsto (fun n => Sob.normHOn 1 (ball (0 : ℂ) R) (fun x => f x - g n x)) atTop (𝓝 0) := by
  have hfl : LocallyIntegrable f volume := locallyIntegrable_of_memHOn hf
  have h2 : (0 : ℝ) < 1 / 2 := by norm_num
  set b : ℕ → ContDiffBump (0 : ℂ) := bump (1 / 2) h2 with hbdef
  have hbt : Tendsto (fun n => (b n).rOut) atTop (𝓝 0) := bump_rOut_tendsto (1 / 2) h2
  have hb2 : ∀ n, (b n).rOut ≤ 1 / 2 := bump_rOut_le (1 / 2) h2
  have hb1 : ∀ n, (b n).rOut ≤ 1 := fun n => (hb2 n).trans (by norm_num)
  have hgs : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (conv ((b n).normed volume) f) :=
    fun n => contDiff_conv (b n).contDiff_normed (b n).hasCompactSupport_normed hfl
  refine ⟨fun n => conv ((b n).normed volume) f, hgs,
    fun n x => divFree_conv (b n).contDiff_normed (b n).support_normed_eq.subset hfl hdiv x,
    fun n r hr => memHOn_sub (hf r hr) (memHOn_ball_of_contDiff (hgs n) 1 r), ?_⟩
  -- the `H¹(B_R)` convergence, one multi-index at a time
  refine tendsto_sqrt_sum_sq (s := Sob.multiIdx 1)
    (a := fun n γ => Sob.l2On (ball (0 : ℂ) R) (Sob.weakPartialOn (ball (0 : ℂ) R) γ
      (fun x => f x - conv ((b n).normed volume) f x))) fun γ hγ => ?_
  obtain ⟨G0, hG0, hfG0⟩ := (hf (R + 2) (by linarith)).deriv γ hγ
  set G : ℂ → ℂ := (ball (0 : ℂ) (R + 2)).indicator G0 with hGdef
  have hG : MemLp G 2 volume := (memLp_indicator_iff_restrict measurableSet_ball).2 hG0
  have hfG : Sob.HasWeakDerivOn (ball (0 : ℂ) (R + 2)) (Sob.pdList γ) f G :=
    hfG0.congr_ae (Eventually.of_forall fun _ _ => rfl)
      (Eventually.of_forall fun x hx => (indicator_of_mem hx _).symm)
  have hvs : (Sob.pdList γ).length ≤ 1 := by
    rw [Sob.pdList_length]
    exact Sob.mem_multiIdx.1 hγ
  refine tendsto_l2On_weakDerivOn_sub_conv hvs hbt hb1 hfl hG
    (hfG.mono (ball_subset_ball (by linarith))) fun n x hx => ?_
  refine iterDirDeriv_conv_eq_conv (b n).contDiff_normed (b n).support_normed_eq.subset
    (fun y hy => ?_) hvs hfl hfG
  rw [mem_closedBall, dist_eq_norm] at hy
  rw [mem_ball_zero_iff] at hx ⊢
  have h := norm_add_le x (y - x)
  rw [add_sub_cancel] at h
  linarith [hb2 n]

end NonUniqueEuler.Weak
