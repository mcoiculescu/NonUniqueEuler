import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Norm

/-!
# Helper for `P/Sec2/HkCalculus/CutoffBS`: limits of `H^k`-Cauchy sequences converging in `L²`

The closing step of the proof of `lem:Hk-calculus`(3) (`02_prelim.tex:762-766`): if `u n ∈ H^k`
is Cauchy in `H^k` (in the quantitative form `‖u n - u m‖_{H^k} ≤ ε n + ε m`, `ε → 0`), converges
to `f` in `L²`, and `‖u n‖_{H^k} ≤ B + ε n`, then `f ∈ H^k` and `‖f‖_{H^k} ≤ B`. The proof uses the
completeness of the Hilbert space `Sob.Hk k` (`Defs/Infra/SobolevSpace.lean`) and the bridge
`I/Infra/Sobolev/Space.lean`.

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace NonUniqueEuler.Sob.CutoffBSAux

theorem toHk_sub' {k : ℕ} {f g : ℂ → ℂ} (hf : MemH k f) (hg : MemH k g) :
    toHk k (f - g) = toHk k f - toHk k g := by
  have hg' := (hg.const_smul (-1)).1
  have h1 : f - g = f + (-1 : ℂ) • g := by
    funext x
    simp [sub_eq_add_neg]
  rw [h1, toHk_add hf hg', toHk_smul hg]
  simp [sub_eq_add_neg]

/-- The function of an element of `Hk k` is the `L²` class of its `0`-th component. -/
theorem continuous_ofLp_idx0 (k : ℕ) :
    Continuous fun G : Hk k => (G : SobTuple k).ofLp (idx0 k) :=
  ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : SobIdx k => Lp ℂ 2 (volume : Measure ℂ)) (idx0 k)).continuous).comp
    continuous_subtype_val

/-- Limits of `H^k`-Cauchy sequences converging in `L²` (`02_prelim.tex:762-766`). -/
theorem memH_of_cauchy {k : ℕ} {f : ℂ → ℂ} {u : ℕ → ℂ → ℂ} {ε : ℕ → ℝ} {B : ℝ}
    (hu : ∀ n, MemH k (u n))
    (hcau : ∀ n m, normH k (u n - u m) ≤ ε n + ε m)
    (hε : Tendsto ε atTop (𝓝 0))
    (hbd : ∀ n, normH k (u n) ≤ B + ε n)
    (hf : AEStronglyMeasurable f volume)
    (hL2 : Tendsto (fun n => eLpNorm (u n - f) 2 volume) atTop (𝓝 0)) :
    MemH k f ∧ normH k f ≤ B := by
  set F : ℕ → Hk k := fun n => toHk k (u n) with hF
  have hdist : ∀ n m, dist (F n) (F m) ≤ ε n + ε m := by
    intro n m
    rw [dist_eq_norm, hF]
    dsimp only
    rw [← toHk_sub' (hu n) (hu m), norm_toHk ((hu n).sub (hu m)).1]
    exact hcau n m
  have hcauchy : CauchySeq F := by
    rw [Metric.cauchySeq_iff']
    intro δ hδ
    have hev : ∀ᶠ n in atTop, ε n < δ / 2 := hε.eventually (gt_mem_nhds (by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun n hn => ?_⟩
    calc dist (F n) (F N) ≤ ε n + ε N := hdist n N
      _ < δ / 2 + δ / 2 := add_lt_add (hN n hn) (hN N le_rfl)
      _ = δ := by ring
  obtain ⟨Flim, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the functions converge in `L²`
  have h1 : Tendsto (fun n => (F n : SobTuple k).ofLp (idx0 k)) atTop
      (𝓝 ((Flim : SobTuple k).ofLp (idx0 k))) :=
    ((continuous_ofLp_idx0 k).tendsto _).comp hlim
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h1
  have hfnF : ∀ n, (F n).fn =ᵐ[volume] u n := fun n => toHk_fn (hu n)
  have hmeasF : ∀ G : Hk k, AEStronglyMeasurable G.fn volume := fun G =>
    Lp.aestronglyMeasurable _
  have hle : ∀ n, eLpNorm (Flim.fn - f) 2 volume ≤
      eLpNorm (⇑((F n : SobTuple k).ofLp (idx0 k)) - ⇑((Flim : SobTuple k).ofLp (idx0 k)))
        2 volume + eLpNorm (u n - f) 2 volume := by
    intro n
    have hsplit : Flim.fn - f = (Flim.fn - (F n).fn) + ((F n).fn - f) := by abel
    rw [hsplit]
    refine (eLpNorm_add_le ((hmeasF Flim).sub (hmeasF (F n))) ((hmeasF (F n)).sub hf)
      (by norm_num)).trans (add_le_add ?_ ?_)
    · rw [eLpNorm_sub_comm]
      rfl
    · exact (eLpNorm_congr_ae ((hfnF n).sub EventuallyEq.rfl)).le
  have hzero : eLpNorm (Flim.fn - f) 2 volume ≤ 0 := by
    have ht := h1.add hL2
    rw [add_zero] at ht
    exact ge_of_tendsto' ht hle
  have hfn : Flim.fn =ᵐ[volume] f := by
    have h0 : eLpNorm (Flim.fn - f) 2 volume = 0 := le_antisymm hzero (zero_le)
    rw [eLpNorm_eq_zero_iff ((hmeasF Flim).sub hf) (by norm_num)] at h0
    filter_upwards [h0] with x hx
    simpa [sub_eq_zero] using hx
  obtain ⟨hmemF, hnormF⟩ := Hk.memH_fn Flim
  obtain ⟨hmem, hnorm⟩ := hmemF.congr_ae hfn
  refine ⟨hmem, ?_⟩
  rw [hnorm, hnormF]
  have hnormlim : Tendsto (fun n => ‖F n‖) atTop (𝓝 ‖Flim‖) := hlim.norm
  have hB : Tendsto (fun n => B + ε n) atTop (𝓝 (B + 0)) := tendsto_const_nhds.add hε
  rw [add_zero] at hB
  refine le_of_tendsto_of_tendsto' hnormlim hB fun n => ?_
  rw [hF]
  dsimp only
  rw [norm_toHk (hu n)]
  exact hbd n

end NonUniqueEuler.Sob.CutoffBSAux
