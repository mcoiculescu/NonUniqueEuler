import NonUniqueEuler.H.Sec5.Quiet.Key
import NonUniqueEuler.I.Sec5.Quiet.Approx
import NonUniqueEuler.I.Infra.Continuity.Bootstrap

/-!
# Proof: `thm:quiet` (a quiet ring)

Proof of `I/Sec5/Quiet.lean` (`thm:quiet`, `05_single_ring.tex:408-429`, proof `:430-557`).

**Structure.**
1. *Constants* (`05_single_ring.tex:440-461`). The approximate solution
   (`I/Sec5/Quiet/Approx.lean`, `quiet_approx`, which contains `eq:Q-hier` and `eq:Q-res`) comes
   with a constant `C_app ≥ 0`. We take `C_Q = C_app(2 + σ_b⁻¹) + 1`, `C_Δ = 1 + C_BS C_Q/σ_b`,
   `maj_* = min(1, 1/(2C_Q), a/(16C_Δ))`; they depend only on `(Φ, G₁, s_h, N_Q)`.
2. *Comparison step* (`H/Sec5/Quiet/Key.lean`, `QuietH.key`; `05_single_ring.tex:514-549`): if on
   `[0,t']` the trajectories move radially by at most `a/8` and `‖w‖_{H^{s_h}} ≤ 1`, then on
   `[0,t']` the support stays in `N`, `lem:energy` applies, and `eq:Q-v`, `eq:Q-b` and
   `δ_r ≤ C_Δ maj` hold.
3. *Continuity argument* (`05_single_ring.tex:514-555`), with `Continuity.forall_Icc_of_history`
   for `Q(t)`: "`δ_r(t) ≤ C_Δ maj(t)`, `‖w(t)‖ ≤ C_Q maj(t)`, `‖w(t) - wlin(t)‖ ≤ C_Q maj(t)²`".
   `Q(t)` gives `δ_r(t) ≤ a/16` and `‖w(t)‖ ≤ 1/2`. *Extension* (`hext`): from `δ_r(t) ≤ a/16` and
   `‖w‖ ≤ 1/2` on `[0,t]`, the tube lemma (the flow is continuous and `supp Φ` is compact) gives
   `δ_r ≤ a/8` on `[0,t+δ]`, so the support is in `N` there, `w ∈ C([0,t+δ];X^{s_h})`
   (`lem:reduction`(3)), and `‖w‖ ≤ 1` on `[0,t+δ']`; the comparison step gives `Q` on
   `[0,t+δ']`. *Closure* (`hlim`): `δ_r` and `‖w‖` are continuous, so the bounds `a/16`, `1/2`
   pass to the limit `s ↑ t`, and the comparison step gives `Q(t)`.
4. *Conclusion*: (a) from `δ_r ≤ C_Δ maj ≤ a/16` (support in `𝒩₋`) and `lem:reduction`(3) on
   `[0,T]`; (b), (c) are `Q`.

**Deviation.** The manuscript runs the continuity argument on
`t_* = sup{t : δ_r ≤ a/8, ‖w‖ ≤ 1 on [0,t]}` with the continuous function `δ_r(t)` (maximal
radial displacement); we use real induction (`forall_Icc_of_history`) on the improved bounds
directly, and the openness of `{(τ,y) : ||Φ_τ(y)| - |y|| < a/8}` (tube lemma) instead of the
continuity of `δ_r`. The constants `C_Q`, `C_Δ`, `maj_*` are those of the manuscript up to the
packaging of `Σ_j C^{(j)}`, `C_res` into the single constant `C_app` of `quiet_approx`
(`C_Q = C_app(2 + σ_b⁻¹) + 1 ≥` the manuscript's `Σ_j C^{(j)} + C_res(1 + σ_b⁻¹)`; the `+1` makes
`C_Q > 0`, so that `maj_* > 0` also when `C_app = 0`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- **`thm:quiet`** (`05_single_ring.tex:408-429`). Assume (N1)–(N3). Let `s_h ≥ 3` and
`N_Q ≥ 2` be integers with `N_Q σ_b ≥ Λ(s_h)`, `M_h = s_h + N_Q + 1`. There are
`maj_* ∈ (0,1]` and `C_Q, C_Δ < ∞` (here also `≥ 0`), depending only on `(Φ, G₁, s_h, N_Q)`,
with `C_Δ maj_* ≤ a/16`, such that for every configuration of `lem:reduction` on `[0,T]` with
`ω_r(0) = Φ` and `G ∈ [0,G₁]`, every measurable `η` with `‖h(t)‖_{C^{M_h}(N')} ≤ η(t) ≤ 1` on
`[0,T]` whose Duhamel majorant satisfies `maj ≤ maj_*` on `[0,T]`, and every `t ∈ [0,T]`:
(a) every trajectory of `ω_r` moves radially by at most `C_Δ maj(t) ≤ a/16` on `[0,t]`,
`supp ω_r(t) ⊂ 𝒩₋`, and `w = ω_r - Φ` solves `eq:ring` on `[0,T]`;
(b) `‖w(t) - wlin(t)‖_{H^{s_h}} ≤ C_Q maj(t)²`; (c) `‖w(t)‖_{H^{s_h}} ≤ C_Q maj(t)`.
The whole conclusion is `IsQuietConst χ sh NQ maj_* C_Q C_Δ` (D11). -/
theorem quiet (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {sh NQ : ℕ} (hs : 3 ≤ sh) (hQ : 2 ≤ NQ) (hΛ : Lam χ sh ≤ NQ * Eig.sigb χ) :
    ∃ majst CQ CΔ : ℝ, IsQuietConst χ sh NQ majst CQ CΔ := by
  obtain ⟨Capp, hCapp, happrox⟩ := quiet_approx χ hχ hN hs hQ
  have hF := ringFacts_of_admissible hχ
  have ha0 : 0 < a := hF.2.2.2.2.2.2.1
  have hσb : 0 < Eig.sigb χ := by
    have := (Eig.propU_a χ hχ hN).2.2.2.1
    linarith
  set σb := Eig.sigb χ with hσbdef
  -- the constants
  obtain ⟨CQ, hCQdef⟩ : ∃ CQ : ℝ, CQ = Capp * (2 + σb⁻¹) + 1 := ⟨_, rfl⟩
  obtain ⟨CΔ, hCΔdef⟩ : ∃ CΔ : ℝ, CΔ = 1 + CBS * CQ / σb := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = min 1 (min (1 / (2 * CQ)) (a / (16 * CΔ))) := ⟨_, rfl⟩
  have hσbinv : 0 ≤ σb⁻¹ := inv_nonneg.2 hσb.le
  have hCQapp : Capp * (2 + σb⁻¹) ≤ CQ := by rw [hCQdef]; linarith
  have hCQpos : 0 < CQ := by
    rw [hCQdef]
    have : 0 ≤ Capp * (2 + σb⁻¹) := mul_nonneg hCapp (by linarith)
    linarith
  have hCappCQ : Capp ≤ CQ := by
    have : Capp ≤ Capp * (2 + σb⁻¹) := by nlinarith
    linarith
  have hCBS := CBS_pos
  have hCΔpos : 0 < CΔ := by
    rw [hCΔdef]
    have : 0 ≤ CBS * CQ / σb := div_nonneg (mul_nonneg hCBS.le hCQpos.le) hσb.le
    linarith
  have hMpos : 0 < M := by
    rw [hMdef]
    refine lt_min one_pos (lt_min ?_ ?_)
    · exact div_pos one_pos (mul_pos two_pos hCQpos)
    · exact div_pos ha0 (mul_pos (by norm_num) hCΔpos)
  have hM1 : M ≤ 1 := by rw [hMdef]; exact min_le_left _ _
  have hMQ : M ≤ 1 / (2 * CQ) := by
    rw [hMdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hMΔ : M ≤ a / (16 * CΔ) := by
    rw [hMdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hCΔM : CΔ * M ≤ a / 16 := by
    calc CΔ * M ≤ CΔ * (a / (16 * CΔ)) := mul_le_mul_of_nonneg_left hMΔ hCΔpos.le
      _ = a / 16 := by field_simp
  have hCQM : CQ * M ≤ 1 / 2 := by
    calc CQ * M ≤ CQ * (1 / (2 * CQ)) := mul_le_mul_of_nonneg_left hMQ hCQpos.le
      _ = 1 / 2 := by field_simp
  refine ⟨M, CQ, CΔ, ⟨hMpos, hM1⟩, hCQpos.le, hCΔpos.le, hCΔM, ?_⟩
  intro c T hc hr hG η hη hh hmaj
  -- notation
  set m := maj (Eig.sigma χ c.G) η with hmdef
  have hT : 0 < T := hc.T_pos
  have hmaj1 : ∀ t ∈ Icc (0 : ℝ) T, m t ≤ 1 := fun t ht => (hmaj t ht).trans hM1
  -- the field
  have hfield := reduction_field hc
  have hsym : ∀ t ∈ Icc (0 : ℝ) T, IsSymFieldOn annN' (c.h t) := by
    intro t ht
    obtain ⟨U, -, hU, -, -, -, hsU, -⟩ := hfield.1 t ht
    exact fun x hx => hsU x (hU hx)
  -- the approximate solution
  obtain ⟨wapp, wapp', happ, happ', hreal, hzero, hbd⟩ :=
    happrox c.G T c.h η hG hT (hfield.2 (Mh sh NQ)) hsym hη hh hmaj1
  have hwapp1 : ∀ t ∈ Icc (0 : ℝ) T, Sob.normH (sh + 1) (wapp t) ≤ 1 := by
    intro t ht
    have h1 : Capp * m t ≤ Capp * M := mul_le_mul_of_nonneg_left (hmaj t ht) hCapp
    have h2 : Capp * M ≤ CQ * M := mul_le_mul_of_nonneg_right hCappCQ hMpos.le
    linarith [(hbd t ht).1]
  -- the comparison step
  have K := fun t' : ℝ => QuietH.key χ hχ hN hs hQ hΛ hc hr hG hη hh hmaj1 hCapp hCQapp happ
    happ' hreal hzero hbd hwapp1 (t' := t')
  rw [← hσbdef, ← hCΔdef] at K
  -- the induction statement
  let Q : ℝ → Prop := fun τ => c.MovesRadially τ (CΔ * m τ) ∧
    Sob.normH sh (c.w χ τ) ≤ CQ * m τ ∧
    Sob.normH sh (c.w χ τ - (wlin χ sh c.G c.h τ).fn) ≤ CQ * m τ ^ 2
  have hQmove : ∀ τ ∈ Icc (0 : ℝ) T, Q τ → c.MovesRadially τ (a / 16) := fun τ hτ hQτ =>
    hQτ.1.mono ((mul_le_mul_of_nonneg_left (hmaj τ hτ) hCΔpos.le).trans hCΔM)
  have hQw : ∀ τ ∈ Icc (0 : ℝ) T, Q τ → Sob.normH sh (c.w χ τ) ≤ 1 / 2 := fun τ hτ hQτ =>
    hQτ.2.1.trans ((mul_le_mul_of_nonneg_left (hmaj τ hτ) hCQpos.le).trans hCQM)
  -- the flow and the support of `Φ`
  have hcont := QuietH.flow_continuous hc
  have hK : IsCompact (tsupport c.ring0) := by rw [hr]; exact hF.2.1
  have hgcont : ∀ y : ℂ, Continuous (fun s : ℝ => |‖c.flow s y‖ - ‖y‖|) := fun y =>
    ((hcont.comp (continuous_id.prodMk continuous_const)).norm.sub continuous_const).abs
  -- extension step
  have hext : ∀ t ∈ Ico (0 : ℝ) T, c.MovesRadially t (a / 16) →
      (∀ s ∈ Icc (0 : ℝ) t, Sob.normH sh (c.w χ s) ≤ 1 / 2) →
      ∃ δ > 0, t + δ ≤ T ∧ c.MovesRadially (t + δ) (a / 8) ∧
        ∀ s ∈ Icc (0 : ℝ) (t + δ), Sob.normH sh (c.w χ s) ≤ 1 := by
    intro t ht hmv hw
    -- tube lemma
    let n : Set (ℝ × ℂ) := {p | |‖c.flow p.1 p.2‖ - ‖p.2‖| < a / 8}
    have hn : IsOpen n :=
      isOpen_lt ((hcont.norm.sub continuous_snd.norm).abs) continuous_const
    have hsub : ({t} : Set ℝ) ×ˢ tsupport c.ring0 ⊆ n := by
      rintro ⟨s, y⟩ ⟨hs, hy⟩
      have hs' : s = t := hs
      show |‖c.flow s y‖ - ‖y‖| < a / 8
      rw [hs']
      exact lt_of_le_of_lt (hmv y hy t ⟨ht.1, le_rfl⟩) (by linarith)
    obtain ⟨u, v, hu, -, htu, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK hn hsub
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hu t (htu rfl)
    obtain ⟨δ₁, hδ₁def⟩ : ∃ δ₁ : ℝ, δ₁ = min (ε / 2) (T - t) := ⟨_, rfl⟩
    have hδ₁ : 0 < δ₁ := by rw [hδ₁def]; exact lt_min (by linarith) (by linarith [ht.2])
    have hδ₁ε : δ₁ ≤ ε / 2 := by rw [hδ₁def]; exact min_le_left _ _
    have hδ₁T : t + δ₁ ≤ T := by
      have : δ₁ ≤ T - t := by rw [hδ₁def]; exact min_le_right _ _
      linarith
    have hmv1 : c.MovesRadially (t + δ₁) (a / 8) := by
      intro y hy s hs
      by_cases hst : s ≤ t
      · exact (hmv y hy s ⟨hs.1, hst⟩).trans (by linarith)
      · replace hst := lt_of_not_ge hst
        have hsu : s ∈ u := hball (by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          constructor <;> linarith [hs.2])
        exact (huv ⟨hsu, hKv hy⟩ : (s, y) ∈ n).le
    -- `‖w‖` is continuous on `[0, t + δ₁]`
    have hsupp1 := (QuietH.supp_of_movesRadially hχ hc hr hmv1).2 le_rfl
    have hct1 : c.Hyp (t + δ₁) := hc.mono (by linarith [ht.1]) hδ₁T
    have hpe1 := (reduction_eq χ hχ hct1 hsupp1).2
    have hcn := QuietH.continuousOn_normH (hpe1 sh).1
    have htmem : t ∈ Icc (0 : ℝ) (t + δ₁) := ⟨ht.1, by linarith⟩
    have hlt : Sob.normH sh (c.w χ t) < 1 := by linarith [hw t ⟨ht.1, le_rfl⟩]
    have hev := hcn t htmem (Iio_mem_nhds hlt)
    obtain ⟨δ₂, hδ₂, hδ₂b⟩ := Metric.mem_nhdsWithin_iff.1 hev
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δ₁ (δ₂ / 2) := ⟨_, rfl⟩
    have hδ : 0 < δ := by rw [hδdef]; exact lt_min hδ₁ (by linarith)
    have hδδ₁ : δ ≤ δ₁ := by rw [hδdef]; exact min_le_left _ _
    have hδδ₂ : δ ≤ δ₂ / 2 := by rw [hδdef]; exact min_le_right _ _
    refine ⟨δ, hδ, by linarith, hmv1.mono_time (by linarith), fun s hs => ?_⟩
    by_cases hst : s ≤ t
    · exact (hw s ⟨hs.1, hst⟩).trans (by norm_num)
    · replace hst := lt_of_not_ge hst
      have hs' : s ∈ ball t δ₂ ∩ Icc (0 : ℝ) (t + δ₁) := by
        refine ⟨?_, hs.1, by linarith [hs.2]⟩
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hs.2]
      exact (hδ₂b hs' : Sob.normH sh (c.w χ s) < 1).le
  -- `Q 0`
  have hw0 : c.w χ 0 = 0 := by
    rw [(RingConfig.setting_sol_eq_parts hc).2.2.2.2.2 χ]
    funext x
    simp [RingConfig.pert0, hr]
  have hw00 : Sob.normH sh (c.w χ 0) = 0 := by
    rw [hw0]
    exact QuietH.normH_eq_zero_of_ae (Filter.EventuallyEq.refl _ _)
  have hflow0 := (RingConfig.setting_sol_eq_parts hc).2.2.2.1
  have hmv0 : c.MovesRadially 0 (a / 16) := by
    intro y _ s hs
    have : s = 0 := le_antisymm hs.2 hs.1
    rw [this, hflow0 y, sub_self, abs_zero]
    linarith
  have h0 : Q 0 := by
    obtain ⟨δ, hδ, hδT, hmvδ, hwδ⟩ := hext 0 ⟨le_rfl, hT⟩ hmv0 (fun s hs => by
      have : s = 0 := le_antisymm hs.2 hs.1
      rw [this, hw00]; norm_num)
    rw [zero_add] at hδT hmvδ hwδ
    exact K δ hδ hδT hmvδ hwδ 0 ⟨le_rfl, hδ.le⟩
  -- closure step
  have hlim : ∀ t ∈ Ioc (0 : ℝ) T, (∀ s ∈ Ico (0 : ℝ) t, Q s) → Q t := by
    intro t ht hQs
    have hfilt : Ioo (0 : ℝ) t ∈ 𝓝[<] t := Ioo_mem_nhdsLT ht.1
    have hmv : c.MovesRadially t (a / 16) := by
      intro y hy s hs
      rcases lt_or_eq_of_le hs.2 with hst | hst
      · exact hQmove s ⟨hs.1, hst.le.trans ht.2⟩ (hQs s ⟨hs.1, hst⟩) y hy s ⟨hs.1, le_rfl⟩
      · rw [hst]
        have hlim' : Tendsto (fun r : ℝ => |‖c.flow r y‖ - ‖y‖|) (𝓝[<] t)
            (𝓝 (|‖c.flow t y‖ - ‖y‖|)) :=
          ((hgcont y).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
        refine le_of_tendsto hlim' ?_
        filter_upwards [hfilt] with r hr
        exact hQmove r ⟨hr.1.le, hr.2.le.trans ht.2⟩ (hQs r ⟨hr.1.le, hr.2⟩) y hy r
          ⟨hr.1.le, le_rfl⟩
    have hsupp := (QuietH.supp_of_movesRadially hχ hc hr hmv).2 (by linarith)
    have hct : c.Hyp t := hc.mono ht.1 ht.2
    have hpe := (reduction_eq χ hχ hct hsupp).2
    have hcn := QuietH.continuousOn_normH (hpe sh).1
    have hwt : Sob.normH sh (c.w χ t) ≤ 1 / 2 := by
      have hIcc : Icc (0 : ℝ) t ∈ 𝓝[<] t := mem_of_superset hfilt Ioo_subset_Icc_self
      have hlim' : Tendsto (fun r => Sob.normH sh (c.w χ r)) (𝓝[<] t)
          (𝓝 (Sob.normH sh (c.w χ t))) :=
        (hcn t ⟨ht.1.le, le_rfl⟩).tendsto.mono_left (nhdsWithin_le_of_mem hIcc)
      refine le_of_tendsto hlim' ?_
      filter_upwards [hfilt] with r hr
      exact hQw r ⟨hr.1.le, hr.2.le.trans ht.2⟩ (hQs r ⟨hr.1.le, hr.2⟩)
    have hw1 : ∀ s ∈ Icc (0 : ℝ) t, Sob.normH sh (c.w χ s) ≤ 1 := by
      intro s hs
      rcases lt_or_eq_of_le hs.2 with hst | hst
      · exact (hQw s ⟨hs.1, hst.le.trans ht.2⟩ (hQs s ⟨hs.1, hst⟩)).trans (by norm_num)
      · rw [hst]; exact hwt.trans (by norm_num)
    exact K t ht.1 ht.2 (hmv.mono (by linarith)) hw1 t ⟨ht.1.le, le_rfl⟩
  -- extension step for the induction
  have hstep : ∀ t ∈ Ico (0 : ℝ) T, (∀ s ∈ Icc (0 : ℝ) t, Q s) →
      ∃ δ > 0, ∀ s ∈ Ioc t (t + δ), Q s := by
    intro t ht hQs
    have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    have hmv := hQmove t htT (hQs t ⟨ht.1, le_rfl⟩)
    have hw : ∀ s ∈ Icc (0 : ℝ) t, Sob.normH sh (c.w χ s) ≤ 1 / 2 := fun s hs =>
      hQw s ⟨hs.1, hs.2.trans htT.2⟩ (hQs s hs)
    obtain ⟨δ, hδ, hδT, hmvδ, hwδ⟩ := hext t ht hmv hw
    refine ⟨δ, hδ, fun s hs => ?_⟩
    exact K (t + δ) (by linarith [ht.1]) hδT hmvδ hwδ s ⟨by linarith [hs.1, ht.1], hs.2⟩
  have hall : ∀ t ∈ Icc (0 : ℝ) T, Q t := Continuity.forall_Icc_of_history h0 hlim hstep
  -- conclusion
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  refine ⟨?_, fun t ht => ?_⟩
  · have hmvT := hQmove T hTmem (hall T hTmem)
    have hsuppT := (QuietH.supp_of_movesRadially hχ hc hr hmvT).2 (by linarith)
    exact (reduction_eq χ hχ hc hsuppT).2
  · obtain ⟨h1, h2, h3⟩ := hall t ht
    refine ⟨h1, ?_, h3, h2⟩
    exact (QuietH.supp_of_movesRadially hχ hc hr (hQmove t ht (hall t ht))).1 le_rfl t
      ⟨ht.1, le_rfl⟩

end OneRing

end NonUniqueEuler
