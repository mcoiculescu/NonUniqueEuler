import NonUniqueEuler.H.Sec6.Adm.Basic

/-!
# Helpers for `lem:adm`: `f^{(n)} → f` in `L^q`

Helper of `P/Sec6/Adm.lean`, second paragraph of the proof of `lem:adm` (`06_datum.tex:101-113`).

Write `T_k = A_k Φ(·/r_k)`, `S_n = Σ_{k ≤ n} T_k`, `U_n = A_n Φ^κ(·/r_n)` and
`g_m = 1_{B̄_{r_m}} f`. Then (pointwise, `n ≥ 1`)
* `f - S_n = g_{n+1}` (`AdmH.datum_sub_partialSum`: the rings `k > n` lie in `B̄_{r_{n+1}}`, the
  rings `k ≤ n` outside it);
* `|T_n| ≤ |g_n|` (`AdmH.term_norm_le`: on the `n`-th annulus, `f = T_n`);
* `f^{(n)} = S_n - T_n + U_n` (`AdmH.approxDatum_eq`);
so `f^{(n)} - f = U_n - T_n - g_{n+1}` and, with `‖U_n‖_q = ‖T_n‖_q` (equimeasurability),
`‖f^{(n)} - f‖_q ≤ 2‖g_n‖_q + ‖g_{n+1}‖_q → 0` (`AdmH.tendsto_eLpNorm_approxDatum_sub`).

Deviation: the manuscript bounds the tail by
`(Σ_{k>n} A_k^q r_k²)^{1/q} ‖Φ‖_q`; here the tail `f - S_n = 1_{B̄_{r_{n+1}}} f` is controlled by
the absolute continuity of the `L^q` norm of `f ∈ L^q` (`prop:integrability`), which is the same
fact in another form.

The facts of `prop:integrability` and `lem:ring-facts` used are hypotheses (`RingFacts χ`, the
disjointness of the terms, `f ∈ L^q`), as is the measure preservation of `Y_κ` (`lem:seed`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace NonUniqueEuler.Datum.AdmH

open RingData

variable {χ : ℝ → ℝ} {A₁ μ sbar κs : ℝ}

/-- If `Φ(x/r) ≠ 0` (`r > 0`) then `a r ≤ |x| ≤ r` (`lem:ring-facts`, `supp Φ ⊂ {a ≤ |y| ≤ 1}`). -/
theorem mem_annulus_of_ne_zero (hR : RingFacts χ) {r : ℝ} (hr : 0 < r) {x : ℂ}
    (h : ringPhi χ (x / (r : ℂ)) ≠ 0) : a * r ≤ ‖x‖ ∧ ‖x‖ ≤ r := by
  have hy : a ≤ ‖x / (r : ℂ)‖ ∧ ‖x / (r : ℂ)‖ ≤ 1 := hR.2.2.2.2.2.1 (subset_tsupport _ h)
  have hn : ‖x / (r : ℂ)‖ = ‖x‖ / r := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [hn] at hy
  exact ⟨(le_div_iff₀ hr).mp hy.1, (div_le_one hr).mp hy.2⟩

/-- `f - S_n = 1_{B̄_{r_{n+1}}} f` for `n ≥ 1`. -/
theorem datum_sub_partialSum (hR : RingFacts χ) (hp : DatumParams A₁ μ sbar) {n : ℕ}
    (hn : 1 ≤ n) (x : ℂ) :
    datum χ A₁ μ sbar x -
        ∑ j ∈ Finset.range n, amp A₁ μ (j + 1) * ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) =
      (closedBall (0 : ℂ) (radius sbar μ (n + 1))).indicator (datum χ A₁ μ sbar) x := by
  have hμ : 0 < μ := by linarith [hp.one_lt_μ]
  have hμ2 : 1 ≤ 2 * μ := by linarith [hp.one_lt_μ]
  have ha : 0 < a := hR.2.2.2.2.2.2.1
  have ha1 : a < 1 := hR.2.2.2.2.2.2.2
  have hs1 : sbar ≤ 1 := hp.sbar_le.trans (by linarith)
  have hanti := radius_antitone hp.sbar_pos hs1 hμ2
  by_cases hx : x ∈ closedBall (0 : ℂ) (radius sbar μ (n + 1))
  · rw [Set.indicator_of_mem hx, Finset.sum_eq_zero, sub_zero]
    intro j hj
    have hjn : j + 1 ≤ n := Finset.mem_range.mp hj
    by_contra hne
    have hΦ := right_ne_zero_of_mul hne
    obtain ⟨h1, -⟩ := mem_annulus_of_ne_zero hR (radius_pos hp.sbar_pos hμ (j + 1)) hΦ
    have h2 : ‖x‖ ≤ radius sbar μ (n + 1) := mem_closedBall_zero_iff.mp hx
    have h3 := radius_succ_lt hp ha hn
    have h4 : a * radius sbar μ n ≤ a * radius sbar μ (j + 1) :=
      mul_le_mul_of_nonneg_left (hanti hjn) ha.le
    linarith
  · rw [Set.indicator_of_notMem hx, sub_eq_zero]
    unfold datum
    apply tsum_eq_sum
    intro j hj
    have hjn : n ≤ j := by simpa using hj
    by_contra hne
    have hΦ := right_ne_zero_of_mul hne
    obtain ⟨-, h1⟩ := mem_annulus_of_ne_zero hR (radius_pos hp.sbar_pos hμ (j + 1)) hΦ
    have h2 : radius sbar μ (j + 1) ≤ radius sbar μ (n + 1) := hanti (by omega)
    exact hx (mem_closedBall_zero_iff.mpr (h1.trans h2))

/-- `|T_n| ≤ |1_{B̄_{r_n}} f|` for `n ≥ 1` (on the `n`-th annulus `f = T_n`). -/
theorem term_norm_le (hR : RingFacts χ) (hp : DatumParams A₁ μ sbar)
    (hdisj : ∀ (x : ℂ) (j l : ℕ), j ≠ l → ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) ≠ 0 →
      ringPhi χ (x / ((radius sbar μ (l + 1) : ℝ) : ℂ)) = 0)
    {n : ℕ} (hn : 1 ≤ n) (x : ℂ) :
    ‖amp A₁ μ n * ringPhi χ (x / ((radius sbar μ n : ℝ) : ℂ))‖ ≤
      ‖(closedBall (0 : ℂ) (radius sbar μ n)).indicator (datum χ A₁ μ sbar) x‖ := by
  have hμ : 0 < μ := by linarith [hp.one_lt_μ]
  by_cases hne : amp A₁ μ n * ringPhi χ (x / ((radius sbar μ n : ℝ) : ℂ)) = 0
  · rw [hne, norm_zero]
    exact norm_nonneg _
  have hΦ := right_ne_zero_of_mul hne
  obtain ⟨-, h1⟩ := mem_annulus_of_ne_zero hR (radius_pos hp.sbar_pos hμ n) hΦ
  have hx : x ∈ closedBall (0 : ℂ) (radius sbar μ n) := mem_closedBall_zero_iff.mpr h1
  rw [Set.indicator_of_mem hx]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e : datum χ A₁ μ sbar x =
      amp A₁ μ (m + 1) * ringPhi χ (x / ((radius sbar μ (m + 1) : ℝ) : ℂ)) := by
    unfold datum
    apply tsum_eq_single m
    intro j hj
    rw [hdisj x m j (Ne.symm hj) hΦ, mul_zero]
  rw [e]

/-- `f^{(n)} = S_n - T_n + U_n` for `n ≥ 1`. -/
theorem approxDatum_eq {n : ℕ} (hn : 1 ≤ n) (x : ℂ) :
    approxDatum χ A₁ μ sbar κs n x =
      ∑ j ∈ Finset.range n, amp A₁ μ (j + 1) * ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) -
        amp A₁ μ n * ringPhi χ (x / ((radius sbar μ n : ℝ) : ℂ)) +
        amp A₁ μ n * OneRing.PhiSeed χ κs (x / ((radius sbar μ n : ℝ) : ℂ)) := by
  rw [approxDatum_split χ A₁ μ sbar κs hn le_rfl x, Finset.Ioc_self, Finset.sum_empty, add_zero,
    approxTerm_self]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ]
  have e : ∑ i ∈ Finset.Ico 1 (m + 1), approxTerm χ A₁ μ sbar κs (m + 1) i x =
      ∑ j ∈ Finset.range m, amp A₁ μ (j + 1) * ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < m := Finset.mem_range.mp hj
    rw [approxTerm_of_lt (by omega) (by omega), add_comm 1 j]
  rw [e]
  ring

/-- **`f^{(n)} → f` in `L^q`** for every `q ∈ [1, ∞)` (`06_datum.tex:101-113`). -/
theorem tendsto_eLpNorm_approxDatum_sub (hR : RingFacts χ) (hp : DatumParams A₁ μ sbar)
    (hdisj : ∀ (x : ℂ) (j l : ℕ), j ≠ l → ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) ≠ 0 →
      ringPhi χ (x / ((radius sbar μ (l + 1) : ℝ) : ℂ)) = 0)
    (hF : ∀ q : ℝ, 1 ≤ q → MemLp (datum χ A₁ μ sbar) (ENNReal.ofReal q) volume)
    (hY : MeasurePreserving (OneRing.seedFlow χ κs) volume volume) {q : ℝ} (hq : 1 ≤ q) :
    Tendsto (fun n => eLpNorm (approxDatum χ A₁ μ sbar κs n - datum χ A₁ μ sbar)
      (ENNReal.ofReal q) volume) atTop (𝓝 0) := by
  set p := ENNReal.ofReal q with hpdef
  have hp1 : 1 ≤ p := ENNReal.one_le_ofReal.mpr hq
  have hptop : p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hμ : 0 < μ := by linarith [hp.one_lt_μ]
  have hμ2 : 1 ≤ 2 * μ := by linarith [hp.one_lt_μ]
  have ha1 : a < 1 := hR.2.2.2.2.2.2.2
  have hs1 : sbar < 1 := lt_of_le_of_lt hp.sbar_le (by linarith)
  have hFq := hF q hq
  set F := datum χ A₁ μ sbar with hFdef
  set g : ℕ → ℂ → ℝ := fun m => (closedBall (0 : ℂ) (radius sbar μ m)).indicator F with hgdef
  have hg : Tendsto (fun m => eLpNorm (g m) p volume) atTop (𝓝 0) :=
    tendsto_eLpNorm_indicator_closedBall hp1 hptop hFq (tendsto_radius hp.sbar_pos hs1 hμ2)
  have hg1 : Tendsto (fun m => eLpNorm (g (m + 1)) p volume) atTop (𝓝 0) :=
    hg.comp (tendsto_add_atTop_nat 1)
  have hΦc : Continuous (ringPhi χ) := hR.1.continuous
  have hbound : ∀ n, 1 ≤ n → eLpNorm (approxDatum χ A₁ μ sbar κs n - F) p volume ≤
      eLpNorm (g n) p volume + eLpNorm (g n) p volume + eLpNorm (g (n + 1)) p volume := by
    intro n hn
    set T : ℂ → ℝ := fun x => amp A₁ μ n * ringPhi χ (x / ((radius sbar μ n : ℝ) : ℂ)) with hT
    set U : ℂ → ℝ := fun x => amp A₁ μ n * OneRing.PhiSeed χ κs (x / ((radius sbar μ n : ℝ) : ℂ))
      with hU
    have hdec : approxDatum χ A₁ μ sbar κs n - F = U - T - g (n + 1) := by
      funext x
      simp only [Pi.sub_apply, U, T, g]
      rw [← datum_sub_partialSum hR hp hn x, approxDatum_eq hn x]
      ring
    have hDc : Continuous (fun x : ℂ => x / ((radius sbar μ n : ℝ) : ℂ)) :=
      continuous_id.div_const _
    have hTm : AEStronglyMeasurable T volume :=
      (continuous_const.mul (hΦc.comp hDc)).aestronglyMeasurable
    have hUm : AEStronglyMeasurable U volume :=
      (measurable_const.mul (hΦc.measurable.comp (hY.measurable.comp hDc.measurable))).aestronglyMeasurable
    have hgm : AEStronglyMeasurable (g (n + 1)) volume :=
      hFq.aestronglyMeasurable.indicator measurableSet_closedBall
    have hUT : eLpNorm U p volume = eLpNorm T p volume :=
      eLpNorm_comp_mp_div (g := fun y => amp A₁ μ n * ringPhi χ y) (continuous_const.mul hΦc) hY
        (radius_pos hp.sbar_pos hμ n).ne' p
    have hTg : eLpNorm T p volume ≤ eLpNorm (g n) p volume :=
      eLpNorm_mono fun x => term_norm_le hR hp hdisj hn x
    rw [hdec]
    calc eLpNorm (U - T - g (n + 1)) p volume
        ≤ eLpNorm (U - T) p volume + eLpNorm (g (n + 1)) p volume :=
          eLpNorm_sub_le (hUm.sub hTm) hgm hp1
      _ ≤ eLpNorm U p volume + eLpNorm T p volume + eLpNorm (g (n + 1)) p volume := by
          gcongr
          exact eLpNorm_sub_le hUm hTm hp1
      _ ≤ _ := by
          rw [hUT]
          gcongr
  have hup : Tendsto (fun n => eLpNorm (g n) p volume + eLpNorm (g n) p volume +
      eLpNorm (g (n + 1)) p volume) atTop (𝓝 0) := by
    simpa using (hg.add hg).add hg1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hbound n hn

end NonUniqueEuler.Datum.AdmH
