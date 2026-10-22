import NonUniqueEuler.H.Sec11.BootContinuity.Basic
import NonUniqueEuler.I.Sec11.BootStart
import NonUniqueEuler.I.Sec11.BootSteps
import NonUniqueEuler.I.Sec11.Geometry
import NonUniqueEuler.I.Sec11.BA
import NonUniqueEuler.I.Sec11.ContinuityProps
import NonUniqueEuler.I.Sec6.FieldContinuity
import NonUniqueEuler.I.Sec6.RegionsBasic

/-!
# Helpers for `P/Sec11/BootContinuity`: the extension step `t_* = T_end`

Step 7 of the proof of `prop:bootstrap`, first part (`11_bootstrap.tex:576-591`): if (BA°) holds at
every time of `[0, t]`, `0 ≤ t < T_end`, then (BA°) holds on `(t, t + δ]` for some `δ > 0`
(`boot_extend`). By Steps 1–6, (BA*)(t) holds; then
* (BA1): each `S_j(t)` is a compact subset of `𝒩_j ⊂ int N♭_j`, and the flow is continuous
  (`ext_ba1`, via `flow_image_eventually`);
* `δ₁ > 0` with no phase boundary `t♯_i`, `T_i` in `(t, t + δ₁]`, `t + δ₁ ≤ T_end`, and (BA1) on
  `(t, t + δ₁]`; `lem:geometry` at `t + δ₁` (`ext_geometry`);
* (BA2): `maj_j(A_jt) ≤ Āε_j < 2Āε_j` and `maj_j` is continuous (`ext_ba2_ring`);
* (BA3): `‖w_k(t)‖_{H^s} ≤ C₂â_k(1 + ρ̂_k) < R_k` at `u_*`, `w_k` is continuous and `R_k` is
  right-continuous (`ext_ba3_ring`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Relay

namespace BootContinuityH

open RingData Datum

variable (S : Standing)

/-- **(BA1) just after `t`** (`11_bootstrap.tex:580-582`): `S_j(t) ⊂ 𝒩_j ⊂ int N♭_j` for the rings
not debris at `t`, `S_j` is compact and the flow is continuous; a ring debris at `t` stays debris. -/
theorem ext_ba1 (hS : S.Holds) {t : ℝ} (ht : 0 ≤ t) (hstar : S.BA1At S.P.Nnk t)
    (hroom : ∀ j ∈ Finset.Icc 1 S.P.n, S.P.Nnk j ⊆ interior (S.P.Nflatk j)) :
    ∀ᶠ s in 𝓝[>] t, S.BA1At S.P.Nflatk s := by
  have hle : 𝓝[>] t ≤ 𝓝[Ici 0] t := nhdsWithin_mono _ (fun s hs => ht.trans (le_of_lt hs))
  show ∀ᶠ s in 𝓝[>] t, ∀ j ∈ Finset.Icc 1 S.P.n, ¬ S.P.DebrisAt j s → S.P.St j s ⊆ S.P.Nflatk j
  rw [Filter.eventually_all_finset]
  intro j hj
  by_cases hd : S.P.DebrisAt j t
  · filter_upwards [self_mem_nhdsWithin] with s hs hnd
    exact absurd ⟨hd.1, hd.2.trans hs⟩ hnd
  · have hK := ((S.P.regions_basic_one hS.valid hS.hN).1 j hj).1
    have hsub : S.P.flow t '' S.P.S j ⊆ interior (S.P.Nflatk j) :=
      (hstar j hj hd).trans (hroom j hj)
    have hev := S.P.flow_image_eventually hS.valid hS.hN hK isOpen_interior ht hsub
    filter_upwards [hev.filter_mono hle] with s hs _
    exact hs.trans interior_subset

/-- No phase boundary `b > t` (`b = t♯_i` or `T_i`) lies just after `t`. -/
theorem ext_boundaries {t : ℝ} (b : ℕ → ℝ) (I : Finset ℕ) :
    ∀ᶠ s in 𝓝[>] t, ∀ i ∈ I, t < b i → s < b i := by
  rw [Filter.eventually_all_finset]
  intro i _
  by_cases hti : t < b i
  · filter_upwards [(eventually_lt_nhds hti).filter_mono nhdsWithin_le_nhds] with s hs _
    exact hs
  · exact Eventually.of_forall fun s h' => absurd h' hti

/-- **`lem:geometry` at `t + δ₁`** (`11_bootstrap.tex:582-584`): (BA1) on `[0, t + δ₁]`, and no
`t♯_k` lies in `(t, t + δ₁]`, so the levels with `t♯_k < t + δ₁` have `t♯_k ≤ t` and Step 3 at
`t♯_k` (from Steps 1–6 at `t`) gives `κ♯_k ≥ K_lo s_k^{m+2}`. -/
theorem ext_geometry (hS : S.Holds) (hL : S.ParamLists) {t δ₁ : ℝ} (ht : 0 ≤ t)
    (hδ₁ : 0 < δ₁) (hTend : t + δ₁ ≤ S.P.Tend) (hsteps : S.BootStepsConcl t)
    (hGtsh : ∀ i ∈ Finset.Icc 1 S.P.n, t < S.P.tsh i → t + δ₁ < S.P.tsh i)
    (hba1 : ∀ s ∈ Icc (0 : ℝ) (t + δ₁), S.BA1At S.P.Nflatk s) :
    S.GeometryConcl (t + δ₁) := by
  refine geometry S hS hL ⟨by linarith, hTend⟩ ⟨hba1, fun k hk hc hlt => ?_⟩
  have hk' : k ∈ Finset.Icc 1 S.P.n := by
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
    exact Finset.mem_Icc.2 ⟨h1, h2.le⟩
  have hle : S.P.tsh k ≤ t := by
    by_contra hlt'
    have := hGtsh k hk' (lt_of_not_ge hlt')
    linarith
  exact (hsteps.handoff k hk hc hle).amp_lo

/-- **(BA2) just after `t` for the ring `j < n`** (`11_bootstrap.tex:582-586`): if ring `j` is quiet
up to `t + δ₁`, `h_j` is defined on `[0, t + δ₁]` (`lem:geometry`(b)), `maj_j` is continuous and
`maj_j(A_jt) ≤ Āε_j < 2Āε_j`; otherwise ring `j` is not quiet after `t`. -/
theorem ext_ba2_ring (hS : S.Holds) {t δ₁ : ℝ} (ht : 0 ≤ t) (hδ₁ : 0 < δ₁)
    (hGtsh : ∀ i ∈ Finset.Icc 1 S.P.n, t < S.P.tsh i → t + δ₁ < S.P.tsh i)
    (hgeom : S.GeometryConcl (t + δ₁)) (hstar : S.BA2At S.Abar t)
    (hroom : ∀ j ∈ Finset.Ico 1 S.P.n, S.Abar * S.P.eps j < 2 * S.Abar * S.P.eps j)
    {j : ℕ} (hj : j ∈ Finset.Ico 1 S.P.n) :
    ∀ᶠ s in 𝓝[>] t, s ≤ t + δ₁ → S.P.QuietAt j s →
      (∀ t'' ∈ Icc (0 : ℝ) s, S.P.HDefined j t'') ∧
        S.maj j (S.P.A j * s) ≤ 2 * S.Abar * S.P.eps j := by
  obtain ⟨hj1, hjn⟩ := Finset.mem_Ico.1 hj
  have hj' : j ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hj1, hjn.le⟩
  by_cases hq : S.P.QuietAt j (t + δ₁)
  · have hdef : ∀ t'' ∈ Icc (0 : ℝ) (t + δ₁), S.P.HDefined j t'' := fun t'' ht'' =>
      (hgeom.ring t'' ht'' j hj'
        (not_debris_of_quiet S hS hj' (quietAt_anti S hq ht''.2))).2.2.1
    have hqt : S.P.QuietAt j t := quietAt_anti S hq (by linarith)
    have hlt : S.maj j (S.P.A j * t) < 2 * S.Abar * S.P.eps j :=
      lt_of_le_of_lt (hstar j hj hqt).2 (hroom j hj)
    have hcont := (S.P.maj_continuous hS.valid hS.hN hj1 hjn.le (by linarith : 0 ≤ t + δ₁)
      S.Mh).1 hdef
    have hA := hS.valid.A_pos j
    have hg : ContinuousOn (fun s => S.maj j (S.P.A j * s)) (Icc 0 (t + δ₁)) :=
      hcont.comp (continuous_const.mul continuous_id).continuousOn
        (fun s hs => ⟨mul_nonneg hA.le hs.1, mul_le_mul_of_nonneg_left hs.2 hA.le⟩)
    have hmem : Icc 0 (t + δ₁) ∈ 𝓝[≥] t :=
      mem_of_superset (Icc_mem_nhdsGE (by linarith : t < t + δ₁)) (Icc_subset_Icc_left ht)
    have hgt : ContinuousWithinAt (fun s => S.maj j (S.P.A j * s)) (Ici t) t :=
      (hg t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin hmem
    have hev := (Filter.Tendsto.eventually_lt_const hlt hgt.tendsto).filter_mono
      (nhdsWithin_mono _ Ioi_subset_Ici_self)
    filter_upwards [hev] with s hs hsδ _
    exact ⟨fun t'' ht'' => hdef t'' ⟨ht''.1, ht''.2.trans hsδ⟩, hs.le⟩
  · simp only [Datum.Approx.QuietAt, not_or, not_not, not_le] at hq
    have htsh : S.P.tsh j ≤ t := by
      by_contra hlt'
      have := hGtsh j hj' (lt_of_not_ge hlt')
      linarith [hq.2]
    filter_upwards [self_mem_nhdsWithin] with s hs _ hqs
    exfalso
    rcases hqs with h1 | h1
    · exact h1 hq.1
    · have hs' : t < s := hs
      linarith

/-- **(BA3) just after `t` for the ring `k`** (`11_bootstrap.tex:586-589`): if ring `k` is active at
`t` with `t < T_k`, then `‖w_k(t)‖_{H^s} ≤ C₂â_k(1 + ρ̂_k) < R_k` at `u_* = A_k(t - t♯_k)`, `w_k` is
continuous on `[t, t + δ₁]` (`w_continuous`) and `R_k` is right-continuous
(`rhoHat_semicontinuous`); otherwise ring `k` is not active on `(t, t + δ₁]`. -/
theorem ext_ba3_ring (hS : S.Holds) {t δ₁ : ℝ} (ht : 0 ≤ t) (hδ₁ : 0 < δ₁)
    (hGtsh : ∀ i ∈ Finset.Icc 1 S.P.n, t < S.P.tsh i → t + δ₁ < S.P.tsh i)
    (hGT : ∀ i ∈ Finset.Icc 1 S.P.n, t < S.P.T i → t + δ₁ < S.P.T i)
    (hba1 : ∀ s ∈ Icc (0 : ℝ) (t + δ₁), S.BA1At S.P.Nflatk s)
    (hstar : ∀ k ∈ Finset.Icc 1 S.P.n, S.BA3At S.C2 k t)
    (hroom : ∀ k ∈ Finset.Icc 1 S.P.n, S.P.ClockUpTo k → ∀ u : ℝ, 0 ≤ u →
      S.C2 * S.ahatK k u * (1 + S.rhoHatK S.C0 k u) <
        2 * S.C2 * S.ahatK k u * (1 + S.rhoHatK S.C0 k u))
    {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n) :
    ∀ᶠ s in 𝓝[>] t, s ≤ t + δ₁ → S.BA3At (2 * S.C2) k s := by
  by_cases hcase : S.P.ActiveAt k t ∧ t < S.P.T k
  · obtain ⟨⟨hc, hts, htT⟩, htT'⟩ := hcase
    have hTδ : t + δ₁ < S.P.T k := hGT k hk htT'
    have hpd : ∀ s ∈ Icc t (t + δ₁), S.P.PertDefined k s := fun s hs =>
      pertDefined_of_BA1 S (hba1 s ⟨ht.trans hs.1, hs.2⟩) k hk
        (fun hd => by linarith [hd.2, hs.2])
    have hF := (S.P.w_continuous hS.valid hS.hN hk ht hpd S.s).2.2
    have hu0 : 0 ≤ S.P.activeTime k t := activeTime_nonneg S hS k hts
    have hmem : Icc t (t + δ₁) ∈ 𝓝[≥] t := Icc_mem_nhdsGE (by linarith)
    have hFt : ContinuousWithinAt (fun s => Sob.normH S.s (S.P.w k s)) (Ici t) t :=
      (hF t ⟨le_rfl, by linarith⟩).mono_of_mem_nhdsWithin hmem
    have hρ := (rhoHat_semicontinuous (sigma_gt S hS hk) S.one_le_C0).1 _ hu0
    have hρt : ContinuousWithinAt (fun s => S.rhoHatK S.C0 k (S.P.activeTime k s)) (Ici t) t :=
      hρ.comp (continuous_activeTime S k).continuousWithinAt
        (fun s hs => activeTime_le_activeTime S hS k hs)
    have hR : ContinuousWithinAt (fun s => 2 * S.C2 * S.ahatK k (S.P.activeTime k s) *
        (1 + S.rhoHatK S.C0 k (S.P.activeTime k s))) (Ici t) t :=
      (continuous_envelope S k).continuousWithinAt.mul (continuousWithinAt_const.add hρt)
    have hlt : Sob.normH S.s (S.P.w k t) < 2 * S.C2 * S.ahatK k (S.P.activeTime k t) *
        (1 + S.rhoHatK S.C0 k (S.P.activeTime k t)) :=
      lt_of_le_of_lt (hstar k hk ⟨hc, hts, htT⟩) (hroom k hk hc _ hu0)
    have hev := (Filter.Tendsto.eventually_lt hFt.tendsto hR.tendsto hlt).filter_mono
      (nhdsWithin_mono _ Ioi_subset_Ici_self)
    filter_upwards [hev] with s hs _ _
    exact hs.le
  · filter_upwards [self_mem_nhdsWithin] with s hs hsδ hact
    exfalso
    apply hcase
    obtain ⟨hc, hts, hsT⟩ := hact
    have hs' : t < s := hs
    have htsh : S.P.tsh k ≤ t := by
      by_contra hlt'
      have := hGtsh k hk (lt_of_not_ge hlt')
      linarith
    exact ⟨⟨hc, htsh, by linarith⟩, by linarith⟩

/-- **The extension step of Step 7** (`11_bootstrap.tex:576-591`): if (BA°) holds at every time of
`[0, t]`, `0 ≤ t < T_end`, then (BA°) holds on `(t, t + δ]` for some `δ > 0`. -/
theorem boot_extend (hS : S.Holds) (hL : S.ParamLists) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) S.P.Tend) (h : ∀ s ∈ Icc (0 : ℝ) t, S.BAcirc s) :
    ∃ δ > 0, ∀ s ∈ Ioc t (t + δ), S.BAcirc s := by
  have hBAt : S.BAcirc t := h t ⟨ht.1, le_rfl⟩
  have hsteps := boot_steps S hS hL ⟨ht.1, ht.2.le⟩ (boot_start S hS hL) hBAt
  have hstar : S.BAstar t := hsteps.ba_star
  have hroom := BAstar_room S hS hL
  -- Step 1: `δ₁` (no phase boundary in `(t, t + δ₁]`, `t + δ₁ ≤ T_end`, (BA1) on `(t, t + δ₁]`)
  obtain ⟨δ₁, hδ₁, hG⟩ : ∃ δ₁ > 0, ∀ s ∈ Ioc t (t + δ₁), s ≤ S.P.Tend ∧
      (∀ i ∈ Finset.Icc 1 S.P.n, t < S.P.tsh i → s < S.P.tsh i) ∧
      (∀ i ∈ Finset.Icc 1 S.P.n, t < S.P.T i → s < S.P.T i) ∧
      S.BA1At S.P.Nflatk s := by
    apply exists_delta_of_eventually
    have e1 : ∀ᶠ s in 𝓝[>] t, s ≤ S.P.Tend :=
      ((eventually_lt_nhds ht.2).filter_mono nhdsWithin_le_nhds).mono fun s hs => hs.le
    have e4 := ext_ba1 S hS ht.1 (hstar.ba1 t ⟨ht.1, le_rfl⟩) hroom.1
    filter_upwards [e1, ext_boundaries S.P.tsh (Finset.Icc 1 S.P.n),
      ext_boundaries S.P.T (Finset.Icc 1 S.P.n), e4] with s h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hGδ := hG (t + δ₁) ⟨by linarith, le_rfl⟩
  have hba1 : ∀ s ∈ Icc (0 : ℝ) (t + δ₁), S.BA1At S.P.Nflatk s := by
    intro s hs
    by_cases hst : s ≤ t
    · exact hBAt.ba1 s ⟨hs.1, hst⟩
    · exact (hG s ⟨lt_of_not_ge hst, hs.2⟩).2.2.2
  have hgeom := ext_geometry S hS hL ht.1 hδ₁ hGδ.1 hsteps hGδ.2.1 hba1
  -- Steps 2–3: (BA2) and (BA3) just after `t`
  have e2 : ∀ᶠ s in 𝓝[>] t, ∀ j ∈ Finset.Ico 1 S.P.n, s ≤ t + δ₁ → S.P.QuietAt j s →
      (∀ t'' ∈ Icc (0 : ℝ) s, S.P.HDefined j t'') ∧
        S.maj j (S.P.A j * s) ≤ 2 * S.Abar * S.P.eps j :=
    (Filter.eventually_all_finset _).2 fun j hj =>
      ext_ba2_ring S hS ht.1 hδ₁ hGδ.2.1 hgeom (hstar.ba2 t ⟨ht.1, le_rfl⟩) hroom.2.1 hj
  have e3 : ∀ᶠ s in 𝓝[>] t, ∀ k ∈ Finset.Icc 1 S.P.n, s ≤ t + δ₁ →
      S.BA3At (2 * S.C2) k s :=
    (Filter.eventually_all_finset _).2 fun k hk =>
      ext_ba3_ring S hS ht.1 hδ₁ hGδ.2.1 hGδ.2.2.1 hba1 (hstar.ba3 t ⟨ht.1, le_rfl⟩) hroom.2.2 hk
  have e5 : ∀ᶠ s in 𝓝[>] t, s ∈ Ioc t (t + δ₁) := Ioc_mem_nhdsGT (by linarith)
  obtain ⟨δ, hδ, hgood⟩ := exists_delta_of_eventually (e2.and (e3.and e5))
  refine ⟨δ, hδ, fun s hs => ⟨fun t' ht' => ?_, fun t' ht' => ?_, fun t' ht' k hk hne => ?_⟩⟩
  · by_cases htt : t' ≤ t
    · exact hBAt.ba1 t' ⟨ht'.1, htt⟩
    · have hgood' := hgood t' ⟨lt_of_not_ge htt, ht'.2.trans hs.2⟩
      exact (hG t' hgood'.2.2).2.2.2
  · by_cases htt : t' ≤ t
    · exact hBAt.ba2 t' ⟨ht'.1, htt⟩
    · have hgood' := hgood t' ⟨lt_of_not_ge htt, ht'.2.trans hs.2⟩
      intro j hj hq
      exact hgood'.1 j hj hgood'.2.2.2 hq
  · by_cases htt : t' ≤ t
    · exact hBAt.ba3 t' ⟨ht'.1, htt⟩ k hk hne
    · have hgood' := hgood t' ⟨lt_of_not_ge htt, ht'.2.trans hs.2⟩
      exact hgood'.2.1 k hk hgood'.2.2.2

end BootContinuityH

end Relay

end NonUniqueEuler
