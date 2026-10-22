import NonUniqueEuler.H.Sec11.BootContinuity.Basic
import NonUniqueEuler.I.Sec11.BootStart
import NonUniqueEuler.I.Sec11.BootSteps
import NonUniqueEuler.I.Sec11.Geometry
import NonUniqueEuler.I.Sec11.BA
import NonUniqueEuler.I.Sec11.ContinuityProps
import NonUniqueEuler.I.Sec6.FieldContinuity

/-!
# Helpers for `P/Sec11/BootContinuity`: the limit step `t_* ∈ 𝓑`

Step 7 of the proof of `prop:bootstrap`, first part (`11_bootstrap.tex:552-574`): if (BA°) holds at
every time of `[0, t)`, `0 < t ≤ T_end`, then (BA°)(t) holds (`boot_limit`).
* (BA1) at `t`: `N♭_j` is closed and `s ↦ Φ_s(y)` is continuous (`limit_ba1`, via
  `flow_image_eventually` applied to a point);
* `lem:geometry` at `t`, with the amplitudes from Step 3 at the levels with `t♯_k < t`
  (`limit_geometry`);
* (BA2) at `t`: `h_j` is defined on `[0, t]` by `lem:geometry`(b), `maj_j` is continuous
  (`maj_continuous`) (`limit_ba2`);
* (BA3) at `t ≠ t♯_k`: `w_k` is continuous in `H^s` on `[t♯_k, t]` (`w_continuous`), the envelope
  `2C₂â_k` is continuous and nonnegative, and `ρ̂_k(v) ≤ ρ̂_k(u) + ε` for `v` just to the left of
  `u = A_k(t - t♯_k) > 0` (`rhoHat_semicontinuous`) (`limit_ba3`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Relay

namespace BootContinuityH

open RingData Datum

variable (S : Standing)

/-- **(BA1) at the limit time** (`11_bootstrap.tex:556-559`): `N♭_j` is closed and `s ↦ Φ_s(y)` is
continuous, so (BA1) at the times of `[0, t)` gives (BA1) at `t`. -/
theorem limit_ba1 (hS : S.Holds) {t : ℝ} (ht : 0 < t)
    (h : ∀ s ∈ Ico (0 : ℝ) t, S.BA1At S.P.Nflatk s) : S.BA1At S.P.Nflatk t := by
  intro j hj hnd y hy
  obtain ⟨x, hx, rfl⟩ := hy
  by_contra hout
  have hU : IsOpen (S.P.Nflatk j)ᶜ := (isClosed_Nflatk S j).isOpen_compl
  have hsub : S.P.flow t '' {x} ⊆ (S.P.Nflatk j)ᶜ := by
    rintro _ ⟨x', hx', rfl⟩
    rw [mem_singleton_iff.1 hx']
    exact hout
  have hev := Datum.Approx.flow_image_eventually S.P hS.valid hS.hN isCompact_singleton hU
    ht.le hsub
  have hmono : 𝓝[Ico (0 : ℝ) t] t ≤ 𝓝[Ici 0] t := nhdsWithin_mono _ Ico_subset_Ici_self
  have : (𝓝[Ico (0 : ℝ) t] t).NeBot := by
    rw [nhdsWithin_Ico_eq_nhdsLT ht]
    infer_instance
  obtain ⟨s, hs1, hs2⟩ := ((hev.filter_mono hmono).and self_mem_nhdsWithin).exists
  have hnd' : ¬ S.P.DebrisAt j s := fun hd => hnd ⟨hd.1, hd.2.trans hs2.2⟩
  exact hs1 (mem_image_of_mem _ (mem_singleton x)) (h s hs2 j hj hnd' (mem_image_of_mem _ hx))

/-- **`lem:geometry` at the limit time** (`11_bootstrap.tex:559-562`): (BA1) on `[0, t]`, and every
level `k < n` with `t♯_k < t` has `t♯_k ∈ 𝓑`, so Step 3 gives `κ♯_k ≥ K_lo s_k^{m+2}`. -/
theorem limit_geometry (hS : S.Holds) (hL : S.ParamLists) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) S.P.Tend)
    (hba1 : ∀ s ∈ Icc (0 : ℝ) t, S.BA1At S.P.Nflatk s)
    (h : ∀ s ∈ Ico (0 : ℝ) t, S.BAcirc s) : S.GeometryConcl t := by
  refine geometry S hS hL ht ⟨hba1, fun k hk hc hlt => ?_⟩
  have hk' : k ∈ Finset.Icc 1 S.P.n := by
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
    exact Finset.mem_Icc.2 ⟨h1, h2.le⟩
  have h0 : 0 ≤ S.P.tsh k := tsh_nonneg_of_succ S hS hk' hc
  have hBA : S.BAcirc (S.P.tsh k) := h _ ⟨h0, hlt⟩
  exact ((boot_steps S hS hL ⟨h0, hlt.le.trans ht.2⟩ (boot_start S hS hL) hBA).handoff k hk hc
    le_rfl).amp_lo

/-- **(BA2) at the limit time** (`11_bootstrap.tex:562-564`): `h_j` is defined on `[0, t]`
(`lem:geometry`(b)), so `maj_j` is continuous there and the bound passes to the limit. -/
theorem limit_ba2 (hS : S.Holds) {t : ℝ} (ht : 0 < t) (hgeom : S.GeometryConcl t)
    (h : ∀ s ∈ Ico (0 : ℝ) t, S.BA2At (2 * S.Abar) s) : S.BA2At (2 * S.Abar) t := by
  intro j hj hq
  obtain ⟨hj1, hjn⟩ := Finset.mem_Ico.1 hj
  have hj' : j ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hj1, hjn.le⟩
  have hdef : ∀ t'' ∈ Icc (0 : ℝ) t, S.P.HDefined j t'' := fun t'' ht'' =>
    (hgeom.ring t'' ht'' j hj' (not_debris_of_quiet S hS hj' (quietAt_anti S hq ht''.2))).2.2.1
  refine ⟨hdef, ?_⟩
  have hcont := (S.P.maj_continuous hS.valid hS.hN hj1 hjn.le ht.le S.Mh).1 hdef
  have hA := hS.valid.A_pos j
  have hg : ContinuousOn (fun s => S.maj j (S.P.A j * s)) (Icc 0 t) :=
    hcont.comp (continuous_const.mul continuous_id).continuousOn
      (fun s hs => ⟨mul_nonneg hA.le hs.1, mul_le_mul_of_nonneg_left hs.2 hA.le⟩)
  exact le_of_forall_Ico (f := fun s => S.maj j (S.P.A j * s)) ht ((hg t ⟨ht.le, le_rfl⟩).mono Ico_subset_Icc_self)
    (fun s hs => (h s hs j hj (quietAt_anti S hq hs.2.le)).2)

/-- **(BA3) at the limit time** (`11_bootstrap.tex:564-572`), for a ring `k` with `t ≠ t♯_k`:
`w_k` is continuous on `[t♯_k, t]` and `R_k(u) = 2C₂â_k(u)(1 + ρ̂_k(u))` satisfies
`R_k(u_*) ≥ limsup_{u ↑ u_*} R_k(u)` (`rhoHat_semicontinuous`). -/
theorem limit_ba3 (hS : S.Holds) {t : ℝ}
    (hba1 : ∀ s ∈ Icc (0 : ℝ) t, S.BA1At S.P.Nflatk s)
    (h : ∀ s ∈ Ico (0 : ℝ) t, ∀ k ∈ Finset.Icc 1 S.P.n, s ≠ S.P.tsh k →
      S.BA3At (2 * S.C2) k s)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n) (hne : t ≠ S.P.tsh k) :
    S.BA3At (2 * S.C2) k t := by
  rintro ⟨hc, hts, htT⟩
  have hlt : S.P.tsh k < t := lt_of_le_of_ne hts (Ne.symm hne)
  have h0 : 0 ≤ S.P.tsh k := tsh_nonneg_of_clock S hS (Finset.mem_Icc.1 hk).1 hc
  have hpd : ∀ s ∈ Icc (S.P.tsh k) t, S.P.PertDefined k s := fun s hs =>
    pertDefined_of_BA1 S (hba1 s ⟨h0.trans hs.1, hs.2⟩) k hk
      (fun hd => absurd (hd.2.trans_le (hs.2.trans htT)) (lt_irrefl _))
  have hF := (S.P.w_continuous hS.valid hS.hN hk h0 hpd S.s).2.2
  have hFt : Tendsto (fun s => Sob.normH S.s (S.P.w k s)) (𝓝[<] t)
      (𝓝 (Sob.normH S.s (S.P.w k t))) := by
    have hle : 𝓝[<] t ≤ 𝓝[Icc (S.P.tsh k) t] t := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hlt]
      exact nhdsWithin_mono _ Ioo_subset_Icc_self
    exact (hF t ⟨hlt.le, le_rfl⟩).tendsto.mono_left hle
  have hu : 0 < S.P.activeTime k t := by
    have := activeTime_lt_activeTime S hS k hlt
    rwa [Datum.Approx.activeTime_tsh] at this
  have hρ := (rhoHat_semicontinuous (sigma_gt S hS hk) S.one_le_C0).2 _ hu
  have hat : Tendsto (S.P.activeTime k) (𝓝[<] t) (𝓝[<] (S.P.activeTime k t)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((continuous_activeTime S k).tendsto t).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact activeTime_lt_activeTime S hS k hs
  set a : ℝ → ℝ := fun s => 2 * S.C2 * S.ahatK k (S.P.activeTime k s) with ha_def
  set ρ : ℝ := S.rhoHatK S.C0 k (S.P.activeTime k t) with hρ_def
  have ha_cont : Continuous a := continuous_envelope S k
  have key : ∀ ε : ℝ, 0 < ε →
      Sob.normH S.s (S.P.w k t) ≤ a t * (1 + ρ) + a t * ε := by
    intro ε hε
    have hev : ∀ᶠ s in 𝓝[<] t, Sob.normH S.s (S.P.w k s) ≤ a s * (1 + ρ + ε) := by
      filter_upwards [hat.eventually (hρ ε hε), Ioo_mem_nhdsLT hlt] with s hs1 hs2
      have hb := h s ⟨h0.trans hs2.1.le, hs2.2⟩ k hk (ne_of_gt hs2.1)
        ⟨hc, hs2.1.le, hs2.2.le.trans htT⟩
      have hs1' : S.rhoHatK S.C0 k (S.P.activeTime k s) ≤ ρ + ε := hs1
      calc Sob.normH S.s (S.P.w k s)
          ≤ a s * (1 + S.rhoHatK S.C0 k (S.P.activeTime k s)) := hb
        _ ≤ a s * (1 + ρ + ε) := by
          apply mul_le_mul_of_nonneg_left _ (envelope_nonneg S hS k s)
          linarith
    have hlim : Tendsto (fun s => a s * (1 + ρ + ε)) (𝓝[<] t) (𝓝 (a t * (1 + ρ + ε))) :=
      ((ha_cont.tendsto t).mono_left nhdsWithin_le_nhds).mul_const _
    have := le_of_tendsto_of_tendsto hFt hlim hev
    linarith
  show Sob.normH S.s (S.P.w k t) ≤ a t * (1 + ρ)
  exact le_of_forall_eps (envelope_nonneg S hS k t) key

/-- **The limit step of Step 7** (`11_bootstrap.tex:552-574`): if (BA°) holds at every time of
`[0, t)`, `0 < t ≤ T_end`, then (BA°)(t) holds. -/
theorem boot_limit (hS : S.Holds) (hL : S.ParamLists) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) S.P.Tend) (h : ∀ s ∈ Ico (0 : ℝ) t, S.BAcirc s) : S.BAcirc t := by
  have hba1t : S.BA1At S.P.Nflatk t :=
    limit_ba1 S hS ht.1 (fun s hs => (h s hs).ba1 s ⟨hs.1, le_rfl⟩)
  have hba1 : ∀ s ∈ Icc (0 : ℝ) t, S.BA1At S.P.Nflatk s := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with he | hlt
    · rw [he]
      exact hba1t
    · exact (h s ⟨hs.1, hlt⟩).ba1 s ⟨hs.1, le_rfl⟩
  have hgeom : S.GeometryConcl t := limit_geometry S hS hL ⟨ht.1.le, ht.2⟩ hba1 h
  refine ⟨hba1, ?_, ?_⟩
  · intro s hs
    rcases eq_or_lt_of_le hs.2 with he | hlt
    · rw [he]
      exact limit_ba2 S hS ht.1 hgeom (fun s' hs' => (h s' hs').ba2 s' ⟨hs'.1, le_rfl⟩)
    · exact (h s ⟨hs.1, hlt⟩).ba2 s ⟨hs.1, le_rfl⟩
  · intro s hs k hk hne
    rcases eq_or_lt_of_le hs.2 with he | hlt
    · rw [he] at hne ⊢
      exact limit_ba3 S hS hba1
        (fun s' hs' k' hk' hne' => (h s' hs').ba3 s' ⟨hs'.1, le_rfl⟩ k' hk' hne') hk hne
    · exact (h s ⟨hs.1, hlt⟩).ba3 s ⟨hs.1, le_rfl⟩ k hk hne

end BootContinuityH

end Relay

end NonUniqueEuler
