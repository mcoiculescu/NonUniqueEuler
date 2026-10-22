import NonUniqueEuler.H.Sec11.Geometry.Induction
import NonUniqueEuler.I.Sec11.Stop
import NonUniqueEuler.I.Sec7.FieldBound

/-!
# Proof: `lem:geometry` (localization at equal times gives confinement on the windows)

Proof of the interface `I/Sec11/Geometry.lean` (`11_bootstrap.tex:121-144`, proof `:146-218`).
The downward induction on the level (the claim on `D_{j+1}` and conclusion (a)) is in
`H/Sec11/Geometry/Induction.lean` (`GeometryH.inner_of_mem`), with the window length in
`H/Sec11/Geometry/Window.lean` and the elementary facts in `H/Sec11/Geometry/Basic.lean`. Here:
(b) from (BA1), `quiet_of_lt` and `phase_trichotomy` (the remarks after `def:stop`), the inclusion
`N♭_i ⊂ ℝ² ∖ B_{6r_j}` for `i < j`, the induction, and `lem:field-bound` with (B9); (c) from (BA1),
(b) and (a).

Uses (as black boxes): `Relay.phase_trichotomy`, `Relay.quiet_of_lt` (`I/Sec11/Stop.lean`),
`Rings.field_bound` (`I/Sec7/FieldBound.lean`), and through the helpers `Rings.confine`,
`Rings.window_length`, `Relay.detuning`, `Rings.sk_small`, `Approx.clock_order`,
`Relay.standing_levels`, `Relay.constants_pos`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- **`lem:geometry`** (`11_bootstrap.tex:121-144`). Assume (N), (P0)–(P6), `t ∈ [0, T_end]`,
(BA1) on `[0, t]` and `κ♯_k ≥ K_lo s_k^{m+2}` for every level `k < n` with `t♯_k < t`
(`S.GeometryHyp t`). Then the conclusions (a)–(c) hold (`S.GeometryConcl t`). -/
theorem geometry (S : Standing) (hS : S.Holds) (hL : S.ParamLists) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) S.P.Tend) (h : S.GeometryHyp t) : S.GeometryConcl t := by
  have hall : ∀ {j : ℕ}, j ∈ Finset.Icc 1 S.P.n →
      (∀ t' ∈ Icc (0 : ℝ) t, ¬ S.P.DebrisAt j t' → S.P.HInDefined j t') ∧
        (j < S.P.n → S.P.ClockUpTo (j + 1) → S.P.T (j + 1) ≤ t → S.GeometryWindow j t) :=
    fun hj => GeometryH.inner_of_mem hS hL ht h hj
  -- (b), `11_bootstrap.tex:151-157`, `:202-212`
  have hring : ∀ t' ∈ Icc (0 : ℝ) t, ∀ j ∈ Finset.Icc 1 S.P.n, ¬ S.P.DebrisAt j t' →
      S.GeometryRing j t' := by
    intro t' ht' j hj hd
    have hj' := Finset.mem_Icc.1 hj
    have hTend : t' ≤ S.P.Tend := ht'.2.trans ht.2
    have hqa : S.P.QuietAt j t' ∨ S.P.ActiveAt j t' := by
      rcases phase_trichotomy S hTend hj with hq | ha | hdb
      · exact Or.inl hq
      · exact Or.inr ha
      · exact absurd hdb hd
    have hq := quiet_of_lt S hS hj hqa
    have hout : ∀ i ∈ Finset.Ico 1 j, S.P.St i t' ⊆ S.P.Nflatk i ∧
        S.P.Nflatk i ⊆ (ball (0 : ℂ) (6 * S.P.r j))ᶜ := by
      intro i hi
      have hi' := Finset.mem_Ico.1 hi
      have himem : i ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hi'.1, by omega⟩
      exact ⟨h.ba1 t' ht' i himem (GeometryH.not_debris_of_quiet hS himem (hq i hi)),
        GeometryH.Nflatk_subset_compl_ball hS hi'.1 hi'.2⟩
    have hin : S.P.HInDefined j t' := (hall hj).1 t' ht' hd
    have hHout : S.P.HOutDefined j t' := by
      intro i hi
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
      exact (hout i hi).2 ((hout i hi).1 hx.1) hx.2
    refine ⟨fun i hi => ⟨hq i hi, (hout i hi).1, (hout i hi).2⟩, hin, ⟨hin, hHout⟩,
      fun hjn => ?_⟩
    have hMh : 1 ≤ S.Mh := by rw [Standing.Mh_def]; omega
    have hFB := Rings.fieldBoundConst_spec (Rings.field_bound S.P.χ hS.admissible hS.hN S.Mh hMh)
    have hb := (hFB.bound S.P rfl hS.valid hS.sbar_pow_le j hj'.1 hjn t' ht'.1
      (fun i hi => (hout i hi).1.trans (GeometryH.Nflatk_subset_Nk hS i)) hHout hin).2.2
    exact hb.trans hL.sbar.b9_eta
  refine ⟨?_, hring, ?_⟩
  -- (a)
  · intro k hk hc hT
    have hk' := Finset.mem_Ico.1 hk
    exact (hall (Finset.mem_Icc.2 ⟨hk'.1, hk'.2.le⟩)).2 hk'.2 hc hT
  -- (c), `11_bootstrap.tex:213-218`
  · intro t' ht'
    refine ⟨?_, ?_⟩
    · intro i hi hle
      have hd : ¬ S.P.DebrisAt i t' := fun hd => absurd (hle hd.1) (not_le.2 hd.2)
      exact (h.ba1 t' ht' i hi hd).trans (GeometryH.Nflatk_subset_Nk hS i)
    · intro j hj hq
      have hd := GeometryH.not_debris_of_quiet hS hj hq
      have hr := hring t' ht' j hj hd
      refine ⟨hr.2.2.1.2, hr.2.1, fun hc hT => ?_⟩
      have hj' := Finset.mem_Icc.1 hj
      rcases Nat.lt_or_ge j S.P.n with hjn | hjn
      · have he : t' ≤ S.P.endW j := by
          rcases hq with hq | hq
          · exact absurd hc hq
          · exact hq.trans (GeometryH.tsh_le_endW hS hj)
        exact (((hall hj).2 hjn hc (hT.trans ht'.2)).2 t' ⟨hT, le_min ht'.2 he⟩).1
      · have hjeq : j = S.P.n := le_antisymm hj'.2 hjn
        rw [hjeq, Approx.D_succ_n]
        exact Set.empty_subset _

end Relay

end NonUniqueEuler
