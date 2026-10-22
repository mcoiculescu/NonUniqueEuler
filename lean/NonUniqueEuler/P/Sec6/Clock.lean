import NonUniqueEuler.Defs.Sec6.All
import NonUniqueEuler.I.Sec4.PropSU
import NonUniqueEuler.I.Sec6.InnerCirc
import NonUniqueEuler.I.Sec6.Adm
import NonUniqueEuler.I.SmoothB.SmoothFlow
import NonUniqueEuler.I.SmoothB.ODE
import NonUniqueEuler.H.Sec6.Clock.FlowAgree
import NonUniqueEuler.H.Sec6.Clock.Core
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Proof of `lem:clock` (order and causality of the phase clock)

Proof of `I/Sec6/Clock.lean` (`06_datum.tex:445-497`).

* (1) `clock_order`: `σ_i > 211/2500 > 0` (`prop:SU`, `Eig.lam_SU`, with `G_i ∈ [0, Ḡ]` from
  `lem:inner-circ` and `P.GSmall`) and `κ♯_i ∈ (0, δ₀)` give `T_i > t♯_i`; `t♯_{i-1} - T_i =
  T_pin/A_i > 0`. The bookkeeping is `ClockH.order_core` (`H/Sec6/Clock/Core.lean`).
* (2) `clock_causal`: the velocities of `ω^{(n)}` and `ω̃` agree on `[0, t̄] × ℝ²`; the flow of
  `ω^{(n)}` is global (`thm:smooth`(4), `Smooth.flow_global`; `f^{(n)}` is a smooth datum by
  `lem:adm`) and the flow equation of `K_BS * ω̃` has maximal solutions (`lem:ode`(i),
  `Smooth.ode_exists_isMaxSol`), so the two flows agree on `[0, t̄]`
  (`Smooth.ClockH.flowOf_eq_of_eqOn_Icc`, `H/Sec6/Clock/FlowAgree.lean`). The downward induction
  is `ClockH.causal_core`.
* (3) `clock_determined`: as in the manuscript, with the least element `i₀` of `𝒥_t` and the
  order of the clock of `ω̃` (`ClockH.order_core` applied to `P.withOm ω̃`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Datum

namespace Approx

open RingData

namespace ClockH

/-- `σ_j > 0` for `j ∈ [1, n]` (`prop:SU` with `G_j ∈ [0, Ḡ]`, `06_datum.tex:463-464`). -/
theorem sigma_pos_of (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    (hG : P.GSmall) {j : ℕ} (hj : j ∈ Finset.Icc 1 P.n) : 0 < P.sigma j := by
  have hG0 := ((inner_circ P hP hN).2.2.1 j hj).1
  have hGle := hG j hj
  have h := (Eig.lam_SU P.χ hP.admissible hN ⟨hG0, hGle⟩ 0).1
  show 0 < (Eig.lam P.χ (P.G j)).re
  linarith

theorem sigma_pos_of_le (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    (hG : P.GSmall) {k : ℕ} (hk : 1 ≤ k) : ∀ j ∈ Finset.Icc k P.n, 0 < P.sigma j := by
  intro j hj
  rw [Finset.mem_Icc] at hj
  exact sigma_pos_of P hP hN hG (Finset.mem_Icc.mpr ⟨hk.trans hj.1, hj.2⟩)

/-- `f^{(n)}` is a datum of `thm:smooth` (`lem:adm`: `f^{(n)} ∈ C_c^∞`). -/
theorem exists_isSmoothDatum (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) :
    ∃ R : ℝ, Smooth.IsSmoothDatum P.f R := by
  obtain ⟨hcd, hcs, -⟩ := (Datum.adm P.χ hP.admissible hN hP.datumParams
    ⟨hP.kseed_pos, hP.kseed_le⟩).1 P.n hP.two_le_n
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).mp hcs.isCompact.isBounded
  exact ⟨R, hcd, hR⟩

/-- **The flows agree on `[0, t̄]`** (`06_datum.tex:475-478`): for a comparison vorticity `ω̃`
equal to `ω^{(n)}` on `[0, t̄] × ℝ²`, the flow of `K_BS * ω̃` is the flow of `v^{(n)}` on
`[0, t̄]`. -/
theorem flow_agree (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {tbar : ℝ}
    (h0 : 0 ≤ tbar) {om' : ℝ → ℂ → ℝ} (hom' : IsComparisonVort om')
    (heq : ∀ t ∈ Icc (0 : ℝ) tbar, om' t = P.om t) :
    ∀ t ∈ Icc (0 : ℝ) tbar, (P.withOm om').flow t = P.flow t := by
  intro t ht
  funext y
  obtain ⟨R, hR⟩ := exists_isSmoothDatum P hP hN
  have hγ : Smooth.IsMaxSol (velocityField P.om) univ 0 y univ
      (fun t => Smooth.flowOf (velocityField P.om) t 0 y) := by
    rw [hP.om_eq]
    exact (Smooth.flow_global hR y).2
  have hcd : ContDiff ℝ 1 (Function.uncurry (velocityField om')) :=
    hom'.velocity_contDiff.of_le (by exact_mod_cast le_top)
  have hex' : ∀ (s : ℝ) (z : ℂ), ∃ (J : Set ℝ) (γ : ℝ → ℂ),
      Smooth.IsMaxSol (velocityField om') univ s z J γ := fun s z =>
    Smooth.ode_exists_isMaxSol isOpen_univ hcd.contDiffOn (mem_univ _)
  have hveq : ∀ s ∈ Icc (0 : ℝ) tbar, velocityField om' s = velocityField P.om s := by
    intro s hs
    funext x
    simp only [velocityField, heq s hs]
  exact Smooth.ClockH.flowOf_eq_of_eqOn_Icc h0 hγ hex' hveq ht

end ClockH

/-- **`lem:clock`(1)** (`06_datum.tex:449-450`): if `G_k ≤ G₁` for all levels and the clock is
defined up to level `k ≥ 1`, then `t♯_i < T_i` for `i ∈ [k,n]` and `T_i < t♯_{i-1}` for
`i ∈ [k,n]`, `i ≥ 2`; hence `T_j < t♯_i` for `k ≤ i < j ≤ n`, and `0 ≤ t♯_i` for `i ∈ [k,n]`
(`t♯_n = 0` is `tsh_n`). -/
theorem clock_order (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall)
    {k : ℕ} (hk : 1 ≤ k) (hc : P.ClockUpTo k) :
    (∀ i ∈ Finset.Icc k P.n, P.tsh i < P.T i) ∧
    (∀ i ∈ Finset.Icc k P.n, 2 ≤ i → P.T i < P.tsh (i - 1)) ∧
    (∀ i j : ℕ, k ≤ i → i < j → j ≤ P.n → P.T j < P.tsh i) ∧
    (∀ i ∈ Finset.Icc k P.n, 0 ≤ P.tsh i) := by
  obtain ⟨h1, h2, hmono⟩ := ClockH.order_core P hP.A_pos hP.Tpin_pos
    (ClockH.sigma_pos_of_le P hP hN hG hk) hc
  refine ⟨h1, fun i hi h2i => h2 i hi (by omega), ?_, ?_⟩
  · intro i j hki hij hjn
    have hj : j ∈ Finset.Icc k P.n := Finset.mem_Icc.mpr ⟨by omega, hjn⟩
    exact (h2 j hj (by omega)).trans_le (hmono i (j - 1) (by omega) (by omega) (by omega))
  · intro i hi
    rw [Finset.mem_Icc] at hi
    have := hmono i P.n (by omega) hi.2 le_rfl
    rwa [tsh_n] at this

/-- **`lem:clock`(2)** (`06_datum.tex:451-452`): for `i ∈ [k,n]`, the numbers `t♯_i`, `c_i(0)`,
`κ♯_i`, `T_i` and (if `i ≥ 2`) `t♯_{i-1}` are determined by `ω^{(n)}` on `[0, t♯_i]`: they are the
same for `P.withOm ω̃` whenever `ω̃` is a comparison vorticity with `ω̃ = ω^{(n)}` on `[0, t̄] × ℝ²`,
`t̄ ≥ t♯_i`. -/
theorem clock_causal (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall)
    {k : ℕ} (hk : 1 ≤ k) (hc : P.ClockUpTo k) {i : ℕ} (hi : i ∈ Finset.Icc k P.n) {tbar : ℝ}
    (ht : P.tsh i ≤ tbar) {om' : ℝ → ℂ → ℝ} (hom' : IsComparisonVort om')
    (heq : ∀ t ∈ Icc (0 : ℝ) tbar, om' t = P.om t) :
    (P.withOm om').tsh i = P.tsh i ∧ (P.withOm om').c0 i = P.c0 i ∧
    (P.withOm om').ksh i = P.ksh i ∧ (P.withOm om').T i = P.T i ∧
    (2 ≤ i → (P.withOm om').tsh (i - 1) = P.tsh (i - 1)) := by
  have h0 : 0 ≤ tbar := ((clock_order P hP hN hG hk hc).2.2.2 i hi).trans ht
  have hfl := ClockH.flow_agree P hP hN h0 hom' heq
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := ClockH.causal_core P hP.A_pos hP.Tpin_pos
    (ClockH.sigma_pos_of_le P hP hN hG hk) hc hi ht hfl heq
  exact ⟨e1, e2, e3, e4, fun h2i => e5 (by omega)⟩

/-- **`lem:clock`(3)** (`06_datum.tex:453-459`): for `t ≥ 0` and a comparison vorticity `ω̃` with
`ω̃ = ω^{(n)}` on `[0, t] × ℝ²`, for every `i ∈ [k,n]`: `t̃♯_i` is defined and `≤ t` iff `t♯_i ≤ t`;
if `t♯_i ≤ t`, the clock of `ω̃` is defined up to level `i` and `t̃♯_i = t♯_i`, `T̃_i = T_i`; and
ring `i` is quiet (resp. active, debris) at `t` for `ω̃` iff it is for `ω^{(n)}`. -/
theorem clock_determined (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    (hG : P.GSmall) {k : ℕ} (hk : 1 ≤ k) (hc : P.ClockUpTo k) {t : ℝ} (ht : 0 ≤ t)
    {om' : ℝ → ℂ → ℝ} (hom' : IsComparisonVort om') (heq : ∀ s ∈ Icc (0 : ℝ) t, om' s = P.om s) :
    ∀ i ∈ Finset.Icc k P.n,
      (((P.withOm om').ClockUpTo (i + 1) ∧ (P.withOm om').tsh i ≤ t) ↔ P.tsh i ≤ t) ∧
      (P.tsh i ≤ t → (P.withOm om').ClockUpTo i ∧ (P.withOm om').tsh i = P.tsh i ∧
        (P.withOm om').T i = P.T i) ∧
      ((P.withOm om').QuietAt i t ↔ P.QuietAt i t) ∧
      ((P.withOm om').ActiveAt i t ↔ P.ActiveAt i t) ∧
      ((P.withOm om').DebrisAt i t ↔ P.DebrisAt i t) := by
  have hA := hP.A_pos
  have hTp := hP.Tpin_pos
  have hσ := ClockH.sigma_pos_of_le P hP hN hG hk
  have hfl := ClockH.flow_agree P hP hN ht hom' heq
  have hσQ : ∀ j, (P.withOm om').sigma j = P.sigma j := ClockH.sigma_agree hfl heq ht
  have hord := ClockH.order_core P hA hTp hσ hc
  -- the order of the clock of `ω̃` from any level `l ≥ k` at which it is defined
  have hQσ : ∀ l, k ≤ l → ∀ j ∈ Finset.Icc l (P.withOm om').n, 0 < (P.withOm om').sigma j := by
    intro l hl j hj
    rw [hσQ]
    rw [withOm_n, Finset.mem_Icc] at hj
    exact hσ j (Finset.mem_Icc.mpr ⟨hl.trans hj.1, hj.2⟩)
  -- (b): `t♯_i ≤ t` gives the agreement
  have hb : ∀ i ∈ Finset.Icc k P.n, P.tsh i ≤ t → (P.withOm om').ClockUpTo i ∧
      (P.withOm om').tsh i = P.tsh i ∧ (P.withOm om').T i = P.T i := by
    intro i hi hti
    obtain ⟨e1, -, -, e4, -, -⟩ := ClockH.causal_core P hA hTp hσ hc hi hti hfl heq
    exact ⟨ClockH.clockUpTo_withOm P hA hTp hσ hc hi hti hfl heq, e1, e4⟩
  -- (a), forward direction: a defined `t̃♯_i ≤ t` forces `t♯_i ≤ t`
  have ha : ∀ i ∈ Finset.Icc k P.n, (P.withOm om').ClockUpTo (i + 1) →
      (P.withOm om').tsh i ≤ t → P.tsh i ≤ t := by
    intro i hi hQc hQt
    rw [Finset.mem_Icc] at hi
    by_contra hlt
    rw [not_le] at hlt
    classical
    have hex : ∃ d, i + d ≤ P.n ∧ P.tsh (i + d) ≤ t :=
      ⟨P.n - i, by omega, by rw [show i + (P.n - i) = P.n by omega, tsh_n]; exact ht⟩
    have hd₀ := Nat.find_spec hex
    have hd₀pos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · exfalso
        have h' := hd₀.2
        rw [h, add_zero] at h'
        linarith
      · exact h
    have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    have hgt : t < P.tsh (i + Nat.find hex - 1) := by
      rw [show i + Nat.find hex - 1 = i + (Nat.find hex - 1) by omega]
      by_contra hle
      exact hmin ⟨by omega, not_lt.mp hle⟩
    have hi₀ : i + Nat.find hex ∈ Finset.Icc k P.n :=
      Finset.mem_Icc.mpr ⟨by omega, hd₀.1⟩
    have hc' := (ClockH.causal_core P hA hTp hσ hc hi₀ hd₀.2 hfl heq).2.2.2.2.1 (by omega)
    have hQmono := (ClockH.order_core (P.withOm om') hA hTp (hQσ (i + 1) (by omega)) hQc).2.2
    have hle := hQmono i (i + Nat.find hex - 1) (by omega) (by omega)
      (by rw [withOm_n]; omega)
    rw [hc'] at hle
    linarith
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  have hPci : P.ClockUpTo i := hc.mono hi'.1
  have hPci1 : P.ClockUpTo (i + 1) := hc.mono (by omega)
  refine ⟨⟨fun h => ha i hi h.1 h.2, fun h => ?_⟩, hb i hi, ?_, ?_, ?_⟩
  · obtain ⟨hQc, hQt, -⟩ := hb i hi h
    exact ⟨hQc.mono (Nat.le_succ i), hQt ▸ h⟩
  · -- quiet
    by_cases hti : P.tsh i ≤ t
    · obtain ⟨hQc, hQt, -⟩ := hb i hi hti
      have hQc1 : (P.withOm om').ClockUpTo (i + 1) := hQc.mono (Nat.le_succ i)
      unfold QuietAt
      rw [hQt]
      exact ⟨fun h => h.elim (fun h' => absurd hQc1 h') Or.inr,
        fun h => h.elim (fun h' => absurd hPci1 h') Or.inr⟩
    · rw [not_le] at hti
      refine iff_of_true ?_ (Or.inr hti.le)
      by_cases hQc1 : (P.withOm om').ClockUpTo (i + 1)
      · right
        by_contra h
        exact absurd (ha i hi hQc1 (not_le.mp h).le) (not_le.mpr hti)
      · exact Or.inl hQc1
  · -- active
    by_cases hti : P.tsh i ≤ t
    · obtain ⟨hQc, hQt, hQT⟩ := hb i hi hti
      unfold ActiveAt
      rw [hQt, hQT]
      exact ⟨fun h => ⟨hPci, h.2⟩, fun h => ⟨hQc, h.2⟩⟩
    · exact iff_of_false (fun h => hti (ha i hi (h.1.mono (Nat.le_succ i)) h.2.1))
        (fun h => hti h.2.1)
  · -- debris
    by_cases hti : P.tsh i ≤ t
    · obtain ⟨hQc, -, hQT⟩ := hb i hi hti
      unfold DebrisAt
      rw [hQT]
      exact ⟨fun h => ⟨hPci, h.2⟩, fun h => ⟨hQc, h.2⟩⟩
    · rw [not_le] at hti
      refine iff_of_false (fun h => ?_) (fun h => ?_)
      · have hlt := (ClockH.order_core (P.withOm om') hA hTp (hQσ i hi'.1) h.1).1 i
          (Finset.mem_Icc.mpr ⟨le_rfl, by rw [withOm_n]; exact hi'.2⟩)
        exact absurd (ha i hi (h.1.mono (Nat.le_succ i)) (by linarith [h.2]))
          (not_le.mpr hti)
      · have := hord.1 i hi
        linarith [h.2]

end Approx

end Datum

end NonUniqueEuler
