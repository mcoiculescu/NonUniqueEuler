import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.H.Sec9.ActiveRing.Supports
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec6.InnerCirc
import NonUniqueEuler.I.Sec5.Active

/-!
# Proof: `thm:active` applied to ring `k` with time origin `t♯_k` (bridges)

Proof of `I/Sec9/ActiveRing.lean` (`09_relay.tex:759-767`).

* `activeConfig_units`: `t♯_k ≥ 0` (`lem:clock`(1), `clock_order`, with `P.GSmall` from
  `lem:inner-circ` and (SA3)); the rest is `ActiveRingAux.active_parts`, `active_scale`, `active_G`,
  `active_h`, `active_runCoef` (`H/Sec9/ActiveRing/Units.lean`): the datum of `P.activeConfig k` is
  `A_k⁻¹ω^{(n)}(t♯_k, r_k ·)` (the parts sum to `ω^{(n)}(t♯_k)`, `eq:omega-ge`), so by
  `sol_timeShift` and `sol_scale` its flow is `r_k⁻¹Φ_{t♯+u/A_k}Φ_{t♯}⁻¹(r_k ·)`, which is
  `r_k⁻¹Φ_v(t♯_k + u/A_k, t♯_k, r_k ·)` by the cocycle identity (`flowOf_cocycle`).
* `activeConfig_hyp`: as `ringConfig_hyp` (`H/Sec9/ActiveRing/Supports.lean`).
* `active_ring`: `IsActiveConst` (`thm:active`, `cor:active-moment`, through `activeConsts_spec`)
  applied to `P.activeConfig k` with `κ = κ♯_k`; (Init), (Field), (Coef) and the conclusions are
  translated with `activeConfig_units`, `supp (A_k⁻¹g(r_k ·)) = r_k⁻¹ supp g` and
  `supp ω(t)1_{S_k(t)} = S_k(t)`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace ActiveRingAux

/-- `t♯_k ≥ 0` under (SA) and the clock defined up to level `k` (`lem:clock`(1)). -/
theorem tsh_nonneg (S : Standing) (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ S.P.n)
    (hc : S.P.ClockUpTo k) : 0 ≤ S.P.tsh k := by
  have hG : S.P.GSmall := ((Approx.inner_circ S.P hS.valid hS.hN).2.2.2 hS.CG_le).2
  exact (Approx.clock_order S.P hS.valid hS.hN hG hk hc).2.2.2 k (Finset.mem_Icc.mpr ⟨le_refl k, hkn⟩)

end ActiveRingAux

open ActiveRingAux

/-- **Ring `k` in ring-`k` units with time origin `t♯_k`** (`09_relay.tex:759-767`): `t♯_k ≥ 0`,
`P.activeConfig k` has inner circulation `G_k` and initial perturbation `w_k(t♯_k)`, and for every
active time `u ≥ 0` its ring part, perturbation, field and flow are the rescaled ones of
`ω^{(n)}` at the real time `t♯_k + u/A_k` (`h(u) = h_k(t̄♯_k + u)`), and its running coefficient is
`c_k(u)`. -/
theorem activeConfig_units (S : Standing) (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ S.P.n)
    (hc : S.P.ClockUpTo k) :
    0 ≤ S.P.tsh k ∧
    (S.P.activeConfig k).G = S.P.G k ∧
    (S.P.activeConfig k).pert0 S.P.χ = S.P.w k (S.P.tsh k) ∧
    (∀ u : ℝ, 0 ≤ u → (S.P.activeConfig k).ringPart u =
      S.P.unitsVort k (S.P.omegaRing k (S.P.tsh k + u / S.P.A k))) ∧
    (∀ u : ℝ, 0 ≤ u → (S.P.activeConfig k).w S.P.χ u = S.P.w k (S.P.tsh k + u / S.P.A k)) ∧
    (∀ u : ℝ, 0 ≤ u → ∀ y : ℂ, (S.P.activeConfig k).h u y = S.P.hField k (S.P.tash k + u) y) ∧
    (∀ u : ℝ, 0 ≤ u → ∀ y : ℂ, (S.P.activeConfig k).flow u y =
      ((S.P.r k : ℝ) : ℂ)⁻¹ * Smooth.flowOf (velocityField S.P.om) (S.P.tsh k + u / S.P.A k)
        (S.P.tsh k) (((S.P.r k : ℝ) : ℂ) * y)) ∧
    (∀ u : ℝ, 0 ≤ u → OneRing.runCoef S.P.χ (S.P.activeConfig k).G
        ((S.P.activeConfig k).pert0 S.P.χ) (S.P.activeConfig k).h u = S.P.runCoefK k u) := by
  have hP := hS.valid
  have hN := hS.hN
  have ht := tsh_nonneg S hS hk hkn hc
  refine ⟨ht, active_G hP hN hk hkn ht, rfl, fun u hu => (active_parts hP hN hk hkn ht hu).1,
    fun u hu => ?_, fun u hu y => active_h hP hN hk hkn ht hu y, fun u _ y => ?_,
    fun u hu => active_runCoef hP hN hk hkn ht hu⟩
  · funext x
    simp only [OneRing.RingConfig.w, Approx.w, Approx.wR]
    rw [(active_parts hP hN hk hkn ht hu).1]
  · rw [(active_scale hP hN hk hkn ht).1 u y, flowOf_eq hP hN]

/-- **Ring `k` with time origin `t♯_k` satisfies the hypotheses of `lem:reduction` on `[0, ū]`**
(`09_relay.tex:759-767`, `06_datum.tex:323-330`) if `ū > 0` and `h_k` is defined at every real time
`t ∈ [t♯_k, t♯_k + ū/A_k]`. -/
theorem activeConfig_hyp (S : Standing) (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ S.P.n)
    (hc : S.P.ClockUpTo k) {ubar : ℝ} (hu : 0 < ubar)
    (hdef : ∀ t ∈ Icc (S.P.tsh k) (S.P.tsh k + ubar / S.P.A k), S.P.HDefined k t) :
    (S.P.activeConfig k).Hyp ubar := by
  have hP := hS.valid
  have hN := hS.hN
  have ht := tsh_nonneg S hS hk hkn hc
  obtain ⟨-, -, hcd, hcs⟩ := active_scale hP hN hk hkn ht
  obtain ⟨d1, d2, d3⟩ := active_disjoint hP hN hk hkn ht
  obtain ⟨s1, s2, s3⟩ := active_sym hP hN hk hkn ht
  have hA := hP.A_pos k
  have htime : ∀ u ∈ Icc (0 : ℝ) ubar,
      S.P.tsh k + u / S.P.A k ∈ Icc (S.P.tsh k) (S.P.tsh k + ubar / S.P.A k) := fun u hu' =>
    ⟨le_add_of_nonneg_right (div_nonneg hu'.1 hA.le),
      add_le_add le_rfl (div_le_div_of_nonneg_right hu'.2 hA.le)⟩
  refine ⟨hcd, hcs, d1, d2, d3, s1, s2, s3, hu, fun u hu' => ?_, fun u hu' => ?_⟩
  · rw [(active_parts hP hN hk hkn ht hu'.1).2.1]
    exact nuIn_tsupport hP (hdef _ (htime u hu')).1
  · rw [(active_parts hP hN hk hkn ht hu'.1).2.2]
    exact nuOut_tsupport hP hN hkn (ht.trans (htime u hu').1) (hdef _ (htime u hu')).2

/-- **`thm:active` and `cor:active-moment` for ring `k`** (`09_relay.tex:759-767`): with `G = G_k`,
`κ = κ♯_k`, the constants of (SA1), `C₀ ≥ 1` and `η_b ∈ [0, η_max]`, if `h_k` is defined on
`[t♯_k, t♯_k + ū/A_k]` and (Init), (Field), (Coef) on `[0,ū]` and (Small) `κ♯_k ≤ κ₀(C₀)` hold for
ring `k`, then the conclusions (a), (b) of `thm:active` and that of `cor:active-moment` hold for ring
`k` at every active time `u ∈ [0, min(ū, T̂_k)]`. -/
theorem active_ring (S : Standing) (hS : S.Holds) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ S.P.n) (hc : S.P.ClockUpTo k) {ubar : ℝ} (hu : 0 < ubar)
    (hdef : ∀ t ∈ Icc (S.P.tsh k) (S.P.tsh k + ubar / S.P.A k), S.P.HDefined k t) {ηb : ℝ}
    (hηb : ηb ∈ Icc (0 : ℝ) OneRing.etaMax) (hinit : S.ActiveInitK C₀ k)
    (hfield : S.ActiveFieldK C₀ ηb k ubar) (hcoef : S.CoefK C₀ k ubar)
    (hsmall : S.P.ksh k ≤ S.kappa0 C₀) :
    ∀ u ∈ Icc (0 : ℝ) (min ubar (S.P.That k)), S.ActiveConclAt C₀ ηb k u := by
  intro u hu'
  have hP := hS.valid
  have hN := hS.hN
  have ht := tsh_nonneg S hS hk hkn hc
  have hkI : k ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.mpr ⟨hk, hkn⟩
  have hA := hP.A_pos k
  have hr := hP.r_pos k
  set c := S.P.activeConfig k with hc_def
  have hG' : c.G = S.P.G k := active_G hP hN hk hkn ht
  have hGmem : S.P.G k ∈ Icc (0 : ℝ) Gbar :=
    ((Approx.inner_circ S.P hP hN).2.2.2 hS.CG_le).1 k hkI
  have hκ : 0 < S.P.ksh k := (hc.ksh_mem le_rfl hkn).1
  obtain ⟨-, -, -, -, hmain⟩ := OneRing.activeConsts_spec
    (OneRing.active S.P.χ hS.admissible hS.hN hS.three_le_s hS.σ'_mem)
  have hHyp : c.Hyp ubar := activeConfig_hyp S hS hk hkn hc hu hdef
  -- the support of the ring part at `t♯_k`
  have hring0 : tsupport c.ring0 =
      (fun y : ℂ => ((S.P.r k : ℝ) : ℂ) * y) ⁻¹' S.P.St k (S.P.tsh k) := by
    show tsupport (S.P.unitsVort k (S.P.omegaRing k (S.P.tsh k))) = _
    rw [tsupport_unitsVort hP, tsupport_omegaRing hP hN hkI ht]
  -- (Init)
  have hinit' : c.ActiveInit S.P.χ S.s C₀ (S.P.ksh k) := by
    refine ⟨hinit.1, fun y hy => ?_⟩
    rw [hring0] at hy
    have h1 := hinit.2 hy
    simp only [Approx.Nmk, mem_scaleSet] at h1
    rwa [r_inv_mul_r hP] at h1
  -- (Field)
  have hfield' : c.ActiveField S.P.χ S.s ubar C₀ (S.P.ksh k) ηb := by
    obtain ⟨h₁, h₂, hh⟩ := hfield
    refine ⟨h₁, h₂, fun v hv => ?_⟩
    obtain ⟨⟨U, hU, hNU, hUeq⟩, m1, b1, m2, b2⟩ := hh v hv
    refine ⟨⟨U, hU, hNU, fun x hx => ?_⟩, m1, b1, m2, ?_⟩
    · rw [active_h hP hN hk hkn ht hv.1]
      exact hUeq x hx
    · rw [hG']
      exact b2
  -- (Coef)
  have hcoef' : c.ActiveCoef S.P.χ ubar C₀ (S.P.ksh k) := by
    intro v hv
    rw [active_runCoef hP hN hk hkn ht hv.1, hG']
    exact hcoef v hv
  have huc : u ∈ Icc (0 : ℝ) (min ubar (OneRing.That (Eig.sigma S.P.χ c.G) S.P.δ₀ (S.P.ksh k))) := by
    rw [hG']
    exact hu'
  obtain ⟨hrad, hsupp, hmode, hbound, hmom⟩ :=
    hmain C₀ hC₀ c ubar hHyp (by rw [hG']; exact hGmem) (S.P.ksh k) ηb S.P.δ₀ hκ hηb
      hS.δ₀_mem hinit' hfield' hcoef' hsmall u huc
  have hw : c.w S.P.χ u = S.P.w k (S.P.tsh k + u / S.P.A k) := by
    funext x
    simp only [OneRing.RingConfig.w, Approx.w, Approx.wR]
    rw [(active_parts hP hN hk hkn ht hu'.1).1]
  rw [active_runCoef hP hN hk hkn ht hu'.1, hw, hG'] at hmode hmom
  rw [hw, hG'] at hbound
  refine ⟨⟨?_, ?_, hmode, hbound⟩, hmom⟩
  · -- (a): radial motion, back in physical units
    intro x hx t' ht'
    have hy : ((S.P.r k : ℝ) : ℂ)⁻¹ * x ∈ tsupport c.ring0 := by
      rw [hring0]
      rw [Set.mem_preimage, r_mul_r_inv hP]
      exact hx
    have hτ : S.P.A k * (t' - S.P.tsh k) ∈ Icc (0 : ℝ) u := by
      refine ⟨mul_nonneg hA.le (by linarith [ht'.1]), ?_⟩
      have h2 : t' - S.P.tsh k ≤ u / S.P.A k := by linarith [ht'.2]
      calc S.P.A k * (t' - S.P.tsh k) ≤ S.P.A k * (u / S.P.A k) :=
            mul_le_mul_of_nonneg_left h2 hA.le
        _ = u := by field_simp
    have htime : S.P.tsh k + S.P.A k * (t' - S.P.tsh k) / S.P.A k = t' := by
      field_simp
      ring
    have hflow : c.flow (S.P.A k * (t' - S.P.tsh k)) (((S.P.r k : ℝ) : ℂ)⁻¹ * x) =
        ((S.P.r k : ℝ) : ℂ)⁻¹ * Smooth.flowOf (velocityField S.P.om) t' (S.P.tsh k) x := by
      rw [(active_scale hP hN hk hkn ht).1, htime, r_mul_r_inv hP, flowOf_eq hP hN]
    have h := hrad _ hy _ hτ
    rw [hflow] at h
    have hn1 : ‖((S.P.r k : ℝ) : ℂ)⁻¹ * Smooth.flowOf (velocityField S.P.om) t' (S.P.tsh k) x‖ =
        (S.P.r k)⁻¹ * ‖Smooth.flowOf (velocityField S.P.om) t' (S.P.tsh k) x‖ := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hn2 : ‖((S.P.r k : ℝ) : ℂ)⁻¹ * x‖ = (S.P.r k)⁻¹ * ‖x‖ := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    rw [hn1, hn2, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hr)] at h
    have h3 := mul_le_mul_of_nonneg_left h hr.le
    rwa [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at h3
  · -- (a): the support of the ring part at `t♯_k + u/A_k`
    intro x hx
    have ht'' : 0 ≤ S.P.tsh k + u / S.P.A k := add_nonneg ht (div_nonneg hu'.1 hA.le)
    show ((S.P.r k : ℝ) : ℂ)⁻¹ * x ∈ annNn
    apply hsupp
    rw [(active_parts hP hN hk hkn ht hu'.1).1, tsupport_unitsVort hP,
      tsupport_omegaRing hP hN hkI ht'']
    rw [Set.mem_preimage, r_mul_r_inv hP]
    exact hx

end Relay

end NonUniqueEuler
