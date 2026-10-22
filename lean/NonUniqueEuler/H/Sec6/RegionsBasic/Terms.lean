import NonUniqueEuler.H.Sec6.RegionsBasic.Basic
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec5.Seed
import NonUniqueEuler.I.SmoothB.SmoothFlow
import NonUniqueEuler.I.SmoothB.SmoothCovariance

/-!
# Helpers for `lem:regions-basic`: the terms `f^{(n)}_k` and the flow `Φ_t`

Helper of `P/Sec6/RegionsBasic.lean`.

* `RegionsBasicAux.term_eq_scale`: `f^{(n)}_k = A_k G(·/r_k)` with `G = Φ` (`k < n`) or
  `G = Φ^{κ_seed}` (`k = n`), a nonnegative `3`-fold symmetric `C_c^∞` profile supported in `𝒩₋`
  with `∫ G = ‖Φ‖_{L¹}` (`lem:ring-facts`, `lem:seed`; `06_datum.tex:246-250`, `:280-284`);
* consequences: `term_isGood`, `S_subset_Nmk`, `S_subset_ann`, `norm_le_of_mem_S`,
  `integral_term`;
* radii: `r_succ_le`, `r_le_of_lt` (`r_k ≤ (a/16) r_i` for `i < k`, `06_datum.tex:251-253`);
* the flow of a valid approximation (`thm:smooth`(4), the symmetry part of `lem:regions-basic`(2),
  `06_datum.tex:255-267`): `f_isGood`, `flow_props`, `exists_flowInv_homeomorph`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.Datum.Approx.RegionsBasicAux

open RingData

/-! ### Profiles -/

/-- A profile of a term of `f^{(n)}`: good, supported in `𝒩₋`, with integral `‖Φ‖_{L¹}`. -/
def IsRingProfile (χ : ℝ → ℝ) (G : ℂ → ℝ) : Prop :=
  IsGood (2 * Real.pi / 3) G ∧ tsupport G ⊆ annNm ∧ ∫ y, G y = PhiL1 χ

theorem ringAnn_subset_annNm' (ha : 0 < a) : {y : ℂ | a ≤ ‖y‖ ∧ ‖y‖ ≤ 1} ⊆ annNm :=
  fun y hy => show 7 / 8 * a ≤ ‖y‖ ∧ ‖y‖ ≤ 5 / 4 from ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- `∫ Φ = ‖Φ‖_{L¹}` (`Φ ≥ 0`). -/
theorem integral_ringPhi {χ : ℝ → ℝ} (hR : RingFacts χ) : ∫ y, ringPhi χ y = PhiL1 χ := by
  have hint : Integrable (ringPhi χ) := hR.1.continuous.integrable_of_hasCompactSupport hR.2.1
  rw [PhiL1, eLpNorm_one_of_nonneg hint (fun y => (hR.2.2.2.1 y).1),
    ENNReal.toReal_ofReal (integral_nonneg fun y => (hR.2.2.2.1 y).1)]

theorem isRingProfile_phi {χ : ℝ → ℝ} (hR : RingFacts χ) : IsRingProfile χ (ringPhi χ) :=
  ⟨⟨hR.1, hR.2.1, fun y => (hR.2.2.2.1 y).1, fun y => hR.2.2.1 _ y⟩,
    hR.2.2.2.2.2.1.trans (ringAnn_subset_annNm' hR.2.2.2.2.2.2.1), integral_ringPhi hR⟩

theorem isRingProfile_seed {χ : ℝ → ℝ} (hR : RingFacts χ)
    (hS : OneRing.IsSeedFlow χ (OneRing.seedFlow χ) (OneRing.kL χ) (OneRing.Cprime χ)) {κ : ℝ}
    (hκ : κ ∈ Ioc 0 (OneRing.kL χ)) : IsRingProfile χ (OneRing.PhiSeed χ κ) := by
  refine ⟨⟨hS.phi_contDiff κ hκ, hS.phi_hasCompactSupport κ hκ, hS.phi_nonneg κ hκ,
    hS.phi_sym κ hκ⟩, hS.phi_tsupport κ hκ, ?_⟩
  show ∫ y, ringPhi χ (OneRing.seedFlow χ κ y) = PhiL1 χ
  have hmp := hS.measurePreserving κ
  rw [← integral_map hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hR.1.continuous.aestronglyMeasurable), hmp.map_eq]
  exact integral_ringPhi hR

variable {P : Approx}

/-- **The terms of `f^{(n)}`** (`06_datum.tex:162-164`): `f^{(n)}_k = A_k G(·/r_k)` for a ring
profile `G`, which is `Φ` for `k < n`. -/
theorem term_eq_scale (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) :
    ∃ G : ℂ → ℝ, IsRingProfile P.χ G ∧ P.term k = (fun x => P.A k * G (x / (P.r k : ℂ))) ∧
      (k < P.n → G = ringPhi P.χ) := by
  have hR := ringFacts_of_admissible hP.admissible
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hk
  rcases lt_or_eq_of_le hkn with hlt | heq
  · refine ⟨ringPhi P.χ, isRingProfile_phi hR, ?_, fun _ => rfl⟩
    funext x
    exact approxTerm_of_lt hk1 hlt x
  · subst heq
    have hS := OneRing.seedData_spec (OneRing.seed P.χ hP.admissible hN)
    refine ⟨OneRing.PhiSeed P.χ P.κs,
      isRingProfile_seed hR hS ⟨hP.kseed_pos, hP.kseed_le⟩, ?_, fun h => absurd h (lt_irrefl _)⟩
    funext x
    exact approxTerm_self x

theorem term_isGood (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) : IsGood (2 * Real.pi / 3) (P.term k) := by
  obtain ⟨G, hG, he, -⟩ := term_eq_scale hP hN hk
  rw [he]
  exact isGood_scale hG.1 (hP.A_pos k).le (hP.r_pos k).ne'

theorem norm_div_r (hP : P.Valid) (k : ℕ) (x : ℂ) : ‖x / (P.r k : ℂ)‖ = ‖x‖ / P.r k := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hP.r_pos k).le]

/-- `S_k ⊂ 𝒩₋_k` (`06_datum.tex:246-250`). -/
theorem S_subset_Nmk (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) : P.S k ⊆ P.Nmk k := by
  obtain ⟨G, hG, he, -⟩ := term_eq_scale hP hN hk
  intro x hx
  have hx' : x / (P.r k : ℂ) ∈ tsupport G := by
    have h := tsupport_scale_subset (P.A k) G (P.r k)
    rw [← he] at h
    exact h hx
  show ((P.r k : ℝ) : ℂ)⁻¹ * x ∈ annNm
  rw [← div_eq_inv_mul]
  exact hG.2.1 hx'

/-- `S_k ⊂ {a r_k ≤ |x| ≤ r_k}` for `k < n` (`06_datum.tex:246-247`). -/
theorem S_subset_ann (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < P.n) : P.S k ⊆ {x : ℂ | a * P.r k ≤ ‖x‖ ∧ ‖x‖ ≤ P.r k} := by
  have hkI : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨hk, hkn.le⟩
  obtain ⟨G, -, he, hG⟩ := term_eq_scale hP hN hkI
  rw [hG hkn] at he
  have hR := ringFacts_of_admissible hP.admissible
  intro x hx
  have hx' : x / (P.r k : ℂ) ∈ tsupport (ringPhi P.χ) := by
    have h := tsupport_scale_subset (P.A k) (ringPhi P.χ) (P.r k)
    rw [← he] at h
    exact h hx
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.2.1 hx'
  rw [norm_div_r hP] at h1 h2
  have hr := hP.r_pos k
  refine ⟨?_, ?_⟩
  · rwa [le_div_iff₀ hr] at h1
  · rwa [div_le_one hr] at h2

/-- Points of `S_k` satisfy `|x| ≤ (5/4) r_k`. -/
theorem norm_le_of_mem_S (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) {x : ℂ} (hx : x ∈ P.S k) : ‖x‖ ≤ 5 / 4 * P.r k := by
  have h := S_subset_Nmk hP hN hk hx
  have h2 : ‖((P.r k : ℝ) : ℂ)⁻¹ * x‖ ≤ 5 / 4 := h.2
  rw [← div_eq_inv_mul, norm_div_r hP, div_le_iff₀ (hP.r_pos k)] at h2
  exact h2

/-- `∫ f^{(n)}_k = A_k r_k² ‖Φ‖_{L¹}` (`06_datum.tex:280-284`). -/
theorem integral_term (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) : ∫ x, P.term k x = P.A k * P.r k ^ 2 * PhiL1 P.χ := by
  obtain ⟨G, hG, he, -⟩ := term_eq_scale hP hN hk
  rw [he, integral_scale _ _ (hP.r_pos k), hG.2.2]

/-! ### Radii -/

theorem a_pos' : 0 < a := Real.exp_pos _

/-- `r_{i+1} ≤ (a/16) r_i` for `i ≥ 1`. -/
theorem r_succ_le (hP : P.Valid) {i : ℕ} (hi : 1 ≤ i) : P.r (i + 1) ≤ a / 16 * P.r i := by
  rw [r_def, radius_succ _ _ hi, ← r_def, ← s_def]
  have hs : P.s i ≤ P.sbar := by
    rw [s_def, ratio]
    exact div_le_self hP.datumParams.sbar_pos.le
      (one_le_pow₀ (by linarith [hP.datumParams.one_lt_μ]))
  have := hP.datumParams.sbar_le
  exact mul_le_mul_of_nonneg_right (hs.trans this) (hP.r_pos i).le

/-- `r_{k+1} ≤ r_k` for every `k`. -/
theorem r_succ_le_self (hP : P.Valid) (k : ℕ) : P.r (k + 1) ≤ P.r k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [r_def, radius]
  · have h := r_succ_le hP hk
    have ha1 : a / 16 ≤ 1 := by
      have : a < 1 := (ringFacts_of_admissible hP.admissible).2.2.2.2.2.2.2
      linarith
    nlinarith [hP.r_pos k]

theorem r_antitone (hP : P.Valid) : Antitone P.r :=
  antitone_nat_of_succ_le (r_succ_le_self hP)

/-- `r_k ≤ (a/16) r_i` for `1 ≤ i < k` (`06_datum.tex:251-253`). -/
theorem r_le_of_lt (hP : P.Valid) {i k : ℕ} (hi : 1 ≤ i) (hik : i < k) :
    P.r k ≤ a / 16 * P.r i :=
  (r_antitone hP (Nat.succ_le_of_lt hik)).trans (r_succ_le hP hi)

/-! ### The datum and the flow -/

theorem f_isGood (hP : P.Valid) (hN : NumericalHypothesis P.χ) :
    IsGood (2 * Real.pi / 3) P.f := by
  have e : P.f = fun x => ∑ k ∈ Finset.Icc 1 P.n, P.term k x := funext P.f_apply
  rw [e]
  exact isGood_sum _ fun k hk => term_isGood hP hN hk

theorem exists_isSmoothDatum (hP : P.Valid) (hN : NumericalHypothesis P.χ) :
    ∃ R : ℝ, Smooth.IsSmoothDatum P.f R := by
  have hG := f_isGood hP hN
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_ball (0 : ℂ)).1 hG.2.1.isCompact.isBounded
  exact ⟨R, ⟨hG.1, hR⟩⟩

/-- **The flow of `v^{(n)}`** (`thm:smooth`(4), `06_datum.tex:255-270`): `Φ_t` and `Φ_t⁻¹` are
inverse `C^∞` maps, `Φ_t⁻¹` preserves area, `ω(t) = f^{(n)} ∘ Φ_t⁻¹`, and both maps commute with
`O = O_{2π/3}`. -/
theorem flow_props (hP : P.Valid) (hN : NumericalHypothesis P.χ) (t : ℝ) :
    (∀ y, P.flowInv t (P.flow t y) = y) ∧ (∀ x, P.flow t (P.flowInv t x) = x) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.flow t) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.flowInv t) ∧
    MeasurePreserving (P.flowInv t) volume volume ∧
    (∀ x, P.om t x = P.f (P.flowInv t x)) ∧
    (∀ y, P.flow t (rot (2 * Real.pi / 3) y) = rot (2 * Real.pi / 3) (P.flow t y)) ∧
    (∀ x, P.flowInv t (rot (2 * Real.pi / 3) x) = rot (2 * Real.pi / 3) (P.flowInv t x)) := by
  obtain ⟨R, hD⟩ := exists_isSmoothDatum hP hN
  obtain ⟨hl, hr, hc, hci, -⟩ := Smooth.flow_diffeo hD t
  obtain ⟨-, hrot, hroti⟩ := Smooth.vel_flow_rot_of_symm hD (f_isGood hP hN).2.2.2 t
  rw [hP.flow_eq t, hP.flowInv_eq t]
  refine ⟨hl, hr, hc, hci, (Smooth.flow_measurePreserving hD t).2, fun x => ?_, hrot, hroti⟩
  rw [hP.om_eq]
  exact Smooth.sol_eq_comp_flowInv hD t x

/-- `Φ_t⁻¹` as a homeomorphism, with inverse `Φ_t`. -/
theorem exists_flowInv_homeomorph (hP : P.Valid) (hN : NumericalHypothesis P.χ) (t : ℝ) :
    ∃ e : ℂ ≃ₜ ℂ, ⇑e = P.flowInv t ∧ ⇑e.symm = P.flow t := by
  obtain ⟨hl, hr, hc, hci, -⟩ := flow_props hP hN t
  exact ⟨{ toFun := P.flowInv t
           invFun := P.flow t
           left_inv := hr
           right_inv := hl
           continuous_toFun := hci.continuous
           continuous_invFun := hc.continuous }, rfl, rfl⟩

end NonUniqueEuler.Datum.Approx.RegionsBasicAux
