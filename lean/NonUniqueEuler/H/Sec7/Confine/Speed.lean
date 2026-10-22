import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import NonUniqueEuler.Defs.Sec7.All
import NonUniqueEuler.I.Sec6.Speed
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec7.SkSmall
import NonUniqueEuler.I.Sec2.Hollow
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.H.Sec7.Confine.Arith

/-!
# Helper for `prop:confine`(b): the speed bound on `\bar B_{Λ r_{k+1}}`

Helper of `P/Sec7/Confine.lean` (`07_several_rings.tex:322-349`). For `t ∈ [T_{k+1}, t₁]` and
`|x| ≤ Λ r_{k+1}`: `v(t,x) = K*ω_{≥k+1}(t)(x) + Σ_{j≤k} K*g_j(x)`, `g_j = ω(t)1_{S_j(t)}`
(`lem:regions-basic`(2),(3)); the first term is `≤ C_*A_{k+1}r_{k+1}` (`lem:speed`), and by (Cl),
`lem:hollow` (`m₀ = 3`, `R_j = (a/2) r_j`), `‖g_j‖_{L¹} = A_jr_j²‖Φ‖_{L¹} ≤ πA_jr_j²`, `eq:sk-small`
and (iii), (iv), the sum is `≤ C_*A_{k+1}r_{k+1}`.

Main result: `confine_speed`. Also `T_succ_nonneg` (`T_{k+1} ≥ 0`, from `lem:clock`(1)).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.Rings.ConfineH

open RingData Datum Datum.Approx

/-! ### Generic lemmas -/

/-- Linearity of `K * ·` at a point, for a finite sum with absolutely convergent integrals. -/
theorem velocity_finset_sum {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℝ) (x : ℂ)
    (hg : ∀ i ∈ s, Integrable (fun y => biotSavartKernel (x - y) * (g i y : ℂ))) :
    velocity (fun y => ∑ i ∈ s, g i y) x = ∑ i ∈ s, velocity (g i) x := by
  unfold velocity
  simp_rw [Complex.ofReal_sum, Finset.mul_sum]
  exact integral_finsetSum s hg

/-- `‖g‖_{L¹} = ∫ ‖g‖` (as real numbers). -/
theorem toReal_eLpNorm_one_eq {g : ℂ → ℝ} (hg : AEStronglyMeasurable g volume) :
    (eLpNorm g 1 volume).toReal = ∫ x, ‖g x‖ := by
  rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm hg]

/-- `‖Φ‖_{L¹} ≤ π` (`lem:ring-facts`: `0 ≤ Φ < 1`, `supp Φ ⊂ \bar B_1`). -/
theorem PhiL1_le_pi {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) : PhiL1 χ ≤ Real.pi := by
  obtain ⟨hcd, _, _, hbd, _, hsupp, _, _⟩ := ringFacts_of_admissible hχ
  have hint : Integrable ((closedBall (0 : ℂ) 1).indicator (fun _ => (1 : ℝ))) volume := by
    refine (integrable_indicator_iff measurableSet_closedBall).mpr ?_
    exact integrableOn_const (by simp [Complex.volume_closedBall]) |>.mono_set subset_rfl
  have hle : (fun y => ‖ringPhi χ y‖) ≤ᵐ[volume]
      (closedBall (0 : ℂ) 1).indicator (fun _ => (1 : ℝ)) := by
    refine Filter.Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ closedBall (0 : ℂ) 1
    · show ‖ringPhi χ y‖ ≤ _
      rw [indicator_of_mem hy, Real.norm_eq_abs, abs_of_nonneg (hbd y).1]
      exact (hbd y).2.le
    · rw [indicator_of_notMem hy]
      have hy' : y ∉ tsupport (ringPhi χ) := fun h => hy (by
        have := (hsupp h).2
        simpa [mem_closedBall, dist_zero_right] using this)
      show ‖ringPhi χ y‖ ≤ 0
      rw [image_eq_zero_of_notMem_tsupport hy', norm_zero]
  rw [PhiL1, toReal_eLpNorm_one_eq hcd.continuous.aestronglyMeasurable]
  calc ∫ y, ‖ringPhi χ y‖
      ≤ ∫ y, (closedBall (0 : ℂ) 1).indicator (fun _ => (1 : ℝ)) y :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _) hint hle
    _ = Real.pi := by
        rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul, mul_one,
          Measure.real, Complex.volume_closedBall]
        simp

/-- A pointwise `3`-fold symmetric function is `3`-fold symmetric in the a.e. sense. -/
theorem isMFoldSymmetric_three_of_forall {g : ℂ → ℝ}
    (h : ∀ x, g (rot (2 * Real.pi / 3) x) = g x) : IsMFoldSymmetric 3 g := by
  unfold IsMFoldSymmetric
  refine Filter.Eventually.of_forall fun x => ?_
  simpa using h x

/-! ### The approximation -/

variable (P : Approx)

/-- `T_{k+1} ≥ 0` under the hypotheses of `prop:confine` (`lem:clock`(1): `T_{k+1} > t♯_{k+1} ≥ 0`). -/
theorem T_succ_nonneg (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall) {k : ℕ}
    {t₁ : ℝ} (h : P.ConfineHyp k t₁) : 0 ≤ P.T (k + 1) := by
  have hc := P.clock_order hP hN hG (k := k + 1) (by omega) h.clock
  have hk : k + 1 ∈ Finset.Icc (k + 1) P.n := Finset.mem_Icc.mpr ⟨le_rfl, h.lt_n⟩
  exact (hc.2.2.2 _ hk).trans (hc.1 _ hk).le

/-- The ring pieces `g_i = ω(t)1_{S_i(t)}`, `1 ≤ i ≤ n`, `t ≥ 0`: they are in `L¹ ∩ L^∞`, `K*g_i`
converges absolutely at every point, `g_i ≥ 0`, `g_i` is `3`-fold symmetric and
`‖g_i‖_{L¹} = A_i r_i² ‖Φ‖_{L¹}`. -/
theorem omegaRing_facts (hP : P.Valid) (hN : NumericalHypothesis P.χ) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 P.n) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (P.omegaRing i t) 1 volume ∧ MemLp (P.omegaRing i t) ⊤ volume ∧
    (∀ x : ℂ, Integrable (fun y => biotSavartKernel (x - y) * (P.omegaRing i t y : ℂ))) ∧
    IsMFoldSymmetric 3 (P.omegaRing i t) ∧
    (eLpNorm (P.omegaRing i t) 1 volume).toReal = P.A i * P.r i ^ 2 * PhiL1 P.χ := by
  obtain ⟨_, _, _, _, _, hint, ⟨hcd, hcs, hnn, hsym⟩, _⟩ := P.regions_basic_three hP hN hi ht
  have h1 : MemLp (P.omegaRing i t) 1 volume := hcd.continuous.memLp_of_hasCompactSupport hcs
  have htop : MemLp (P.omegaRing i t) ⊤ volume := hcd.continuous.memLp_of_hasCompactSupport hcs
  refine ⟨h1, htop, fun x => (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf h1 htop x).1,
    isMFoldSymmetric_three_of_forall hsym, ?_⟩
  rw [toReal_eLpNorm_one_eq hcd.continuous.aestronglyMeasurable, ← hint]
  congr 1
  ext y
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn y)]

/-- The velocity splits as `v(t,x) = K*ω_{≥k+1}(t)(x) + Σ_{j ≤ k} K*g_j(x)` (`k < n`, `t ≥ 0`;
`lem:regions-basic`(2),(3)). -/
theorem vel_split (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hkn : k < P.n)
    {t : ℝ} (ht : 0 ≤ t) (x : ℂ) :
    P.vel t x = velocity (P.omegaGe (k + 1) t) x +
      ∑ j ∈ Finset.Icc 1 k, velocity (P.omegaRing j t) x := by
  have hint : ∀ i ∈ Finset.Icc 1 P.n,
      Integrable (fun y => biotSavartKernel (x - y) * (P.omegaRing i t y : ℂ)) :=
    fun i hi => (omegaRing_facts P hP hN hi ht).2.2.1 x
  have hsum : P.om t = fun y => ∑ i ∈ Finset.Icc 1 P.n, P.omegaRing i t y :=
    (P.regions_basic_two hP hN ht).2.2.2.2.2
  have hk1 : k + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨by omega, hkn⟩
  have hge : P.omegaGe (k + 1) t = fun y => ∑ i ∈ Finset.Icc (k + 1) P.n, P.omegaRing i t y :=
    (P.regions_basic_three hP hN hk1 ht).2.2.1
  have hunion : Finset.Icc 1 P.n = Finset.Icc 1 k ∪ Finset.Icc (k + 1) P.n := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 k) (Finset.Icc (k + 1) P.n) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_Icc] at hi hi'
    omega
  have hsub : Finset.Icc (k + 1) P.n ⊆ Finset.Icc 1 P.n := by
    intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  show velocity (P.om t) x = _
  rw [hsum, velocity_finset_sum _ _ x hint, hge,
    velocity_finset_sum _ _ x (fun i hi => hint i (hsub hi)), hunion,
    Finset.sum_union hdisj, add_comm]

/-- The ratio estimate `r_{k+1} ≤ s_k 2^{j-k} r_j` for `1 ≤ j ≤ k` (`eq:sk-small` and
`s̄^{m-2} ≤ 1/2`, `07_several_rings.tex:343-345`). -/
theorem r_succ_le (hP : P.Valid) {k j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hsbar : P.sbar ^ (3 - 2) ≤ 1 / 2) :
    P.r (k + 1) ≤ P.s k * (1 / 2 : ℝ) ^ (k - j) * P.r j := by
  have hsk := (Rings.sk_small P hP).2.1 j (k + 1) hj1 (by omega)
  have hrj := hP.r_pos j
  rw [div_le_iff₀ hrj] at hsk
  have he1 : k + 1 - 1 = k := by omega
  have he2 : k + 1 - j - 1 = k - j := by omega
  rw [he1, he2] at hsk
  have hsb : P.sbar ≤ 1 / 2 := by simpa using hsbar
  have hsb0 : 0 ≤ P.sbar := hP.datumParams.sbar_pos.le
  have hpow : P.sbar ^ (k - j) ≤ (1 / 2 : ℝ) ^ (k - j) := pow_le_pow_left₀ hsb0 hsb _
  have hs0 := (hP.s_pos k).le
  calc P.r (k + 1) ≤ P.s k * P.sbar ^ (k - j) * P.r j := hsk
    _ ≤ P.s k * (1 / 2 : ℝ) ^ (k - j) * P.r j := by gcongr

/-- `μ A_j ≤ A_{k+1}` for `1 ≤ j ≤ k` (`A_j = μ^{j-k-1}A_{k+1}`, `μ > 1`). -/
theorem mu_mul_A_le (hP : P.Valid) {k j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    P.μ * P.A j ≤ P.A (k + 1) := by
  have hμ1 : 1 ≤ P.μ := hP.datumParams.one_lt_μ.le
  have hA₁ := hP.datumParams.A₁_pos
  rw [A_def, A_def, amp, amp]
  have he : P.μ * (P.A₁ * P.μ ^ (j - 1)) = P.A₁ * P.μ ^ j := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  rw [he, Nat.add_sub_cancel]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hμ1 hjk) hA₁.le

/-- `Λ ≥ 2` for `t₁ ≥ T_{k+1}`. -/
theorem two_le_confLambda (hP : P.Valid) {k : ℕ} {t₁ : ℝ} (ht₁ : P.T (k + 1) ≤ t₁) :
    2 ≤ P.confLambda k t₁ := by
  rw [confLambda_def]
  have hC := Cstar_pos
  have hA := hP.A_pos (k + 1)
  have : 0 ≤ 2 * Cstar * P.A (k + 1) * (t₁ - P.T (k + 1)) := by
    have : 0 ≤ t₁ - P.T (k + 1) := by linarith
    positivity
  linarith

/-- **`prop:confine`(b)** (`07_several_rings.tex:322-349`): `|v(t,x)| ≤ 2C_*A_{k+1}r_{k+1}` for
`t ∈ [T_{k+1}, t₁]` and `x ∈ \bar B_{Λ r_{k+1}}`. -/
theorem confine_speed (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall) {k : ℕ}
    {t₁ : ℝ} (h : P.ConfineHyp k t₁) :
    ∀ t ∈ Icc (P.T (k + 1)) t₁, ∀ x ∈ closedBall (0 : ℂ) (P.confLambda k t₁ * P.r (k + 1)),
      ‖P.vel t x‖ ≤ 2 * Cstar * P.A (k + 1) * P.r (k + 1) := by
  intro t ht x hx
  have hT0 := T_succ_nonneg P hP hN hG h
  have ht0 : 0 ≤ t := hT0.trans ht.1
  have hkn := h.lt_n
  have hk1 : k + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨by omega, hkn⟩
  have hxn : ‖x‖ ≤ P.confLambda k t₁ * P.r (k + 1) := by
    simpa [mem_closedBall, dist_zero_right] using hx
  -- constants
  have ha : 0 < a := ringData_order.2.2.2.2.2.2.2.1
  have hC := Cstar_pos
  have hμ : 0 < P.μ := lt_trans zero_lt_one hP.datumParams.one_lt_μ
  have hAk1 := hP.A_pos (k + 1)
  have hrk1 := hP.r_pos (k + 1)
  have hsk := hP.s_pos k
  set Λ := P.confLambda k t₁ with hΛ_def
  have hΛ2 : 2 ≤ Λ := two_le_confLambda P hP h.le_t₁
  have hΛ0 : 0 ≤ Λ := by linarith
  -- the inner part (`lem:speed`)
  have hin : ‖velocity (P.omegaGe (k + 1) t) x‖ ≤ Cstar * P.A (k + 1) * P.r (k + 1) :=
    (P.speed hP hN hk1 ht0).2.1 x
  -- each outer ring `j ≤ k`
  have hring : ∀ j ∈ Finset.Icc 1 k, P.μ * ‖velocity (P.omegaRing j t) x‖ ≤
      4 / 3 * (2 / a) ^ 3 * Λ ^ 2 * P.s k * (1 / 2 : ℝ) ^ (k - j) *
        (P.A (k + 1) * P.r (k + 1)) := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have hjn : j ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨hj'.1, by omega⟩
    obtain ⟨h1, htop, _, hsym, hL1⟩ := omegaRing_facts P hP hN hjn ht0
    have hrj := hP.r_pos j
    have hR : 0 < a / 2 * P.r j := by positivity
    have hrat := r_succ_le P hP hj'.1 hj'.2 h.sbar_pow_le
    -- `|x| ≤ R_j / 2`
    have hxR : ‖x‖ ≤ a / 2 * P.r j / 2 := by
      have hlam := h.lambda_le
      have hpow1 : (1 / 2 : ℝ) ^ (k - j) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hpow0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (k - j) := by positivity
      calc ‖x‖ ≤ Λ * P.r (k + 1) := hxn
        _ ≤ Λ * (P.s k * (1 / 2 : ℝ) ^ (k - j) * P.r j) := mul_le_mul_of_nonneg_left hrat hΛ0
        _ = Λ * P.s k * (1 / 2 : ℝ) ^ (k - j) * P.r j := by ring
        _ ≤ a / 8 * 1 * P.r j := by gcongr
        _ ≤ a / 2 * P.r j / 2 := by nlinarith
    -- the support of `g_j` avoids `B_{R_j}` (Cl)
    have hsupp : ∀ᵐ y ∂volume, ‖y‖ < a / 2 * P.r j → P.omegaRing j t y = 0 := by
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hy' : y ∉ P.St j t := fun hyS => by
        have : a / 2 * P.r j ≤ ‖y‖ := h.cl t ht j hj hyS
        linarith
      exact indicator_of_notMem hy' _
    have hhol := BS.norm_velocity_le_of_hollow (m₀ := 3) (by norm_num) hR h1 htop hsym hsupp hxR
    have hv := hhol.1.trans hhol.2
    rw [hL1] at hv
    have hv' : ‖velocity (P.omegaRing j t) x‖ ≤
        4 / (3 * Real.pi) * (P.A j * P.r j ^ 2 * PhiL1 P.χ) * ‖x‖ ^ 2 *
          ((a / 2 * P.r j) ^ 3)⁻¹ := by
      simpa using hv
    have hPhi := PhiL1_le_pi hP.admissible
    have hAj := (hP.A_pos j).le
    have hL : P.A j * P.r j ^ 2 * PhiL1 P.χ ≤ Real.pi * (P.A j * P.r j ^ 2) := by
      have : 0 ≤ P.A j * P.r j ^ 2 := by positivity
      nlinarith
    have hL0 : 0 ≤ P.A j * P.r j ^ 2 * PhiL1 P.χ := by
      have := PhiL1_nonneg P.χ
      positivity
    have hres := ring_term_le ha hrj hrk1 hAj hμ hΛ0 hL0 (norm_nonneg x) hv' hL hxn hrat
      (mu_mul_A_le P hP hj'.1 hj'.2)
    simpa [mul_assoc] using hres
  -- the sum over `j ≤ k`
  have hsum : P.μ * ∑ j ∈ Finset.Icc 1 k, ‖velocity (P.omegaRing j t) x‖ ≤
      P.μ * (Cstar * P.A (k + 1) * P.r (k + 1)) := by
    rw [Finset.mul_sum]
    have hgeo := sum_Icc_half_pow_le k
    have hiv := h.lambda_pow_le
    have hiv' : 8 / 3 * (2 / a) ^ 3 * Λ ^ 2 * P.s k ≤ P.μ * Cstar := by simpa using hiv
    have hK : 0 ≤ 4 / 3 * (2 / a) ^ 3 * Λ ^ 2 * P.s k * (P.A (k + 1) * P.r (k + 1)) := by
      positivity
    calc ∑ j ∈ Finset.Icc 1 k, P.μ * ‖velocity (P.omegaRing j t) x‖
        ≤ ∑ j ∈ Finset.Icc 1 k, 4 / 3 * (2 / a) ^ 3 * Λ ^ 2 * P.s k * (1 / 2 : ℝ) ^ (k - j) *
            (P.A (k + 1) * P.r (k + 1)) := Finset.sum_le_sum hring
      _ = 4 / 3 * (2 / a) ^ 3 * Λ ^ 2 * P.s k * (P.A (k + 1) * P.r (k + 1)) *
            ∑ j ∈ Finset.Icc 1 k, (1 / 2 : ℝ) ^ (k - j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ 4 / 3 * (2 / a) ^ 3 * Λ ^ 2 * P.s k * (P.A (k + 1) * P.r (k + 1)) * 2 :=
          mul_le_mul_of_nonneg_left hgeo hK
      _ = 8 / 3 * (2 / a) ^ 3 * Λ ^ 2 * P.s k * (P.A (k + 1) * P.r (k + 1)) := by ring
      _ ≤ P.μ * Cstar * (P.A (k + 1) * P.r (k + 1)) :=
          mul_le_mul_of_nonneg_right hiv' (by positivity)
      _ = P.μ * (Cstar * P.A (k + 1) * P.r (k + 1)) := by ring
  have hsum' : ∑ j ∈ Finset.Icc 1 k, ‖velocity (P.omegaRing j t) x‖ ≤
      Cstar * P.A (k + 1) * P.r (k + 1) := le_of_mul_le_mul_left hsum hμ
  -- conclusion
  rw [vel_split P hP hN hkn ht0 x]
  calc ‖velocity (P.omegaGe (k + 1) t) x + ∑ j ∈ Finset.Icc 1 k, velocity (P.omegaRing j t) x‖
      ≤ ‖velocity (P.omegaGe (k + 1) t) x‖ +
          ∑ j ∈ Finset.Icc 1 k, ‖velocity (P.omegaRing j t) x‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ Cstar * P.A (k + 1) * P.r (k + 1) + Cstar * P.A (k + 1) * P.r (k + 1) :=
        add_le_add hin hsum'
    _ = 2 * Cstar * P.A (k + 1) * P.r (k + 1) := by ring

end NonUniqueEuler.Rings.ConfineH
