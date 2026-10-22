import NonUniqueEuler.Defs.Sec2.BiotSavart
import NonUniqueEuler.Defs.Sec2.Spaces
import NonUniqueEuler.H.Sec2.Velocity.Bounds
import NonUniqueEuler.H.Sec2.Velocity.Exponents
import NonUniqueEuler.H.Sec2.Velocity.Weak
import NonUniqueEuler.H.Sec2.Velocity.Grad
import NonUniqueEuler.I.Infra.Sobolev.DensityL1L2
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.ConvMinkowski.YoungGeneral
import NonUniqueEuler.I.Infra.LpInterp.Interp

/-!
# Proof of `lem:velocity` (`I/Sec2/Velocity.lean`)

Manuscript: `lem:velocity`, `02_prelim.tex:304-381`.

* (a) `velocity_bounds`: the exponents `r_p, s_p` (`VelH.exists_exponents`,
  `H/Sec2/Velocity/Exponents.lean`), Young's inequality (`Conv.eLpNorm_convAbs_le_young`,
  `I/Infra/ConvMinkowski/YoungGeneral.lean`) for the near part, interpolation
  (`LpInterp.eLpNorm_le_eLpNorm_add_eLpNorm`), and the helpers of `H/Sec2/Velocity/Bounds.lean`
  (local bound, `L¹ + L^∞`, the energy-type bound); a.e. absolute convergence is
  `BS.ae_integrable_biotSavart_of_L1` (`lem:BS-basic`(e)).
* (b) `velocity_weak_tendsto`: `‖ω‖₁ ≤ M` and `sup ‖ωₙ‖_p < ∞` from `I/Infra/LpDual/WeakBounded.lean`;
  the three-piece kernel split `K = 1_{B_ε}K + 1_{B_L∖B_ε}K + 1_{ℝ²∖B_L}K` and the three
  estimates of `H/Sec2/Velocity/Weak.lean`; an `ε/3` argument.
* (c) `gradL2_velocity`: smooth approximants in `L¹ ∩ L²` (`I/Infra/Sobolev/DensityL1L2.lean`),
  the `L²` limit of `∂_l v_j` and the weak-derivative identity (`H/Sec2/Velocity/Grad.lean`),
  uniqueness of weak derivatives (`Sob.weakDerivOn_ae_eq`).
* the `p = 2` corollaries are the specializations of (a) and (b).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.BS

open VelH

/-- `lem:velocity`(a), `4/3 < p < ∞`, `R > 0`: there is `C = C(p, R) > 0` such that for every
`ω ∈ L¹ ∩ L^p` the integral defining `K ∗ ω` converges absolutely a.e., `v = K ∗ ω ∈ L¹ + L^∞`,
`v ∈ L^{p'}(B_R) ∩ L²(B_R)` with `‖v‖_{L^{p'}(B_R)} + ‖v‖_{L²(B_R)} ≤ C ‖ω‖_{L¹∩L^p}`, and
`∫ |ω| (|K| ∗ |ω|) ≤ C ‖ω‖²_{L¹∩L^p}`. -/
theorem velocity_bounds {p R : ℝ} (hp : 4 / 3 < p) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ ω : ℂ → ℝ, MemLp ω 1 volume → MemLp ω (ENNReal.ofReal p) volume →
      (∀ᵐ x, Integrable (fun y => biotSavartKernel (x - y) * (ω y : ℂ)) volume) ∧
      Prelim.MemL1AddLinf (velocity ω) ∧
      MemLp (velocity ω) (ENNReal.ofReal p.conjExponent) (volume.restrict (ball (0 : ℂ) R)) ∧
      MemLp (velocity ω) 2 (volume.restrict (ball (0 : ℂ) R)) ∧
      eLpNorm (velocity ω) (ENNReal.ofReal p.conjExponent) (volume.restrict (ball (0 : ℂ) R)) +
          eLpNorm (velocity ω) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
        ENNReal.ofReal (C * Prelim.normL1Lp (ENNReal.ofReal p) ω) ∧
      ∫⁻ x, ‖ω x‖ₑ * Conv.convAbs biotSavartKernel ω x ≤
        ENNReal.ofReal (C * Prelim.normL1Lp (ENNReal.ofReal p) ω ^ 2) := by
  obtain ⟨r, s, hs1, hs2, hspr, hr2, hpr, hr1, hr'p⟩ := exists_exponents hp
  have hp1 : 1 < p := by linarith
  have hq1 : 1 ≤ p.conjExponent := one_le_conjExponent hp1
  set A := eLpNorm kernelNear (ENNReal.ofReal s) volume with hAdef
  have hA0 : A ≠ ∞ := (memLp_kernelNear hs1 hs2).eLpNorm_ne_top
  set V := volume (ball (0 : ℂ) R) with hVdef
  have hV : V ≠ ∞ := measure_ball_lt_top.ne
  have hexp1 : 0 ≤ 1 / p.conjExponent - 1 / r := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le (by linarith) hpr
  have hexp2 : 0 ≤ 1 / (2 : ℝ) - 1 / r := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le (by norm_num) hr2
  set A₁ := A * V ^ (1 / p.conjExponent - 1 / r) with hA₁
  set A₂ := A * V ^ (1 / (2 : ℝ) - 1 / r) with hA₂
  set B₁ := cFar * V ^ (1 / p.conjExponent) with hB₁
  set B₂ := cFar * V ^ (1 / (2 : ℝ)) with hB₂
  have hA₁0 : A₁ ≠ ∞ := ENNReal.mul_ne_top hA0 (ENNReal.rpow_ne_top_of_nonneg hexp1 hV)
  have hA₂0 : A₂ ≠ ∞ := ENNReal.mul_ne_top hA0 (ENNReal.rpow_ne_top_of_nonneg hexp2 hV)
  have hB₁0 : B₁ ≠ ∞ := ENNReal.mul_ne_top cFar_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hV)
  have hB₂0 : B₂ ≠ ∞ := ENNReal.mul_ne_top cFar_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hV)
  set C₁ := (A₁ + A₂).toReal + (B₁ + B₂).toReal with hC₁
  set C₂ := A.toReal + cFar.toReal with hC₂
  refine ⟨C₁ + C₂ + 1, by positivity, fun ω h1 hpω => ?_⟩
  have hm := h1.aestronglyMeasurable
  have hY : eLpNorm (Conv.convAbs kernelNear ω) (ENNReal.ofReal r) volume ≤
      A * eLpNorm ω (ENNReal.ofReal p) volume :=
    Conv.eLpNorm_convAbs_le_young measurable_kernelNear.aestronglyMeasurable hm hs1 hp1.le
      hr1.le hspr
  obtain ⟨hmem1, hb1⟩ := velocity_ball_final h1 hpω hq1 hpr hA0 hY R
  obtain ⟨hmem2, hb2⟩ := velocity_ball_final h1 hpω (by norm_num) hr2 hA0 hY R
  rw [ENNReal.ofReal_ofNat] at hmem2 hb2
  have hn0 : 0 ≤ Prelim.normL1Lp (ENNReal.ofReal p) ω := Prelim.normL1Lp_nonneg _ _
  refine ⟨ae_integrable_biotSavart_of_L1 h1, memL1AddLinf_velocity h1, hmem1, hmem2, ?_, ?_⟩
  · have hsum := add_le_add hb1 hb2
    have h' : eLpNorm (velocity ω) (ENNReal.ofReal p.conjExponent)
          (volume.restrict (ball (0 : ℂ) R)) + eLpNorm (velocity ω) 2
          (volume.restrict (ball (0 : ℂ) R)) ≤
        (A₁ + A₂) * eLpNorm ω (ENNReal.ofReal p) volume + (B₁ + B₂) * eLpNorm ω 1 volume := by
      refine hsum.trans (le_of_eq ?_)
      ring
    refine (le_ofReal_mul_normL1Lp h1 hpω (ENNReal.add_ne_top.2 ⟨hA₁0, hA₂0⟩)
      (ENNReal.add_ne_top.2 ⟨hB₁0, hB₂0⟩) h').trans (ofReal_mul_le_of_le hn0 ?_)
    have : 0 ≤ C₂ := by positivity
    linarith
  · have hrr' : r.conjExponent.HolderConjugate r := (Real.HolderConjugate.conjExponent hr1).symm
    have hE := lintegral_mul_convAbs_le hm hrr' hY
    have hr'1 : 1 ≤ r.conjExponent := one_le_conjExponent hr1
    have hint : eLpNorm ω (ENNReal.ofReal r.conjExponent) volume ≤
        eLpNorm ω 1 volume + eLpNorm ω (ENNReal.ofReal p) volume :=
      LpInterp.eLpNorm_le_eLpNorm_add_eLpNorm hm one_pos
        (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr'1)
        (ENNReal.ofReal_le_ofReal hr'p)
    have h' : ∫⁻ x, ‖ω x‖ₑ * Conv.convAbs biotSavartKernel ω x ≤
        (eLpNorm ω 1 volume + eLpNorm ω (ENNReal.ofReal p) volume) *
            (A * eLpNorm ω (ENNReal.ofReal p) volume) +
          cFar * eLpNorm ω 1 volume * eLpNorm ω 1 volume :=
      hE.trans (by gcongr)
    refine (le_ofReal_mul_normL1Lp_sq h1 hpω hA0 cFar_ne_top h').trans
      (ofReal_mul_le_of_le (by positivity) ?_)
    have : 0 ≤ C₁ := by positivity
    linarith

/-- `lem:velocity`(b), `4/3 < p < ∞`, `R > 0`: if `ωₙ ⇀ ω` weakly in `L^p` and
`‖ωₙ‖_{L¹} ≤ M` for all `n`, then `‖ω‖_{L¹} ≤ M` and `K ∗ ωₙ → K ∗ ω` in `L^{p'}(B_R)`. -/
theorem velocity_weak_tendsto {p R M : ℝ} (hp : 4 / 3 < p) (hR : 0 < R) {ωs : ℕ → ℂ → ℝ}
    {ω : ℂ → ℝ} (hconv : Prelim.WeakTendstoLp p ωs ω)
    (hM : ∀ n, eLpNorm (ωs n) 1 volume ≤ ENNReal.ofReal M) :
    eLpNorm ω 1 volume ≤ ENNReal.ofReal M ∧
      Tendsto (fun n => eLpNorm (velocity (ωs n) - velocity ω) (ENNReal.ofReal p.conjExponent)
        (volume.restrict (ball (0 : ℂ) R))) atTop (𝓝 0) := by
  have hp1 : 1 < p := by linarith
  have hω1 : eLpNorm ω 1 volume ≤ ENNReal.ofReal M :=
    LpDual.eLpNorm_one_le_of_tendsto_integral_mul hp1 hconv.2.1 hconv.2.2 hM
  refine ⟨hω1, ?_⟩
  obtain ⟨r, s, hs1, hs2, hspr, -, hpr, hr1, -⟩ := exists_exponents hp
  obtain ⟨N, hN, hNb⟩ := LpDual.exists_eLpNorm_le_of_forall_bdd hp1 hconv.1 (fun φ hφ => by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
      (Metric.isBounded_range_of_tendsto _ (hconv.2.2 φ hφ))
    exact ⟨C, fun n => by simpa [Real.norm_eq_abs] using hC _ (mem_range_self n)⟩)
  have hq1 : 1 ≤ p.conjExponent := one_le_conjExponent hp1
  have hq1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p.conjExponent := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1
  have hq0 : ENNReal.ofReal p.conjExponent ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hp1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le
  have hV : volume (ball (0 : ℂ) R) ≠ ∞ := measure_ball_lt_top.ne
  have hωL1 : MemLp ω 1 volume := ⟨hconv.2.1.1, hω1.trans_lt ENNReal.ofReal_lt_top⟩
  have hωsL1 : ∀ n, MemLp (ωs n) 1 volume := fun n =>
    ⟨(hconv.1 n).1, (hM n).trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨c1, hc1def⟩ : ∃ c : ℝ≥0∞, c = (N + eLpNorm ω (ENNReal.ofReal p) volume) *
      volume (ball (0 : ℂ) R) ^ (1 / p.conjExponent - 1 / r) := ⟨_, rfl⟩
  have hc1 : c1 ≠ ∞ := by
    rw [hc1def]
    exact ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hN, hconv.2.1.eLpNorm_ne_top⟩)
      (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 (one_div_le_one_div_of_le (by linarith) hpr))
        hV)
  obtain ⟨c3, hc3def⟩ : ∃ c : ℝ≥0∞, c = 2 * ENNReal.ofReal M *
      volume (ball (0 : ℂ) R) ^ (ENNReal.ofReal p.conjExponent).toReal⁻¹ := ⟨_, rfl⟩
  have hc3 : c3 ≠ ∞ := by
    rw [hc3def]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hV)
  have key : ∀ m L' n : ℕ, eLpNorm (velocity (ωs n) - velocity ω)
      (ENNReal.ofReal p.conjExponent) (volume.restrict (ball (0 : ℂ) R)) ≤
      eLpNorm (kBall (1 / ((m : ℝ) + 1))) (ENNReal.ofReal s) volume * c1 +
        eLpNorm (cv (kAnn (1 / ((m : ℝ) + 1)) ((L' : ℝ) + 1)) (ωs n - ω))
          (ENNReal.ofReal p.conjExponent) (volume.restrict (ball (0 : ℂ) R)) +
        ENNReal.ofReal (2 * Real.pi * ((L' : ℝ) + 1))⁻¹ * c3 := by
    intro m L' n
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hL0 : (0 : ℝ) ≤ L' := Nat.cast_nonneg L'
    have hε1 : 1 / ((m : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hεL : 1 / ((m : ℝ) + 1) ≤ (L' : ℝ) + 1 := by linarith
    have hfm : AEStronglyMeasurable (ωs n - ω) volume := (hconv.1 n).1.sub hconv.2.1.1
    have mB := (aestronglyMeasurable_cv
      (measurable_kBall (1 / ((m : ℝ) + 1))).aestronglyMeasurable hfm).restrict
      (s := ball (0 : ℂ) R)
    have mA := (aestronglyMeasurable_cv
      (measurable_kAnn (1 / ((m : ℝ) + 1)) ((L' : ℝ) + 1)).aestronglyMeasurable hfm).restrict
      (s := ball (0 : ℂ) R)
    have mO := (aestronglyMeasurable_cv
      (measurable_kOut ((L' : ℝ) + 1)).aestronglyMeasurable hfm).restrict (s := ball (0 : ℂ) R)
    rw [eLpNorm_congr_ae (ae_restrict_of_ae (velocity_sub_ae_eq_split (hωsL1 n) hωL1 hεL))]
    refine (eLpNorm_add_le (mB.add mA) mO hq1').trans (add_le_add
      ((eLpNorm_add_le mB mA hq1').trans (add_le_add ?_ le_rfl)) ?_)
    · refine (eLpNorm_cv_young_ball (measurable_kBall _).aestronglyMeasurable hfm hs1 hp1.le
        hr1.le hspr (by linarith) hpr R).trans ?_
      rw [hc1def, mul_assoc]
      gcongr
      exact (eLpNorm_sub_le (hconv.1 n).1 hconv.2.1.1 hp1').trans (add_le_add (hNb n) le_rfl)
    · refine (eLpNorm_cv_kOut_ball hfm (by positivity) R _).trans ?_
      rw [hc3def, mul_assoc, mul_assoc]
      gcongr
      calc eLpNorm (ωs n - ω) 1 volume ≤ eLpNorm (ωs n) 1 volume + eLpNorm ω 1 volume :=
            eLpNorm_sub_le (hconv.1 n).1 hconv.2.1.1 le_rfl
        _ ≤ ENNReal.ofReal M + ENNReal.ofReal M := add_le_add (hM n) hω1
        _ = 2 * ENNReal.ofReal M := (two_mul _).symm
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδ3 : 0 < δ / 3 := ENNReal.div_pos hδ.ne' (by norm_num)
  have hBt := ENNReal.Tendsto.mul_const (tendsto_eLpNorm_kBall hs1 hs2) (Or.inr hc1)
  rw [zero_mul] at hBt
  obtain ⟨m, hm⟩ := ((ENNReal.tendsto_nhds_zero.1 hBt) (δ / 3) hδ3).exists
  have hLt : Tendsto (fun L' : ℕ => ENNReal.ofReal (2 * Real.pi * ((L' : ℝ) + 1))⁻¹ * c3) atTop
      (𝓝 0) := by
    have h0 : Tendsto (fun L' : ℕ => (2 * Real.pi * ((L' : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * Real.pi)⁻¹
      rw [mul_zero] at this
      refine this.congr fun L' => ?_
      rw [mul_inv (2 * Real.pi), one_div]
    have h1 := ENNReal.tendsto_ofReal h0
    rw [ENNReal.ofReal_zero] at h1
    have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr hc3)
    rwa [zero_mul] at h2
  obtain ⟨L', hL'⟩ := ((ENNReal.tendsto_nhds_zero.1 hLt) (δ / 3) hδ3).exists
  have hA := (ENNReal.tendsto_nhds_zero.1 (tendsto_eLpNorm_cv_kAnn hp1 hconv hN hNb
    (ε := 1 / ((m : ℝ) + 1)) (by positivity) ((L' : ℝ) + 1) R hq0 ENNReal.ofReal_ne_top))
    (δ / 3) hδ3
  filter_upwards [hA] with n hn
  calc _ ≤ _ := key m L' n
    _ ≤ δ / 3 + δ / 3 + δ / 3 := add_le_add (add_le_add hm hn) hL'
    _ = δ := ENNReal.add_thirds δ

/-- `lem:velocity`(c): for `ω ∈ L¹ ∩ L²`, the weak gradient of `v = K ∗ ω` lies in `L²` and
`‖∇v‖_{L²} = ‖ω‖_{L²}`. -/
theorem gradL2_velocity {ω : ℂ → ℝ} (h1 : MemLp ω 1 volume) (h2 : MemLp ω 2 volume) :
    Prelim.HasGradH 0 (velocity ω) ∧ Prelim.gradL2 (velocity ω) = (eLpNorm ω 2 volume).toReal := by
  obtain ⟨ws, hs, hc, hc1, hc2⟩ := Sob.exists_seq_smooth_tendsto_L1_L2 h1 h2
  choose F hF hGF hnorm using fun l : Fin 2 => exists_lim_pd_velocity h2 hs hc hc2 l
  have hW : ∀ l, Sob.HasWeakDerivOn univ [Prelim.e2 l] (velocity ω) (F l) := fun l =>
    hasWeakDerivOn_velocity h1 hs hc hc1 l (hF l) (hGF l)
  refine ⟨⟨fun l => ⟨F l, (Sob.normH_zero (hF l)).1, hW l⟩⟩, ?_⟩
  have hl2 : ∀ l : Fin 2, Sob.l2 (Sob.weakDerivOn univ [Prelim.e2 l] (velocity ω)) =
      (eLpNorm (F l) 2 volume).toReal := fun l => by
    have h := Sob.weakDerivOn_ae_eq isOpen_univ
      (((hF l).locallyIntegrable one_le_two).locallyIntegrableOn univ) (hW l)
    have hae : Sob.weakDerivOn univ [Prelim.e2 l] (velocity ω) =ᵐ[volume] F l := by
      filter_upwards [h] with x hx using hx (mem_univ x)
    unfold Sob.l2
    rw [eLpNorm_congr_ae hae]
  have h10 : Sob.weakPartial (1, 0) (velocity ω) =
      Sob.weakDerivOn univ [Prelim.e2 0] (velocity ω) := by
    rw [Sob.weakPartial, Sob.weakPartialOn, Prelim.pdList_one_zero]
  have h01 : Sob.weakPartial (0, 1) (velocity ω) =
      Sob.weakDerivOn univ [Prelim.e2 1] (velocity ω) := by
    rw [Sob.weakPartial, Sob.weakPartialOn, Prelim.pdList_zero_one]
  have hsum : (eLpNorm (F 0) 2 volume).toReal ^ 2 + (eLpNorm (F 1) 2 volume).toReal ^ 2 =
      (eLpNorm ω 2 volume).toReal ^ 2 := by
    have hA := ((hnorm 0).pow 2).add ((hnorm 1).pow 2)
    have hB := (tendsto_toReal_eLpNorm_of_tendsto (fun j => memLp_of_smooth (hs j) (hc j) 2) h2
      hc2).pow 2
    have heq : (fun j => (eLpNorm (Prelim.pd 0 (velocity (ws j))) 2 volume).toReal ^ 2 +
        (eLpNorm (Prelim.pd 1 (velocity (ws j))) 2 volume).toReal ^ 2) =
        fun j => (eLpNorm (ws j) 2 volume).toReal ^ 2 :=
      funext fun j => sum_sq_l2_pd_velocity (hs j) (hc j)
    rw [heq] at hA
    exact tendsto_nhds_unique hA hB
  unfold Prelim.gradL2
  rw [h10, h01, hl2, hl2, hsum, Real.sqrt_sq ENNReal.toReal_nonneg]

/-! ### The case `p = 2` used downstream (D9) -/

/-- `lem:velocity`(a) for `p = 2` (`p' = 2`): the constant `C_v = C(2, R)`. -/
theorem velocity_bounds_two {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ ω : ℂ → ℝ, MemLp ω 1 volume → MemLp ω 2 volume →
      (∀ᵐ x, Integrable (fun y => biotSavartKernel (x - y) * (ω y : ℂ)) volume) ∧
      Prelim.MemL1AddLinf (velocity ω) ∧
      MemLp (velocity ω) 2 (volume.restrict (ball (0 : ℂ) R)) ∧
      eLpNorm (velocity ω) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
        ENNReal.ofReal (C * Prelim.normL1Lp 2 ω) ∧
      ∫⁻ x, ‖ω x‖ₑ * Conv.convAbs biotSavartKernel ω x ≤
        ENNReal.ofReal (C * Prelim.normL1Lp 2 ω ^ 2) := by
  obtain ⟨C, hC, h⟩ := velocity_bounds (p := 2) (by norm_num) hR
  refine ⟨C, hC, fun ω h1 h2 => ?_⟩
  have h2' : MemLp ω (ENNReal.ofReal 2) volume := by rwa [ENNReal.ofReal_ofNat]
  obtain ⟨ha, hb, -, hd, he, hf⟩ := h ω h1 h2'
  rw [ENNReal.ofReal_ofNat] at he hf
  exact ⟨ha, hb, hd, le_add_self.trans he, hf⟩

/-- `lem:velocity`(b) for `p = 2`: `ωₙ ⇀ ω` weakly in `L²` with `‖ωₙ‖₁ ≤ M` gives `‖ω‖₁ ≤ M`
and `K ∗ ωₙ → K ∗ ω` in `L²(B_R)`. -/
theorem velocity_weak_tendsto_two {R M : ℝ} (hR : 0 < R) {ωs : ℕ → ℂ → ℝ} {ω : ℂ → ℝ}
    (hconv : Prelim.WeakTendstoLp 2 ωs ω) (hM : ∀ n, eLpNorm (ωs n) 1 volume ≤ ENNReal.ofReal M) :
    eLpNorm ω 1 volume ≤ ENNReal.ofReal M ∧
      Tendsto (fun n => eLpNorm (velocity (ωs n) - velocity ω) 2
        (volume.restrict (ball (0 : ℂ) R))) atTop (𝓝 0) := by
  have h := velocity_weak_tendsto (p := 2) (by norm_num) hR hconv hM
  rwa [VelH.conjExponent_two, ENNReal.ofReal_ofNat] at h

end NonUniqueEuler.BS
