import NonUniqueEuler.H.Sec3.Transport.CommSlab
import NonUniqueEuler.I.Sec3.Transport.MollifyLp
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Helper for `P/Sec3/Transport`: the three limits `ε → 0`

Proof of `lem:transport`(i) (`03_compactness.tex:503-518`), the passage to the limit in the
mollified renormalized identity (`I/Sec3/Transport/Mollified.lean`) along `ε_n = 1/(n+1)`:

* `tendsto_lintegral_transportIntegrand_mollify`: `Υ(u_ε)(∂_tφ + w·∇φ) → Υ(u)(∂_tφ + w·∇φ)` in
  `L¹((t₀,T)×ℝ²)`. For a.e. `t`, `|Υ(u_ε) - Υ(u)| |∂_tφ + w·∇φ| ≤ C |u_ε - u| (D + D|w|) 1_{B_R}`,
  so by Hölder the slice integral is at most `C ‖u_ε(t) - u(t)‖₂ K₀` with
  `K₀ = D |B_R|^{1/2} + D ‖w‖_{L^∞(L²(B_R))}`; this tends to `0`
  (`tendsto_eLpNorm_mollify_sub`, `u(t) ∈ L²`) and is bounded by `2 C M₂ K₀`
  (`memLp_mollify`); dominated convergence in `t`. This is the manuscript's
  "`wΥ(u_ε) → wΥ(u)` in `L¹_loc` because `u_ε(t) → u(t)` in `L^b(B_R)` for a.e. `t`, with the
  bound `2‖u‖_{L^∞(L^b)}`, and `w ∈ L^∞(L^{b'}(B_R))`".
* `tendsto_lintegral_datum_mollify`: `Υ(u₀,ε) φ(t₀) → Υ(u₀) φ(t₀)` in `L¹(ℝ²)` (Hölder,
  `u₀,ε → u₀` in `L²`).
* `tendsto_lintegral_comm_mollify`: `φ Υ'(u_ε) C_ε[u,w] → 0` in `L¹((t₀,T)×ℝ²)`, from
  `lem:commutator` on `(t₀,T') × B_R` (`H/Sec3/Transport/CommSlab.lean`).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Weak.TransportH

/-! ### The sequence `ε_n = 1/(n+1)` -/

/-- `ε_n = 1/(n+1)`. -/
def epsSeq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem epsSeq_pos (n : ℕ) : 0 < epsSeq n := by
  unfold epsSeq; positivity

theorem tendsto_epsSeq : Tendsto epsSeq atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall epsSeq_pos⟩

/-! ### Hölder in `ℝ≥0∞` form -/

theorem lintegral_enorm_mul_le_eLpNorm_two {μ : Measure ℂ} {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {f : ℂ → E} {g : ℂ → F} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf.enorm hg.enorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simpa using h

/-- `‖Υ(a) - Υ(b)‖ₑ ≤ C ‖a - b‖ₑ`. -/
theorem enorm_sub_le_of_abs {Υ : ℝ → ℝ} {C : ℝ} (hC : ∀ a b, |Υ a - Υ b| ≤ C * |a - b|)
    (hC0 : 0 ≤ C) (a b : ℝ) : ‖Υ a - Υ b‖ₑ ≤ ENNReal.ofReal C * ‖a - b‖ₑ := by
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hC0]
  exact ENNReal.ofReal_le_ofReal (hC a b)

/-! ### The convergence of the transport term -/

section Transport

variable {T t₀ : ℝ} {w : ℝ → ℂ → ℂ} {u : ℝ → ℂ → ℝ}

/-- The pointwise bound `|Υ(a)(∂_tφ + w·∇φ) - Υ(b)(∂_tφ + w·∇φ)| ≤ C |a - b| (D + D|w|) 1_{B_R}`. -/
theorem enorm_transportIntegrand_sub_le {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) {R : ℝ}
    (hsupp : ∀ p ∈ tsupport φ, p.2 ∈ ball (0 : ℂ) R) {D : ℝ}
    (hD : ∀ p, ‖fderiv ℝ φ p‖ ≤ D) {Υ : ℝ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ a b, |Υ a - Υ b| ≤ C * |a - b|) (v : ℝ → ℂ → ℝ) (t : ℝ) (x : ℂ) :
    ‖transportIntegrand (fun t x => Υ (v t x)) w φ (t, x) -
        transportIntegrand (fun t x => Υ (u t x)) w φ (t, x)‖ₑ ≤
      ENNReal.ofReal C * (‖v t x - u t x‖ₑ *
        ‖(ball (0 : ℂ) R).indicator (fun x => D + D * ‖w t x‖) x‖ₑ) := by
  simp only [transportIntegrand]
  rw [← sub_mul, enorm_mul]
  by_cases hx : x ∈ ball (0 : ℂ) R
  · rw [indicator_of_mem hx, ← mul_assoc]
    refine mul_le_mul' (enorm_sub_le_of_abs hC hC0 _ _) ?_
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    refine (abs_timeDeriv_add_spaceDeriv_le hφ hD t x (w t x)).trans (le_abs_self _)
  · have hp : (t, x) ∉ tsupport φ := fun h => hx (hsupp _ h)
    rw [timeDeriv_add_spaceDeriv_eq_zero hφ hp]
    simp

/-- The `L²(B_R)` norm of `D + D|w(t)|` is bounded by `D |B_R|^{1/2} + D ‖w(t)‖_{L²(B_R)}`. -/
theorem eLpNorm_indicator_le {R D : ℝ} (hD0 : 0 ≤ D) {g : ℂ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (ball (0 : ℂ) R))) :
    eLpNorm ((ball (0 : ℂ) R).indicator (fun x => D + D * ‖g x‖)) 2 volume ≤
      ENNReal.ofReal D * volume (ball (0 : ℂ) R) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal D * eLpNorm g 2 (volume.restrict (ball (0 : ℂ) R)) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]
  have h1 : AEStronglyMeasurable (fun _ : ℂ => D) (volume.restrict (ball (0 : ℂ) R)) :=
    aestronglyMeasurable_const
  have h2 : AEStronglyMeasurable (fun x => D * ‖g x‖) (volume.restrict (ball (0 : ℂ) R)) :=
    hg.norm.const_mul D
  refine (eLpNorm_add_le h1 h2 one_le_two).trans (add_le_add ?_ ?_)
  · rw [eLpNorm_const' _ two_ne_zero ENNReal.ofNat_ne_top, Measure.restrict_apply_univ,
      Real.enorm_eq_ofReal_abs, abs_of_nonneg hD0]
    norm_num
  · have : (fun x => D * ‖g x‖) = D • fun x => ‖g x‖ := rfl
    rw [this, eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal_abs, abs_of_nonneg hD0]

/-- `Υ(u_ε)(∂_tφ + w·∇φ) → Υ(u)(∂_tφ + w·∇φ)` in `L¹((t₀,T)×ℝ²)` along `ε_n = 1/(n+1)`. -/
theorem tendsto_lintegral_transportIntegrand_mollify {ρ : ℂ → ℝ} (hρ : IsMollifier ρ)
    (ht₀ : t₀ ∈ Ico 0 T) (hw : IsBddH1DivFreeField (Ioo 0 T) w)
    (hu2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 u)
    {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ)
    (hint : ∀ n : ℕ, IntegrableOn (fun p =>
      transportIntegrand (fun t x => Υ (mollify ρ (epsSeq n) (u t) x)) w φ p -
        transportIntegrand (fun t x => Υ (u t x)) w φ p) (slabFrom t₀ T)) :
    Tendsto (fun n : ℕ => ∫⁻ p in slabFrom t₀ T,
      ‖transportIntegrand (fun t x => Υ (mollify ρ (epsSeq n) (u t) x)) w φ p -
        transportIntegrand (fun t x => Υ (u t x)) w φ p‖ₑ) atTop (𝓝 0) := by
  obtain ⟨R, hR, b, -, hsupp⟩ := exists_ball_of_isTestFunction hφ
  obtain ⟨D, hD0, hD⟩ := exists_bound_fderiv_of_isTestFunction hφ
  obtain ⟨C, hC0, -, hC⟩ := exists_lipschitz_of_isRenormalization hΥ
  obtain ⟨M₂, hM₂⟩ := hu2.essBounded
  obtain ⟨MR, hMR⟩ := (memLinfLp_two_of_isBddH1 hw hR).essBounded
  set K₀ : ℝ≥0∞ := ENNReal.ofReal D * volume (ball (0 : ℂ) R) ^ (1 / 2 : ℝ) +
    ENNReal.ofReal D * ENNReal.ofReal MR with hK₀def
  have hK₀ : K₀ ≠ ∞ := ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne),
     ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
  set F : ℕ → ℝ × ℂ → ℝ := fun n p =>
    transportIntegrand (fun t x => Υ (mollify ρ (epsSeq n) (u t) x)) w φ p -
      transportIntegrand (fun t x => Υ (u t x)) w φ p with hFdef
  -- the good times
  have hgood : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)),
      MemLp (u t) 2 volume ∧ eLpNorm (u t) 2 volume ≤ ENNReal.ofReal M₂ ∧
        AEStronglyMeasurable (w t) (volume.restrict (ball (0 : ℂ) R)) ∧
        eLpNorm (w t) 2 (volume.restrict (ball (0 : ℂ) R)) ≤ ENNReal.ofReal MR := by
    have h1 := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left ht₀.1) hM₂
    have h2 := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left ht₀.1) hMR
    filter_upwards [h1, h2] with t ht1 ht2
    rw [Measure.restrict_univ] at ht1
    exact ⟨ht1.1, eLpNorm_le_ofReal ht1.1 ht1.2, ht2.1.aestronglyMeasurable,
      eLpNorm_le_ofReal ht2.1 ht2.2⟩
  -- the slice bound
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ n : ℕ,
      ∫⁻ x, ‖F n (t, x)‖ₑ ≤ ENNReal.ofReal C *
        (eLpNorm (fun x => mollify ρ (epsSeq n) (u t) x - u t x) 2 volume * K₀) := by
    filter_upwards [hgood] with t ⟨hu, _, hwm, _⟩ n
    obtain ⟨hmo, -⟩ := memLp_mollify hρ (epsSeq_pos n) one_le_two hu
    have hind : AEStronglyMeasurable
        ((ball (0 : ℂ) R).indicator (fun x => D + D * ‖w t x‖)) volume := by
      rw [aestronglyMeasurable_indicator_iff measurableSet_ball]
      exact aestronglyMeasurable_const.add (hwm.norm.const_mul D)
    calc ∫⁻ x, ‖F n (t, x)‖ₑ
        ≤ ∫⁻ x, ENNReal.ofReal C * (‖mollify ρ (epsSeq n) (u t) x - u t x‖ₑ *
            ‖(ball (0 : ℂ) R).indicator (fun x => D + D * ‖w t x‖) x‖ₑ) :=
          lintegral_mono fun x => enorm_transportIntegrand_sub_le hφ
            (fun p hp => (hsupp p hp).2) hD hC0 hC _ t x
      _ = ENNReal.ofReal C * ∫⁻ x, ‖mollify ρ (epsSeq n) (u t) x - u t x‖ₑ *
            ‖(ball (0 : ℂ) R).indicator (fun x => D + D * ‖w t x‖) x‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * (eLpNorm (fun x => mollify ρ (epsSeq n) (u t) x - u t x) 2 volume *
            eLpNorm ((ball (0 : ℂ) R).indicator (fun x => D + D * ‖w t x‖)) 2 volume) := by
          gcongr
          exact lintegral_enorm_mul_le_eLpNorm_two
            (hmo.aestronglyMeasurable.sub hu.aestronglyMeasurable) hind
      _ ≤ ENNReal.ofReal C *
            (eLpNorm (fun x => mollify ρ (epsSeq n) (u t) x - u t x) 2 volume * K₀) := by
          gcongr
          refine (eLpNorm_indicator_le hD0 hwm).trans ?_
          rw [hK₀def]
          gcongr
  -- Tonelli
  have hprod : ∀ n : ℕ, ∫⁻ p in slabFrom t₀ T, ‖F n p‖ₑ =
      ∫⁻ t in Ioo t₀ T, ∫⁻ x, ‖F n (t, x)‖ₑ := by
    intro n
    have hm := (hint n).aestronglyMeasurable
    rw [restrict_slabFrom_eq_prod] at hm ⊢
    exact lintegral_prod _ hm.enorm
  have hmeas : ∀ n : ℕ, AEMeasurable (fun t => ∫⁻ x, ‖F n (t, x)‖ₑ)
      (volume.restrict (Ioo t₀ T)) := by
    intro n
    have hm := (hint n).aestronglyMeasurable
    rw [restrict_slabFrom_eq_prod] at hm
    exact hm.enorm.lintegral_prod_right'
  show Tendsto (fun n : ℕ => ∫⁻ p in slabFrom t₀ T, ‖F n p‖ₑ) atTop (𝓝 0)
  simp_rw [hprod]
  -- dominated convergence in `t`
  set B : ℝ≥0∞ := ENNReal.ofReal C * (2 * ENNReal.ofReal M₂ * K₀) with hBdef
  have hbound : ∀ n : ℕ, (fun t => ∫⁻ x, ‖F n (t, x)‖ₑ) ≤ᵐ[volume.restrict (Ioo t₀ T)]
      fun _ => B := by
    intro n
    filter_upwards [hslice, hgood] with t ht ⟨hu, hule, _, _⟩
    refine (ht n).trans ?_
    obtain ⟨hmo, hmole⟩ := memLp_mollify hρ (epsSeq_pos n) one_le_two hu
    have hsub : eLpNorm (fun x => mollify ρ (epsSeq n) (u t) x - u t x) 2 volume ≤
        2 * ENNReal.ofReal M₂ := by
      refine (eLpNorm_sub_le hmo.aestronglyMeasurable hu.aestronglyMeasurable one_le_two).trans ?_
      rw [two_mul]
      exact add_le_add (hmole.trans hule) hule
    rw [hBdef]
    gcongr
  have hfin : ∫⁻ _t in Ioo t₀ T, B ≠ ∞ := by
    rw [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hK₀))
      (volume_Ioo_ne_top _ _)
  have hlim : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)),
      Tendsto (fun n : ℕ => ∫⁻ x, ‖F n (t, x)‖ₑ) atTop (𝓝 0) := by
    filter_upwards [hslice, hgood] with t ht ⟨hu, _, _, _⟩
    have h1 : Tendsto (fun n : ℕ =>
        eLpNorm (fun x => mollify ρ (epsSeq n) (u t) x - u t x) 2 volume) atTop (𝓝 0) :=
      (tendsto_eLpNorm_mollify_sub hρ one_le_two ENNReal.ofNat_ne_top hu).comp tendsto_epsSeq
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal C *
        (eLpNorm (fun x => mollify ρ (epsSeq n) (u t) x - u t x) 2 volume * K₀)) atTop
        (𝓝 (ENNReal.ofReal C * (0 * K₀))) :=
      ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul_const h1 (Or.inr hK₀))
        (Or.inr ENNReal.ofReal_ne_top)
    rw [zero_mul, mul_zero] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
      (fun _ => zero_le) ht
  have := tendsto_lintegral_of_dominated_convergence' (fun _ => B) hmeas hbound hfin hlim
  simpa using this

end Transport

/-! ### The datum term -/

/-- The slice `x ↦ φ(t₀, x)` of a test function is continuous with compact support. -/
theorem slice_continuous_hasCompactSupport {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ)
    (t₀ : ℝ) :
    Continuous (fun x : ℂ => φ (t₀, x)) ∧ HasCompactSupport (fun x : ℂ => φ (t₀, x)) := by
  refine ⟨hφ.contDiff.continuous.comp (continuous_const.prodMk continuous_id), ?_⟩
  refine HasCompactSupport.intro (hφ.hasCompactSupport.isCompact.image continuous_snd)
    fun x hx => ?_
  by_contra hne
  exact hx ⟨(t₀, x), subset_tsupport _ hne, rfl⟩

theorem memLp_slice {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) (t₀ : ℝ)
    (p : ℝ≥0∞) : MemLp (fun x : ℂ => φ (t₀, x)) p volume :=
  (slice_continuous_hasCompactSupport hφ t₀).1.memLp_of_hasCompactSupport
    (slice_continuous_hasCompactSupport hφ t₀).2

/-- `Υ(u₀,ε) φ(t₀) → Υ(u₀) φ(t₀)` in `L¹(ℝ²)` along `ε_n`. -/
theorem tendsto_lintegral_datum_mollify {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {u₀ : ℂ → ℝ}
    (hu₀2 : MemLp u₀ 2 volume) {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) {T : ℝ}
    {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) (t₀ : ℝ) :
    Tendsto (fun n : ℕ => ∫⁻ x, ‖Υ (mollify ρ (epsSeq n) u₀ x) * φ (t₀, x) -
      Υ (u₀ x) * φ (t₀, x)‖ₑ) atTop (𝓝 0) := by
  obtain ⟨C, hC0, -, hC⟩ := exists_lipschitz_of_isRenormalization hΥ
  have hφ2 := memLp_slice hφ t₀ 2
  have h1 : Tendsto (fun n : ℕ =>
      eLpNorm (fun x => mollify ρ (epsSeq n) u₀ x - u₀ x) 2 volume) atTop (𝓝 0) :=
    (tendsto_eLpNorm_mollify_sub hρ one_le_two ENNReal.ofNat_ne_top hu₀2).comp tendsto_epsSeq
  have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal C *
      (eLpNorm (fun x => mollify ρ (epsSeq n) u₀ x - u₀ x) 2 volume *
        eLpNorm (fun x : ℂ => φ (t₀, x)) 2 volume)) atTop
      (𝓝 (ENNReal.ofReal C * (0 * eLpNorm (fun x : ℂ => φ (t₀, x)) 2 volume))) :=
    ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul_const h1 (Or.inr hφ2.eLpNorm_ne_top))
      (Or.inr ENNReal.ofReal_ne_top)
  rw [zero_mul, mul_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le)
    fun n => ?_
  obtain ⟨hmo, -⟩ := memLp_mollify hρ (epsSeq_pos n) one_le_two hu₀2
  calc ∫⁻ x, ‖Υ (mollify ρ (epsSeq n) u₀ x) * φ (t₀, x) - Υ (u₀ x) * φ (t₀, x)‖ₑ
      ≤ ∫⁻ x, ENNReal.ofReal C * (‖mollify ρ (epsSeq n) u₀ x - u₀ x‖ₑ * ‖φ (t₀, x)‖ₑ) := by
        refine lintegral_mono fun x => ?_
        rw [← sub_mul, enorm_mul, ← mul_assoc]
        exact mul_le_mul' (enorm_sub_le_of_abs hC hC0 _ _) le_rfl
    _ = ENNReal.ofReal C * ∫⁻ x, ‖mollify ρ (epsSeq n) u₀ x - u₀ x‖ₑ * ‖φ (t₀, x)‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * (eLpNorm (fun x => mollify ρ (epsSeq n) u₀ x - u₀ x) 2 volume *
          eLpNorm (fun x : ℂ => φ (t₀, x)) 2 volume) := by
        gcongr
        exact lintegral_enorm_mul_le_eLpNorm_two
          (hmo.aestronglyMeasurable.sub hu₀2.aestronglyMeasurable) hφ2.aestronglyMeasurable

/-- The mollified datum term is integrable. -/
theorem integrable_datum_mollify {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {u₀ : ℂ → ℝ} (hu₀2 : MemLp u₀ 2 volume) {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) {T : ℝ}
    {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) (t₀ : ℝ) :
    Integrable (fun x => Υ (mollify ρ ε u₀ x) * φ (t₀, x)) := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_le_of_isRenormalization hΥ
  obtain ⟨hmo, -⟩ := memLp_mollify hρ hε one_le_two hu₀2
  have hΥm : MemLp (fun x => Υ (mollify ρ ε u₀ x)) 2 volume := by
    refine (hmo.const_mul L).of_le
      ((continuous_of_isRenormalization hΥ).comp_aestronglyMeasurable hmo.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hL0]
    exact hL _
  exact hΥm.integrable_mul (memLp_slice hφ t₀ 2)

/-! ### The commutator term -/

/-- `φ Υ'(u_ε) C_ε[u,w] → 0` in `L¹((t₀,T)×ℝ²)` along `ε_n` (`lem:commutator`). -/
theorem tendsto_lintegral_comm_mollify {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {T t₀ : ℝ}
    (ht₀ : t₀ ∈ Ico 0 T) {w : ℝ → ℂ → ℂ} (hw : IsBddH1DivFreeField (Ioo 0 T) w)
    {u : ℝ → ℂ → ℝ} (hu2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 u) {Υ : ℝ → ℝ}
    (hΥ : IsRenormalization Υ) {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Tendsto (fun n : ℕ => ∫⁻ p in slabFrom t₀ T,
      ‖φ p * deriv Υ (mollify ρ (epsSeq n) (u p.1) p.2) * commEps ρ (epsSeq n) u w p.1 p.2‖ₑ)
      atTop (𝓝 0) := by
  obtain ⟨R, hR, b, hb, hsupp⟩ := exists_ball_of_isTestFunction hφ
  obtain ⟨A, hA0, hA⟩ := exists_bound_of_isTestFunction hφ
  obtain ⟨C, hC0, hC', -⟩ := exists_lipschitz_of_isRenormalization hΥ
  have hbT' : b < (b + T) / 2 := by linarith
  have hT' : (b + T) / 2 < T := by linarith
  have hc := (tendsto_lintegral_commEps_slab hρ ht₀.1 hw hu2 hT' hR).comp tendsto_epsSeq
  have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (A * C) *
      ∫⁻ p in Ioo t₀ ((b + T) / 2) ×ˢ ball (0 : ℂ) R, ‖commEps ρ (epsSeq n) u w p.1 p.2‖ₑ)
      atTop (𝓝 (ENNReal.ofReal (A * C) * 0)) :=
    ENNReal.Tendsto.const_mul hc (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le)
    fun n => ?_
  have hS : MeasurableSet (Ioo t₀ ((b + T) / 2) ×ˢ ball (0 : ℂ) R) :=
    measurableSet_Ioo.prod measurableSet_ball
  calc ∫⁻ p in slabFrom t₀ T,
        ‖φ p * deriv Υ (mollify ρ (epsSeq n) (u p.1) p.2) * commEps ρ (epsSeq n) u w p.1 p.2‖ₑ
      ≤ ∫⁻ p in slabFrom t₀ T, (Ioo t₀ ((b + T) / 2) ×ˢ ball (0 : ℂ) R).indicator
          (fun p => ENNReal.ofReal (A * C) * ‖commEps ρ (epsSeq n) u w p.1 p.2‖ₑ) p := by
        refine setLIntegral_mono' (measurableSet_Ioo.prod MeasurableSet.univ) fun p hp => ?_
        by_cases hφp : φ p = 0
        · simp [hφp]
        · have hpt : p ∈ tsupport φ := subset_tsupport _ hφp
          have hmem : p ∈ Ioo t₀ ((b + T) / 2) ×ˢ ball (0 : ℂ) R :=
            ⟨⟨hp.1.1, lt_of_le_of_lt (hsupp p hpt).1 hbT'⟩, (hsupp p hpt).2⟩
          rw [indicator_of_mem hmem, enorm_mul, enorm_mul, ENNReal.ofReal_mul hA0]
          refine mul_le_mul' (mul_le_mul' ?_ ?_) le_rfl
          · rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (hA p)
          · rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (hC' _)
    _ ≤ ∫⁻ p, (Ioo t₀ ((b + T) / 2) ×ˢ ball (0 : ℂ) R).indicator
          (fun p => ENNReal.ofReal (A * C) * ‖commEps ρ (epsSeq n) u w p.1 p.2‖ₑ) p :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (A * C) *
          ∫⁻ p in Ioo t₀ ((b + T) / 2) ×ˢ ball (0 : ℂ) R, ‖commEps ρ (epsSeq n) u w p.1 p.2‖ₑ := by
        rw [lintegral_indicator hS, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end NonUniqueEuler.Weak.TransportH
