import NonUniqueEuler.H.Sec3.Compact.Velocity
import NonUniqueEuler.I.Sec2.WeakIntegrability
import NonUniqueEuler.I.Infra.ConvMinkowski.Measurable
import NonUniqueEuler.I.Infra.JointRep.Slab

/-!
# Helpers for `prop:compact`: the limit is a weak solution with datum `g`

Helper file of `P/Sec3/Compact.lean`. Manuscript: proof of `prop:compact`, last paragraph
(`03_compactness.tex:322-340`).

Restructured argument (recorded as a deviation; same ingredients). Fix `φ ∈ 𝒟_T` with
`supp φ ⊂ ℝ × B_r`. For each `t ∈ (0,T)` the inner integral
`Aₙ(t) = ∫ ωₙ(t)(∂_tφ(t) + vₙ(t)·∇φ(t))` converges to `A(t) = ∫ ω(t)(∂_tφ(t) + v(t)·∇φ(t))`:
the `∂_tφ` part by (i), the nonlinear part by weak–strong pairing (`ωₙ(t) ⇀ ω(t)` in `L²`, bounded
by `M`; `vₙ(t)·∇φ(t) → v(t)·∇φ(t)` in `L²` since `vₙ(t) → v(t)` in `L²(B_r)`), which is the
manuscript's splitting `ωₙ(vₙ - v)·∇φ + (ωₙ - ω) v·∇φ` performed at a fixed time. Moreover
`|Aₙ(t)| ≤ M (‖∂_tφ(t)‖₂ + ‖∇φ‖_∞ C(2,r) M)` uniformly; dominated convergence in `t` gives
`∫₀ᵀ Aₙ → ∫₀ᵀ A`. With `∫ gₙ φ(0) → ∫ g φ(0)` (weak convergence of the data), the identity
`(eq:weak)` passes to the limit; `isWeakSolution_iff_of_memX` (`I/Sec2/WeakIntegrability.lean`)
supplies the integrability fields of `IsWeakSolution`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.PropCompact

open Weak

variable {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}

/-! ### Fields `x ↦ B(x) w(x)` with `B` bounded and supported in `B_r` -/

section Field

variable {B : ℂ → ℂ →L[ℝ] ℝ} {r D : ℝ}

theorem support_clm_apply_subset (hB0 : ∀ x : ℂ, r ≤ ‖x‖ → B x = 0) (w : ℂ → ℂ) :
    Function.support (fun x => B x (w x)) ⊆ ball (0 : ℂ) r := by
  intro x hx
  rw [mem_ball, dist_zero_right]
  by_contra hcon
  exact hx (by show B x (w x) = 0; rw [hB0 x (not_lt.1 hcon)]; rfl)

theorem eLpNorm_clm_apply_le (hBD : ∀ x, ‖B x‖ ≤ D) (hB0 : ∀ x : ℂ, r ≤ ‖x‖ → B x = 0)
    (w : ℂ → ℂ) :
    eLpNorm (fun x => B x (w x)) 2 volume ≤
      ENNReal.ofReal D * eLpNorm w 2 (volume.restrict (ball (0 : ℂ) r)) := by
  rw [← eLpNorm_restrict_eq_of_support_subset (support_clm_apply_subset hB0 w)]
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (ae_of_all _ fun x => ?_) 2
  exact ((B x).le_opNorm (w x)).trans (mul_le_mul_of_nonneg_right (hBD x) (norm_nonneg _))

theorem aestronglyMeasurable_clm_apply (hBc : Continuous B) {w : ℂ → ℂ}
    (hw : AEStronglyMeasurable w volume) :
    AEStronglyMeasurable (fun x => B x (w x)) volume :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
    hBc.aestronglyMeasurable hw

theorem memLp_clm_apply (hBc : Continuous B) (hBD : ∀ x, ‖B x‖ ≤ D)
    (hB0 : ∀ x : ℂ, r ≤ ‖x‖ → B x = 0) {w : ℂ → ℂ} (hw : AEStronglyMeasurable w volume)
    (hw2 : MemLp w 2 (volume.restrict (ball (0 : ℂ) r))) :
    MemLp (fun x => B x (w x)) 2 volume :=
  ⟨aestronglyMeasurable_clm_apply hBc hw, (eLpNorm_clm_apply_le hBD hB0 w).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hw2.eLpNorm_lt_top)⟩

/-- The `L²` distance of `B wₙ` and `B w` is controlled by `‖wₙ - w‖_{L²(B_r)}`. -/
theorem eLpNorm_clm_apply_sub_le (hBD : ∀ x, ‖B x‖ ≤ D) (hB0 : ∀ x : ℂ, r ≤ ‖x‖ → B x = 0)
    (w w' : ℂ → ℂ) :
    eLpNorm ((fun x => B x (w x)) - fun x => B x (w' x)) 2 volume ≤
      ENNReal.ofReal D * eLpNorm (w - w') 2 (volume.restrict (ball (0 : ℂ) r)) := by
  have : ((fun x => B x (w x)) - fun x => B x (w' x)) = fun x => B x ((w - w') x) := by
    funext x
    simp only [Pi.sub_apply, map_sub]
  rw [this]
  exact eLpNorm_clm_apply_le hBD hB0 _

/-- The bound of the inner integral at a fixed time. -/
theorem abs_integral_slice_le {a f : ℂ → ℝ} (ha : MemLp a 2 volume) (hf : MemLp f 2 volume)
    (hBc : Continuous B) (hD : 0 ≤ D) (hBD : ∀ x, ‖B x‖ ≤ D)
    (hB0 : ∀ x : ℂ, r ≤ ‖x‖ → B x = 0) {w : ℂ → ℂ} (hw : AEStronglyMeasurable w volume)
    (hw2 : MemLp w 2 (volume.restrict (ball (0 : ℂ) r))) {Mf Da W : ℝ} (hMf : 0 ≤ Mf)
    (hW : 0 ≤ W) (hfb : (eLpNorm f 2 volume).toReal ≤ Mf) (hab : (eLpNorm a 2 volume).toReal ≤ Da)
    (hwb : eLpNorm w 2 (volume.restrict (ball (0 : ℂ) r)) ≤ ENNReal.ofReal W) :
    |∫ x, f x * (a x + B x (w x))| ≤ Mf * (Da + D * W) := by
  have hbw := memLp_clm_apply hBc hBD hB0 hw hw2
  have hsplit : ∫ x, f x * (a x + B x (w x)) =
      (∫ x, f x * a x) + ∫ x, f x * B x (w x) := by
    rw [← integral_add (integrable_mul_of_L2 hf ha) (integrable_mul_of_L2 hf hbw)]
    congr 1
    funext x
    ring
  have hbn : (eLpNorm (fun x => B x (w x)) 2 volume).toReal ≤ D * W := by
    refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hD hW) ?_
    refine (eLpNorm_clm_apply_le hBD hB0 w).trans ?_
    rw [ENNReal.ofReal_mul hD]
    gcongr
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have h1 := abs_integral_mul_le hf ha
  have h2 := abs_integral_mul_le hf hbw
  have hf0 : 0 ≤ (eLpNorm f 2 volume).toReal := ENNReal.toReal_nonneg
  calc |∫ x, f x * a x| + |∫ x, f x * B x (w x)|
      ≤ (eLpNorm f 2 volume).toReal * (eLpNorm a 2 volume).toReal +
          (eLpNorm f 2 volume).toReal * (eLpNorm (fun x => B x (w x)) 2 volume).toReal :=
        add_le_add h1 h2
    _ ≤ Mf * Da + Mf * (D * W) := by
        gcongr
    _ = Mf * (Da + D * W) := by ring

/-- The convergence of the inner integral at a fixed time. -/
theorem tendsto_integral_slice {a : ℂ → ℝ} (ha : MemLp a 2 volume) (hBc : Continuous B)
    (hBD : ∀ x, ‖B x‖ ≤ D) (hB0 : ∀ x : ℂ, r ≤ ‖x‖ → B x = 0)
    {fs : ℕ → ℂ → ℝ} {f : ℂ → ℝ} {Mf : ℝ} (hfs : ∀ n, MemLp (fs n) 2 volume)
    (hf : MemLp f 2 volume) (hfsb : ∀ n, (eLpNorm (fs n) 2 volume).toReal ≤ Mf)
    (hwk : ∀ ψ : ℂ → ℝ, MemLp ψ 2 volume →
      Tendsto (fun n => ∫ x, fs n x * ψ x) atTop (𝓝 (∫ x, f x * ψ x)))
    {ws : ℕ → ℂ → ℂ} {w : ℂ → ℂ} (hwsm : ∀ n, AEStronglyMeasurable (ws n) volume)
    (hws2 : ∀ n, MemLp (ws n) 2 (volume.restrict (ball (0 : ℂ) r)))
    (hwm : AEStronglyMeasurable w volume) (hw2 : MemLp w 2 (volume.restrict (ball (0 : ℂ) r)))
    (hwt : Tendsto (fun n => eLpNorm (ws n - w) 2 (volume.restrict (ball (0 : ℂ) r))) atTop
      (𝓝 0)) :
    Tendsto (fun n => ∫ x, fs n x * (a x + B x (ws n x))) atTop
      (𝓝 (∫ x, f x * (a x + B x (w x)))) := by
  have hbws := fun n => memLp_clm_apply hBc hBD hB0 (hwsm n) (hws2 n)
  have hbw := memLp_clm_apply hBc hBD hB0 hwm hw2
  have hsplit : ∀ (u : ℂ → ℝ) (b : ℂ → ℝ), MemLp u 2 volume → MemLp b 2 volume →
      ∫ x, u x * (a x + b x) = (∫ x, u x * a x) + ∫ x, u x * b x := by
    intro u b hu hb
    rw [← integral_add (integrable_mul_of_L2 hu ha) (integrable_mul_of_L2 hu hb)]
    congr 1
    funext x
    ring
  have hseq : (fun n => ∫ x, fs n x * (a x + B x (ws n x))) =
      fun n => (∫ x, fs n x * a x) + ∫ x, fs n x * B x (ws n x) :=
    funext fun n => hsplit (fs n) _ (hfs n) (hbws n)
  rw [hseq, hsplit f _ hf hbw]
  refine (hwk a ha).add ?_
  refine tendsto_integral_mul_of_weak_strong hfs hbws hbw hwk hfsb ?_
  have hlim : Tendsto (fun n => ENNReal.ofReal D *
      eLpNorm (ws n - w) 2 (volume.restrict (ball (0 : ℂ) r))) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hwt (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    (fun n => eLpNorm_clm_apply_sub_le hBD hB0 (ws n) w)

end Field

/-- `L²` bound for a function bounded by `D` and vanishing outside `B_r`. -/
theorem toReal_eLpNorm_le_of_bound {a : ℂ → ℝ} {r D : ℝ} (hab : ∀ x, |a x| ≤ D)
    (ha0 : ∀ x : ℂ, r ≤ ‖x‖ → a x = 0) :
    (eLpNorm a 2 volume).toReal ≤
      (volume (ball (0 : ℂ) r) ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal D).toReal := by
  have hsupp : Function.support a ⊆ ball (0 : ℂ) r := by
    intro x hx
    rw [mem_ball, dist_zero_right]
    by_contra hcon
    exact hx (ha0 x (not_lt.1 hcon))
  have hle : eLpNorm a 2 volume ≤
      volume (ball (0 : ℂ) r) ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal D := by
    rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
    have := eLpNorm_le_of_ae_bound (μ := volume.restrict (ball (0 : ℂ) r)) (p := 2) (f := a)
      (C := D) (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hab x)
    rwa [Measure.restrict_apply_univ] at this
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    measure_ball_lt_top.ne) ENNReal.ofReal_ne_top) hle

/-- **The limit is a weak solution with datum `g`** (`03_compactness.tex:322-340`). -/
theorem isWeakSolution_limit (h : IsCompactSeq T M gs g ωs) (hM : 0 ≤ M) {ω : ℝ → ℂ → ℝ}
    (hX : MemX 2 T ω) (hi : WeakTendstoUnifL2On ωs ω (Icc 0 T))
    (hω2 : ∀ t ∈ Icc 0 T, MemLp (ω t) 2 volume)
    (hωb : ∀ t ∈ Icc 0 T, normL1LpE 2 (ω t) ≤ ENNReal.ofReal M) :
    IsWeakSolution 2 T g ω := by
  have hT := h.T_pos
  refine (isWeakSolution_iff_of_memX (by norm_num) hT h.memLp_one
    (by simpa using h.memLp_two) hX).2 fun φ hφ => ?_
  obtain ⟨r, hr, D, hD, hφb⟩ := exists_testFn_bounds hφ
  obtain ⟨C, hC0, hC⟩ := BS.velocity_bounds_two hr
  set Da := (volume (ball (0 : ℂ) r) ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal D).toReal
    with hDa
  -- the data at a fixed time
  have ha : ∀ t, MemLp (fun x => timeDeriv φ t x) 2 volume := fun t =>
    memLp_of_continuous_of_vanish (testFn_continuous_timeDeriv hφ t)
      (fun x hx => ((hφb t x).2.2.2 hx).2.1) 2
  have hab : ∀ t, (eLpNorm (fun x => timeDeriv φ t x) 2 volume).toReal ≤ Da := fun t =>
    toReal_eLpNorm_le_of_bound (fun x => (hφb t x).2.1) (fun x hx => ((hφb t x).2.2.2 hx).2.1)
  have hvm : ∀ f : ℂ → ℝ, MemLp f 2 volume → AEStronglyMeasurable (velocity f) volume :=
    fun f hf => (Conv.stronglyMeasurable_velocity hf.aestronglyMeasurable).aestronglyMeasurable
  have hA : ∀ (u : ℝ → ℂ → ℝ) (t : ℝ),
      ∫ x, transportIntegrand u (velocityField u) φ (t, x) =
        ∫ x, u t x * ((fun x => timeDeriv φ t x) x +
          (fun x => fderiv ℝ (fun y => φ (t, y)) x) x (velocity (u t) x)) := fun u t => rfl
  have hpt : ∀ t ∈ Ioo 0 T,
      Tendsto (fun n => ∫ x, transportIntegrand (ωs n) (velocityField (ωs n)) φ (t, x)) atTop
        (𝓝 (∫ x, transportIntegrand ω (velocityField ω) φ (t, x))) := by
    intro t ht
    have ht' := Ioo_subset_Icc_self ht
    simp only [hA]
    exact tendsto_integral_slice (ha t) (testFn_continuous_fderiv_slice hφ t)
      (fun x => (hφb t x).2.2.1) (fun x hx => ((hφb t x).2.2.2 hx).2.2)
      (fun n => seq_memLp_two h n ht') (hω2 t ht')
      (fun n => seq_toReal_eLpNorm_two_le h hM n ht') (fun ψ hψ => (hi ψ hψ).tendsto_at ht')
      (fun n => hvm _ (seq_memLp_two h n ht'))
      (fun n => (velocity_memLp_le hC0 hC hM (seq_memLp_two h n ht') (h.bound n t ht')).1)
      (hvm _ (hω2 t ht')) (velocity_memLp_le hC0 hC hM (hω2 t ht') (hωb t ht')).1
      (velocity_slice_tendsto h hi hω2 hr ht')
  have hbd : ∀ n, ∀ t ∈ Ioo 0 T,
      ‖∫ x, transportIntegrand (ωs n) (velocityField (ωs n)) φ (t, x)‖ ≤
        M * (Da + D * (C * M)) := by
    intro n t ht
    have ht' := Ioo_subset_Icc_self ht
    rw [Real.norm_eq_abs, hA]
    exact abs_integral_slice_le (ha t) (seq_memLp_two h n ht')
      (testFn_continuous_fderiv_slice hφ t) hD (fun x => (hφb t x).2.2.1)
      (fun x hx => ((hφb t x).2.2.2 hx).2.2) (hvm _ (seq_memLp_two h n ht'))
      (velocity_memLp_le hC0 hC hM (seq_memLp_two h n ht') (h.bound n t ht')).1 hM
      (mul_nonneg hC0.le hM) (seq_toReal_eLpNorm_two_le h hM n ht') (hab t)
      (velocity_memLp_le hC0 hC hM (seq_memLp_two h n ht') (h.bound n t ht')).2
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun t => ∫ x, transportIntegrand (ωs n) (velocityField (ωs n)) φ (t, x))
      (volume.restrict (Ioo 0 T)) := fun n =>
    JointRep.aestronglyMeasurable_integral_slab
      ((h.weakSolution n).weak.integrableOn φ hφ).aestronglyMeasurable
  have h1 := tendsto_integral_of_dominated_convergence (fun _ => M * (Da + D * (C * M))) hmeas
    (integrable_const _) (fun n => ae_restrict_of_forall_mem measurableSet_Ioo (hbd n))
    (ae_restrict_of_forall_mem measurableSet_Ioo hpt)
  have hφ0 : MemLp (fun x => φ (0, x)) 2 volume :=
    memLp_of_continuous_of_vanish (hφ.contDiff.continuous.comp (Continuous.prodMk_right 0))
      (fun x hx => ((hφb 0 x).2.2.2 hx).1) 2
  have h2 : Tendsto (fun n => ∫ x, gs n x * φ (0, x)) atTop (𝓝 (∫ x, g x * φ (0, x))) :=
    (weakTendstoLp_two_iff.1 h.weakTendsto).2.2 _ hφ0
  have hid : ∀ n, (∫ t in Ioo 0 T,
      ∫ x, transportIntegrand (ωs n) (velocityField (ωs n)) φ (t, x)) +
        ∫ x, gs n x * φ (0, x) = 0 :=
    fun n => (h.weakSolution n).weak.identity φ hφ
  have h3 := h1.add h2
  rw [show (fun n => (∫ t in Ioo 0 T,
      ∫ x, transportIntegrand (ωs n) (velocityField (ωs n)) φ (t, x)) +
        ∫ x, gs n x * φ (0, x)) = fun _ => (0 : ℝ) from funext hid] at h3
  exact (tendsto_nhds_unique tendsto_const_nhds h3).symm

end NonUniqueEuler.Compact.PropCompact
