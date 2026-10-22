import NonUniqueEuler.Defs.Sec3.Transport
import NonUniqueEuler.Defs.Sec3.Commutator
import NonUniqueEuler.Defs.Sec2.Spaces
import NonUniqueEuler.I.Sec2.Velocity
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Sec2.WeakIntegrability
import NonUniqueEuler.I.Infra.ConvMinkowski.Measurable
import NonUniqueEuler.H.Sec3.VelocityField.NormHOnMeas
import NonUniqueEuler.H.Sec3.VelocityField.LocalH1

/-!
# Proof: the velocity field of a weak solution (`03_compactness.tex:57-66`, `:228-237`, `:243-247`)

Proof of `I/Sec3/VelocityField.lean`.

* `memLinfLp_velocityField`: `lem:velocity`(a) (`BS.velocity_bounds`, `p = q`) at a.e. time,
  with the essential bound `M` of `‖ω(t)‖_{L¹∩L^q}`; space–time measurability from
  `Conv.aestronglyMeasurable_velocityField_slab`.
* `integrable_smul_velocityField`: `|ω v| ≤ |ω| (|K| ∗ |ω|)` (`Conv.enorm_velocity_le`), Tonelli
  (`lintegral_prod_le`) and `∫ |ω(t)| (|K| ∗ |ω(t)|) ≤ C M²` (`exists_bound_convAbs_of_memX`).
* `isTEData`: `ω ∈ L¹((0,T)×ℝ²)` (Tonelli, `‖ω(t)‖₁ ≤ M`); `v ∈ L¹((0,T)×B_R)` by
  `∫_{B_R} |K| ∗ |ω(t)| ≤ R ‖ω(t)‖₁` (`BS.setLIntegral_convAbs_ball_le`); `ωv` from the previous
  item; `ω^in ∈ L¹ ⊂ L¹_loc`.
* `isBddH1DivFreeField_velocityField`: at a.e. time, `v(t) ∈ L²(B_R)` (`BS.velocity_bounds_two`)
  and `∇v(t) ∈ L²` with `‖∇v(t)‖₂ = ‖ω(t)‖₂` (`BS.gradL2_velocity`), so `v(t) ∈ H¹(B_R)` with a
  bound uniform in `t` (`H.VelocityField.memHOn_one_of_hasGradH`); the measurability of
  `t ↦ ‖v(t)‖_{H¹(B_R)}` is `H.VelocityField.aestronglyMeasurable_normHOn` (countable supremum
  over a dense sequence of test functions, as indicated in the interface); `div v(t) = 0` by
  `BS.isWeaklyDivFree_velocity_of_L1`.

**Deviation.** For `v ∈ L^∞(0,T; L¹(B_R))` (part of `IsTEData`) the proof uses the elementary
bound `‖v(t)‖_{L¹(B_R)} ≤ R ‖ω(t)‖_{L¹}` of `lem:BS-basic`(e) instead of `lem:velocity`(a); the
statement is the same.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak

/-- The slab measure is the product of the restricted measures. -/
theorem _root_.NonUniqueEuler.H.VelocityField.restrict_slab_eq_prod (T : ℝ) :
    (volume.restrict (slab T) : Measure (ℝ × ℂ)) =
      (volume.restrict (Ioo (0 : ℝ) T)).prod volume := by
  rw [slab, Measure.volume_eq_prod, Measure.restrict_prod_eq_prod_univ]

theorem _root_.NonUniqueEuler.H.VelocityField.restrict_Ioo_prod_ball_eq_prod (T R : ℝ) :
    (volume.restrict (Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R) : Measure (ℝ × ℂ)) =
      (volume.restrict (Ioo (0 : ℝ) T)).prod (volume.restrict (ball (0 : ℂ) R)) := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

theorem _root_.NonUniqueEuler.H.VelocityField.lintegral_const_Ioo_lt_top (T c : ℝ) :
    ∫⁻ _ in Ioo (0 : ℝ) T, ENNReal.ofReal c < ⊤ := by
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

open NonUniqueEuler.H.VelocityField in
/-- `03_compactness.tex:228-233`: for a weak solution in `X_q(T)`, `4/3 < q < ∞`, the velocity
`v = K ∗ ω` lies in `L^∞(0,T;L²(B_R))` and in `L^∞(0,T;L^{q'}(B_R))` for every `R > 0`. -/
theorem _root_.NonUniqueEuler.IsWeakSolution.memLinfLp_velocityField {q T : ℝ}
    {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ} (h : IsWeakSolution q T ωin ω) {R : ℝ} (hR : 0 < R) :
    Prelim.MemLinfLp (Ioo 0 T) (ball (0 : ℂ) R) 2 (velocityField ω) ∧
      Prelim.MemLinfLp (Ioo 0 T) (ball (0 : ℂ) R) (ENNReal.ofReal q.conjExponent)
        (velocityField ω) := by
  obtain ⟨C, hC, hCb⟩ := BS.velocity_bounds h.q_gt hR
  obtain ⟨M, hM⟩ := h.memX.essBounded
  have hmeas : AEStronglyMeasurable (Function.uncurry (velocityField ω))
      (volume.restrict (Ioo 0 T ×ˢ ball (0 : ℂ) R)) :=
    (Conv.aestronglyMeasurable_velocityField_slab h.memX.aestronglyMeasurable).mono_measure
      (Measure.restrict_mono (prod_mono subset_rfl (subset_univ _)) le_rfl)
  have hCM : 0 ≤ C * max M 0 := mul_nonneg hC.le (le_max_right _ _)
  have hb : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
      MemLp (velocityField ω t) (ENNReal.ofReal q.conjExponent)
          (volume.restrict (ball (0 : ℂ) R)) ∧
        MemLp (velocityField ω t) 2 (volume.restrict (ball (0 : ℂ) R)) ∧
        eLpNorm (velocityField ω t) (ENNReal.ofReal q.conjExponent)
            (volume.restrict (ball (0 : ℂ) R)) +
          eLpNorm (velocityField ω t) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
          ENNReal.ofReal (C * max M 0) := by
    filter_upwards [hM] with t ht
    obtain ⟨h1, hq, hle⟩ := ht
    obtain ⟨-, -, hmq, hm2, hbd, -⟩ := hCb (ω t) h1 hq
    refine ⟨hmq, hm2, hbd.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    exact mul_le_mul_of_nonneg_left (hle.trans (le_max_left _ _)) hC.le
  refine ⟨⟨hmeas, C * max M 0, hb.mono fun t ht => ⟨ht.2.1, ?_⟩⟩,
    ⟨hmeas, C * max M 0, hb.mono fun t ht => ⟨ht.1, ?_⟩⟩⟩
  · exact ENNReal.toReal_le_of_le_ofReal hCM (le_trans le_add_self ht.2.2)
  · exact ENNReal.toReal_le_of_le_ofReal hCM (le_trans le_self_add ht.2.2)

open NonUniqueEuler.H.VelocityField in
/-- `03_compactness.tex:233-235`: for a weak solution in `X_q(T)`, `ωv ∈ L¹((0,T)×ℝ²)`. -/
theorem _root_.NonUniqueEuler.IsWeakSolution.integrable_smul_velocityField {q T : ℝ}
    {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ} (h : IsWeakSolution q T ωin ω) :
    Integrable (fun p : ℝ × ℂ => ω p.1 p.2 • velocityField ω p.1 p.2)
      (volume.restrict (slab T)) := by
  obtain ⟨C, -, hCb⟩ := exists_bound_convAbs_of_memX h.q_gt
  obtain ⟨M, hM⟩ := h.memX.essBounded
  have hK := hCb T M ω hM
  refine ⟨h.memX.aestronglyMeasurable.smul
    (Conv.aestronglyMeasurable_velocityField_slab h.memX.aestronglyMeasurable), ?_⟩
  rw [HasFiniteIntegral, restrict_slab_eq_prod]
  calc ∫⁻ p, ‖ω p.1 p.2 • velocityField ω p.1 p.2‖ₑ
        ∂((volume.restrict (Ioo (0 : ℝ) T)).prod volume)
      ≤ ∫⁻ p, ‖ω p.1 p.2‖ₑ * Conv.convAbs biotSavartKernel (ω p.1) p.2
          ∂((volume.restrict (Ioo (0 : ℝ) T)).prod volume) := by
        refine lintegral_mono fun p => ?_
        rw [enorm_smul]
        gcongr
        exact Conv.enorm_velocity_le _ _
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) T, ∫⁻ x, ‖ω t x‖ₑ * Conv.convAbs biotSavartKernel (ω t) x :=
        lintegral_prod_le _
    _ ≤ ∫⁻ _ in Ioo (0 : ℝ) T, ENNReal.ofReal (C * M ^ 2) := lintegral_mono_ae hK
    _ < ⊤ := lintegral_const_Ioo_lt_top T _

open NonUniqueEuler.H.VelocityField in
/-- `03_compactness.tex:57-66`: a weak solution in `X_q(T)` satisfies the standing assumptions of
`(te)` on `[0,T)` with field `v = K ∗ ω` and datum `ω^in` (`u = ω`, `v`, `ωv` integrable on
`(0,T') × B_R`, `ω^in ∈ L¹_loc`). -/
theorem _root_.NonUniqueEuler.IsWeakSolution.isTEData {q T : ℝ} {ωin : ℂ → ℝ}
    {ω : ℝ → ℂ → ℝ} (h : IsWeakSolution q T ωin ω) :
    IsTEData 0 T ω (velocityField ω) ωin := by
  obtain ⟨M, hM⟩ := h.memX.essBounded
  -- `‖ω(t)‖_{L¹} ≤ M` for a.e. `t`
  have hM1 : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
      MemLp (ω t) 1 volume ∧ eLpNorm (ω t) 1 volume ≤ ENNReal.ofReal M := by
    filter_upwards [hM] with t ht
    obtain ⟨h1, -, hle⟩ := ht
    refine ⟨h1, ?_⟩
    have hM0 : 0 ≤ M := le_trans (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) hle
    exact (ENNReal.le_ofReal_iff_toReal_le h1.eLpNorm_ne_top hM0).2
      (le_trans (le_add_of_nonneg_right ENNReal.toReal_nonneg) hle)
  have hωslab : IntegrableOn (Function.uncurry ω) (slab T) := by
    refine ⟨h.memX.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, restrict_slab_eq_prod]
    calc ∫⁻ p, ‖Function.uncurry ω p‖ₑ ∂((volume.restrict (Ioo (0 : ℝ) T)).prod volume)
        ≤ ∫⁻ t in Ioo (0 : ℝ) T, ∫⁻ x, ‖ω t x‖ₑ := lintegral_prod_le _
      _ ≤ ∫⁻ _ in Ioo (0 : ℝ) T, ENNReal.ofReal M := by
          refine lintegral_mono_ae (hM1.mono fun t ht => ?_)
          rw [← eLpNorm_one_eq_lintegral_enorm]
          exact ht.2
      _ < ⊤ := lintegral_const_Ioo_lt_top T _
  have hvball : ∀ R : ℝ, 0 < R →
      IntegrableOn (Function.uncurry (velocityField ω)) (Ioo 0 T ×ˢ ball (0 : ℂ) R) := by
    intro R hR
    refine ⟨(Conv.aestronglyMeasurable_velocityField_slab
      h.memX.aestronglyMeasurable).mono_measure
        (Measure.restrict_mono (prod_mono subset_rfl (subset_univ _)) le_rfl), ?_⟩
    rw [HasFiniteIntegral, restrict_Ioo_prod_ball_eq_prod]
    calc ∫⁻ p, ‖Function.uncurry (velocityField ω) p‖ₑ
          ∂((volume.restrict (Ioo (0 : ℝ) T)).prod (volume.restrict (ball (0 : ℂ) R)))
        ≤ ∫⁻ t in Ioo (0 : ℝ) T, ∫⁻ x in ball (0 : ℂ) R, ‖velocityField ω t x‖ₑ :=
          lintegral_prod_le _
      _ ≤ ∫⁻ t in Ioo (0 : ℝ) T, ∫⁻ x in ball (0 : ℂ) R,
            Conv.convAbs biotSavartKernel (ω t) x :=
          lintegral_mono fun t => lintegral_mono fun x => Conv.enorm_velocity_le _ _
      _ ≤ ∫⁻ _ in Ioo (0 : ℝ) T, ENNReal.ofReal (R * M) := by
          refine lintegral_mono_ae (hM1.mono fun t ht => ?_)
          refine (BS.setLIntegral_convAbs_ball_le ht.1 hR).trans ?_
          rw [ENNReal.ofReal_mul hR.le]
          gcongr
          exact ht.2
      _ < ⊤ := lintegral_const_Ioo_lt_top T _
  have hωv : IntegrableOn (fun p : ℝ × ℂ => ω p.1 p.2 • velocityField ω p.1 p.2) (slab T) :=
    h.integrable_smul_velocityField
  refine ⟨fun T' hT' R _ => hωslab.mono_set ?_, fun T' hT' R hR => (hvball R hR).mono_set ?_,
    fun T' hT' R _ => hωv.mono_set ?_,
    (memLp_one_iff_integrable.1 h.datum_memLp_one).locallyIntegrable⟩
  · exact prod_mono (Ioo_subset_Ioo_right hT'.le) (subset_univ _)
  · exact prod_mono (Ioo_subset_Ioo_right hT'.le) subset_rfl
  · exact prod_mono (Ioo_subset_Ioo_right hT'.le) (subset_univ _)

open NonUniqueEuler.H.VelocityField in
/-- `03_compactness.tex:243-247`: if `ω ∈ L^∞(0,T;L¹) ∩ L^∞(0,T;L²)`, then
`v = K ∗ ω ∈ L^∞(0,T;W^{1,2}(B_R))` for every `R > 0` and `div v = 0`
(`lem:velocity`(c), `lem:BS-basic`(e)). -/
theorem isBddH1DivFreeField_velocityField {T : ℝ} {ω : ℝ → ℂ → ℝ}
    (h1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 ω) (h2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 ω) :
    IsBddH1DivFreeField (Ioo 0 T) (velocityField ω) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry (velocityField ω))
      (volume.restrict (Ioo 0 T ×ˢ univ)) :=
    Conv.aestronglyMeasurable_velocityField_slab h1.aestronglyMeasurable
  obtain ⟨M₁, hM₁⟩ := h1.essBounded
  obtain ⟨M₂, hM₂⟩ := h2.essBounded
  have hsl : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), MemLp (ω t) 1 volume ∧
      MemLp (ω t) 2 volume ∧ (eLpNorm (ω t) 1 volume).toReal ≤ M₁ ∧
        (eLpNorm (ω t) 2 volume).toReal ≤ M₂ := by
    filter_upwards [hM₁, hM₂] with t ht1 ht2
    rw [Measure.restrict_univ] at ht1 ht2
    exact ⟨ht1.1, ht2.1, ht1.2, ht2.2⟩
  have hkey : ∀ R : ℝ, 0 < R → ∃ M : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
      Sob.MemHOn 1 (ball (0 : ℂ) R) (velocityField ω t) ∧
        Sob.normHOn 1 (ball (0 : ℂ) R) (velocityField ω t) ≤ M := by
    intro R hR
    obtain ⟨C, hC, hCb⟩ := BS.velocity_bounds_two hR
    refine ⟨Real.sqrt ((Sob.multiIdx 1).card • (C * (M₁ + M₂) + M₂) ^ 2),
      hsl.mono fun t ht => ?_⟩
    obtain ⟨ha, hb, hc, hd⟩ := ht
    obtain ⟨-, -, hv2, hvb, -⟩ := hCb (ω t) ha hb
    obtain ⟨hgrad, hgradeq⟩ := BS.gradL2_velocity ha hb
    have hloc : LocallyIntegrableOn (velocity (ω t)) (ball (0 : ℂ) R) :=
      (BS.locallyIntegrable_velocity_of_L1 ha).locallyIntegrableOn _
    obtain ⟨hH, hterm⟩ := memHOn_one_of_hasGradH isOpen_ball hv2 hloc hgrad
    refine ⟨hH, normHOn_le_of_forall_le fun γ hγ => (hterm γ hγ).trans ?_⟩
    have hl2 : Sob.l2On (ball (0 : ℂ) R) (velocity (ω t)) ≤ C * (M₁ + M₂) := by
      have h0 : Sob.l2On (ball (0 : ℂ) R) (velocity (ω t)) ≤ C * Prelim.normL1Lp 2 (ω t) :=
        ENNReal.toReal_le_of_le_ofReal
          (mul_nonneg hC.le (Prelim.normL1Lp_nonneg _ _)) hvb
      exact h0.trans (mul_le_mul_of_nonneg_left (add_le_add hc hd) hC.le)
    rw [hgradeq]
    exact add_le_add hl2 hd
  refine ⟨hmeas, fun R hR => ?_, hkey, ?_⟩
  · obtain ⟨M, hM⟩ := hkey R hR
    have hf : AEStronglyMeasurable (Function.uncurry (velocityField ω))
        ((volume.restrict (Ioo (0 : ℝ) T)).prod volume) := by
      rw [← restrict_slab_eq_prod]
      exact hmeas
    exact aestronglyMeasurable_normHOn hf hR (hM.mono fun t ht => ht.1)
  · filter_upwards [hsl] with t ht
    exact BS.isWeaklyDivFree_velocity_of_L1 ht.1

end NonUniqueEuler.Weak
