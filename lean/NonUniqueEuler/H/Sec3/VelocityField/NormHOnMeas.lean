import NonUniqueEuler.H.Sec3.VelocityField.NormSup
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Helpers for `I/Sec3/VelocityField`: measurability of `t ↦ ‖f(t)‖_{H^k(B_R)}`

Helper file of `P/Sec3/VelocityField.lean` (the measurability clause of
`Weak.IsBddH1DivFreeField` in the remark `03_compactness.tex:243-247`).

* `aestronglyMeasurable_l2On_weakDerivOn`: if `f` is a.e. strongly measurable on `I × ℂ` and,
  for a.e. `t`, `f(t)` has a weak derivative `∂_{vs} f(t)` in `L²(B_R)`, then
  `t ↦ ‖∂_{vs} f(t)‖_{L²(B_R)}` (the chosen weak derivative) is a.e. strongly measurable.
  Proof: with a dense sequence `d_m = φ_m` of test functions in `L²(B_R)`
  (`exists_denseRange_testFn_ball`), `‖g‖_{L²(B_R)} = sup_m re ⟪d_m, g⟫ / ‖d_m‖`
  (`enorm_eq_iSup_re_inner`) and `⟪φ_m, ∂_{vs} f(t)⟫ = (-1)^{|vs|} ∫ f(t) ∂_{vs} φ̄_m`, which is
  measurable in `t` by Fubini (`AEStronglyMeasurable.integral_prod_right'`).
* `aestronglyMeasurable_normHOn`: the same for `t ↦ ‖f(t)‖_{H^k(B_R)}` when `f(t) ∈ H^k(B_R)`
  for a.e. `t`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff ComplexConjugate

namespace NonUniqueEuler.H.VelocityField

/-- The conjugate of a test function is a test function. -/
theorem isTestFn_conj {V : Set ℂ} {φ : ℂ → ℂ} (hφ : Sob.IsTestFn V φ) :
    Sob.IsTestFn V (fun x => conj (φ x)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Complex.conjCLE.contDiff.comp hφ.smooth
  · exact hφ.compact.comp_left (g := fun z : ℂ => conj z) (map_zero _)
  · exact (tsupport_comp_subset (g := fun z : ℂ => conj z) (map_zero _) φ).trans hφ.subset

/-- Measurability in `t` of the `L²(B_R)` norm of the chosen weak derivative `∂_{vs} f(t)`. -/
theorem aestronglyMeasurable_l2On_weakDerivOn {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ → ℂ}
    (hf : AEStronglyMeasurable (Function.uncurry f) (μ.prod volume)) {R : ℝ} (hR : 0 < R)
    (vs : List ℂ)
    (h : ∀ᵐ t ∂μ, ∃ G : ℂ → ℂ, MemLp G 2 (volume.restrict (ball (0 : ℂ) R)) ∧
      Sob.HasWeakDerivOn (ball (0 : ℂ) R) vs (f t) G) :
    AEStronglyMeasurable
      (fun t => Sob.l2On (ball (0 : ℂ) R) (Sob.weakDerivOn (ball (0 : ℂ) R) vs (f t))) μ := by
  set B : Set ℂ := ball (0 : ℂ) R with hB
  set ν : Measure ℂ := volume.restrict B with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  obtain ⟨D, hD, hDφ⟩ := exists_denseRange_testFn_ball hR
  choose φ hφT hφae using hDφ
  set ψ : ℕ → ℂ → ℂ := fun m x => conj (φ m x) with hψ
  have hψT : ∀ m, Sob.IsTestFn B (ψ m) := fun m => isTestFn_conj (hφT m)
  set ξ : ℕ → ℂ → ℂ := fun m => Sob.iterDirDeriv vs (ψ m) with hξ
  have hξc : ∀ m, Continuous (ξ m) := fun m => ((hψT m).iterDirDeriv vs).continuous
  set F : ℝ → ℝ≥0∞ := fun t => ⨆ m, ENNReal.ofReal
    (RCLike.re ((-1 : ℂ) ^ vs.length * ∫ x, f t x * ξ m x) / ‖D m‖) with hF_def
  have hF : AEMeasurable F μ := by
    refine AEMeasurable.iSup fun m => ?_
    have h1 : AEStronglyMeasurable (fun t => ∫ x, f t x * ξ m x) μ := by
      have : AEStronglyMeasurable (fun p : ℝ × ℂ => f p.1 p.2 * ξ m p.2) (μ.prod volume) :=
        hf.mul ((hξc m).comp continuous_snd).aestronglyMeasurable
      exact this.integral_prod_right'
    have h2 : AEStronglyMeasurable
        (fun t => RCLike.re ((-1 : ℂ) ^ vs.length * ∫ x, f t x * ξ m x)) μ :=
      (RCLike.continuous_re.comp (continuous_const.mul continuous_id)).comp_aestronglyMeasurable h1
    exact ENNReal.measurable_ofReal.comp_aemeasurable (h2.aemeasurable.div_const _)
  have hae : ∀ᵐ t ∂μ, eLpNorm (Sob.weakDerivOn B vs (f t)) 2 ν = F t := by
    filter_upwards [h] with t ⟨G, hG2, hGw⟩
    have hG1 : MemLp G 1 ν := hG2.mono_exponent one_le_two
    have hGloc : LocallyIntegrableOn G B :=
      IntegrableOn.locallyIntegrableOn (memLp_one_iff_integrable.1 hG1)
    have hW := Sob.weakDerivOn_ae_eq isOpen_ball hGloc hGw
    have hWG : Sob.weakDerivOn B vs (f t) =ᵐ[ν] G := (ae_restrict_iff' measurableSet_ball).2 hW
    rw [eLpNorm_congr_ae hWG, ← Lp.enorm_toLp hG2, enorm_eq_iSup_re_inner (𝕜 := ℂ) hD]
    refine iSup_congr fun m => ?_
    congr 3
    rw [L2.inner_def]
    calc ∫ a, inner ℂ ((D m : ℂ → ℂ) a) ((hG2.toLp G : ℂ → ℂ) a) ∂ν
        = ∫ a, G a * ψ m a ∂ν := by
          refine integral_congr_ae ?_
          filter_upwards [hφae m, hG2.coeFn_toLp] with a h1 h2
          rw [h1, h2, RCLike.inner_apply]
      _ = ∫ a, G a * ψ m a := by
          refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
          have : ψ m x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx ((hψT m).subset h)
          rw [this, mul_zero]
      _ = (-1 : ℂ) ^ vs.length * ∫ x, f t x * ξ m x := by
          have := hGw (ψ m) (hψT m)
          rw [show (∫ x, f t x * ξ m x) = ∫ x, f t x * Sob.iterDirDeriv vs (ψ m) x from rfl,
            this, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  have hW : AEMeasurable (fun t => eLpNorm (Sob.weakDerivOn B vs (f t)) 2 ν) μ :=
    hF.congr (hae.mono fun t ht => ht.symm)
  exact hW.ennreal_toReal.aestronglyMeasurable

/-- Measurability in `t` of `‖f(t)‖_{H^k(B_R)}`, when `f(t) ∈ H^k(B_R)` for a.e. `t`. -/
theorem aestronglyMeasurable_normHOn {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ → ℂ}
    (hf : AEStronglyMeasurable (Function.uncurry f) (μ.prod volume)) {R : ℝ} (hR : 0 < R)
    {k : ℕ} (h : ∀ᵐ t ∂μ, Sob.MemHOn k (ball (0 : ℂ) R) (f t)) :
    AEStronglyMeasurable (fun t => Sob.normHOn k (ball (0 : ℂ) R) (f t)) μ := by
  have hγ : ∀ γ ∈ Sob.multiIdx k, AEStronglyMeasurable
      (fun t => Sob.l2On (ball (0 : ℂ) R) (Sob.weakPartialOn (ball (0 : ℂ) R) γ (f t)) ^ 2) μ :=
    fun γ hγ => (aestronglyMeasurable_l2On_weakDerivOn hf hR (Sob.pdList γ)
      (h.mono fun t ht => ht.deriv γ hγ)).pow 2
  exact Real.continuous_sqrt.comp_aestronglyMeasurable
    (Finset.aestronglyMeasurable_fun_sum (Sob.multiIdx k) hγ)

end NonUniqueEuler.H.VelocityField
