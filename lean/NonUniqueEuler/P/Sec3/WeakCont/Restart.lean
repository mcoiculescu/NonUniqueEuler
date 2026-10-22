import NonUniqueEuler.Defs.Sec3.Transport
import NonUniqueEuler.Defs.Sec3.Paths
import NonUniqueEuler.H.Sec3.WeakCont.Restart.Slice
import NonUniqueEuler.H.Sec3.WeakCont.Restart.Kappa
import NonUniqueEuler.H.Sec3.WeakCont.Restart.Limit

/-!
# Proof: `lem:weak-cont`, step 3 — restarting `(te)` at a time `t₀ ∈ (0,T)` (part (c))

Proof of `I/Sec3/WeakCont/Restart.lean` (manuscript `03_compactness.tex:209-225`, `b = 2`).

* `continuousOn_integral_mul_slice`: `g(t) - g(s) = ∫ ũ(t) (φ(t) - φ(s)) + ∫ (ũ(t) - ũ(s)) φ(s)`;
  the first term is at most `N L |t - s| |K|^{1/2}` (Cauchy–Schwarz, `φ` is `L`-Lipschitz and its
  slices vanish off the compact `K = Prod.snd '' tsupport φ`), the second tends to `0` by weak
  continuity.
* `solvesTE_restart`: test `(te)` with `ϰ_h φ`, `ϰ_h(t) = ϰ((t - t₀)/h)`
  (`Restart.kappa_identity`), and let `h → 0⁺` (`Restart.tendsto_integral_kappaShift_mul`,
  `Restart.tendsto_integral_deriv_kappaShift_mul`).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology

namespace NonUniqueEuler.Weak.WeakCont

/-- Continuity of `t ↦ ∫ ũ(t) φ(t,·)` on `[0,T]` for a weakly continuous `ũ` bounded in `L²` and
`φ ∈ C_c¹(ℝ × ℝ²)` (`03_compactness.tex:216-219`). -/
theorem continuousOn_integral_mul_slice {T N : ℝ} {ũ : ℝ → ℂ → ℝ}
    (hũ : IsWeakContL2On (Icc 0 T) ũ)
    (hũN : ∀ t ∈ Icc 0 T, eLpNorm (ũ t) 2 volume ≤ ENNReal.ofReal N) {φ : ℝ × ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ContinuousOn (fun t => ∫ x, ũ t x * φ (t, x)) (Icc 0 T) := by
  obtain ⟨C, hC⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc one_ne_zero
  have hφcont : Continuous φ := hφ.continuous
  have hsl : ∀ t, MemLp (fun x : ℂ => φ (t, x)) 2 volume := fun t =>
    Restart.memLp_slice hφcont hφc t 2
  intro s hs
  rw [ContinuousWithinAt, ← tendsto_sub_nhds_zero_iff]
  have hdec : ∀ t ∈ Icc 0 T, (∫ x, ũ t x * φ (t, x)) - ∫ x, ũ s x * φ (s, x) =
      (∫ x, ũ t x * (φ (t, x) - φ (s, x))) +
        ((∫ x, ũ t x * φ (s, x)) - ∫ x, ũ s x * φ (s, x)) := by
    intro t ht
    have h1 : Integrable (fun x => ũ t x * φ (t, x)) volume :=
      (hũ.memLp t ht).integrable_mul (hsl t)
    have h2 : Integrable (fun x => ũ t x * φ (s, x)) volume :=
      (hũ.memLp t ht).integrable_mul (hsl s)
    have e : (fun x => ũ t x * (φ (t, x) - φ (s, x))) =
        fun x => ũ t x * φ (t, x) - ũ t x * φ (s, x) := by
      funext x
      ring
    rw [e, integral_sub h1 h2]
    ring
  have hA : Tendsto (fun t => ∫ x, ũ t x * (φ (t, x) - φ (s, x))) (𝓝[Icc 0 T] s) (𝓝 0) := by
    have hbound : ∀ᶠ t in 𝓝[Icc 0 T] s, ‖∫ x, ũ t x * (φ (t, x) - φ (s, x))‖ ≤
        (ENNReal.ofReal N).toReal * ((C : ℝ) * |t - s| *
          (volume (Prod.snd '' tsupport φ) ^ (1 / (2 : ℝ≥0∞).toReal)).toReal) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [Real.norm_eq_abs]
      refine (Restart.abs_integral_mul_le (hũ.memLp t ht) ((hsl t).sub (hsl s))).trans ?_
      exact mul_le_mul (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hũN t ht))
        (Restart.toReal_eLpNorm_slice_sub_le hC hφc t s) ENNReal.toReal_nonneg
        ENNReal.toReal_nonneg
    have hcont : Continuous fun t : ℝ => (ENNReal.ofReal N).toReal * ((C : ℝ) * |t - s| *
        (volume (Prod.snd '' tsupport φ) ^ (1 / (2 : ℝ≥0∞).toReal)).toReal) := by
      fun_prop
    have hlim := (hcont.tendsto s).mono_left (nhdsWithin_le_nhds (s := Icc 0 T))
    simp only [sub_self, abs_zero, mul_zero, zero_mul] at hlim
    exact squeeze_zero_norm' hbound hlim
  have hB : Tendsto (fun t => (∫ x, ũ t x * φ (s, x)) - ∫ x, ũ s x * φ (s, x))
      (𝓝[Icc 0 T] s) (𝓝 0) := by
    rw [tendsto_sub_nhds_zero_iff]
    exact hũ.continuousOn _ (hsl s) s hs
  have hAB := hA.add hB
  rw [add_zero] at hAB
  refine hAB.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hdec t ht).symm

namespace Restart

/-- `C^∞ ⇒ C¹`. -/
theorem contDiff_one_of_isTestFunction {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    ContDiff ℝ 1 φ :=
  hφ.contDiff.of_le (by exact_mod_cast le_top)

/-- Fubini on the slab: the slice integrals of `transportIntegrand u w φ` are integrable in time,
and the slices are integrable for a.e. `t ∈ (0,T)`. -/
theorem integrable_transportIntegrand_prod {T : ℝ} {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ}
    {u₀ : ℂ → ℝ} (hte : SolvesTE 0 T u w u₀) {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Integrable (transportIntegrand u w φ)
      ((volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure ℂ)) := by
  rw [← JointRep.volume_restrict_slab]
  exact hte.integrableOn φ hφ

/-- `(te)` tested with `ϰ_h φ`, `h > 0` (`03_compactness.tex:211-215`):
`∫_0^T ϰ_h' g + ∫_0^T ϰ_h I = 0`, with `g(t) = ∫ ũ(t) φ(t)` and `I(t) = ∫ u (∂_t φ + w·∇φ)(t)`. -/
theorem kappa_identity {T t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) {u ũ : ℝ → ℂ → ℝ}
    {w : ℝ → ℂ → ℂ} {u₀ : ℂ → ℝ} (hte : SolvesTE 0 T u w u₀)
    (hũ : IsWeakContL2On (Icc 0 T) ũ)
    (hae : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ũ t =ᵐ[volume] u t)
    {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ)
    (hg : ContinuousOn (fun t => ∫ x, ũ t x * φ (t, x)) (Icc 0 T)) {h : ℝ} (hh : 0 < h) :
    (∫ t in Ioo 0 T, deriv (fun t : ℝ => kappa ((t - t₀) / h)) t * ∫ x, ũ t x * φ (t, x)) +
      ∫ t in Ioo 0 T, kappa ((t - t₀) / h) * ∫ x, transportIntegrand u w φ (t, x) = 0 := by
  have hφ1 := contDiff_one_of_isTestFunction hφ
  have hφh := isTestFunction_kappaShift_mul hφ t₀ h
  have e := hte.identity _ hφh
  have hk0 : kappa ((0 - t₀) / h) = 0 := kappaShift_eq_zero hh ht₀.1.le
  have hdat : (fun x : ℂ => u₀ x * (fun p : ℝ × ℂ => kappa ((p.1 - t₀) / h) * φ p) (0, x)) =
      fun _ => 0 := by
    funext x
    simp only [hk0, zero_mul, mul_zero]
  have hprod := integrable_transportIntegrand_prod hte hφ
  have hI : IntegrableOn (fun t => ∫ x, transportIntegrand u w φ (t, x)) (Ioo 0 T) :=
    hprod.integral_prod_left
  have hinner : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
      ∫ x, transportIntegrand u w (fun p : ℝ × ℂ => kappa ((p.1 - t₀) / h) * φ p) (t, x) =
        deriv (fun t : ℝ => kappa ((t - t₀) / h)) t * (∫ x, ũ t x * φ (t, x)) +
          kappa ((t - t₀) / h) * ∫ x, transportIntegrand u w φ (t, x) := by
    filter_upwards [hae, hprod.prod_right_ae, ae_restrict_mem measurableSet_Ioo] with t h1 h2 h3
    have hmem : MemLp (ũ t) 2 volume := hũ.memLp t (Ioo_subset_Icc_self h3)
    have hũφ : Integrable (fun x => ũ t x * φ (t, x)) volume :=
      hmem.integrable_mul (memLp_slice hφ.contDiff.continuous hφ.hasCompactSupport t 2)
    have hcongr : (fun x => u t x * φ (t, x)) =ᵐ[volume] fun x => ũ t x * φ (t, x) :=
      h1.mono fun x hx => by simp only [hx]
    have huφ : Integrable (fun x => u t x * φ (t, x)) volume := hũφ.congr hcongr.symm
    have hfun : (fun x => transportIntegrand u w
        (fun p : ℝ × ℂ => kappa ((p.1 - t₀) / h) * φ p) (t, x)) =
        fun x => deriv (fun t : ℝ => kappa ((t - t₀) / h)) t * (u t x * φ (t, x)) +
          kappa ((t - t₀) / h) * transportIntegrand u w φ (t, x) :=
      funext fun x => transportIntegrand_kappaShift_mul u w hφ1 t₀ h t x
    rw [hfun, integral_add (huφ.const_mul _) (h2.const_mul _), integral_const_mul,
      integral_const_mul, integral_congr_ae hcongr]
  have hint1 : IntegrableOn
      (fun t => deriv (fun t : ℝ => kappa ((t - t₀) / h)) t * ∫ x, ũ t x * φ (t, x))
      (Ioo 0 T) :=
    ((continuous_deriv_kappaShift t₀ h).continuousOn.mul hg).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hint2 : IntegrableOn
      (fun t => kappa ((t - t₀) / h) * ∫ x, transportIntegrand u w φ (t, x)) (Ioo 0 T) :=
    hI.bdd_mul (continuous_kappaShift t₀ h).aestronglyMeasurable
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs]
        exact abs_kappaShift_le_one t₀ h t)
  rw [hdat, integral_zero, add_zero, integral_congr_ae hinner, integral_add hint1 hint2] at e
  exact e

end Restart

/-- `lem:weak-cont`(c) for `t₀ ∈ (0,T)` (`03_compactness.tex:209-225`): `u` satisfies `(te)` on
`[t₀,T)` with field `w` and datum `ũ(t₀)`. -/
theorem solvesTE_restart {T N t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) {u ũ : ℝ → ℂ → ℝ}
    {w : ℝ → ℂ → ℂ} {u₀ : ℂ → ℝ} (hte : SolvesTE 0 T u w u₀)
    (hũ : IsWeakContL2On (Icc 0 T) ũ)
    (hũN : ∀ t ∈ Icc 0 T, eLpNorm (ũ t) 2 volume ≤ ENNReal.ofReal N)
    (hae : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ũ t =ᵐ[volume] u t) :
    SolvesTE t₀ T u w (ũ t₀) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · exact (hte.integrableOn φ hφ).mono_set
      (prod_mono (Ioo_subset_Ioo_left ht₀.1.le) subset_rfl)
  · exact (hũ.memLp t₀ (Ioo_subset_Icc_self ht₀)).integrable_mul
      (Restart.memLp_slice hφ.contDiff.continuous hφ.hasCompactSupport t₀ 2)
  · have hg := continuousOn_integral_mul_slice hũ hũN (Restart.contDiff_one_of_isTestFunction hφ)
      hφ.hasCompactSupport
    have hI : IntegrableOn (fun t => ∫ x, transportIntegrand u w φ (t, x)) (Ioo 0 T) :=
      (Restart.integrable_transportIntegrand_prod hte hφ).integral_prod_left
    have hsum := (Restart.tendsto_integral_deriv_kappaShift_mul ht₀ hg).add
      (Restart.tendsto_integral_kappaShift_mul ht₀.1 hI)
    have h0 : Tendsto (fun h : ℝ =>
        (∫ t in Ioo 0 T,
          deriv (fun t : ℝ => kappa ((t - t₀) / h)) t * ∫ x, ũ t x * φ (t, x)) +
        ∫ t in Ioo 0 T, kappa ((t - t₀) / h) * ∫ x, transportIntegrand u w φ (t, x))
        (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact (Restart.kappa_identity ht₀ hte hũ hae hφ hg hh).symm
    have hlim := tendsto_nhds_unique hsum h0
    beta_reduce at hlim
    linarith

end NonUniqueEuler.Weak.WeakCont
