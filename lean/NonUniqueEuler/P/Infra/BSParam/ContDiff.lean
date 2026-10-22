import NonUniqueEuler.Statement.WeakSolution
import NonUniqueEuler.Defs.Infra.ConvMinkowski
import NonUniqueEuler.I.Sec2.BSBasic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Proof: the Biot–Savart velocity of a space–time family with locally bounded support

Proof of `NonUniqueEuler/I/Infra/BSParam/ContDiff.lean` (same declarations, statements copied
verbatim). Manuscript: `lem:iterates`(iii), `B_global_smooth.tex:229-238`, and
`prop:iter-limit`, `B_global_smooth.tex:456-460`.

Structure. With `L` a continuous bilinear map `ℂ × E' → F` and `g : ℝ → ℂ → E'`, write
`Φ L g (t, x) = (K_BS ⋆[L] g t)(x) = ∫ L (K_BS z) (g t (x - z)) dz`.
* `velocityField G` is `Φ L₀ (ofReal ∘ G)` with `L₀ = (mul ℝ ℂ).flip`
  (`uncurry_velocityField_eq`, from `Conv.velocity_eq_convolution`).
* Smoothness: Mathlib's `contDiffOn_convolution_right_with_param` on each open slab
  `(-T, T) × ℂ`, with the compact set `closedBall 0 ρ_T`.
* Bounds, by induction on `k`, simultaneously for all `E'`, `F`, `L`, `g`:
  - `k = 0`: `‖Φ L g (t, x)‖ ≤ ‖L‖ M ∫_{B̄(x, ρ)} |K_BS| ≤ ‖L‖ M (1 + |B̄(0, ρ)|/(2π))`
    (`norm_conv_le`, `lintegral_closedBall_norm_kernel_le`: split `|K_BS| ≤ 1_{B₁}|K_BS| + 1/(2π)`);
  - `k → k + 1`: `fderiv (Φ L g) = Φ (L.precompR (ℝ × ℂ)) (fderiv ↿g)` everywhere
    (`fderiv_convParam_eq`, from `hasFDerivAt_convolution_right_with_param`), the slab support
    passes to `fderiv ↿g` (`slabSupport_fderiv`), and
    `‖D^{k+1} Φ‖ = ‖D^k (fderiv Φ)‖` (`norm_iteratedFDeriv_fderiv`).
  This is the manuscript's "differentiation under the integral sign … dominated by a constant
  multiple of the integrable function `|K_BS(z)| 1_{|z| ≤ ρ}`" with the derivatives on `G`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Convolution ENNReal Topology

namespace NonUniqueEuler.BSParamH

/-- The Biot–Savart kernel is locally integrable (`lem:BS-basic`(a)). -/
theorem locallyIntegrable_kernel : LocallyIntegrable biotSavartKernel volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨r, hr, hkr⟩ := hk.isBounded.subset_ball_lt 0 0
  exact (BS.integral_norm_biotSavartKernel_ball hr).1.mono_set hkr

/-- Pointwise: `|K_BS(z)| ≤ 1_{B₁}(z) |K_BS(z)| + 1/(2π)`. -/
theorem enorm_kernel_le (z : ℂ) :
    ‖biotSavartKernel z‖ₑ ≤
      (ball (0 : ℂ) 1).indicator (fun z => ‖biotSavartKernel z‖ₑ) z +
        ENNReal.ofReal (1 / (2 * Real.pi)) := by
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · rw [indicator_of_mem hz]
    exact le_self_add
  · rw [indicator_of_notMem hz, zero_add]
    have h1 : 1 ≤ ‖z‖ := by simpa [mem_ball_zero_iff] using hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      linarith
    rw [← ofReal_norm, BS.norm_biotSavartKernel_eq hz0]
    apply ENNReal.ofReal_le_ofReal
    rw [one_div]
    apply inv_anti₀ (by positivity)
    have := Real.pi_pos
    nlinarith

/-- `∫_{B̄(x, ρ)} |K_BS| ≤ 1 + |B̄(0, ρ)|/(2π)`, uniformly in the center `x`. -/
theorem lintegral_closedBall_norm_kernel_le (x : ℂ) (ρ : ℝ) :
    ∫⁻ z in closedBall x ρ, ‖biotSavartKernel z‖ₑ ≤
      ENNReal.ofReal 1 + ENNReal.ofReal (1 / (2 * Real.pi)) * volume (closedBall (0 : ℂ) ρ) := by
  calc ∫⁻ z in closedBall x ρ, ‖biotSavartKernel z‖ₑ
      ≤ ∫⁻ z in closedBall x ρ, ((ball (0 : ℂ) 1).indicator (fun z => ‖biotSavartKernel z‖ₑ) z +
          ENNReal.ofReal (1 / (2 * Real.pi))) := lintegral_mono fun z => enorm_kernel_le z
    _ = (∫⁻ z in closedBall x ρ, (ball (0 : ℂ) 1).indicator (fun z => ‖biotSavartKernel z‖ₑ) z) +
          ∫⁻ _ in closedBall x ρ, ENNReal.ofReal (1 / (2 * Real.pi)) :=
        lintegral_add_right _ measurable_const
    _ ≤ (∫⁻ z, (ball (0 : ℂ) 1).indicator (fun z => ‖biotSavartKernel z‖ₑ) z) +
          ENNReal.ofReal (1 / (2 * Real.pi)) * volume (closedBall x ρ) := by
        gcongr
        · exact Measure.restrict_le_self
        · rw [setLIntegral_const]
    _ = ENNReal.ofReal 1 + ENNReal.ofReal (1 / (2 * Real.pi)) * volume (closedBall (0 : ℂ) ρ) := by
        rw [lintegral_indicator measurableSet_ball,
          (BS.integral_norm_biotSavartKernel_ball one_pos).2.2,
          Measure.addHaar_closedBall_center]

/-- The uniform constant `1 + |B̄(0, ρ)|/(2π)` of `lintegral_closedBall_norm_kernel_le`. -/
theorem kernelBallConst_ne_top (ρ : ℝ) :
    ENNReal.ofReal 1 + ENNReal.ofReal (1 / (2 * Real.pi)) * volume (closedBall (0 : ℂ) ρ) ≠ ⊤ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_closedBall_lt_top).ne⟩

section Generic

variable {E' F : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The base estimate: if `‖g‖ ≤ M` and `g = 0` outside `B̄(0, ρ)`, then
`‖(K_BS ⋆[L] g)(x)‖ ≤ ‖L‖ M (1 + |B̄(0, ρ)|/(2π))` for every `x`. -/
theorem norm_conv_le (L : ℂ →L[ℝ] E' →L[ℝ] F) {g : ℂ → E'} {M ρ : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y, ‖g y‖ ≤ M) (hsupp : ∀ y, ρ < ‖y‖ → g y = 0) (x : ℂ) :
    ‖(biotSavartKernel ⋆[L, volume] g) x‖ ≤
      ‖L‖ * M * (ENNReal.ofReal 1 +
        ENNReal.ofReal (1 / (2 * Real.pi)) * volume (closedBall (0 : ℂ) ρ)).toReal := by
  set B := ENNReal.ofReal 1 + ENNReal.ofReal (1 / (2 * Real.pi)) * volume (closedBall (0 : ℂ) ρ)
  have hB : B ≠ ⊤ := kernelBallConst_ne_top ρ
  have hpt : ∀ z, ‖L (biotSavartKernel z) (g (x - z))‖ₑ ≤
      (closedBall x ρ).indicator
        (fun z => ENNReal.ofReal (‖L‖ * M) * ‖biotSavartKernel z‖ₑ) z := by
    intro z
    by_cases hz : z ∈ closedBall x ρ
    · rw [indicator_of_mem hz, ← ofReal_norm, ← ofReal_norm,
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      calc ‖L (biotSavartKernel z) (g (x - z))‖
          ≤ ‖L‖ * ‖biotSavartKernel z‖ * ‖g (x - z)‖ := L.le_opNorm₂ _ _
        _ ≤ ‖L‖ * ‖biotSavartKernel z‖ * M := by gcongr; exact hM _
        _ = ‖L‖ * M * ‖biotSavartKernel z‖ := by ring
    · have hxz : ρ < ‖x - z‖ := by
        rw [mem_closedBall, dist_eq_norm, not_le, norm_sub_rev] at hz
        exact hz
      rw [hsupp _ hxz, map_zero, enorm_zero]
      exact bot_le
  have hint : ‖(biotSavartKernel ⋆[L, volume] g) x‖ₑ ≤ ENNReal.ofReal (‖L‖ * M) * B := by
    rw [convolution_def]
    calc ‖∫ z, L (biotSavartKernel z) (g (x - z))‖ₑ
        ≤ ∫⁻ z, ‖L (biotSavartKernel z) (g (x - z))‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z, (closedBall x ρ).indicator
            (fun z => ENNReal.ofReal (‖L‖ * M) * ‖biotSavartKernel z‖ₑ) z := lintegral_mono hpt
      _ = ∫⁻ z in closedBall x ρ, ENNReal.ofReal (‖L‖ * M) * ‖biotSavartKernel z‖ₑ :=
          lintegral_indicator measurableSet_closedBall _
      _ = ENNReal.ofReal (‖L‖ * M) * ∫⁻ z in closedBall x ρ, ‖biotSavartKernel z‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (‖L‖ * M) * B := by
          gcongr
          exact lintegral_closedBall_norm_kernel_le x ρ
  have hfin : ENNReal.ofReal (‖L‖ * M) * B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB
  calc ‖(biotSavartKernel ⋆[L, volume] g) x‖
      = (‖(biotSavartKernel ⋆[L, volume] g) x‖ₑ).toReal := (toReal_enorm _).symm
    _ ≤ (ENNReal.ofReal (‖L‖ * M) * B).toReal := ENNReal.toReal_mono hfin hint
    _ = ‖L‖ * M * B.toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- The slab support passes to the derivative: if `g(t, x) = 0` for `|t| ≤ T`, `|x| > ρ_T`, then
`D↿g(t, x) = 0` for `|t| ≤ T`, `|x| > ρ_{T+1}`. -/
theorem slabSupport_fderiv {g : ℝ → ℂ → E'}
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → g t x = 0) :
    ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ →
      (fun p y => fderiv ℝ (Function.uncurry g) (p, y)) t x = 0 := by
  intro T
  obtain ⟨ρ, hρ⟩ := hsupp (T + 1)
  refine ⟨ρ, fun t ht x hx => ?_⟩
  refine (hasFDerivAt_zero_of_eventually_const (0 : E') ?_).fderiv
  have M1 : Ioo (-(T + 1)) (T + 1) ∈ 𝓝 t :=
    Ioo_mem_nhds (by linarith [ht.1]) (by linarith [ht.2])
  have M2 : {y : ℂ | ρ < ‖y‖} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hx
  rw [nhds_prod_eq]
  filter_upwards [prod_mem_prod M1 M2]
  rintro ⟨p, y⟩ ⟨hp, hy⟩
  exact hρ p (Ioo_subset_Icc_self hp) y hy

/-- The derivative of `Φ L g (t, x) = (K_BS ⋆[L] g t)(x)` is `Φ (L.precompR (ℝ × ℂ)) (D↿g)`, at
every point. -/
theorem fderiv_convParam_eq (L : ℂ →L[ℝ] E' →L[ℝ] F) {g : ℝ → ℂ → E'}
    (hg : ContDiff ℝ 1 (Function.uncurry g))
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → g t x = 0) :
    fderiv ℝ (fun q : ℝ × ℂ => (biotSavartKernel ⋆[L, volume] g q.1) q.2) =
      fun q : ℝ × ℂ => (biotSavartKernel ⋆[L.precompR (ℝ × ℂ), volume]
        (fun p y => fderiv ℝ (Function.uncurry g) (p, y)) q.1) q.2 := by
  funext q₀
  obtain ⟨ρ, hρ⟩ := hsupp (|q₀.1| + 1)
  have hgs : ∀ p, ∀ x, p ∈ Ioo (-(|q₀.1| + 1)) (|q₀.1| + 1) → x ∉ closedBall (0 : ℂ) ρ →
      g p x = 0 := by
    intro p x hp hx
    apply hρ p (Ioo_subset_Icc_self hp) x
    simpa [mem_closedBall_zero_iff] using hx
  have hq₀ : q₀.1 ∈ Ioo (-(|q₀.1| + 1)) (|q₀.1| + 1) :=
    ⟨by linarith [neg_abs_le q₀.1], by linarith [le_abs_self q₀.1]⟩
  exact (hasFDerivAt_convolution_right_with_param L isOpen_Ioo (isCompact_closedBall 0 ρ) hgs
    locallyIntegrable_kernel hg.contDiffOn q₀ hq₀).fderiv

end Generic

/-- The derivative bounds, by induction on `k`, for all `E'`, `F`, `L`, `g` at once. -/
theorem norm_iteratedFDeriv_convParam_le (k : ℕ) :
    ∀ {E' F : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F]
      [NormedSpace ℝ F] (L : ℂ →L[ℝ] E' →L[ℝ] F) (g : ℝ → ℂ → E'),
      ContDiff ℝ k (Function.uncurry g) →
      (∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → g t x = 0) →
      ∀ T : ℝ, ∃ C : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ,
        ‖iteratedFDeriv ℝ k (fun q : ℝ × ℂ => (biotSavartKernel ⋆[L, volume] g q.1) q.2)
          (t, x)‖ ≤ C := by
  induction k with
  | zero =>
    intro E' F _ _ _ _ L g hg hsupp T
    obtain ⟨ρ, hρ⟩ := hsupp T
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : ℂ) ρ)).exists_bound_of_continuousOn
      hg.continuous.continuousOn
    set M := max C 0
    have hM : ∀ t ∈ Icc (-T) T, ∀ y, ‖g t y‖ ≤ M := by
      intro t ht y
      by_cases hy : ‖y‖ ≤ ρ
      · exact (hC (t, y) ⟨ht, mem_closedBall_zero_iff.2 hy⟩).trans (le_max_left _ _)
      · rw [hρ t ht y (not_le.1 hy), norm_zero]
        exact le_max_right _ _
    refine ⟨‖L‖ * M * (ENNReal.ofReal 1 +
        ENNReal.ofReal (1 / (2 * Real.pi)) * volume (closedBall (0 : ℂ) ρ)).toReal,
      fun t ht x => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    exact norm_conv_le L (le_max_right _ _) (hM t ht) (hρ t ht) x
  | succ k ih =>
    intro E' F _ _ _ _ L g hg hsupp T
    have hg1 : ContDiff ℝ 1 (Function.uncurry g) := hg.of_le (by exact_mod_cast Nat.succ_pos k)
    have hgk : ContDiff ℝ k
        (Function.uncurry fun p y => fderiv ℝ (Function.uncurry g) (p, y)) := by
      have h := hg.fderiv_right (m := (k : WithTop ℕ∞)) (by push_cast; exact le_rfl)
      have he : (Function.uncurry fun p y => fderiv ℝ (Function.uncurry g) (p, y)) =
          fderiv ℝ (Function.uncurry g) := by
        funext q
        rfl
      rw [he]
      exact h
    obtain ⟨C, hC⟩ := ih (L.precompR (ℝ × ℂ)) (fun p y => fderiv ℝ (Function.uncurry g) (p, y))
      hgk (slabSupport_fderiv hsupp) T
    refine ⟨C, fun t ht x => ?_⟩
    rw [← norm_iteratedFDeriv_fderiv, fderiv_convParam_eq L hg1 hsupp]
    exact hC t ht x

/-- `velocityField G` as a parametric convolution `(K_BS ⋆[L₀] (ofReal ∘ G t))(x)`. -/
theorem uncurry_velocityField_eq (G : ℝ → ℂ → ℝ) :
    Function.uncurry (velocityField G) = fun q : ℝ × ℂ =>
      (biotSavartKernel ⋆[(ContinuousLinearMap.mul ℝ ℂ).flip, volume]
        (fun p y => (G p y : ℂ)) q.1) q.2 := by
  funext q
  rcases q with ⟨t, x⟩
  simp only [Function.uncurry_apply_pair, velocityField]
  rw [convolution_flip, ← Conv.velocity_eq_convolution]

/-- Transfer of smoothness and slab support to `ofReal ∘ G`. -/
theorem contDiff_ofReal_uncurry {n : WithTop ℕ∞} {G : ℝ → ℂ → ℝ}
    (hG : ContDiff ℝ n (Function.uncurry G)) :
    ContDiff ℝ n (Function.uncurry fun p y => (G p y : ℂ)) := by
  have h := Complex.ofRealCLM.contDiff.comp hG
  have he : (Function.uncurry fun p y => (G p y : ℂ)) = Complex.ofRealCLM ∘ Function.uncurry G := by
    funext ⟨p, y⟩
    simp
  rw [he]
  exact h

end NonUniqueEuler.BSParamH

namespace NonUniqueEuler.BS

open NonUniqueEuler.BSParamH

/-- The Biot–Savart velocity of a `C^n` space–time family with locally (in time) bounded support
is `C^n` in `(t, x)` (`B_global_smooth.tex:229-238`). -/
theorem contDiff_velocityField_of_slabSupport {n : ℕ∞} {G : ℝ → ℂ → ℝ}
    (hG : ContDiff ℝ n (Function.uncurry G))
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → G t x = 0) :
    ContDiff ℝ n (Function.uncurry (velocityField G)) := by
  rw [uncurry_velocityField_eq]
  have hG' := contDiff_ofReal_uncurry hG
  refine contDiff_iff_contDiffAt.2 fun q => ?_
  obtain ⟨ρ, hρ⟩ := hsupp (|q.1| + 1)
  have hgs : ∀ p, ∀ x, p ∈ Ioo (-(|q.1| + 1)) (|q.1| + 1) → x ∉ closedBall (0 : ℂ) ρ →
      (G p x : ℂ) = 0 := by
    intro p x hp hx
    rw [hρ p (Ioo_subset_Icc_self hp) x (by simpa [mem_closedBall_zero_iff] using hx),
      Complex.ofReal_zero]
  have hq : q.1 ∈ Ioo (-(|q.1| + 1)) (|q.1| + 1) :=
    ⟨by linarith [neg_abs_le q.1], by linarith [le_abs_self q.1]⟩
  have hOn := contDiffOn_convolution_right_with_param (μ := volume)
    (ContinuousLinearMap.mul ℝ ℂ).flip isOpen_Ioo (isCompact_closedBall 0 ρ) hgs
    locallyIntegrable_kernel hG'.contDiffOn
  exact hOn.contDiffAt (prod_mem_nhds (isOpen_Ioo.mem_nhds hq) univ_mem)

/-- The derivatives of order `k ≤ n` of the velocity of such a family are bounded on every slab
`[-T, T] × ℝ²` (`B_global_smooth.tex:229-238`). -/
theorem iteratedFDeriv_velocityField_bounded {n : ℕ∞} {G : ℝ → ℂ → ℝ}
    (hG : ContDiff ℝ n (Function.uncurry G))
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → G t x = 0)
    {T : ℝ} (hT : 0 < T) {k : ℕ} (hk : (k : ℕ∞) ≤ n) :
    ∃ C : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ,
      ‖iteratedFDeriv ℝ k (Function.uncurry (velocityField G)) (t, x)‖ ≤ C := by
  rw [uncurry_velocityField_eq]
  have hGk : ContDiff ℝ k (Function.uncurry fun p y => (G p y : ℂ)) :=
    (contDiff_ofReal_uncurry hG).of_le (by exact_mod_cast hk)
  have hsupp' : ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → (G t x : ℂ) = 0 := by
    intro T
    obtain ⟨ρ, hρ⟩ := hsupp T
    exact ⟨ρ, fun t ht x hx => by rw [hρ t ht x hx, Complex.ofReal_zero]⟩
  exact norm_iteratedFDeriv_convParam_le k (ContinuousLinearMap.mul ℝ ℂ).flip _ hGk hsupp' T

end NonUniqueEuler.BS
