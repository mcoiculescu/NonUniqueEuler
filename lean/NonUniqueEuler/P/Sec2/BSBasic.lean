import NonUniqueEuler.Defs.Sec2.BiotSavart
import NonUniqueEuler.I.Infra.Polar.Power
import NonUniqueEuler.I.Infra.ConvMinkowski.Young
import NonUniqueEuler.I.Infra.ConvMinkowski.Measurable
import NonUniqueEuler.I.Infra.Polar.Rearrangement
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.Polar.RadialDeriv

/-!
# Proof: `lem:BS-basic` (a), (b), (c), (e), the basic properties of the Biot–Savart kernel

Proof of `I/Sec2/BSBasic.lean` (`02_prelim.tex:142-302`). Same declarations, same statements.

* (a) `K_BS(w) = (i/(2π)) conj(w⁻¹)` (`biotSavartKernel_eq_conj_inv`), so `K_BS` is smooth off `0`
  and `D K_BS(z) v = (i/(2π)) conj(-v/z²)`, whence `|D K_BS(z) v| = |v|/(2π|z|²)`; each entry
  `∂_l (K_BS)_i` is bounded by this modulus. (This replaces the manuscript's componentwise
  computation; same bound.) `∫_{B_ρ} |K_BS| = ρ` from `Polar.setIntegral_ball_norm_rpow` (exponent
  `-1`), using `‖K_BS(z)‖ = (2π)⁻¹‖z‖^{-1}` for every `z`.
* (b) The manuscript's split at radius `r`, `convAbs_le_split`, with `r = s/(2‖g‖_∞)`,
  `s = (2‖g‖₁‖g‖_∞/π)^{1/2}` (the manuscript's optimal radius, written without nested roots);
  the degenerate case `‖g‖₁‖g‖_∞ = 0` is `g = 0` a.e.
* (e) Tonelli (`Conv.setLIntegral_convAbs`) and the disk rearrangement
  (`Polar.setLIntegral_ball_sub_le`); a.e. finiteness on each `B_{n+1}`.
  The divergence: Fubini reduces to `J(y) = ∫ Dφ(y+z) K_BS(z) dz`; instead of the divergence
  theorem on `{|z| > ε}` we use polar coordinates directly (`Polar.integral_eq_integral_Ioi_
  intervalIntegral`): `Dφ(z) K_BS(z) = (2π|z|²)⁻¹ ∂_θ φ(z)` and `∫₀^{2π} ∂_θ φ(re^{iθ}) dθ = 0`
  (`Polar.intervalIntegral_angular_deriv_eq_zero`). This is the same identity (`K_BS · z = 0`
  and `div K_BS = 0` are encoded in `K_BS(z) = (2π|z|²)⁻¹ z^⊥`).
* (c) `Conv.eLpNorm_convAbs_ball_le` with `∫_{B_{R+ρ}} |K_BS| = R + ρ`; the a.e. convergence from
  (e), since `g ∈ L²` vanishing outside `B_ρ` is in `L¹`. (c) is placed after (e) in this file.
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate
open scoped ENNReal ContDiff

namespace NonUniqueEuler.BS

/-! ### Helpers for (a) -/

/-- `K_BS(w) = (i/(2π)) · conj(w⁻¹)` for every `w` (both sides vanish at `0`). -/
private theorem biotSavartKernel_eq_conj_inv (w : ℂ) :
    biotSavartKernel w = (Complex.I / (2 * Real.pi)) * conj w⁻¹ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [biotSavartKernel]
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  have hcw : conj w ≠ 0 := (map_ne_zero _).mpr hw
  rw [biotSavartKernel]
  push_cast
  rw [← Complex.mul_conj', map_inv₀]
  field_simp

private theorem biotSavartKernel_eq_fun :
    biotSavartKernel = fun w : ℂ => (Complex.I / (2 * Real.pi)) * conj w⁻¹ :=
  funext biotSavartKernel_eq_conj_inv

/-- `‖K_BS(z)‖ = (2π‖z‖)⁻¹` for every `z` (both sides vanish at `z = 0`). -/
private theorem norm_biotSavartKernel_eq' (z : ℂ) :
    ‖biotSavartKernel z‖ = (2 * Real.pi * ‖z‖)⁻¹ := by
  have hpi : 0 < 2 * Real.pi := by positivity
  rcases eq_or_ne z 0 with rfl | hz
  · simp [biotSavartKernel]
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [biotSavartKernel, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp

private theorem measurable_biotSavartKernel : Measurable biotSavartKernel := by
  unfold biotSavartKernel
  fun_prop

private theorem hasFDerivAt_biotSavartKernel {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt biotSavartKernel
      ((Complex.I / (2 * Real.pi) : ℂ) • (Complex.conjCLE.toContinuousLinearMap.comp
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(z ^ 2)⁻¹)).restrictScalars ℝ))) z := by
  rw [biotSavartKernel_eq_fun]
  have h1 := ((hasDerivAt_inv hz).hasFDerivAt).restrictScalars ℝ
  have h2 := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z h1
  exact h2.const_mul _

private theorem fderiv_biotSavartKernel_apply {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    fderiv ℝ biotSavartKernel z v =
      (Complex.I / (2 * Real.pi)) * conj (v * (-(z ^ 2)⁻¹)) := by
  rw [(hasFDerivAt_biotSavartKernel hz).fderiv]
  simp

private theorem norm_fderiv_biotSavartKernel_apply {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    ‖fderiv ℝ biotSavartKernel z v‖ = ‖v‖ * (2 * Real.pi * ‖z‖ ^ 2)⁻¹ := by
  rw [fderiv_biotSavartKernel_apply hz]
  have hpi : 0 < 2 * Real.pi := by positivity
  have h2 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    simp
  rw [norm_mul, norm_div, Complex.norm_I, h2, Complex.norm_conj, norm_mul, norm_neg, norm_inv,
    norm_pow]
  field_simp

/-! ### (a) The kernel -/

/-- `lem:BS-basic`(a): `|K(z)| = 1/(2π|z|)` for `z ≠ 0`. -/
theorem norm_biotSavartKernel_eq {z : ℂ} (hz : z ≠ 0) :
    ‖biotSavartKernel z‖ = (2 * Real.pi * ‖z‖)⁻¹ :=
  (fun _ => norm_biotSavartKernel_eq' z) hz

/-- The kernel is smooth on `ℝ² ∖ {0}` (`02_prelim.tex:290`, used in (a) and (e)). -/
theorem contDiffOn_biotSavartKernel : ContDiffOn ℝ ∞ biotSavartKernel {0}ᶜ := by
  rw [biotSavartKernel_eq_fun]
  intro w hw
  have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => w⁻¹) w :=
    (contDiffAt_inv ℂ (by simpa using hw)).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ∞ (fun w : ℂ => conj w⁻¹) w :=
    Complex.conjCLE.contDiff.contDiffAt.comp w h1
  exact (contDiffAt_const.mul h2).contDiffWithinAt

/-- `lem:BS-basic`(a): `|∂_l (K_BS)_i(z)| ≤ 1/(2π|z|²)` for `z ≠ 0` and `i, l ∈ {1, 2}`. -/
theorem abs_gradEntry_biotSavartKernel_le {z : ℂ} (hz : z ≠ 0) (i l : Fin 2) :
    |Prelim.gradEntry biotSavartKernel i l z| ≤ (2 * Real.pi * ‖z‖ ^ 2)⁻¹ := by
  have hcomp : ∀ w : ℂ, |Prelim.comp2 i w| ≤ ‖w‖ := by
    intro w
    fin_cases i
    · simpa using Complex.abs_re_le_norm w
    · simpa using Complex.abs_im_le_norm w
  have he : ‖Prelim.e2 l‖ = 1 := by
    fin_cases l <;> simp
  refine (hcomp _).trans (le_of_eq ?_)
  rw [Prelim.pd, norm_fderiv_biotSavartKernel_apply hz, he, one_mul]

/-- `‖K_BS(z)‖ = (2π)⁻¹ ‖z‖^{-1}` for every `z` (real power; both sides vanish at `0`). -/
private theorem norm_biotSavartKernel_eq_rpow (z : ℂ) :
    ‖biotSavartKernel z‖ = (2 * Real.pi)⁻¹ * ‖z‖ ^ (-1 : ℝ) := by
  rw [norm_biotSavartKernel_eq', Real.rpow_neg_one, mul_inv]

/-- `lem:BS-basic`(a): `∫_{B_ρ} |K_BS| dz = ρ` for `ρ > 0` (Bochner and lower-integral forms;
`K_BS` is integrable on `B_ρ`). -/
theorem integral_norm_biotSavartKernel_ball {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn biotSavartKernel (ball (0 : ℂ) ρ) volume ∧
      ∫ z in ball (0 : ℂ) ρ, ‖biotSavartKernel z‖ = ρ ∧
      ∫⁻ z in ball (0 : ℂ) ρ, ‖biotSavartKernel z‖ₑ = ENNReal.ofReal ρ := by
  have hs : (-2 : ℝ) < -1 := by norm_num
  have hint : IntegrableOn (fun z : ℂ => (2 * Real.pi)⁻¹ * ‖z‖ ^ (-1 : ℝ)) (ball (0 : ℂ) ρ) :=
    (Polar.integrableOn_ball_norm_rpow hs ρ).const_mul _
  have hK : IntegrableOn biotSavartKernel (ball (0 : ℂ) ρ) volume := by
    refine Integrable.mono' hint measurable_biotSavartKernel.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun z => le_of_eq (norm_biotSavartKernel_eq_rpow z)
  have hI : ∫ z in ball (0 : ℂ) ρ, ‖biotSavartKernel z‖ = ρ := by
    simp_rw [norm_biotSavartKernel_eq_rpow]
    rw [integral_const_mul, Polar.setIntegral_ball_norm_rpow hs hρ.le]
    have hpi : 0 < Real.pi := Real.pi_pos
    norm_num
    field_simp
  refine ⟨hK, hI, ?_⟩
  rw [← ofReal_integral_norm_eq_lintegral_enorm hK, hI]

/-- `‖K_BS(z)‖ₑ = ofReal((2π‖z‖)⁻¹)` for every `z`. -/
private theorem enorm_biotSavartKernel_eq (z : ℂ) :
    ‖biotSavartKernel z‖ₑ = ENNReal.ofReal ((2 * Real.pi * ‖z‖)⁻¹) := by
  rw [← ofReal_norm, norm_biotSavartKernel_eq']

/-! ### (b) `L¹ ∩ L^∞` vorticities -/

/-- The elementary inequality of (b): `(2ab/π)^{1/2} ≤ b + a/(2π)` for `a, b ≥ 0`
(`2(xy)^{1/2} ≤ x + y`). -/
theorem sqrt_two_mul_mul_div_pi_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (2 * a * b / Real.pi) ≤ b + a / (2 * Real.pi) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have key : (b + a / (2 * Real.pi)) ^ 2 - 2 * a * b / Real.pi =
      (b - a / (2 * Real.pi)) ^ 2 := by
    field_simp
    ring
  nlinarith [sq_nonneg (b - a / (2 * Real.pi))]

/-- The split estimate of (b): for every `r > 0`,
`(|K| ∗ |g|)(x) ≤ ‖g‖_∞ r + (2πr)⁻¹ ‖g‖₁`. -/
private theorem convAbs_le_split {g : ℂ → ℝ} (x : ℂ) {r : ℝ} (hr : 0 < r) :
    Conv.convAbs biotSavartKernel g x ≤
      eLpNorm g ⊤ volume * ENNReal.ofReal r +
        ENNReal.ofReal ((2 * Real.pi * r)⁻¹) * eLpNorm g 1 volume := by
  rw [Conv.convAbs_eq_lintegral_sub,
    ← lintegral_add_compl _ (measurableSet_ball (x := (0 : ℂ)) (ε := r))]
  gcongr ?_ + ?_
  · calc ∫⁻ z in ball (0 : ℂ) r, ‖biotSavartKernel z‖ₑ * ‖g (x - z)‖ₑ
        ≤ ∫⁻ z in ball (0 : ℂ) r, ‖biotSavartKernel z‖ₑ * eLpNorm g ⊤ volume := by
          apply lintegral_mono_ae
          have h := (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae
            (ae_le_eLpNormEssSup (f := g) (μ := volume))
          filter_upwards [ae_restrict_of_ae h] with z hz
          rw [eLpNorm_exponent_top]
          gcongr
      _ = eLpNorm g ⊤ volume * ENNReal.ofReal r := by
          rw [lintegral_mul_const _ measurable_biotSavartKernel.enorm, mul_comm,
            (integral_norm_biotSavartKernel_ball hr).2.2]
  · calc ∫⁻ z in (ball (0 : ℂ) r)ᶜ, ‖biotSavartKernel z‖ₑ * ‖g (x - z)‖ₑ
        ≤ ∫⁻ z in (ball (0 : ℂ) r)ᶜ, ENNReal.ofReal ((2 * Real.pi * r)⁻¹) * ‖g (x - z)‖ₑ := by
          apply setLIntegral_mono' measurableSet_ball.compl
          intro z hz
          gcongr
          rw [enorm_biotSavartKernel_eq]
          apply ENNReal.ofReal_le_ofReal
          have hz' : r ≤ ‖z‖ := by simpa [mem_ball_zero_iff] using hz
          gcongr
      _ ≤ ∫⁻ z, ENNReal.ofReal ((2 * Real.pi * r)⁻¹) * ‖g (x - z)‖ₑ :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal ((2 * Real.pi * r)⁻¹) * eLpNorm g 1 volume := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_sub_left_eq_self (fun y => ‖g y‖ₑ) x, eLpNorm_one_eq_lintegral_enorm]

/-- `lem:BS-basic`(b): for `g ∈ L¹ ∩ L^∞` and every `x`,
`(|K| ∗ |g|)(x) ≤ (2‖g‖₁‖g‖_∞/π)^{1/2}`. -/
theorem convAbs_le_sqrt_L1_Linf {g : ℂ → ℝ} (hg1 : MemLp g 1 volume) (hginf : MemLp g ⊤ volume)
    (x : ℂ) :
    Conv.convAbs biotSavartKernel g x ≤
      ENNReal.ofReal (Real.sqrt (2 * (eLpNorm g 1 volume).toReal *
        (eLpNorm g ⊤ volume).toReal / Real.pi)) := by
  set A := (eLpNorm g 1 volume).toReal with hAdef
  set B := (eLpNorm g ⊤ volume).toReal with hBdef
  have hA : eLpNorm g 1 volume = ENNReal.ofReal A := (ENNReal.ofReal_toReal hg1.eLpNorm_ne_top).symm
  have hB : eLpNorm g ⊤ volume = ENNReal.ofReal B :=
    (ENNReal.ofReal_toReal hginf.eLpNorm_ne_top).symm
  by_cases h0 : A = 0 ∨ B = 0
  · have hg0 : g =ᵐ[volume] 0 := by
      rcases h0 with h | h
      · have : eLpNorm g 1 volume = 0 := by rw [hA, h, ENNReal.ofReal_zero]
        exact (eLpNorm_eq_zero_iff hg1.1 one_ne_zero).mp this
      · have : eLpNorm g ⊤ volume = 0 := by rw [hB, h, ENNReal.ofReal_zero]
        exact (eLpNorm_eq_zero_iff hginf.1 ENNReal.top_ne_zero).mp this
    have : Conv.convAbs biotSavartKernel g x = 0 := by
      unfold Conv.convAbs
      rw [lintegral_congr_ae (g := fun _ => 0), lintegral_zero]
      filter_upwards [hg0] with y hy
      simp [hy]
    rw [this]
    exact zero_le
  · push Not at h0
    have hA0 : 0 < A := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h0.1)
    have hB0 : 0 < B := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h0.2)
    have hpi : 0 < Real.pi := Real.pi_pos
    set s := Real.sqrt (2 * A * B / Real.pi) with hsdef
    have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
    have hs2 : s ^ 2 = 2 * A * B / Real.pi := Real.sq_sqrt (by positivity)
    have hr : 0 < s / (2 * B) := by positivity
    refine (convAbs_le_split x hr).trans (le_of_eq ?_)
    rw [hA, hB, ← ENNReal.ofReal_mul hB0.le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    have hs2' : Real.pi * s ^ 2 = 2 * A * B := by rw [hs2]; field_simp
    field_simp
    linear_combination (-1) * hs2'

/-- `lem:BS-basic`(b): for `g ∈ L¹ ∩ L^∞` the integral defining `K ∗ g(x)` converges absolutely
for every `x`, and `|K ∗ g(x)| ≤ (2‖g‖₁‖g‖_∞/π)^{1/2}`. -/
theorem integrable_and_norm_velocity_le_sqrt_L1_Linf {g : ℂ → ℝ} (hg1 : MemLp g 1 volume)
    (hginf : MemLp g ⊤ volume) (x : ℂ) :
    Integrable (fun y => biotSavartKernel (x - y) * (g y : ℂ)) volume ∧
      ‖velocity g x‖ ≤
        Real.sqrt (2 * (eLpNorm g 1 volume).toReal * (eLpNorm g ⊤ volume).toReal / Real.pi) := by
  have h := convAbs_le_sqrt_L1_Linf hg1 hginf x
  refine ⟨Conv.integrable_conv_of_convAbs_ne_top measurable_biotSavartKernel.aestronglyMeasurable
    hg1.1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h), ?_⟩
  have h2 := (Conv.enorm_velocity_le g x).trans h
  rw [← ofReal_norm] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp h2

/-- `lem:BS-basic`(b), `L^∞` form: `‖K ∗ g‖_{L^∞} ≤ (2‖g‖₁‖g‖_∞/π)^{1/2}`. -/
theorem eLpNorm_velocity_top_le_sqrt_L1_Linf {g : ℂ → ℝ} (hg1 : MemLp g 1 volume)
    (hginf : MemLp g ⊤ volume) :
    eLpNorm (velocity g) ⊤ volume ≤
      ENNReal.ofReal (Real.sqrt (2 * (eLpNorm g 1 volume).toReal *
        (eLpNorm g ⊤ volume).toReal / Real.pi)) := by
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_enorm_bound (Filter.Eventually.of_forall fun x =>
    (Conv.enorm_velocity_le g x).trans (convAbs_le_sqrt_L1_Linf hg1 hginf x))

/-! ### (e) `L¹` vorticities: the majorant -/

/-- `lem:BS-basic`(e): `∫_{B_R} (|K| ∗ |g|) dx ≤ R ‖g‖_{L¹}` for `g ∈ L¹`, `R > 0`. -/
theorem setLIntegral_convAbs_ball_le {g : ℂ → ℝ} (hg : MemLp g 1 volume) {R : ℝ} (hR : 0 < R) :
    ∫⁻ x in ball (0 : ℂ) R, Conv.convAbs biotSavartKernel g x ≤
      ENNReal.ofReal R * eLpNorm g 1 volume := by
  rw [Conv.setLIntegral_convAbs measurable_biotSavartKernel.aestronglyMeasurable hg.1
    measurableSet_ball, eLpNorm_one_eq_lintegral_enorm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  rw [mul_comm]
  gcongr
  have hφm : Measurable (fun r : ℝ => ENNReal.ofReal ((2 * Real.pi * r)⁻¹)) := by fun_prop
  have hφ : AntitoneOn (fun r : ℝ => ENNReal.ofReal ((2 * Real.pi * r)⁻¹)) (Ioi 0) := by
    intro a ha b _ hab
    apply ENNReal.ofReal_le_ofReal
    exact inv_anti₀ (mul_pos (by positivity) ha) (by gcongr)
  have h := Polar.setLIntegral_ball_sub_le hφm hφ y R
  simp only [← enorm_biotSavartKernel_eq] at h
  rwa [(integral_norm_biotSavartKernel_ball hR).2.2] at h

/-- For `g ∈ L¹`, `(|K| ∗ |g|)(x) < ∞` for almost every `x`. -/
private theorem ae_convAbs_lt_top_of_L1 {g : ℂ → ℝ} (hg : MemLp g 1 volume) :
    ∀ᵐ x, Conv.convAbs biotSavartKernel g x < ⊤ := by
  have hmeas := Conv.measurable_convAbs (K := biotSavartKernel)
    measurable_biotSavartKernel.aestronglyMeasurable hg.1
  have h : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (ball (0 : ℂ) (n + 1))),
      Conv.convAbs biotSavartKernel g x < ⊤ := by
    intro n
    refine ae_lt_top hmeas ?_
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_ne_top)
      (setLIntegral_convAbs_ball_le hg (by positivity))
  have := (ae_restrict_iUnion_iff (fun n : ℕ => ball (0 : ℂ) (n + 1)) _).mpr h
  rwa [iUnion_ball_nat_succ, Measure.restrict_univ] at this

/-- `lem:BS-basic`(e): for `g ∈ L¹` the integral defining `K ∗ g` converges absolutely almost
everywhere. -/
theorem ae_integrable_biotSavart_of_L1 {g : ℂ → ℝ} (hg : MemLp g 1 volume) :
    ∀ᵐ x, Integrable (fun y => biotSavartKernel (x - y) * (g y : ℂ)) volume := by
  filter_upwards [ae_convAbs_lt_top_of_L1 hg] with x hx
  exact Conv.integrable_conv_of_convAbs_ne_top measurable_biotSavartKernel.aestronglyMeasurable
    hg.1 hx.ne

/-- For `g ∈ L¹`, `K ∗ g` is integrable on every disk `B_R`. -/
private theorem integrableOn_velocity_ball_of_L1 {g : ℂ → ℝ} (hg : MemLp g 1 volume) {R : ℝ}
    (hR : 0 < R) : IntegrableOn (velocity g) (ball (0 : ℂ) R) volume := by
  refine ⟨(Conv.stronglyMeasurable_velocity hg.1).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ x in ball (0 : ℂ) R, ‖velocity g x‖ₑ
      ≤ ∫⁻ x in ball (0 : ℂ) R, Conv.convAbs biotSavartKernel g x :=
        lintegral_mono fun x => Conv.enorm_velocity_le g x
    _ ≤ ENNReal.ofReal R * eLpNorm g 1 volume := setLIntegral_convAbs_ball_le hg hR
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top

/-- `lem:BS-basic`(e): `K ∗ g ∈ L¹_loc(ℝ²)` for `g ∈ L¹`. -/
theorem locallyIntegrable_velocity_of_L1 {g : ℂ → ℝ} (hg : MemLp g 1 volume) :
    LocallyIntegrable (velocity g) volume := by
  intro x
  refine ⟨ball (0 : ℂ) (‖x‖ + 1), isOpen_ball.mem_nhds ?_,
    integrableOn_velocity_ball_of_L1 hg (by positivity)⟩
  simp

/-! ### (c) Local `L²` bound -/

/-- `lem:BS-basic`(c): for `ρ, R > 0` and `g ∈ L²` vanishing (a.e.) outside `B_ρ`, `K ∗ g` is
defined almost everywhere and `‖K ∗ g‖_{L²(B_R)} ≤ (R + ρ) ‖g‖_{L²}`. -/
theorem velocity_L2_ball_le {g : ℂ → ℝ} {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R)
    (hg : MemLp g 2 volume) (hsupp : ∀ᵐ y, y ∉ ball (0 : ℂ) ρ → g y = 0) :
    (∀ᵐ x, Integrable (fun y => biotSavartKernel (x - y) * (g y : ℂ)) volume) ∧
      MemLp (velocity g) 2 (volume.restrict (ball (0 : ℂ) R)) ∧
      eLpNorm (velocity g) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
        ENNReal.ofReal (R + ρ) * eLpNorm g 2 volume := by
  have hsupp' : ∀ᵐ y, ρ ≤ ‖y‖ → g y = 0 := by
    filter_upwards [hsupp] with y hy h
    exact hy (by simpa [mem_ball_zero_iff] using h)
  have hbound : eLpNorm (Conv.convAbs biotSavartKernel g) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
      ENNReal.ofReal (R + ρ) * eLpNorm g 2 volume := by
    have := Conv.eLpNorm_convAbs_ball_le measurable_biotSavartKernel.aestronglyMeasurable hg.1
      (p := 2) one_le_two (R := R) hsupp'
    rwa [(integral_norm_biotSavartKernel_ball (by linarith : 0 < R + ρ)).2.2] at this
  have hv : eLpNorm (velocity g) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
      eLpNorm (Conv.convAbs biotSavartKernel g) 2 (volume.restrict (ball (0 : ℂ) R)) :=
    eLpNorm_mono_enorm fun x => (Conv.enorm_velocity_le g x).trans (le_of_eq (enorm_eq_self _).symm)
  have hg1 : MemLp g 1 volume := by
    have hind : (ball (0 : ℂ) ρ).indicator g =ᵐ[volume] g := by
      filter_upwards [hsupp] with y hy
      by_cases h : y ∈ ball (0 : ℂ) ρ
      · simp [h]
      · simp [h, hy h]
    have : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) ρ)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have h2 : MemLp g 2 (volume.restrict (ball (0 : ℂ) ρ)) := hg.restrict _
    have h1 : MemLp g 1 (volume.restrict (ball (0 : ℂ) ρ)) := h2.mono_exponent one_le_two
    exact ((memLp_indicator_iff_restrict measurableSet_ball).mpr h1).ae_eq hind
  refine ⟨ae_integrable_biotSavart_of_L1 hg1,
    ⟨(Conv.stronglyMeasurable_velocity hg.1).aestronglyMeasurable,
      (hv.trans hbound).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top)⟩,
    hv.trans hbound⟩

/-! ### (e) The distributional divergence -/

/-- `L(K_BS(z)) = (2π|z|²)⁻¹ L(iz)` for every real-linear `L`. -/
private theorem clm_apply_biotSavartKernel (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L (biotSavartKernel z) = (2 * Real.pi * ‖z‖ ^ 2)⁻¹ * L (Complex.I * z) := by
  rw [biotSavartKernel, div_eq_inv_mul, ← Complex.ofReal_inv, ← Complex.real_smul, map_smul,
    smul_eq_mul]

/-- For `φ ∈ C¹_c`, `z ↦ Dφ(z) K_BS(z)` is integrable. -/
private theorem integrable_fderiv_apply_biotSavartKernel {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    Integrable (fun z => fderiv ℝ φ z (biotSavartKernel z)) := by
  have hcont : Continuous (fun z => fderiv ℝ φ z) := hφ.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_ball (0 : ℂ)
  set R' := max R 1 with hR'
  have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsub : tsupport φ ⊆ ball (0 : ℂ) R' := hR.trans (ball_subset_ball (le_max_left _ _))
  have hmeas : AEStronglyMeasurable (fun z => fderiv ℝ φ z (biotSavartKernel z)) volume := by
    have h1 : Continuous (fun z => fderiv ℝ φ z (Complex.I * z)) :=
      hcont.clm_apply (continuous_const.mul continuous_id)
    have h2 : Measurable (fun z : ℂ => (2 * Real.pi * ‖z‖ ^ 2)⁻¹) := by fun_prop
    have : (fun z => fderiv ℝ φ z (biotSavartKernel z)) =
        fun z => (2 * Real.pi * ‖z‖ ^ 2)⁻¹ * fderiv ℝ φ z (Complex.I * z) := by
      funext z
      exact clm_apply_biotSavartKernel _ z
    rw [this]
    exact (h2.mul h1.measurable).aestronglyMeasurable
  have hon : IntegrableOn (fun z => fderiv ℝ φ z (biotSavartKernel z)) (ball (0 : ℂ) R') := by
    have hK := (integral_norm_biotSavartKernel_ball hR'pos).1
    refine Integrable.mono' (hK.norm.const_mul C) hmeas.restrict ?_
    refine Filter.Eventually.of_forall fun z => ?_
    exact ((fderiv ℝ φ z).le_opNorm _).trans (by gcongr; exact hC z)
  refine hon.integrable_of_forall_notMem_eq_zero fun z hz => ?_
  have hz' : z ∉ tsupport φ := fun h => hz (hsub h)
  have : fderiv ℝ φ z = 0 := by
    by_contra hne
    exact hz' (support_fderiv_subset ℝ hne)
  simp [this]

/-- `div K_BS = 0` in `𝒟'`: `∫ Dφ(z) K_BS(z) dz = 0` for `φ ∈ C¹_c` (polar coordinates:
`Dφ(z) K_BS(z) = (2π|z|²)⁻¹ ∂_θ φ(z)`, and `∫₀^{2π} ∂_θ φ(re^{iθ}) dθ = 0`). -/
private theorem integral_fderiv_apply_biotSavartKernel_eq_zero {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    ∫ z, fderiv ℝ φ z (biotSavartKernel z) = 0 := by
  rw [Polar.integral_eq_integral_Ioi_intervalIntegral
    (integrable_fderiv_apply_biotSavartKernel hφ hc)]
  have h : ∀ r : ℝ, ∫ θ in (0 : ℝ)..2 * Real.pi,
      fderiv ℝ φ (circleMap 0 r θ) (biotSavartKernel (circleMap 0 r θ)) = 0 := by
    intro r
    simp_rw [clm_apply_biotSavartKernel, norm_circleMap_zero]
    rw [intervalIntegral.integral_const_mul, Polar.intervalIntegral_angular_deriv_eq_zero hφ r,
      mul_zero]
  simp [h]

/-- `‖(a : ℂ)‖ₑ = ‖a‖ₑ` for real `a`. -/
private theorem enorm_ofReal' (a : ℝ) : ‖(a : ℂ)‖ₑ = ‖a‖ₑ := by
  simp only [enorm, Complex.nnnorm_real]

/-- `lem:BS-basic`(e): `div (K ∗ g) = 0` in `𝒟'(ℝ²)` for `g ∈ L¹`. -/
theorem isWeaklyDivFree_velocity_of_L1 {g : ℂ → ℝ} (hg : MemLp g 1 volume) :
    Prelim.IsWeaklyDivFree (velocity g) := by
  intro φ hφ hc
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hcont : Continuous (fun z => fderiv ℝ φ z) := hφ1.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_ball (0 : ℂ)
  set R' := max R 1 with hR'
  have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsub : tsupport φ ⊆ ball (0 : ℂ) R' := hR.trans (ball_subset_ball (le_max_left _ _))
  have hzero : ∀ x, x ∉ ball (0 : ℂ) R' → fderiv ℝ φ x = 0 := by
    intro x hx
    by_contra hne
    exact hx (hsub (support_fderiv_subset ℝ hne))
  set F : ℂ → ℂ → ℝ := fun x y => fderiv ℝ φ x (biotSavartKernel (x - y) * (g y : ℂ))
    with hFdef
  have hFeq' : ∀ x y, F x y = g y * fderiv ℝ φ x (biotSavartKernel (x - y)) := by
    intro x y
    simp only [hFdef]
    rw [mul_comm, ← Complex.real_smul, map_smul, smul_eq_mul]
  have hFeq : ∀ x y, F x y =
      g y * ((2 * Real.pi * ‖x - y‖ ^ 2)⁻¹ * fderiv ℝ φ x (Complex.I * (x - y))) := by
    intro x y
    rw [hFeq', clm_apply_biotSavartKernel]
  -- measurability on the product
  have hFmeas : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
    have h1 : Continuous (fun p : ℂ × ℂ => fderiv ℝ φ p.1 (Complex.I * (p.1 - p.2))) :=
      (hcont.comp continuous_fst).clm_apply
        (continuous_const.mul (continuous_fst.sub continuous_snd))
    have h2 : Measurable (fun p : ℂ × ℂ => (2 * Real.pi * ‖p.1 - p.2‖ ^ 2)⁻¹) := by fun_prop
    have h3 : AEStronglyMeasurable (fun p : ℂ × ℂ => g p.2) (volume.prod volume) :=
      hg.1.comp_snd
    have : Function.uncurry F = fun p : ℂ × ℂ => g p.2 *
        ((2 * Real.pi * ‖p.1 - p.2‖ ^ 2)⁻¹ * fderiv ℝ φ p.1 (Complex.I * (p.1 - p.2))) := by
      funext p
      exact hFeq p.1 p.2
    rw [this]
    exact h3.mul (h2.mul h1.measurable).aestronglyMeasurable
  -- pointwise bound
  have hFbound : ∀ x y, ‖F x y‖ₑ ≤ (ball (0 : ℂ) R').indicator (fun _ => ENNReal.ofReal C) x *
      (‖biotSavartKernel (x - y)‖ₑ * ‖g y‖ₑ) := by
    intro x y
    by_cases hx : x ∈ ball (0 : ℂ) R'
    · rw [indicator_of_mem hx]
      calc ‖F x y‖ₑ
          ≤ ‖fderiv ℝ φ x‖ₑ * ‖biotSavartKernel (x - y) * (g y : ℂ)‖ₑ :=
            (fderiv ℝ φ x).le_opENorm _
        _ ≤ ENNReal.ofReal C * (‖biotSavartKernel (x - y)‖ₑ * ‖g y‖ₑ) := by
            rw [enorm_mul, enorm_ofReal']
            gcongr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hC x)
    · rw [indicator_of_notMem hx, zero_mul]
      simp [hFdef, hzero x hx]
  -- integrability on the product (Tonelli and the bound of (e))
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine ⟨hFmeas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hFmeas.enorm]
    calc ∫⁻ x, ∫⁻ y, ‖Function.uncurry F (x, y)‖ₑ
        ≤ ∫⁻ x, (ball (0 : ℂ) R').indicator (fun _ => ENNReal.ofReal C) x *
            Conv.convAbs biotSavartKernel g x := by
          refine lintegral_mono fun x => ?_
          rw [Conv.convAbs, ← lintegral_const_mul' _ _
            (by by_cases hx : x ∈ ball (0 : ℂ) R' <;> simp [hx])]
          exact lintegral_mono fun y => hFbound x y
      _ = ∫⁻ x in ball (0 : ℂ) R', ENNReal.ofReal C * Conv.convAbs biotSavartKernel g x := by
          rw [← lintegral_indicator measurableSet_ball]
          congr 1
          funext x
          by_cases hx : x ∈ ball (0 : ℂ) R' <;> simp [hx]
      _ = ENNReal.ofReal C * ∫⁻ x in ball (0 : ℂ) R', Conv.convAbs biotSavartKernel g x :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal R' * eLpNorm g 1 volume) := by
          gcongr
          exact setLIntegral_convAbs_ball_le hg hR'pos
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top)
  -- `Dφ(x) (K ∗ g)(x) = ∫ Dφ(x) (K(x - y) g(y)) dy` for a.e. `x`
  have hae : (fun x => fderiv ℝ φ x (velocity g x)) =ᵐ[volume] fun x => ∫ y, F x y := by
    filter_upwards [ae_integrable_biotSavart_of_L1 hg] with x hx
    simp only [hFdef, velocity]
    exact ((fderiv ℝ φ x).integral_comp_comm hx).symm
  have hint : Integrable (fun x => fderiv ℝ φ x (velocity g x)) :=
    hFint.integral_prod_left.congr hae.symm
  refine ⟨hint, ?_⟩
  rw [integral_congr_ae hae, integral_integral_swap hFint]
  -- `J(y) = ∫ K(z) · ∇_z φ(y + z) dz = 0`
  have hJ : ∀ y, ∫ x, F x y = 0 := by
    intro y
    simp_rw [hFeq' _ y]
    rw [integral_const_mul]
    have h2 : ∫ x, fderiv ℝ φ x (biotSavartKernel (x - y)) =
        ∫ z, fderiv ℝ (fun w => φ (w + y)) z (biotSavartKernel z) := by
      rw [← integral_sub_right_eq_self
        (fun z => fderiv ℝ (fun w => φ (w + y)) z (biotSavartKernel z)) y]
      congr 1
      funext x
      rw [fderiv_comp_add_right, sub_add_cancel]
    rw [h2, integral_fderiv_apply_biotSavartKernel_eq_zero, mul_zero]
    · exact hφ1.comp (contDiff_id.add contDiff_const)
    · exact hc.comp_homeomorph (Homeomorph.addRight y)
  simp [hJ]

end NonUniqueEuler.BS
