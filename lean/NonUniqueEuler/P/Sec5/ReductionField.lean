import NonUniqueEuler.H.Sec5.ReductionField.Joint
import NonUniqueEuler.H.Sec5.ReductionField.Circle
import NonUniqueEuler.I.Sec2.BSSmooth
import NonUniqueEuler.I.Infra.Multipole.StreamFunction
import NonUniqueEuler.I.Infra.Multipole.Circulation
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Proof: `lem:reduction`(1) (the field `h` of the other vorticity near the ring)

Proof of `OneRing.reduction_field` (`I/Sec5/ReductionField.lean`, statement copied verbatim).
Manuscript `05_single_ring.tex:102-109` (statement), `:129-184` (proof).

**Proof.** Fix `t ∈ [0,T]`, put `g = ω_i(t) + ω_o(t)` (`C_c^∞`, `3`-fold symmetric) and take
`U = {a/8 < |x| < 6}`, an open neighbourhood of `N'` on which `g = 0` (the hypotheses
`supp ω_i(t) ⊂ \bar B_{a/8}`, `supp ω_o(t) ∩ B_6 = ∅`). Then:
* `h = K * g - G x^⊥/|x|²` is `C^∞` on `U` (`BS.contDiff_velocity_of_smooth`, the vortex is smooth
  off `0`);
* `ψ = (2π)⁻¹ log|·| * g - G log|·|` satisfies `h = ∇^⊥ψ` on `U` (`BS.velocity_eq_perpGrad_of_smooth`,
  `∇^⊥ log|x| = x^⊥/|x|²`) and is harmonic there (`Δ((2π)⁻¹ log|·| * g) = g = 0` on `U`,
  `log|·|` harmonic off `0`); this is the single-valued stream function of the manuscript, given
  explicitly (restructuring R11, as in `I/Infra/Multipole/StreamFunction.lean`), so the
  topological argument (`C_r` generates `π₁(U)`) is not needed;
* `div h = div ∇^⊥ψ = 0` and `curl h = Δψ = 0` on `U`;
* symmetry: `K(Ox) = O K(x)` and `g ∘ O = g` give `(K * g)(Ox) = O (K * g)(x)`, and the vortex is
  equivariant;
* circles `r ∈ (a/4,3)`: `g` vanishes near `C_r`, so (I-MULT) the flux of `K * g` is `0` and its
  circulation is `∫_{B_r} g = ∫ ω_i(t) = 2πG`; the vortex has radial part `0` and angular part
  `G/r`; both averages vanish;
* `t ↦ h(t) ∈ C^k(N')`: `RedFieldH.ckPathOn_h` (joint smoothness of `h` on
  `(-1,T+1) × (ℝ² ∖ {0})`).

Deviation of proof: `U = {a/8 < |x| < 6}` for every `t` (the manuscript's `U`
depends on `ρ_i`); smoothness in `(t, x)` comes from the parametric convolution theorem (the
derivatives fall on `ω_i + ω_o`) instead of the kernel bounds `|∂^βK(z)| ≤ C_β|z|^{-1-|β|}`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff Laplacian

namespace NonUniqueEuler

namespace OneRing

open RingData

namespace RedFieldH

/-- The open annulus `U = {a/8 < |x| < 6}` around `N'`. -/
def annU : Set ℂ := {x : ℂ | a / 8 < ‖x‖ ∧ ‖x‖ < 6}

theorem a_pos' : 0 < a := Real.exp_pos _

theorem isOpen_annU : IsOpen annU :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem annN'_subset_annU : annN' ⊆ annU := by
  intro x hx
  have ha := a_pos'
  obtain ⟨h1, h2⟩ := mem_annN'.1 hx
  exact ⟨by linarith, by linarith⟩

theorem ne_zero_of_mem_annU {x : ℂ} (hx : x ∈ annU) : x ≠ 0 := by
  intro h0
  have ha := a_pos'
  have := hx.1
  rw [h0, norm_zero] at this
  linarith

variable {c : RingConfig} {T : ℝ}

/-- `g = ω_i(t) + ω_o(t)`. -/
def gpart (c : RingConfig) (t : ℝ) : ℂ → ℝ := fun y => c.innerPart t y + c.outerPart t y

theorem gpart_contDiff (hc : c.Hyp T) (t : ℝ) : ContDiff ℝ ∞ (gpart c t) :=
  parts_contDiff hc t

theorem gpart_hasCompactSupport (hc : c.Hyp T) (t : ℝ) : HasCompactSupport (gpart c t) :=
  parts_hasCompactSupport hc t

theorem gpart_eq_zero (hc : c.Hyp T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {x : ℂ}
    (hx : x ∈ annU) : gpart c t x = 0 := by
  obtain ⟨h1, h2⟩ := parts_eq_zero_of_mem hc ht hx.1 hx.2
  simp [gpart, h1, h2]

theorem gpart_eventually_zero (hc : c.Hyp T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {x : ℂ}
    (hx : x ∈ annU) : gpart c t =ᶠ[𝓝 x] 0 :=
  Filter.eventually_of_mem (isOpen_annU.mem_nhds hx) fun _ hy => gpart_eq_zero hc ht hy

theorem h_eq (c : RingConfig) (t : ℝ) :
    c.h t = fun x => velocity (gpart c t) x - vortex c.G x := rfl

/-- The stream function `ψ = (2π)⁻¹ log|·| * g - G log|·|`. -/
def psiH (c : RingConfig) (t : ℝ) : ℂ → ℝ :=
  fun y => Multipole.logPotentialReal (gpart c t) y - c.G * Real.log ‖y‖

theorem psiH_eq (c : RingConfig) (t : ℝ) : psiH c t =
    fun y => Multipole.logPotentialReal (gpart c t) y - c.G * Real.log ‖y‖ := rfl

theorem contDiff_logPot (hc : c.Hyp T) (t : ℝ) :
    ContDiff ℝ ∞ (Multipole.logPotentialReal (gpart c t)) :=
  (BS.contDiff_velocity_of_smooth (gpart_contDiff hc t) (gpart_hasCompactSupport hc t)).2

theorem contDiff_velocity_gpart (hc : c.Hyp T) (t : ℝ) :
    ContDiff ℝ ∞ (velocity (gpart c t)) :=
  (BS.contDiff_velocity_of_smooth (gpart_contDiff hc t) (gpart_hasCompactSupport hc t)).1

/-- `ψ` is harmonic on `U`. -/
theorem harmonicOnNhd_psiH (hc : c.Hyp T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    InnerProductSpace.HarmonicOnNhd (psiH c t) annU := by
  intro x hx
  have h1 : InnerProductSpace.HarmonicAt (Multipole.logPotentialReal (gpart c t)) x := by
    refine ⟨(contDiff_logPot hc t).contDiffAt.of_le (by simp), ?_⟩
    rw [BS.laplacian_logPotentialReal_of_smooth (gpart_contDiff hc t)
      (gpart_hasCompactSupport hc t)]
    exact gpart_eventually_zero hc ht hx
  have h2 : InnerProductSpace.HarmonicAt (c.G • fun y : ℂ => Real.log ‖y‖) x :=
    (Multipole.harmonicOnNhd_log_norm x (ne_zero_of_mem_annU hx)).const_smul
  have h3 := h1.sub h2
  have heq : psiH c t = Multipole.logPotentialReal (gpart c t) -
      (c.G • fun y : ℂ => Real.log ‖y‖) := by
    funext y
    simp [psiH]
  rw [heq]
  exact h3

/-- `h(t) = ∇^⊥ψ` on `U` (indeed off `0`). -/
theorem h_eq_perpGrad (hc : c.Hyp T) (t : ℝ) {x : ℂ} (hx : x ≠ 0) :
    c.h t x = Prelim.perpGrad (psiH c t) x := by
  have hd1 : DifferentiableAt ℝ (Multipole.logPotentialReal (gpart c t)) x :=
    (contDiff_logPot hc t).differentiable (by simp) x
  have hd2 : DifferentiableAt ℝ (fun y : ℂ => Real.log ‖y‖) x :=
    (Multipole.hasFDerivAt_log_norm hx).differentiableAt
  rw [psiH_eq, perpGrad_sub_const_mul hd1 hd2, h_eq, ← vortex_eq_perpGrad c.G hx,
    ← BS.velocity_eq_perpGrad_of_smooth (gpart_contDiff hc t) (gpart_hasCompactSupport hc t)]

theorem h_eventuallyEq_perpGrad (hc : c.Hyp T) (t : ℝ) {x : ℂ} (hx : x ∈ annU) :
    c.h t =ᶠ[𝓝 x] Prelim.perpGrad (psiH c t) :=
  Filter.eventually_of_mem (isOpen_annU.mem_nhds hx) fun _ hy =>
    h_eq_perpGrad hc t (ne_zero_of_mem_annU hy)

theorem divergence_h (hc : c.Hyp T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {x : ℂ}
    (hx : x ∈ annU) : Prelim.divergence (c.h t) x = 0 := by
  have hf := (h_eventuallyEq_perpGrad hc t hx).fderiv_eq (𝕜 := ℝ)
  rw [Prelim.divergence_eq, hf, ← Prelim.divergence_eq]
  exact divergence_perpGrad (harmonicOnNhd_psiH hc ht x hx).1

theorem curl_h (hc : c.Hyp T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {x : ℂ}
    (hx : x ∈ annU) : Prelim.curl (c.h t) x = 0 := by
  have hf := (h_eventuallyEq_perpGrad hc t hx).fderiv_eq (𝕜 := ℝ)
  have hψ := harmonicOnNhd_psiH hc ht x hx
  rw [Prelim.curl_eq, hf, ← Prelim.curl_eq, curl_perpGrad hψ.1]
  exact hψ.2.self_of_nhds

theorem isSymFieldOn_h (hc : c.Hyp T) (t : ℝ) : IsSymFieldOn annU (c.h t) := by
  intro x _
  have hsym := RingConfig.setting_symmetric hc
  have hg : ∀ y, gpart c t (rot (2 * Real.pi / 3) y) = gpart c t y := by
    intro y
    simp only [gpart, hsym.2.2.2.1 t y, hsym.2.2.2.2 t y]
  rw [h_eq]
  dsimp only
  rw [velocity_rot hg, vortex_rot]
  simp only [rot]
  ring

/-! ### The angular averages on circles -/

theorem gpart_integrable (hc : c.Hyp T) (t : ℝ) : Integrable (gpart c t) :=
  (parts_contDiff hc t).continuous.integrable_of_hasCompactSupport (parts_hasCompactSupport hc t)

/-- `g` vanishes on a neighbourhood `{r - δ < |y| < r + δ}` of `C_r`, `r ∈ (a/4, 3)`. -/
theorem gpart_vanishes_near_circle (hc : c.Hyp T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {r : ℝ} :
    ∀ᵐ y, ‖y‖ ∈ Ioo (r - min (r - a / 8) (6 - r)) (r + min (r - a / 8) (6 - r)) →
      gpart c t y = 0 := by
  refine Filter.Eventually.of_forall fun y hy => gpart_eq_zero hc ht ⟨?_, ?_⟩
  · have := min_le_left (r - a / 8) (6 - r)
    linarith [hy.1]
  · have := min_le_right (r - a / 8) (6 - r)
    linarith [hy.2]

theorem min_pos_of_mem {r : ℝ} (hr : r ∈ Ioo (a / 4) 3) : 0 < min (r - a / 8) (6 - r) := by
  have ha := a_pos'
  exact lt_min (by linarith [hr.1]) (by linarith [hr.2])

theorem innerPart_eq_zero (hc : c.Hyp T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {x : ℂ}
    (hx : a / 8 < ‖x‖) : c.innerPart t x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have := hc.inner_tsupport t ht hmem
  rw [mem_closedBall, dist_zero_right] at this
  linarith

theorem outerPart_eq_zero (hc : c.Hyp T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {x : ℂ}
    (hx : ‖x‖ < 6) : c.outerPart t x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hx' : x ∈ tsupport (c.outerPart t) ∩ ball 0 6 :=
    ⟨hmem, by rw [mem_ball, dist_zero_right]; exact hx⟩
  rw [hc.outer_tsupport t ht] at hx'
  exact hx'

/-- `∫_{B_r} g = ∫ ω_i(t) = 2πG` for `r ∈ (a/4, 3)`. -/
theorem setIntegral_gpart_ball (hc : c.Hyp T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {r : ℝ}
    (hr : r ∈ Ioo (a / 4) 3) : ∫ y in ball (0 : ℂ) r, gpart c t y = 2 * Real.pi * c.G := by
  have ha := a_pos'
  obtain ⟨-, -, -, -, hi, ho⟩ := RingConfig.setting_parts_smooth hc
  have hic : Continuous (c.innerPart t) :=
    hi.continuous.comp (continuous_const.prodMk continuous_id)
  have hik : HasCompactSupport (c.innerPart t) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (a / 8))
      ((subset_tsupport _).trans (hc.inner_tsupport t ht))
  have hiI : Integrable (c.innerPart t) := hic.integrable_of_hasCompactSupport hik
  have hzero : ∀ y ∈ ball (0 : ℂ) r, c.outerPart t y = 0 := by
    intro y hy
    rw [mem_ball, dist_zero_right] at hy
    exact outerPart_eq_zero hc ht (by linarith [hr.2])
  have hoI : IntegrableOn (c.outerPart t) (ball (0 : ℂ) r) :=
    (integrableOn_congr_fun (fun y hy => (hzero y hy).symm) measurableSet_ball).1
      (integrableOn_zero (μ := volume) (s := ball (0 : ℂ) r))
  have hsplit : ∫ y in ball (0 : ℂ) r, gpart c t y =
      (∫ y in ball (0 : ℂ) r, c.innerPart t y) + ∫ y in ball (0 : ℂ) r, c.outerPart t y :=
    integral_add hiI.integrableOn hoI
  have h1 : ∫ y in ball (0 : ℂ) r, c.innerPart t y = ∫ y, c.innerPart t y := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    rw [mem_ball, dist_zero_right, not_lt] at hy
    exact innerPart_eq_zero hc ht (by linarith [hr.1])
  have h2 : ∫ y in ball (0 : ℂ) r, c.outerPart t y = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero hzero
  rw [hsplit, h1, h2, add_zero, RingConfig.setting_integral_innerPart hc t]

theorem radComp_sub (F₁ F₂ : ℂ → ℂ) (x : ℂ) :
    radComp (fun y => F₁ y - F₂ y) x = radComp F₁ x - radComp F₂ x := by
  simp only [radComp, sub_mul, Complex.sub_re]

theorem angComp_sub (F₁ F₂ : ℂ → ℂ) (x : ℂ) :
    angComp (fun y => F₁ y - F₂ y) x = angComp F₁ x - angComp F₂ x := by
  simp only [angComp, sub_mul, Complex.sub_re]

/-- The angular average of `h(t)·e_r` vanishes on `|x| = r`, `r ∈ (a/4, 3)`. -/
theorem radial_average (hc : c.Hyp T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {r : ℝ}
    (hr : r ∈ Ioo (a / 4) 3) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      radComp (c.h t) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) = 0 := by
  have ha := a_pos'
  have hr0 : 0 < r := by linarith [hr.1]
  have hfun : (fun θ : ℝ => radComp (c.h t) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) =
      fun θ : ℝ => inner ℝ (velocity (gpart c t) (circleMap 0 r θ))
        (Complex.exp ((θ : ℂ) * Complex.I)) := by
    funext θ
    rw [h_eq, radComp_sub, radComp_circle _ hr0, radComp_vortex_circle _ hr0, sub_zero]
  rw [hfun]
  exact Multipole.integral_inner_velocity_radial (gpart_integrable hc t) hr0 (min_pos_of_mem hr)
    (gpart_vanishes_near_circle hc ht)

/-- The angular average of `h(t)·e_θ` vanishes on `|x| = r`, `r ∈ (a/4, 3)`: the circulation
`2πG` of `K * (ω_i + ω_o)(t)` is cancelled by the point vortex. -/
theorem angular_average (hc : c.Hyp T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {r : ℝ}
    (hr : r ∈ Ioo (a / 4) 3) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      angComp (c.h t) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) = 0 := by
  have ha := a_pos'
  have hr0 : 0 < r := by linarith [hr.1]
  have hfun : (fun θ : ℝ => angComp (c.h t) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) =
      fun θ : ℝ => inner ℝ (velocity (gpart c t) (circleMap 0 r θ))
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) - c.G / r := by
    funext θ
    rw [h_eq, angComp_sub, angComp_circle _ hr0, angComp_vortex_circle _ hr0]
  have hv := (contDiff_velocity_gpart hc t).continuous
  have hcont : Continuous fun θ : ℝ => inner ℝ (velocity (gpart c t) (circleMap 0 r θ))
      (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) :=
    (hv.comp (continuous_circleMap 0 r)).inner (continuous_const.mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)))
  rw [hfun, intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul]
  have htan := Multipole.integral_inner_velocity_tangential (gpart_integrable hc t) hr0
    (min_pos_of_mem hr) (gpart_vanishes_near_circle hc ht)
  rw [setIntegral_gpart_ball hc ht hr] at htan
  have hI : (∫ θ in (0 : ℝ)..2 * Real.pi, inner ℝ (velocity (gpart c t) (circleMap 0 r θ))
      (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) = 2 * Real.pi * c.G / r := by
    rw [eq_div_iff hr0.ne', mul_comm]
    exact htan
  rw [hI]
  field_simp
  ring

end RedFieldH

/-- **`lem:reduction`(1)** (`05_single_ring.tex:102-109`). Under the hypotheses of
`lem:reduction` on `[0,T]`: for every `t ∈ [0,T]` there is an open neighbourhood `U` of `N'` on
which `h(t)` is `C^∞`, divergence free, curl free and `3`-fold symmetric, and `h(t) = ∇^⊥ψ` with a
single-valued harmonic `ψ`; the angular averages of `h(t)·e_r` and `h(t)·e_θ` vanish on every
circle `|x| = r`, `r ∈ (a/4,3)`; and `t ↦ h(t) ∈ C^k(N')` is continuous on `[0,T]` for every
`k`. -/
theorem reduction_field {c : RingConfig} {T : ℝ} (hc : c.Hyp T) :
    (∀ t ∈ Icc (0 : ℝ) T, ∃ U : Set ℂ, IsOpen U ∧ annN' ⊆ U ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c.h t) U ∧
      (∀ x ∈ U, Prelim.divergence (c.h t) x = 0) ∧ (∀ x ∈ U, Prelim.curl (c.h t) x = 0) ∧
      IsSymFieldOn U (c.h t) ∧
      (∃ ψ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd ψ U ∧
        ∀ x ∈ U, c.h t x = Prelim.perpGrad ψ x) ∧
      ∀ r ∈ Ioo (a / 4) 3,
        (∫ θ in (0 : ℝ)..2 * Real.pi,
            radComp (c.h t) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) = 0 ∧
          (∫ θ in (0 : ℝ)..2 * Real.pi,
            angComp (c.h t) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) = 0) ∧
      ∀ k : ℕ, CkPathOn k annN' (Icc 0 T) c.h := by
  refine ⟨fun t ht => ⟨RedFieldH.annU, RedFieldH.isOpen_annU, RedFieldH.annN'_subset_annU, ?_,
    fun x hx => RedFieldH.divergence_h hc ht hx, fun x hx => RedFieldH.curl_h hc ht hx,
    RedFieldH.isSymFieldOn_h hc t,
    ⟨RedFieldH.psiH c t, RedFieldH.harmonicOnNhd_psiH hc ht,
      fun x hx => RedFieldH.h_eq_perpGrad hc t (RedFieldH.ne_zero_of_mem_annU hx)⟩,
    fun r hr => ⟨RedFieldH.radial_average hc ht hr, RedFieldH.angular_average hc ht hr⟩⟩,
    fun k => RedFieldH.ckPathOn_h hc k⟩
  rw [RedFieldH.h_eq]
  exact (RedFieldH.contDiff_velocity_gpart hc t).contDiffOn.sub
    ((RedFieldH.contDiffOn_vortex c.G).mono fun x hx => RedFieldH.ne_zero_of_mem_annU hx)

end OneRing

end NonUniqueEuler
