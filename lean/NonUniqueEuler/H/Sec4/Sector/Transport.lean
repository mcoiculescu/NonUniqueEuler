import NonUniqueEuler.Defs.Sec4.Setting
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.Polar.Radial
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.RotDeriv
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.Sobolev.Symmetry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Helper for `lem:sector`(2): the transport part of `L(G)`, sector projections, realness

Helper file of `P/Sec4/Sector.lean` (fully proved). Manuscript `04_ring.tex:267-277`.

* `ae_of_ae_norm`: a property of almost every radius holds at `|x|` for almost every `x`.
* `ae_intervalIntegrable_rot`: for `f ∈ L¹_loc`, `φ ↦ f(O_φ x)` is integrable on `[0, 2π]`
  for almost every `x`; hence `sectorProj_radial_mul_add_ae`: `P_ℓ(a(|x|)f + h) = a(|x|)P_ℓ f +
  P_ℓ h` a.e. for `f, h ∈ L¹_loc` (`P_ℓ` is the pointwise rotation average).
* `thetaDeriv_comp_rot`: `∂_θ(w ∘ O_φ) = (∂_θ w) ∘ O_φ` for `w ∈ H¹` (the weak chain rule
  `MemH.weakPartial_comp_rot`).
* `weakPartial_im_eq_zero`: weak derivatives of a real `H^k` function are real
  (`∂(conj w) = conj(∂w)`, uniqueness of weak derivatives); `thetaDeriv_im_eq_zero`.
* `MemH.mono`: `H^{k'} ⊆ H^k` for `k ≤ k'`.
-/

noncomputable section

open MeasureTheory Set Real Filter ComplexConjugate
open scoped ENNReal

namespace NonUniqueEuler.SectorH

open Sob Ang

/-! ### Almost every radius, almost every point -/

theorem ae_of_ae_norm {P : ℝ → Prop} (h : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), P r) :
    ∀ᵐ x : ℂ, P ‖x‖ := by
  set N := toMeasurable (volume.restrict (Ioi (0 : ℝ))) {r | ¬ P r} with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume.restrict (Ioi (0 : ℝ)) N = 0 := by
    rw [hN, measure_toMeasurable]
    exact h
  have hpre : MeasurableSet ((fun x : ℂ => ‖x‖) ⁻¹' N) := measurable_norm hNm
  have hvol : volume ((fun x : ℂ => ‖x‖) ⁻¹' N) = 0 := by
    have hF : Measurable (N.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hNm
    have h1 := Polar.lintegral_comp_norm hF
    have h2 : ∫⁻ x : ℂ, N.indicator (1 : ℝ → ℝ≥0∞) ‖x‖ =
        volume ((fun x : ℂ => ‖x‖) ⁻¹' N) := by
      rw [← lintegral_indicator_one hpre]
      congr 1
    have h3 : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * N.indicator (1 : ℝ → ℝ≥0∞) r = 0 := by
      refine (lintegral_eq_zero_iff (measurable_id.ennreal_ofReal.mul hF)).2 ?_
      have : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ N := by
        rw [ae_iff]
        simpa using hN0
      filter_upwards [this] with r hr
      simp [hr]
    rw [← h2, h1, h3, mul_zero]
  have hsub : {x : ℂ | ¬ P ‖x‖} ⊆ (fun x : ℂ => ‖x‖) ⁻¹' N := fun x hx =>
    subset_toMeasurable _ _ hx
  rw [ae_iff]
  exact measure_mono_null hsub hvol

/-! ### Rotation averages of locally integrable functions -/

theorem rot_eq_circleMap (φ : ℝ) (x : ℂ) :
    rot φ x = circleMap 0 ‖x‖ (φ + Complex.arg x) := by
  rw [rot, circleMap, zero_add]
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I x]
  push_cast
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

theorem intervalIntegrable_rot_of_circleIntegrable {f : ℂ → ℂ} {x : ℂ}
    (hf : CircleIntegrable f 0 ‖x‖) :
    IntervalIntegrable (fun φ : ℝ => f (rot φ x)) volume 0 (2 * π) := by
  have hper : Function.Periodic (fun θ : ℝ => f (circleMap 0 ‖x‖ θ)) (2 * π) := fun θ => by
    simp only [periodic_circleMap 0 ‖x‖ θ]
  have h1 : IntervalIntegrable (fun θ : ℝ => f (circleMap 0 ‖x‖ θ)) volume 0 (0 + 2 * π) := by
    rw [zero_add]
    exact hf
  have h2 := hper.intervalIntegrable (by positivity) h1 (Complex.arg x)
    (Complex.arg x + 2 * π)
  have h3 := h2.comp_add_right (Complex.arg x)
  simp only [sub_self, add_sub_cancel_left] at h3
  refine h3.congr fun φ _ => ?_
  simp only [rot_eq_circleMap]

theorem ae_intervalIntegrable_rot {f : ℂ → ℂ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x : ℂ, IntervalIntegrable (fun φ : ℝ => f (rot φ x)) volume 0 (2 * π) := by
  filter_upwards [ae_of_ae_norm (Polar.ae_circleIntegrable_of_locallyIntegrable hf)] with x hx
  exact intervalIntegrable_rot_of_circleIntegrable hx

/-- `P_ℓ(a(|x|) f + h) = a(|x|) P_ℓ f + P_ℓ h` almost everywhere, for `f, h ∈ L¹_loc`. -/
theorem sectorProj_radial_mul_add_ae (ℓ : ℤ) (a : ℝ → ℂ) {f h : ℂ → ℂ}
    (hf : LocallyIntegrable f volume) (hh : LocallyIntegrable h volume) :
    ∀ᵐ x : ℂ, sectorProj ℓ (fun y => a ‖y‖ * f y + h y) x =
      a ‖x‖ * sectorProj ℓ f x + sectorProj ℓ h x := by
  filter_upwards [ae_intervalIntegrable_rot hf, ae_intervalIntegrable_rot hh] with x hfx hhx
  have hc : ContinuousOn (fun φ : ℝ => Complex.exp (-((ℓ : ℂ) * φ * Complex.I)))
      (uIcc 0 (2 * π)) := by fun_prop
  have i1 := hfx.continuousOn_mul hc
  have i2 := hhx.continuousOn_mul hc
  simp only [sectorProj, Polar.norm_rot]
  have e : ∀ φ : ℝ, Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) *
      (a ‖x‖ * f (rot φ x) + h (rot φ x)) =
      a ‖x‖ * (Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * f (rot φ x)) +
        Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * h (rot φ x) := fun φ => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_add (i1.const_mul _) i2, intervalIntegral.integral_const_mul]
  ring

/-! ### `∂_θ` and rotations -/

theorem rot_re (φ : ℝ) (x : ℂ) : (rot φ x).re = Real.cos φ * x.re - Real.sin φ * x.im := by
  simp [rot, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem rot_im (φ : ℝ) (x : ℂ) : (rot φ x).im = Real.sin φ * x.re + Real.cos φ * x.im := by
  simp [rot, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

theorem thetaDeriv_comp_rot {f : ℂ → ℂ} (hf : MemH 1 f) (φ : ℝ) :
    thetaDeriv (fun x => f (rot φ x)) =ᵐ[volume] fun x => thetaDeriv f (rot φ x) := by
  obtain ⟨h1, h2⟩ := hf.weakPartial_comp_rot φ
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [thetaDeriv, hx1, hx2, rot_re, rot_im]
  push_cast
  ring

/-! ### Realness -/

/-- `H^{k'} ⊆ H^k` for `k ≤ k'`. -/
theorem MemH.mono {k k' : ℕ} {f : ℂ → ℂ} (hf : MemH k' f) (hk : k ≤ k') : MemH k f := by
  refine ⟨hf.memLp, fun γ hγ => hf.deriv γ ?_⟩
  simp only [multiIdx, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hγ ⊢
  omega

theorem dirDeriv_conj (v : ℂ) (φ : ℂ → ℂ) :
    dirDeriv v (fun x => conj (φ x)) = fun x => conj (dirDeriv v φ x) := by
  funext x
  have h : (fun x => conj (φ x)) = (Complex.conjCLE : ℂ ≃L[ℝ] ℂ) ∘ φ := by
    funext y; simp
  simp only [dirDeriv]
  rw [h, ContinuousLinearEquiv.comp_fderiv]
  simp

theorem iterDirDeriv_conj (vs : List ℂ) (φ : ℂ → ℂ) :
    iterDirDeriv vs (fun x => conj (φ x)) = fun x => conj (iterDirDeriv vs φ x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [iterDirDeriv_cons, ih, dirDeriv_conj]; rfl

theorem isTestFn_conj {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) :
    IsTestFn univ (fun x => conj (φ x)) := by
  refine ⟨Complex.conjCLE.contDiff.comp hφ.smooth, ?_, subset_univ _⟩
  exact hφ.compact.comp_left (g := conj) (map_zero _)

theorem hasWeakDerivOn_conj {vs : List ℂ} {f g : ℂ → ℂ} (h : HasWeakDerivOn univ vs f g) :
    HasWeakDerivOn univ vs (fun x => conj (f x)) (fun x => conj (g x)) := by
  intro φ hφ
  have hψ := isTestFn_conj hφ
  have k := h _ hψ
  have e1 : iterDirDeriv vs φ = fun x => conj (iterDirDeriv vs (fun x => conj (φ x)) x) := by
    rw [iterDirDeriv_conj]
    simp
  rw [e1]
  have e2 : ∫ x, conj (f x) * conj (iterDirDeriv vs (fun x => conj (φ x)) x) =
      conj (∫ x, f x * iterDirDeriv vs (fun x => conj (φ x)) x) := by
    rw [← integral_conj]
    simp
  have e3 : ∫ x, conj (g x) * φ x = conj (∫ x, g x * conj (φ x)) := by
    rw [← integral_conj]
    simp
  rw [e2, e3, k]
  simp

theorem memLp_conj {g : ℂ → ℂ} (hg : MemLp g 2 volume) :
    MemLp (fun x => conj (g x)) 2 volume :=
  hg.of_le (Complex.continuous_conj.comp_aestronglyMeasurable hg.1)
    (Eventually.of_forall fun x => by simp)

/-- The weak derivatives of a real `H^k` function are real. -/
theorem weakPartial_im_eq_zero {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f)
    (hre : ∀ᵐ x ∂volume, (f x).im = 0) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    ∀ᵐ x ∂volume, (weakPartial γ f x).im = 0 := by
  obtain ⟨hL, hW⟩ := hf.memLp_weakPartial hγ
  have hW' := hasWeakDerivOn_conj hW
  have hconj : ∀ᵐ x ∂volume, x ∈ univ → conj (f x) = f x := by
    filter_upwards [hre] with x hx _
    exact Complex.conj_eq_iff_im.2 hx
  have hW'' : HasWeakDerivOn univ (pdList γ) f (fun x => conj (weakPartial γ f x)) :=
    hW'.congr_ae hconj (Eventually.of_forall fun _ _ => rfl)
  have heq := hf.weakPartial_ae_eq hγ (memLp_conj hL) hW''
  filter_upwards [heq] with x hx
  exact Complex.conj_eq_iff_im.1 hx.symm

theorem thetaDeriv_im_eq_zero {f : ℂ → ℂ} (hf : MemH 1 f) (hre : ∀ᵐ x ∂volume, (f x).im = 0) :
    ∀ᵐ x ∂volume, (thetaDeriv f x).im = 0 := by
  have h10 : ((1, 0) : ℕ × ℕ) ∈ multiIdx 1 := by decide
  have h01 : ((0, 1) : ℕ × ℕ) ∈ multiIdx 1 := by decide
  filter_upwards [weakPartial_im_eq_zero hf hre h10, weakPartial_im_eq_zero hf hre h01]
    with x h1 h2
  simp [thetaDeriv, Complex.mul_im, h1, h2]

end NonUniqueEuler.SectorH
