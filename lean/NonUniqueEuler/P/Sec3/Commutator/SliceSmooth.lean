import NonUniqueEuler.Defs.Sec3.Commutator
import NonUniqueEuler.I.Sec3.CommFormula
import NonUniqueEuler.I.Sec3.Commutator.Moments
import NonUniqueEuler.I.Infra.ConvMinkowski.ApproxIdentity
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Proof: `C_ε[u,w] → 0` for a smooth divergence-free field, at a fixed time

Proof of `NonUniqueEuler/I/Sec3/Commutator/SliceSmooth.lean` (`03_compactness.tex:408-438`).

* Reduction: `C_ε[u,g](t)` depends on `u(t)` only through its a.e. class, so `u(t)` may be
  replaced by a strongly measurable representative `f` (this makes every parametric integral
  below measurable in `x`, by `StronglyMeasurable.integral_prod_right`).
* For `x ∈ B_R`, `0 < ε ≤ 1` (by `commEps_eq_integral_ball`)
  `C_ε(x) = ∫_{B₁} f(x-εz) Dρ(z)(q_ε(x,z)) dz`, `q_ε(x,z) = ε⁻¹(g(x) - g(x-εz))`.
  Taylor (mean value inequality for `g - Dg(x)` on `\bar B(x,ε)`, with `Dg` `L`-Lipschitz on
  `\bar B_{R+1}`): `‖q_ε(x,z) - Dg(x)z‖ ≤ Lε`.
* `Dρ(z)(Dg(x)z) = Σ c_{ji}(x) ψ_{ji}(z)` with `ψ = ℓ_j(z) Dρ(z)e_i`; with the moments
  `∫_{B₁}ψ_{ji} = -δ_{ij}` and `div g = 0`,
  `C_ε(x) = Σ c_{ji}(x) D_{ji,ε}(x) + E_ε(x)` where `D_{ji,ε}` is the approximate-identity error
  `∫_{B₁} f(x-εz)ψ_{ji}(z)dz - (∫_{B₁}ψ_{ji}) f(x)`, and
  `|E_ε(x)| ≤ KLε ∫_{B₁}|f(x-εz)|dz ≤ KLε (|D_{5,ε}(x)| + |B₁| |f(x)|)` with `D_{5,ε}` the
  approximate-identity error of `|f|` against the kernel `1`.
* The approximate identity (`Conv.tendsto_lintegral_ball_integral_comp_sub_smul`) sends every
  `∫_{B_R}|D_{·,ε}|` to `0`; hence `∫_{B_R}|C_ε| → 0`.

Deviation (harmless): the bound on `E_ε` is obtained from the approximate identity applied to
`|f|` (which bounds `∫_{B_R}∫_{B₁}|f(x-εz)|dz dx` for small `ε`) instead of Tonelli and
translation invariance; the conclusion is the manuscript's `‖E_ε(t)‖_{1,R} = O(ε)`.

Helper names live in the namespace `NonUniqueEuler.Weak.SliceSmoothH`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Weak

namespace SliceSmoothH

/-- The kernel `ψ(z) = ℓ(z) Dρ(z) v` (`ψ^{ij}` of `03_compactness.tex:415`). -/
def psi (ρ : ℂ → ℝ) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) (z : ℂ) : ℝ :=
  ℓ z * fderiv ℝ ρ z v

/-- The approximate-identity error `∫_{B₁} f(x - εz) ψ(z) dz - (∫_{B₁} ψ) f(x)`. -/
def aiErr (f ψ : ℂ → ℝ) (ε : ℝ) (x : ℂ) : ℝ :=
  (∫ z in ball (0 : ℂ) 1, f (x - ε • z) * ψ z) - (∫ z in ball (0 : ℂ) 1, ψ z) * f x

theorem continuous_psi {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    Continuous (psi ρ ℓ v) := by
  have h : Continuous (fderiv ℝ ρ) := hρ.contDiff.continuous_fderiv (by simp)
  exact ℓ.continuous.mul (h.clm_apply continuous_const)

/-- The commutator depends on `u(t)` only through its a.e. class. -/
theorem commEps_congr_ae {ρ : ℂ → ℝ} {ε : ℝ} {u u' : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {t : ℝ}
    (h : u t =ᵐ[volume] u' t) (x : ℂ) : commEps ρ ε u w t x = commEps ρ ε u' w t x := by
  unfold commEps dotGradMollify mollifyDiv
  congr 1 <;> refine integral_congr_ae ?_ <;> filter_upwards [h] with y hy <;> rw [hy]

/-- For `f ∈ L¹_loc`, `z ↦ f(x - εz)` is integrable on `B₁`, for every `x`. -/
theorem integrableOn_comp_sub_smul {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) (x : ℂ)
    {ε : ℝ} (hε : 0 < ε) : IntegrableOn (fun z => f (x - ε • z)) (ball (0 : ℂ) 1) volume := by
  have hK : IntegrableOn f (closedBall x ε) volume :=
    hf.integrableOn_isCompact (isCompact_closedBall x ε)
  have hF : Integrable ((closedBall x ε).indicator f) volume :=
    (integrable_indicator_iff measurableSet_closedBall).2 hK
  have h2 : Integrable (fun z => (closedBall x ε).indicator f (x + (-ε) • z)) volume :=
    (hF.comp_add_left x).comp_smul (neg_ne_zero.2 hε.ne')
  refine h2.integrableOn.congr_fun (fun z hz => ?_) measurableSet_ball
  simp only [neg_smul, ← sub_eq_add_neg]
  have hmem : x - ε • z ∈ closedBall x ε := by
    rw [mem_ball_zero_iff] at hz
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg hε.le]
    exact mul_le_of_le_one_right hε.le hz.le
  simp only [indicator_of_mem hmem]

/-- `z ↦ f(x - εz) ψ(z)` is integrable on `B₁` for continuous `ψ`. -/
theorem integrableOn_comp_sub_smul_mul {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) (x : ℂ)
    {ε : ℝ} (hε : 0 < ε) {ψ : ℂ → ℝ} (hψ : Continuous ψ) :
    IntegrableOn (fun z => f (x - ε • z) * ψ z) (ball (0 : ℂ) 1) volume := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hψ.continuousOn
  refine (integrableOn_comp_sub_smul hf x hε).mul_bdd (c := C) hψ.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz using
    hC z (ball_subset_closedBall hz)

/-- Measurability of the approximate-identity error in `x`. -/
theorem measurable_enorm_aiErr {f : ℂ → ℝ} (hf : StronglyMeasurable f) {ψ : ℂ → ℝ}
    (hψ : Continuous ψ) (ε : ℝ) : Measurable fun x => ‖aiErr f ψ ε x‖ₑ := by
  have h1 : StronglyMeasurable fun x => ∫ z in ball (0 : ℂ) 1, f (x - ε • z) * ψ z := by
    refine StronglyMeasurable.integral_prod_right (f := fun x z => f (x - ε • z) * ψ z) ?_
    exact (hf.comp_measurable (by fun_prop)).mul
      (hψ.stronglyMeasurable.comp_measurable measurable_snd)
  exact (h1.sub (stronglyMeasurable_const.mul hf)).enorm

/-- Taylor's formula: `‖ε⁻¹(g(x) - g(x - εz)) - Dg(x)z‖ ≤ Lε` for `x ∈ B_R`, `z ∈ B₁`,
`0 < ε ≤ 1`, when `Dg` is `L`-Lipschitz on `\bar B_{R+1}`. -/
theorem norm_diffQuot_sub_fderiv_le {g : ℂ → ℂ} (hg : Differentiable ℝ g) {R : ℝ} {L : NNReal}
    (hL : LipschitzOnWith L (fderiv ℝ g) (closedBall (0 : ℂ) (R + 1)))
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) R) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    ‖ε⁻¹ • (g x - g (x - ε • z)) - fderiv ℝ g x z‖ ≤ L * ε := by
  rw [mem_ball_zero_iff] at hx hz
  have hsub : closedBall x ε ⊆ closedBall (0 : ℂ) (R + 1) := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_closedBall_zero_iff]
    calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ R + 1 := by linarith
  have hxs : x ∈ closedBall x ε := mem_closedBall_self hε.le
  have hnz : ‖x - ε • z - x‖ ≤ ε := by
    rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hε.le]
    exact mul_le_of_le_one_right hε.le hz.le
  have hys : x - ε • z ∈ closedBall x ε := by
    rw [mem_closedBall, dist_eq_norm]
    exact hnz
  have key := (convex_closedBall x ε).norm_image_sub_le_of_norm_fderiv_le'
    (f := g) (φ := fderiv ℝ g x) (C := L * ε) (fun y _ => hg y)
    (fun y hy => (hL.norm_sub_le (hsub hy) (hsub hxs)).trans (by
      rw [mem_closedBall, dist_eq_norm] at hy
      exact mul_le_mul_of_nonneg_left hy L.coe_nonneg)) hxs hys
  have halg : ε⁻¹ • (g x - g (x - ε • z)) - fderiv ℝ g x z =
      (-ε⁻¹) • (g (x - ε • z) - g x - fderiv ℝ g x (x - ε • z - x)) := by
    have hc : (-ε⁻¹) • (ε • fderiv ℝ g x z) = -fderiv ℝ g x z := by
      rw [smul_smul, neg_mul, inv_mul_cancel₀ hε.ne', neg_smul, one_smul]
    rw [sub_sub_cancel_left, map_neg, map_smul, sub_neg_eq_add, smul_add, hc, neg_smul,
      smul_sub, smul_sub]
    abel
  rw [halg, norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg hε.le]
  calc ε⁻¹ * ‖g (x - ε • z) - g x - fderiv ℝ g x (x - ε • z - x)‖
      ≤ ε⁻¹ * (L * ε * ε) := by
        gcongr
        exact key.trans (mul_le_mul_of_nonneg_left hnz (by positivity))
    _ = L * ε := by field_simp

/-- `B(Az) = Σ_{j,i} (Ae_j)_i ℓ_j(z) B e_i` for real-linear `A : ℂ → ℂ`, `B : ℂ → ℝ`
(coordinates `ℓ_1 = re`, `ℓ_2 = im`, `e_1 = 1`, `e_2 = I`). -/
theorem clm_comp_apply_decomp (A : ℂ →L[ℝ] ℂ) (B : ℂ →L[ℝ] ℝ) (z : ℂ) :
    B (A z) = (A 1).re * (z.re * B 1) + (A 1).im * (z.re * B Complex.I)
      + (A Complex.I).re * (z.im * B 1) + (A Complex.I).im * (z.im * B Complex.I) := by
  have hdec : ∀ w : ℂ, w = w.re • (1 : ℂ) + w.im • Complex.I := fun w => by
    apply Complex.ext <;> simp
  have h1 : B (A z) = z.re * B (A 1) + z.im * B (A Complex.I) := by
    conv_lhs => rw [hdec z]
    simp only [map_add, map_smul, smul_eq_mul]
  have h2 : ∀ w : ℂ, B w = w.re * B 1 + w.im * B Complex.I := fun w => by
    conv_lhs => rw [hdec w]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [h1, h2 (A 1), h2 (A Complex.I)]
  ring

/-- Linearity of the integral for a sum of five terms. -/
theorem integral_add5 {μ : Measure ℂ} {f₁ f₂ f₃ f₄ f₅ : ℂ → ℝ} (h₁ : Integrable f₁ μ)
    (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ) (h₄ : Integrable f₄ μ) (h₅ : Integrable f₅ μ) :
    ∫ z, f₁ z + f₂ z + f₃ z + f₄ z + f₅ z ∂μ =
      (∫ z, f₁ z ∂μ) + (∫ z, f₂ z ∂μ) + (∫ z, f₃ z ∂μ) + (∫ z, f₄ z ∂μ) + ∫ z, f₅ z ∂μ := by
  have e : (fun z => f₁ z + f₂ z + f₃ z + f₄ z + f₅ z) = f₁ + f₂ + f₃ + f₄ + f₅ := rfl
  rw [e, integral_add' (((h₁.add h₂).add h₃).add h₄) h₅, integral_add' ((h₁.add h₂).add h₃) h₄,
    integral_add' (h₁.add h₂) h₃, integral_add' h₁ h₂]

theorem norm_sum4_le {a₁ a₂ a₃ a₄ D₁ D₂ D₃ D₄ E M B : ℝ} (c1 : ‖a₁‖ ≤ M) (c2 : ‖a₂‖ ≤ M)
    (c3 : ‖a₃‖ ≤ M) (c4 : ‖a₄‖ ≤ M) (hE : ‖E‖ ≤ B) :
    ‖a₁ * D₁ + a₂ * D₂ + a₃ * D₃ + a₄ * D₄ + E‖ ≤ M * (‖D₁‖ + ‖D₂‖ + ‖D₃‖ + ‖D₄‖) + B := by
  have t1 := norm_add_le (a₁ * D₁ + a₂ * D₂ + a₃ * D₃ + a₄ * D₄) E
  have t2 := norm_add_le (a₁ * D₁ + a₂ * D₂ + a₃ * D₃) (a₄ * D₄)
  have t3 := norm_add_le (a₁ * D₁ + a₂ * D₂) (a₃ * D₃)
  have t4 := norm_add_le (a₁ * D₁) (a₂ * D₂)
  have n1 : ‖a₁ * D₁‖ ≤ M * ‖D₁‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right c1 (norm_nonneg _)
  have n2 : ‖a₂ * D₂‖ ≤ M * ‖D₂‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right c2 (norm_nonneg _)
  have n3 : ‖a₃ * D₃‖ ≤ M * ‖D₃‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right c3 (norm_nonneg _)
  have n4 : ‖a₄ * D₄‖ ≤ M * ‖D₄‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right c4 (norm_nonneg _)
  linarith

theorem locallyIntegrable_norm {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun y => ‖f y‖) volume :=
  locallyIntegrable_iff.2 fun _ hk => (hf.integrableOn_isCompact hk).norm

/-- The pointwise decomposition and bound (`03_compactness.tex:418-424`): for `x ∈ B_R` and
`0 < ε ≤ 1`, `|C_ε(x)| ≤ M Σ|D_{ji,ε}(x)| + KLε (|D_{5,ε}(x)| + |B₁| |f(x)|)`. -/
theorem norm_commEps_le {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {g : ℂ → ℂ} (hg : ContDiff ℝ 2 g)
    (hdiv : ∀ x, (fderiv ℝ g x 1).re + (fderiv ℝ g x Complex.I).im = 0)
    {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) {R : ℝ} {L : NNReal}
    (hL : LipschitzOnWith L (fderiv ℝ g) (closedBall (0 : ℂ) (R + 1)))
    {K : ℝ} (hK : ∀ z, ‖fderiv ℝ ρ z‖ ≤ K) {M : ℝ}
    (hM : ∀ x ∈ closedBall (0 : ℂ) R, ‖fderiv ℝ g x‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {x : ℂ} (hx : x ∈ ball (0 : ℂ) R) (t : ℝ) :
    ‖commEps ρ ε (fun _ => f) (fun _ => g) t x‖ ≤
      M * (‖aiErr f (psi ρ Complex.reCLM 1) ε x‖ + ‖aiErr f (psi ρ Complex.reCLM Complex.I) ε x‖
        + ‖aiErr f (psi ρ Complex.imCLM 1) ε x‖ + ‖aiErr f (psi ρ Complex.imCLM Complex.I) ε x‖)
      + K * L * ε * (‖aiErr (fun y => ‖f y‖) (fun _ => 1) ε x‖
        + (∫ _ in ball (0 : ℂ) 1, (1 : ℝ)) * ‖f x‖) := by
  have hdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have huw : LocallyIntegrable (fun y => (fun _ => f) t y • (fun _ => g) t y) volume :=
    hf.smul_continuous hg.continuous
  rw [commEps_eq_integral_ball hρ hε hf huw x]
  have hDρ : Continuous (fderiv ℝ ρ) := hρ.contDiff.continuous_fderiv (by simp)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  -- the pointwise identity of the integrands
  have hpt : ∀ z, f (x - ε • z) * fderiv ℝ ρ z (ε⁻¹ • (g x - g (x - ε • z))) =
      (fderiv ℝ g x 1).re * (f (x - ε • z) * psi ρ Complex.reCLM 1 z)
      + (fderiv ℝ g x 1).im * (f (x - ε • z) * psi ρ Complex.reCLM Complex.I z)
      + (fderiv ℝ g x Complex.I).re * (f (x - ε • z) * psi ρ Complex.imCLM 1 z)
      + (fderiv ℝ g x Complex.I).im * (f (x - ε • z) * psi ρ Complex.imCLM Complex.I z)
      + f (x - ε • z) * fderiv ℝ ρ z (ε⁻¹ • (g x - g (x - ε • z)) - fderiv ℝ g x z) := by
    intro z
    have h := clm_comp_apply_decomp (fderiv ℝ g x) (fderiv ℝ ρ z) z
    simp only [psi, map_sub, Complex.reCLM_apply, Complex.imCLM_apply]
    rw [h]
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  have hint : ∀ c : ℝ, ∀ ψ : ℂ → ℝ, Continuous ψ →
      Integrable (fun z => c * (f (x - ε • z) * ψ z)) (volume.restrict (ball (0 : ℂ) 1)) :=
    fun c ψ hψ => (integrableOn_comp_sub_smul_mul hf x hε hψ).const_mul c
  have hqc : Continuous fun z => fderiv ℝ ρ z (ε⁻¹ • (g x - g (x - ε • z)) - fderiv ℝ g x z) :=
    hDρ.clm_apply (by fun_prop)
  have hE := integrableOn_comp_sub_smul_mul hf x hε hqc
  have h1 := hint (fderiv ℝ g x 1).re _ (continuous_psi hρ Complex.reCLM 1)
  have h2 := hint (fderiv ℝ g x 1).im _ (continuous_psi hρ Complex.reCLM Complex.I)
  have h3 := hint (fderiv ℝ g x Complex.I).re _ (continuous_psi hρ Complex.imCLM 1)
  have h4 := hint (fderiv ℝ g x Complex.I).im _ (continuous_psi hρ Complex.imCLM Complex.I)
  rw [integral_add5 h1 h2 h3 h4 hE, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul]
  -- the moments `∫_{B₁} ψ_{ji} = -δ_{ij}` and `div g = 0`
  have m1 : ∫ z in ball (0 : ℂ) 1, psi ρ Complex.reCLM 1 z = -1 := by
    simpa [psi] using setIntegral_ball_mul_fderiv_mollifier_eq_neg hρ Complex.reCLM 1
  have m2 : ∫ z in ball (0 : ℂ) 1, psi ρ Complex.reCLM Complex.I z = 0 := by
    simpa [psi] using setIntegral_ball_mul_fderiv_mollifier_eq_neg hρ Complex.reCLM Complex.I
  have m3 : ∫ z in ball (0 : ℂ) 1, psi ρ Complex.imCLM 1 z = 0 := by
    simpa [psi] using setIntegral_ball_mul_fderiv_mollifier_eq_neg hρ Complex.imCLM 1
  have m4 : ∫ z in ball (0 : ℂ) 1, psi ρ Complex.imCLM Complex.I z = -1 := by
    simpa [psi] using setIntegral_ball_mul_fderiv_mollifier_eq_neg hρ Complex.imCLM Complex.I
  -- the error term
  have hEb : ‖∫ z in ball (0 : ℂ) 1,
      f (x - ε • z) * fderiv ℝ ρ z (ε⁻¹ • (g x - g (x - ε • z)) - fderiv ℝ g x z)‖ ≤
      K * L * ε * (‖aiErr (fun y => ‖f y‖) (fun _ => 1) ε x‖
        + (∫ _ in ball (0 : ℂ) 1, (1 : ℝ)) * ‖f x‖) := by
    have hKLε : 0 ≤ K * (L * ε) := mul_nonneg hK0 (mul_nonneg L.coe_nonneg hε.le)
    have hn : Integrable (fun z => ‖f (x - ε • z)‖ * 1 * (K * (L * ε)))
        (volume.restrict (ball (0 : ℂ) 1)) :=
      (integrableOn_comp_sub_smul_mul (locallyIntegrable_norm hf) x hε
        continuous_const).mul_const _
    refine (norm_integral_le_of_norm_le hn ?_).trans ?_
    · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      rw [norm_mul, mul_one]
      gcongr
      exact ((fderiv ℝ ρ z).le_opNorm _).trans (mul_le_mul (hK z)
        (norm_diffQuot_sub_fderiv_le hdiff hL hx hε hε1 hz) (norm_nonneg _) hK0)
    · rw [integral_mul_const]
      have h5 : ∫ z in ball (0 : ℂ) 1, ‖f (x - ε • z)‖ * 1 =
          aiErr (fun y => ‖f y‖) (fun _ => 1) ε x + (∫ _ in ball (0 : ℂ) 1, (1 : ℝ)) * ‖f x‖ := by
        simp only [aiErr]
        ring
      rw [h5]
      have hle : aiErr (fun y => ‖f y‖) (fun _ => 1) ε x ≤
          ‖aiErr (fun y => ‖f y‖) (fun _ => 1) ε x‖ := Real.le_norm_self _
      nlinarith [mul_le_mul_of_nonneg_right hle hKLε]
  -- the coefficients `c_{ji}(x)` are bounded by `M`
  have hcoef : ∀ v : ℂ, ‖v‖ = 1 → ‖(fderiv ℝ g x v).re‖ ≤ M ∧ ‖(fderiv ℝ g x v).im‖ ≤ M := by
    intro v hv
    have h0 : ‖fderiv ℝ g x v‖ ≤ M := ((fderiv ℝ g x).le_opNorm v).trans (by
      rw [hv, mul_one]; exact hM x (ball_subset_closedBall hx))
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact ⟨(Complex.abs_re_le_norm _).trans h0, (Complex.abs_im_le_norm _).trans h0⟩
  obtain ⟨c1, c2⟩ := hcoef 1 norm_one
  obtain ⟨c3, c4⟩ := hcoef Complex.I Complex.norm_I
  refine le_of_eq_of_le ?_ (norm_sum4_le c1 c2 c3 c4 hEb)
  congr 1
  simp only [aiErr, m1, m2, m3, m4]
  linear_combination (-(f x)) * hdiv x

/-! ### From the pointwise bound to the `L¹(B_R)` bound -/

theorem ofReal_add4_le (a b c d : ℝ) :
    ENNReal.ofReal (a + b + c + d) ≤
      ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c + ENNReal.ofReal d := by
  calc ENNReal.ofReal (a + b + c + d) ≤ ENNReal.ofReal (a + b + c) + ENNReal.ofReal d :=
        ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (a + b) + ENNReal.ofReal c + ENNReal.ofReal d := by
        gcongr; exact ENNReal.ofReal_add_le
    _ ≤ _ := by gcongr; exact ENNReal.ofReal_add_le

theorem enorm_le_of_norm_le {c M K' V d₁ d₂ d₃ d₄ d₅ y : ℝ} (hM : 0 ≤ M) (hK' : 0 ≤ K')
    (hV : 0 ≤ V) (h : ‖c‖ ≤ M * (‖d₁‖ + ‖d₂‖ + ‖d₃‖ + ‖d₄‖) + K' * (‖d₅‖ + V * ‖y‖)) :
    ‖c‖ₑ ≤ ENNReal.ofReal M * (‖d₁‖ₑ + ‖d₂‖ₑ + ‖d₃‖ₑ + ‖d₄‖ₑ)
      + ENNReal.ofReal K' * (‖d₅‖ₑ + ENNReal.ofReal V * ‖y‖ₑ) := by
  calc ‖c‖ₑ = ENNReal.ofReal ‖c‖ := (ofReal_norm c).symm
    _ ≤ ENNReal.ofReal (M * (‖d₁‖ + ‖d₂‖ + ‖d₃‖ + ‖d₄‖) + K' * (‖d₅‖ + V * ‖y‖)) :=
        ENNReal.ofReal_le_ofReal h
    _ ≤ ENNReal.ofReal (M * (‖d₁‖ + ‖d₂‖ + ‖d₃‖ + ‖d₄‖))
          + ENNReal.ofReal (K' * (‖d₅‖ + V * ‖y‖)) := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal M * ENNReal.ofReal (‖d₁‖ + ‖d₂‖ + ‖d₃‖ + ‖d₄‖)
          + ENNReal.ofReal K' * ENNReal.ofReal (‖d₅‖ + V * ‖y‖) := by
        rw [ENNReal.ofReal_mul hM, ENNReal.ofReal_mul hK']
    _ ≤ _ := by
        gcongr
        · exact (ofReal_add4_le _ _ _ _).trans_eq (by simp only [ofReal_norm])
        · refine ENNReal.ofReal_add_le.trans_eq ?_
          rw [ENNReal.ofReal_mul hV, ofReal_norm, ofReal_norm]

theorem lintegral_bound_eq {μ : Measure ℂ} {a₁ a₂ a₃ a₄ a₅ b : ℂ → ℝ≥0∞} (h₁ : Measurable a₁)
    (h₂ : Measurable a₂) (h₃ : Measurable a₃) (h₄ : Measurable a₄) (h₅ : Measurable a₅)
    {c₁ c₂ c₃ : ℝ≥0∞} (hc₁ : c₁ ≠ ⊤) (hc₂ : c₂ ≠ ⊤) (hc₃ : c₃ ≠ ⊤) :
    ∫⁻ x, c₁ * (a₁ x + a₂ x + a₃ x + a₄ x) + c₂ * (a₅ x + c₃ * b x) ∂μ =
      c₁ * (∫⁻ x, a₁ x ∂μ + ∫⁻ x, a₂ x ∂μ + ∫⁻ x, a₃ x ∂μ + ∫⁻ x, a₄ x ∂μ)
        + c₂ * (∫⁻ x, a₅ x ∂μ + c₃ * ∫⁻ x, b x ∂μ) := by
  rw [lintegral_add_left' (f := fun x => c₁ * (a₁ x + a₂ x + a₃ x + a₄ x)) (by fun_prop),
    lintegral_const_mul' _ _ hc₁, lintegral_const_mul' _ _ hc₂,
    lintegral_add_left' (f := fun x => a₁ x + a₂ x + a₃ x) (by fun_prop),
    lintegral_add_left' (f := fun x => a₁ x + a₂ x) (by fun_prop),
    lintegral_add_left' h₁.aemeasurable, lintegral_add_left' h₅.aemeasurable,
    lintegral_const_mul' _ _ hc₃]

theorem tendsto_bound {I₁ I₂ I₃ I₄ I₅ : ℝ → ℝ≥0∞} (h₁ : Tendsto I₁ (𝓝[>] 0) (𝓝 0))
    (h₂ : Tendsto I₂ (𝓝[>] 0) (𝓝 0)) (h₃ : Tendsto I₃ (𝓝[>] 0) (𝓝 0))
    (h₄ : Tendsto I₄ (𝓝[>] 0) (𝓝 0)) (h₅ : Tendsto I₅ (𝓝[>] 0) (𝓝 0))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (k : ℝ) {b : ℝ≥0∞} (hb : b ≠ ⊤) :
    Tendsto (fun ε => c * (I₁ ε + I₂ ε + I₃ ε + I₄ ε) + ENNReal.ofReal (k * ε) * (I₅ ε + b))
      (𝓝[>] 0) (𝓝 0) := by
  have e1 : Tendsto (fun ε => c * (I₁ ε + I₂ ε + I₃ ε + I₄ ε)) (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (((h₁.add h₂).add h₃).add h₄) (Or.inr hc)
    simpa using this
  have e2 : Tendsto (fun ε : ℝ => ENNReal.ofReal (k * ε)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => k * ε) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_const_mul k).tendsto 0
    have : Tendsto (fun ε : ℝ => k * ε) (𝓝[>] 0) (𝓝 0) := h0.mono_left nhdsWithin_le_nhds
    simpa using ENNReal.tendsto_ofReal this
  have e3 : Tendsto (fun ε => I₅ ε + b) (𝓝[>] 0) (𝓝 b) := by
    simpa using h₅.add tendsto_const_nhds
  have e4 := ENNReal.Tendsto.mul e2 (Or.inr hb) e3 (Or.inr ENNReal.zero_ne_top)
  simpa using e1.add e4

/-- The fixed-time statement for a strongly measurable `L¹_loc` function `f`. -/
theorem tendsto_main {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {g : ℂ → ℂ} (hg : ContDiff ℝ 2 g)
    (hdiv : ∀ x, (fderiv ℝ g x 1).re + (fderiv ℝ g x Complex.I).im = 0)
    {f : ℂ → ℝ} (hfm : StronglyMeasurable f) (hf : LocallyIntegrable f volume) (t R : ℝ) :
    Tendsto (fun ε : ℝ => ∫⁻ x in ball (0 : ℂ) R, ‖commEps ρ ε (fun _ => f) (fun _ => g) t x‖ₑ)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K, hK⟩ := (hρ.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hρ.contDiff.continuous_fderiv (by simp))
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
  obtain ⟨L, hL⟩ := hg1.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall (0 : ℂ) (R + 1)) (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hg1.continuous.continuousOn
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hM' : ∀ x ∈ closedBall (0 : ℂ) R, ‖fderiv ℝ g x‖ ≤ max M 0 :=
    fun x hx => (hM x hx).trans (le_max_left _ _)
  have hV : 0 ≤ ∫ _ in ball (0 : ℂ) 1, (1 : ℝ) :=
    setIntegral_nonneg measurableSet_ball (fun _ _ => zero_le_one)
  have hN : ∫⁻ x in ball (0 : ℂ) R, ‖f x‖ₑ ≠ ⊤ :=
    ((hf.integrableOn_isCompact (isCompact_closedBall (0 : ℂ) R)).mono_set
      ball_subset_closedBall).hasFiniteIntegral.ne
  have hA : ∀ ℓ v, Tendsto (fun ε => ∫⁻ x in ball (0 : ℂ) R, ‖aiErr f (psi ρ ℓ v) ε x‖ₑ)
      (𝓝[>] 0) (𝓝 0) :=
    fun ℓ v => Conv.tendsto_lintegral_ball_integral_comp_sub_smul hf (continuous_psi hρ ℓ v) R
  have hA5 : Tendsto (fun ε => ∫⁻ x in ball (0 : ℂ) R,
      ‖aiErr (fun y => ‖f y‖) (fun _ => 1) ε x‖ₑ) (𝓝[>] 0) (𝓝 0) :=
    Conv.tendsto_lintegral_ball_integral_comp_sub_smul (locallyIntegrable_norm hf)
      continuous_const R
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_bound (hA Complex.reCLM 1) (hA Complex.reCLM Complex.I) (hA Complex.imCLM 1)
      (hA Complex.imCLM Complex.I) hA5 (c := ENNReal.ofReal (max M 0)) ENNReal.ofReal_ne_top
      (K * L) (b := ENNReal.ofReal (∫ _ in ball (0 : ℂ) 1, (1 : ℝ)) *
        ∫⁻ x in ball (0 : ℂ) R, ‖f x‖ₑ) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN))
    (Eventually.of_forall fun _ => by simp) ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
  have hKLε : 0 ≤ K * L * ε := mul_nonneg (mul_nonneg hK0 L.coe_nonneg) hε.1.le
  calc ∫⁻ x in ball (0 : ℂ) R, ‖commEps ρ ε (fun _ => f) (fun _ => g) t x‖ₑ
      ≤ ∫⁻ x in ball (0 : ℂ) R,
          ENNReal.ofReal (max M 0) * (‖aiErr f (psi ρ Complex.reCLM 1) ε x‖ₑ
            + ‖aiErr f (psi ρ Complex.reCLM Complex.I) ε x‖ₑ
            + ‖aiErr f (psi ρ Complex.imCLM 1) ε x‖ₑ
            + ‖aiErr f (psi ρ Complex.imCLM Complex.I) ε x‖ₑ)
          + ENNReal.ofReal (K * L * ε) * (‖aiErr (fun y => ‖f y‖) (fun _ => 1) ε x‖ₑ
            + ENNReal.ofReal (∫ _ in ball (0 : ℂ) 1, (1 : ℝ)) * ‖f x‖ₑ) :=
        setLIntegral_mono' measurableSet_ball fun x hx =>
          enorm_le_of_norm_le (le_max_right _ _) hKLε hV
            (norm_commEps_le hρ hg hdiv hf hL hK hM' hε.1 hε.2.le hx t)
    _ = _ := lintegral_bound_eq
          (measurable_enorm_aiErr hfm (continuous_psi hρ _ _) ε)
          (measurable_enorm_aiErr hfm (continuous_psi hρ _ _) ε)
          (measurable_enorm_aiErr hfm (continuous_psi hρ _ _) ε)
          (measurable_enorm_aiErr hfm (continuous_psi hρ _ _) ε)
          (measurable_enorm_aiErr hfm.norm continuous_const ε)
          ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

end SliceSmoothH

/-- Smooth fields (`03_compactness.tex:408-438`): for `g ∈ C²` with `div g = 0` and
`u(t) ∈ L¹_loc`, `C_ε[u,g](t) → 0` in `L¹(B_R)` as `ε → 0⁺`. -/
theorem tendsto_lintegral_commEps_ball_of_contDiff {ρ : ℂ → ℝ} (hρ : IsMollifier ρ)
    {g : ℂ → ℂ} (hg : ContDiff ℝ 2 g)
    (hdiv : ∀ x, (fderiv ℝ g x 1).re + (fderiv ℝ g x Complex.I).im = 0)
    {u : ℝ → ℂ → ℝ} {t : ℝ} (hu : LocallyIntegrable (u t) volume) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => ∫⁻ x in ball (0 : ℂ) R, ‖commEps ρ ε u (fun _ => g) t x‖ₑ)
      (𝓝[>] 0) (𝓝 0) := by
  -- `R > 0` is not needed for the proof
  have _ : 0 < R := hR
  have hm := hu.aestronglyMeasurable
  have hae : u t =ᵐ[volume] (fun _ : ℝ => hm.mk (u t)) t := hm.ae_eq_mk
  have hcongr : ∀ ε x, commEps ρ ε u (fun _ => g) t x =
      commEps ρ ε (fun _ => hm.mk (u t)) (fun _ => g) t x :=
    fun ε x => SliceSmoothH.commEps_congr_ae hae x
  simp_rw [hcongr]
  exact SliceSmoothH.tendsto_main hρ hg hdiv hm.stronglyMeasurable_mk (hu.congr hm.ae_eq_mk) t R

end NonUniqueEuler.Weak
