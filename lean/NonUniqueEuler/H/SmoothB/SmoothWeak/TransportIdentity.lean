import NonUniqueEuler.Statement.WeakSolution
import NonUniqueEuler.Defs.Sec2.Conventions
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Helper for `P/SmoothB/SmoothWeak`: the transport identity for `C¹` solutions

Proof of thm:smooth (7), `B_global_smooth.tex:547-557`: if `u ∈ C¹(ℝ × ℝ²)` solves
`∂_t u + w·∇u = 0` with `w ∈ C¹(ℝ × ℝ²)`, `div w = 0`, then for every `φ ∈ 𝒟_T`
`∫₀ᵀ∫ u (∂_tφ + w·∇φ) dx dt + ∫ u(0) φ(0) dx = 0` (`transport_identity`).

* `integral_mul_fderiv_field`: integration by parts in `x` with a divergence-free field,
  `∫ f (W·∇g) = -∫ (W·∇f) g` for `f, g ∈ C¹`, `g` compactly supported, `W ∈ C¹`, `div W = 0`
  (componentwise `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` in the directions `1`, `i`).
* `transport_identity`: with `g = ∂_t(uφ)`: for each `t`, `∫ u(∂_tφ + w·∇φ) dx = ∫ g(t) dx`
  (transport equation and the spatial integration by parts); for each `x`,
  `∫₀ᵀ g(t,x) dt = -u(0,x)φ(0,x)` (fundamental theorem of calculus, `φ(T,·) = 0`); Fubini on the
  slab (`g` is continuous with compact support).

Only the support of `φ` is used; no support condition on `u` is needed.
-/

noncomputable section

open MeasureTheory Set Filter

namespace NonUniqueEuler.Smooth.SmoothWeakH

/-! ### Generic facts -/

/-- A continuous function on the plane vanishing outside a compact set is integrable. -/
theorem integrable_of_vanish {b : ℂ → ℝ} (hb : Continuous b) {K : Set ℂ} (hK : IsCompact K)
    (h : ∀ x ∉ K, b x = 0) : Integrable b :=
  hb.integrable_of_hasCompactSupport (HasCompactSupport.intro hK h)

/-- If `ψ` vanishes outside the closed set `K`, its derivative vanishes outside `K`. -/
theorem fderiv_eq_zero_of_vanish {ψ : ℂ → ℝ} {K : Set ℂ} (hK : IsClosed K)
    (h : ∀ x ∉ K, ψ x = 0) {x : ℂ} (hx : x ∉ K) : fderiv ℝ ψ x = 0 := by
  have hts : tsupport ψ ⊆ K := closure_minimal (fun y hy => by
    by_contra hyK
    exact hy (h y hyK)) hK
  exact image_eq_zero_of_notMem_tsupport fun h' => hx (hts (tsupport_fderiv_subset ℝ h'))

/-- `L z = Re z · L 1 + Im z · L i` for a real-linear functional on `ℂ`. -/
theorem clm_apply_eq_re_im (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z = z.re * L 1 + z.im * L Complex.I := by
  have hz : z = (z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I := by
    simp
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem hasDerivAt_time {U : ℝ × ℂ → ℝ} (hU : Differentiable ℝ U) (t : ℝ) (x : ℂ) :
    HasDerivAt (fun s => U (s, x)) (fderiv ℝ U (t, x) ((1 : ℝ), (0 : ℂ))) t := by
  have h : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℂ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact (hU (t, x)).hasFDerivAt.comp_hasDerivAt t h

theorem contDiff_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : ℝ × ℂ → E} (hU : ContDiff ℝ 1 U) (t : ℝ) : ContDiff ℝ 1 (fun y : ℂ => U (t, y)) :=
  hU.comp (contDiff_const.prodMk contDiff_id)

/-! ### Integration by parts in `x` with a divergence-free field -/

/-- `∫ f (W·∇g) = -∫ (W·∇f) g` for `f, g ∈ C¹(ℝ²)`, `g` compactly supported, `W ∈ C¹(ℝ²; ℝ²)`
with `div W = 0` (`B_global_smooth.tex:553-555`). -/
theorem integral_mul_fderiv_field {f g : ℂ → ℝ} {W : ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (hW : ContDiff ℝ 1 W)
    (hdiv : ∀ x, Prelim.divergence W x = 0) :
    ∫ x, f x * fderiv ℝ g x (W x) = -∫ x, fderiv ℝ f x (W x) * g x := by
  set K := tsupport g with hK_def
  have hKc : IsCompact K := hgc
  have hKcl : IsClosed K := isClosed_tsupport g
  have hg0 : ∀ x ∉ K, g x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hdg0 : ∀ x ∉ K, fderiv ℝ g x = 0 := fun x hx => fderiv_eq_zero_of_vanish hKcl hg0 hx
  set W₁ : ℂ → ℝ := fun x => (W x).re with hW₁_def
  set W₂ : ℂ → ℝ := fun x => (W x).im with hW₂_def
  have hW₁ : ContDiff ℝ 1 W₁ := Complex.reCLM.contDiff.comp hW
  have hW₂ : ContDiff ℝ 1 W₂ := Complex.imCLM.contDiff.comp hW
  have hWd : Differentiable ℝ W := hW.differentiable one_ne_zero
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hdW₁ : ∀ x, fderiv ℝ W₁ x 1 = (fderiv ℝ W x 1).re := fun x => by
    have h : HasFDerivAt W₁ (Complex.reCLM.comp (fderiv ℝ W x)) x :=
      (Complex.reCLM.hasFDerivAt).comp x (hWd x).hasFDerivAt
    rw [h.fderiv]
    simp
  have hdW₂ : ∀ x, fderiv ℝ W₂ x Complex.I = (fderiv ℝ W x Complex.I).im := fun x => by
    have h : HasFDerivAt W₂ (Complex.imCLM.comp (fderiv ℝ W x)) x :=
      (Complex.imCLM.hasFDerivAt).comp x (hWd x).hasFDerivAt
    rw [h.fderiv]
    simp
  set h₁ : ℂ → ℝ := fun x => f x * W₁ x with hh₁_def
  set h₂ : ℂ → ℝ := fun x => f x * W₂ x with hh₂_def
  have hh₁ : ContDiff ℝ 1 h₁ := hf.mul hW₁
  have hh₂ : ContDiff ℝ 1 h₂ := hf.mul hW₂
  have hdh₁ : ∀ x, fderiv ℝ h₁ x 1 = f x * fderiv ℝ W₁ x 1 + W₁ x * fderiv ℝ f x 1 := fun x => by
    have h : HasFDerivAt h₁ (f x • fderiv ℝ W₁ x + W₁ x • fderiv ℝ f x) x :=
      (hfd x).hasFDerivAt.mul ((hW₁.differentiable one_ne_zero) x).hasFDerivAt
    rw [h.fderiv]
    simp [smul_eq_mul]
  have hdh₂ : ∀ x, fderiv ℝ h₂ x Complex.I =
      f x * fderiv ℝ W₂ x Complex.I + W₂ x * fderiv ℝ f x Complex.I := fun x => by
    have h : HasFDerivAt h₂ (f x • fderiv ℝ W₂ x + W₂ x • fderiv ℝ f x) x :=
      (hfd x).hasFDerivAt.mul ((hW₂.differentiable one_ne_zero) x).hasFDerivAt
    rw [h.fderiv]
    simp [smul_eq_mul]
  -- continuity facts
  have cdg : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have cdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have cdh₁ : Continuous (fderiv ℝ h₁) := hh₁.continuous_fderiv one_ne_zero
  have cdh₂ : Continuous (fderiv ℝ h₂) := hh₂.continuous_fderiv one_ne_zero
  -- integrability: everything vanishes outside `K`
  have i₁ : Integrable (fun x => h₁ x * fderiv ℝ g x 1) :=
    integrable_of_vanish (hh₁.continuous.mul (cdg.clm_apply continuous_const)) hKc
      fun x hx => by simp [hdg0 x hx]
  have i₂ : Integrable (fun x => h₂ x * fderiv ℝ g x Complex.I) :=
    integrable_of_vanish (hh₂.continuous.mul (cdg.clm_apply continuous_const)) hKc
      fun x hx => by simp [hdg0 x hx]
  have j₁ : Integrable (fun x => fderiv ℝ h₁ x 1 * g x) :=
    integrable_of_vanish ((cdh₁.clm_apply continuous_const).mul hg.continuous) hKc
      fun x hx => by simp [hg0 x hx]
  have j₂ : Integrable (fun x => fderiv ℝ h₂ x Complex.I * g x) :=
    integrable_of_vanish ((cdh₂.clm_apply continuous_const).mul hg.continuous) hKc
      fun x hx => by simp [hg0 x hx]
  have k₁ : Integrable (fun x => h₁ x * g x) :=
    integrable_of_vanish (hh₁.continuous.mul hg.continuous) hKc fun x hx => by simp [hg0 x hx]
  have k₂ : Integrable (fun x => h₂ x * g x) :=
    integrable_of_vanish (hh₂.continuous.mul hg.continuous) hKc fun x hx => by simp [hg0 x hx]
  -- the two one-directional integrations by parts
  have ibp₁ : ∫ x, h₁ x * fderiv ℝ g x 1 = -∫ x, fderiv ℝ h₁ x 1 * g x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable j₁ i₁ k₁
      (fun x _ => (hh₁.differentiable one_ne_zero) x) (fun x _ => hgd x)
  have ibp₂ : ∫ x, h₂ x * fderiv ℝ g x Complex.I = -∫ x, fderiv ℝ h₂ x Complex.I * g x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable j₂ i₂ k₂
      (fun x _ => (hh₂.differentiable one_ne_zero) x) (fun x _ => hgd x)
  -- pointwise identities
  have e₁ : (fun x => f x * fderiv ℝ g x (W x)) =
      fun x => h₁ x * fderiv ℝ g x 1 + h₂ x * fderiv ℝ g x Complex.I := by
    funext x
    rw [clm_apply_eq_re_im (fderiv ℝ g x) (W x)]
    simp only [hh₁_def, hh₂_def, hW₁_def, hW₂_def]
    ring
  have e₂ : (fun x => fderiv ℝ f x (W x) * g x) =
      fun x => fderiv ℝ h₁ x 1 * g x + fderiv ℝ h₂ x Complex.I * g x := by
    funext x
    have hd := hdiv x
    rw [Prelim.divergence_eq] at hd
    rw [hdh₁, hdh₂, hdW₁, hdW₂, clm_apply_eq_re_im (fderiv ℝ f x) (W x)]
    simp only [hW₁_def, hW₂_def]
    have : f x * (fderiv ℝ W x 1).re + f x * (fderiv ℝ W x Complex.I).im = 0 := by
      rw [← mul_add, hd, mul_zero]
    linear_combination (-(g x)) * this
  rw [e₁, e₂, integral_add i₁ i₂, integral_add j₁ j₂, ibp₁, ibp₂]
  ring

/-! ### The transport identity -/

/-- **The weak transport identity for `C¹` solutions** (`B_global_smooth.tex:547-557`): if
`u ∈ C¹(ℝ × ℝ²)` solves `∂_t u + w·∇u = 0` with `w ∈ C¹(ℝ × ℝ²)`, `div w = 0`, then for every
`φ ∈ 𝒟_T`, `∫₀ᵀ∫ u (∂_tφ + w·∇φ) dx dt + ∫ u(0) φ(0) dx = 0`. -/
theorem transport_identity {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {T : ℝ} {φ : ℝ × ℂ → ℝ}
    (hu : ContDiff ℝ 1 (Function.uncurry u)) (hw : ContDiff ℝ 1 (Function.uncurry w))
    (hdiv : ∀ t x, Prelim.divergence (w t) x = 0)
    (htr : ∀ t x, deriv (fun s => u s x) t + fderiv ℝ (u t) x (w t x) = 0)
    (hT : 0 < T) (hφ : IsTestFunction T φ) :
    (∫ t in Ioo (0 : ℝ) T, ∫ x : ℂ, transportIntegrand u w φ (t, x)) +
      ∫ x : ℂ, u 0 x * φ (0, x) = 0 := by
  set U : ℝ × ℂ → ℝ := Function.uncurry u with hU_def
  have hUd : Differentiable ℝ U := hu.differentiable one_ne_zero
  have hφ1 : ContDiff ℝ 1 φ := hφ.contDiff.of_le (by exact_mod_cast le_top)
  have hφd : Differentiable ℝ φ := hφ1.differentiable one_ne_zero
  have cdU : Continuous (fderiv ℝ U) := hu.continuous_fderiv one_ne_zero
  have cdφ : Continuous (fderiv ℝ φ) := hφ1.continuous_fderiv one_ne_zero
  have hKφ : IsCompact (tsupport φ) := hφ.hasCompactSupport
  have hφ0 : ∀ p ∉ tsupport φ, φ p = 0 := fun p hp => image_eq_zero_of_notMem_tsupport hp
  have hdφ0 : ∀ p ∉ tsupport φ, fderiv ℝ φ p = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport fun h' => hp (tsupport_fderiv_subset ℝ h')
  -- `g = ∂_t (u φ)`
  set g : ℝ × ℂ → ℝ := fun p =>
    fderiv ℝ U p ((1 : ℝ), (0 : ℂ)) * φ p + U p * fderiv ℝ φ p ((1 : ℝ), (0 : ℂ)) with hg_def
  have hg_cont : Continuous g :=
    ((cdU.clm_apply continuous_const).mul hφ.contDiff.continuous).add
      (hu.continuous.mul (cdφ.clm_apply continuous_const))
  have hg_int : Integrable g (volume : Measure (ℝ × ℂ)) :=
    hg_cont.integrable_of_hasCompactSupport (HasCompactSupport.intro hKφ fun p hp => by
      simp [hg_def, hφ0 p hp, hdφ0 p hp])
  -- partial derivatives through the joint derivative
  have e_ut : ∀ t x, deriv (fun s => u s x) t = fderiv ℝ U (t, x) ((1 : ℝ), (0 : ℂ)) :=
    fun t x => (hasDerivAt_time hUd t x).deriv
  have e_φt : ∀ t x, timeDeriv φ t x = fderiv ℝ φ (t, x) ((1 : ℝ), (0 : ℂ)) :=
    fun t x => (hasDerivAt_time hφd t x).deriv
  -- step 1: the spatial identity at each time
  have hspace : ∀ t, ∫ x, transportIntegrand u w φ (t, x) = ∫ x, g (t, x) := by
    intro t
    set K : Set ℂ := Prod.snd '' tsupport φ with hK_def
    have hK : IsCompact K := hKφ.image continuous_snd
    have hKcl : IsClosed K := hK.isClosed
    have hnot : ∀ x ∉ K, (t, x) ∉ tsupport φ := fun x hx h' => hx ⟨(t, x), h', rfl⟩
    have hut : ContDiff ℝ 1 (u t) := contDiff_slice hu t
    have hφt : ContDiff ℝ 1 (fun y => φ (t, y)) := contDiff_slice hφ1 t
    have hwt : ContDiff ℝ 1 (w t) := contDiff_slice hw t
    have hφt0 : ∀ x ∉ K, φ (t, x) = 0 := fun x hx => hφ0 _ (hnot x hx)
    have hφtc : HasCompactSupport (fun y => φ (t, y)) := HasCompactSupport.intro hK hφt0
    have hdφt0 : ∀ x ∉ K, fderiv ℝ (fun y => φ (t, y)) x = 0 := fun x hx =>
      fderiv_eq_zero_of_vanish hKcl hφt0 hx
    have hτ0 : ∀ x ∉ K, timeDeriv φ t x = 0 := fun x hx => by
      rw [e_φt, hdφ0 _ (hnot x hx)]
      rfl
    have cτ : Continuous (fun x => timeDeriv φ t x) := by
      simp_rw [e_φt]
      exact (cdφ.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const
    have I₁ : Integrable (fun x => u t x * timeDeriv φ t x) :=
      integrable_of_vanish (hut.continuous.mul cτ) hK fun x hx => by simp [hτ0 x hx]
    have I₂ : Integrable (fun x => u t x * fderiv ℝ (fun y => φ (t, y)) x (w t x)) :=
      integrable_of_vanish (hut.continuous.mul
        ((hφt.continuous_fderiv one_ne_zero).clm_apply hwt.continuous)) hK
        fun x hx => by simp [hdφt0 x hx]
    have I₃ : Integrable (fun x => fderiv ℝ (u t) x (w t x) * φ (t, x)) :=
      integrable_of_vanish (((hut.continuous_fderiv one_ne_zero).clm_apply hwt.continuous).mul
        hφt.continuous) hK fun x hx => by simp [hφt0 x hx]
    have hibp := integral_mul_fderiv_field hut hφt hφtc hwt (hdiv t)
    have eL : (fun x => transportIntegrand u w φ (t, x)) =
        fun x => u t x * timeDeriv φ t x + u t x * fderiv ℝ (fun y => φ (t, y)) x (w t x) := by
      funext x
      simp only [transportIntegrand, spaceDeriv]
      ring
    have eR : (fun x => g (t, x)) =
        fun x => -(fderiv ℝ (u t) x (w t x) * φ (t, x)) + u t x * timeDeriv φ t x := by
      funext x
      have h1 := htr t x
      rw [e_ut] at h1
      simp only [hg_def, e_φt]
      have h2 : fderiv ℝ U (t, x) ((1 : ℝ), (0 : ℂ)) = -fderiv ℝ (u t) x (w t x) := by
        linarith
      rw [h2]
      simp only [hU_def, Function.uncurry_apply_pair]
      ring
    have I₃' : Integrable (fun x => -(fderiv ℝ (u t) x (w t x) * φ (t, x))) := I₃.neg
    rw [eL, eR, integral_add I₁ I₂, integral_add I₃' I₁, integral_neg, hibp]
    ring
  -- step 2: the time integral at each point
  have htime : ∀ x, ∫ t in Ioo (0 : ℝ) T, g (t, x) = -(u 0 x * φ (0, x)) := by
    intro x
    have hTx : φ (T, x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact lt_irrefl _ (hφ.support_lt _ h)
    have hcont : Continuous (fun t => g (t, x)) :=
      hg_cont.comp (continuous_id.prodMk continuous_const)
    have hder : ∀ s ∈ uIcc 0 T, HasDerivAt (fun r => U (r, x) * φ (r, x)) (g (s, x)) s :=
      fun s _ => (hasDerivAt_time hUd s x).mul (hasDerivAt_time hφd s x)
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT.le,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.intervalIntegrable _ _), hTx]
    simp [hU_def]
  -- step 3: Fubini on the slab
  have hprod : (volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure ℂ) =
      (volume : Measure (ℝ × ℂ)).restrict (Ioo (0 : ℝ) T ×ˢ univ) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure ℂ)), Measure.prod_restrict]
    rfl
  have hint : Integrable (Function.uncurry fun t x => g (t, x))
      ((volume.restrict (Ioo (0 : ℝ) T)).prod volume) := by
    rw [hprod]
    exact hg_int.restrict
  have hswap := integral_integral_swap hint
  calc (∫ t in Ioo (0 : ℝ) T, ∫ x : ℂ, transportIntegrand u w φ (t, x)) +
        ∫ x : ℂ, u 0 x * φ (0, x)
      = (∫ t in Ioo (0 : ℝ) T, ∫ x : ℂ, g (t, x)) + ∫ x : ℂ, u 0 x * φ (0, x) := by
        simp_rw [hspace]
    _ = (∫ x : ℂ, ∫ t in Ioo (0 : ℝ) T, g (t, x)) + ∫ x : ℂ, u 0 x * φ (0, x) := by
        rw [hswap]
    _ = 0 := by
        simp_rw [htime]
        rw [integral_neg]
        ring

end NonUniqueEuler.Smooth.SmoothWeakH
