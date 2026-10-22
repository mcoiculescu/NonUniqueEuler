import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.CkNorm.Basic
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Polar.Fubini
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Proof: the running coefficient of a restarted problem (`eq:A-restart`, algebraic part)

Proof of `I/Sec5/Active/RunCoefShift.lean` (`05_single_ring.tex:1031-1036`).

Structure (as in the sketch of the interface file):
* `RunCoefShiftAux.ellFn_congr_ae`: `ℓ_*(G)` on functions only sees the a.e. class (Tonelli in
  polar coordinates; copied from `H/Sec5/Running/EllCongr.lean`, whose file cannot be imported
  here, under new names);
* `RunCoefShiftAux.exists_Y_neg_hGradPhi`: for `h ∈ C^0(N')`, `-h·∇Φ` is (a.e.) the function of
  an element of `Y^0(N) = L²(N)` (`lem:uniform` for `H^0`; the weak partials of `Φ` are its
  classical ones, which vanish off `supp Φ ⊂ N`);
* `RunCoefShiftAux.ellFn_neg_hGradPhi_sub`: linearity `ℓ_*(-f·∇Φ) - ℓ_*(-g·∇Φ) = ℓ_*(-(f-g)·∇Φ)`,
  through the bounded functional of `exists_ell` on `Y^0(N)`;
* `RunCoefShiftAux.continuousOn_ellFn_forcing`: `v ↦ ℓ_*(F(v))` is continuous on `[0,T]`
  (`lem:uniform`: `|ℓ_*(-(h(v') - h(v))·∇Φ)| ≤ C_ls‖h(v') - h(v)‖_{C^0(N')}`);
* `runCoef_shift`: split `∫₀^{t₁+u'} = ∫₀^{t₁} + ∫_{t₁}^{t₁+u'}`, shift the second integral by
  `t₁`, and pull out `e^{-λt₁}`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal ContDiff

namespace NonUniqueEuler

namespace OneRing

namespace RunCoefShiftAux

open Sect Sob RingData

/-! ### `ℓ_*(G)` on functions only sees the a.e. class -/

/-- The polar parametrisation `(r, θ) ↦ r e^{iθ}` is continuous. -/
theorem continuous_polarParam :
    Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
  fun_prop

/-- a.e. equal functions on `ℂ` have a.e. equal angular sectors on `(0, ∞)`. -/
theorem angularSector_congr_ae {g g' : ℂ → ℂ} (h : g =ᵐ[volume] g') (ℓ : ℤ) :
    Polar.angularSector g ℓ =ᵐ[volume.restrict (Ioi 0)] Polar.angularSector g' ℓ := by
  have h0 : volume {x | ¬ g x = g' x} = 0 := ae_iff.1 h
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null h0
  have hmeasN : Measurable (N.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hNm
  have hT := Polar.lintegral_eq_lintegral_Ioi_circle hmeasN
  rw [lintegral_indicator_one hNm, hN0] at hT
  have hFm : Measurable fun p : ℝ × ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 p.1 p.2) := by
    refine hmeasN.comp ?_
    have : (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) =
        fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
      funext p; simp [circleMap]
    rw [this]
    exact continuous_polarParam.measurable
  have hGm : Measurable fun r : ℝ => ENNReal.ofReal r *
      ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    ENNReal.measurable_ofReal.mul
      (hFm.lintegral_prod_right' (ν := volume.restrict (Ioc 0 (2 * Real.pi))))
  have hae := (lintegral_eq_zero_iff hGm).1 hT.symm
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with r hr hrpos
  have hrpos' : (0 : ℝ) < r := hrpos
  have hr' : ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi),
      N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 0 := by
    have hr2 : ENNReal.ofReal r *
        ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 0 :=
      hr
    rcases mul_eq_zero.1 hr2 with h1 | h1
    · exact absurd h1 (ENNReal.ofReal_pos.2 hrpos').ne'
    · exact h1
  have hθm : Measurable fun θ : ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    hFm.comp (measurable_const.prodMk measurable_id)
  have hθ := (lintegral_eq_zero_iff hθm).1 hr'
  unfold Polar.angularSector
  congr 1
  rw [intervalIntegral.integral_of_le (by positivity),
    intervalIntegral.integral_of_le (by positivity)]
  refine integral_congr_ae ?_
  filter_upwards [hθ] with θ hθ'
  have hnot : circleMap 0 r θ ∉ N := by
    intro hmem
    have : N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 1 := indicator_of_mem hmem _
    simp [this] at hθ'
  have hcm : circleMap 0 r θ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp [circleMap]
  rw [hcm] at hnot
  have heq : g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      g' ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    by_contra hne
    exact hnot (hNsub hne)
  simp only [heq]

/-- `ℓ_*(G)` on functions (`Eig.ellFn`) only depends on the a.e. class of the function. -/
theorem ellFn_congr_ae (χ : ℝ → ℝ) (G : ℝ) {f g : ℂ → ℂ} (hfg : f =ᵐ[volume] g) :
    Eig.ellFn χ G f = Eig.ellFn χ G g := by
  have hs := angularSector_congr_ae hfg 3
  unfold Eig.ellFn SectorSetting.ellStar
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [hs] with r hr
  rw [hr]

/-! ### Elements of `Y^0(N)` -/

/-- The function of a difference in `Y^s(K)`. -/
theorem Y_fn_sub {s : ℕ} {K : Set ℂ} (w w' : Y s K) :
    (w - w').fn =ᵐ[volume] fun x => w.fn x - w'.fn x := by
  have h : (((w - w' : Y s K) : SobTuple s)).ofLp (idx0 s) =
      (w : SobTuple s).ofLp (idx0 s) - (w' : SobTuple s).ofLp (idx0 s) := rfl
  have h2 : (w - w').fn = (((w - w' : Y s K) : SobTuple s).ofLp (idx0 s) : ℂ → ℂ) := rfl
  rw [h2, h]
  exact Lp.coeFn_sub _ _

/-- A function of `H^s` vanishing a.e. outside the measurable set `K` is the function of an
element of `Y^s(K)`. -/
theorem exists_Y_of_memH {s : ℕ} {K : Set ℂ} (hKm : MeasurableSet K) {f : ℂ → ℂ}
    (hf : MemH s f) (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) :
    ∃ w : Y s K, w.fn =ᵐ[volume] f := by
  set F : Hk s := toHk s f with hFdef
  have hFf : F.fn =ᵐ[volume] f := toHk_fn hf
  have hmem : (F : SobTuple s) ∈ YSub s K := by
    refine Submodule.mem_inf.2 ⟨F.2, LinearMap.mem_ker.2 ?_⟩
    rw [ContinuousLinearMap.coe_coe]
    rw [Lp.eq_zero_iff_ae_eq_zero]
    have h1 := LpToLpRestrictCLM_coeFn ℂ Kᶜ (proj0 s (F : SobTuple s))
    have h2 : ((proj0 s (F : SobTuple s) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =
        F.fn := rfl
    have h3 : F.fn =ᵐ[(volume : Measure ℂ).restrict Kᶜ] 0 := by
      have hFf' : F.fn =ᵐ[(volume : Measure ℂ).restrict Kᶜ] f := ae_restrict_of_ae hFf
      refine hFf'.trans ?_
      rw [EventuallyEq, ae_restrict_iff' hKm.compl]
      filter_upwards [hK] with x hx hxK
      exact hx hxK
    show ((LpToLpRestrictCLM ℂ ℂ ℂ (volume : Measure ℂ) 2 Kᶜ) (proj0 s (F : SobTuple s)) :
        ℂ → ℂ) =ᵐ[(volume : Measure ℂ).restrict Kᶜ] 0
    refine h1.trans ?_
    rw [h2]
    exact h3
  exact ⟨⟨(F : SobTuple s), hmem⟩, hFf⟩

/-! ### The field term `h·∇Φ` -/

/-- `h·∇Φ` is (real-)linear in the field `h`. -/
theorem hGradPhi_sub (χ : ℝ → ℝ) (f g : ℂ → ℂ) (x : ℂ) :
    Eig.hGradPhi χ (f - g) x = Eig.hGradPhi χ f x - Eig.hGradPhi χ g x := by
  simp only [Eig.hGradPhi, Sob.dotGrad, Pi.sub_apply, Complex.sub_re, Complex.sub_im]
  push_cast
  ring

/-- `h·∇Φ` vanishes a.e. outside `N`, for any field `h`: the weak partials of `Φ` are its
classical partials a.e., and those vanish off `supp Φ ⊆ {a ≤ |y| ≤ 1} ⊆ N`. -/
theorem hGradPhi_eq_zero_ae (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hf : ℂ → ℂ) :
    ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → Eig.hGradPhi χ hf x = 0 := by
  obtain ⟨hsmooth, hcpt, -, -, -, htsupp, ha, -⟩ := ringFacts_of_admissible hχ
  have hC : ContDiff ℝ ∞ (PhiC χ) := Complex.ofRealCLM.contDiff.comp hsmooth
  have hcC : HasCompactSupport (PhiC χ) := hcpt.comp_left Complex.ofReal_zero
  have hW := (memH_of_contDiff_hasCompactSupport hC hcC 1).2.1
  have h10 : (1, 0) ∈ multiIdx 1 := by decide
  have h01 : (0, 1) ∈ multiIdx 1 := by decide
  have hts : ∀ x, x ∉ annN → x ∉ tsupport (PhiC χ) := by
    intro x hxN hx
    have hx' : x ∈ tsupport (ringPhi χ) :=
      tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero (ringPhi χ) hx
    obtain ⟨h1, h2⟩ := htsupp hx'
    exact hxN ⟨by linarith, by linarith⟩
  filter_upwards [hW (1, 0) h10, hW (0, 1) h01] with x hx1 hx2 hxN
  have hd : fderiv ℝ (PhiC χ) x = 0 := fderiv_of_notMem_tsupport ℝ (hts x hxN)
  rw [← hGrad_PhiC]
  simp only [hGrad, Sob.dotGrad]
  rw [hx1, hx2]
  show _ * fderiv ℝ (PhiC χ) x 1 + _ * fderiv ℝ (PhiC χ) x Complex.I = 0
  rw [hd]
  simp

/-- For `h ∈ C^0(N')`, `-h·∇Φ` is (a.e.) the function of an element of `Y^0(N) = L²(N)`. -/
theorem exists_Y_neg_hGradPhi (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) {hf : ℂ → ℂ} (hhf : MemCk 0 annN' hf) :
    ∃ w : Y 0 annN, w.fn =ᵐ[volume] fun x => -Eig.hGradPhi χ hf x := by
  have hH : MemH 0 (Eig.hGradPhi χ hf) :=
    ((Eig.uniform_inequalities χ hχ hN).2.2 0 hf hhf).1
  have hneg : (fun x => -Eig.hGradPhi χ hf x) = (-1 : ℂ) • Eig.hGradPhi χ hf := by
    funext x; simp
  refine exists_Y_of_memH (isClosed_closedAnnulus _ _).measurableSet ?_ ?_
  · rw [hneg]; exact (hH.const_smul (-1)).1
  · filter_upwards [hGradPhi_eq_zero_ae χ hχ hf] with x hx hxN
    rw [hx hxN, neg_zero]

/-- Linearity of `ℓ_*(G)` on the field terms: for `f, g ∈ C^0(N')`,
`ℓ_*(-f·∇Φ) - ℓ_*(-g·∇Φ) = ℓ_*(-(f - g)·∇Φ)`. -/
theorem ellFn_neg_hGradPhi_sub (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {f g : ℂ → ℂ}
    (hf : MemCk 0 annN' f) (hg : MemCk 0 annN' g) :
    Eig.ellFn χ G (fun x => -Eig.hGradPhi χ f x) - Eig.ellFn χ G (fun x => -Eig.hGradPhi χ g x) =
      Eig.ellFn χ G (fun x => -Eig.hGradPhi χ (f - g) x) := by
  obtain ⟨L, hL⟩ := Eig.exists_ell χ hχ hN hG 0
  obtain ⟨wf, hwf⟩ := exists_Y_neg_hGradPhi χ hχ hN hf
  obtain ⟨wg, hwg⟩ := exists_Y_neg_hGradPhi χ hχ hN hg
  have h1 : Eig.ellFn χ G (fun x => -Eig.hGradPhi χ f x) = L wf := by
    rw [hL]; exact (ellFn_congr_ae χ G hwf).symm
  have h2 : Eig.ellFn χ G (fun x => -Eig.hGradPhi χ g x) = L wg := by
    rw [hL]; exact (ellFn_congr_ae χ G hwg).symm
  have h3 : Eig.ellFn χ G (fun x => -Eig.hGradPhi χ (f - g) x) = L (wf - wg) := by
    rw [hL]
    refine ellFn_congr_ae χ G ?_
    filter_upwards [Y_fn_sub wf wg, hwf, hwg] with x e1 e2 e3
    rw [e1, e2, e3, hGradPhi_sub]
    ring
  rw [h1, h2, h3, map_sub]

/-- `v ↦ ℓ_*(G)(F(v))`, `F(v) = -h(v)·∇Φ`, is continuous on `[0,T]` for `h` continuous on `[0,T]`
into `C^0(N')`. -/
theorem continuousOn_ellFn_forcing (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) {G T : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {h : ℝ → ℂ → ℂ}
    (hh : CkPathOn 0 annN' (Icc 0 T) h) :
    ContinuousOn (fun v => Eig.ellFn χ G (forcing χ h v)) (Icc 0 T) := by
  intro v hv
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ v' ∈ Icc (0 : ℝ) T,
      ‖Eig.ellFn χ G (forcing χ h v') - Eig.ellFn χ G (forcing χ h v)‖ ≤
        Eig.Cls χ * normCk 0 annN' (h v' - h v) := by
    intro v' hv'
    simp only [forcing_eq]
    rw [ellFn_neg_hGradPhi_sub χ hχ hN hG (hh.1 v' hv') (hh.1 v hv)]
    exact (Eig.uniform_inequalities χ hχ hN).1 G hG _ ((hh.1 v' hv').sub (hh.1 v hv)).1
  have hlim : Tendsto (fun v' => Eig.Cls χ * normCk 0 annN' (h v' - h v))
      (𝓝[Icc (0 : ℝ) T] v) (𝓝 0) := by
    simpa using (hh.2 v hv).const_mul (Eig.Cls χ)
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall hbound) hlim

end RunCoefShiftAux

open RingData

/-- **The running coefficient after a restart** (`05_single_ring.tex:1031-1036`): for
`CkPathOn 0 annN' (Icc 0 T) h`, `t₁, u' ≥ 0`, `t₁ + u' ≤ T`,
`c̃(u') = e^{λt₁}c(t₁ + u') + (ℓ_*(w₁) - e^{λt₁}c(t₁))`, where `c̃` is the running coefficient with
datum `w₁` and field `h(t₁ + ·)`, and `c` the one with datum `w₀` and field `h`. -/
theorem runCoef_shift (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G T : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {h : ℝ → ℂ → ℂ}
    (hh : CkPathOn 0 annN' (Icc 0 T) h) {t₁ u' : ℝ} (ht₁ : 0 ≤ t₁) (hu' : 0 ≤ u')
    (hT : t₁ + u' ≤ T) (w₀ w₁ : ℂ → ℂ) :
    runCoef χ G w₁ (fun τ => h (t₁ + τ)) u' =
      Complex.exp (Eig.lam χ G * t₁) * runCoef χ G w₀ h (t₁ + u') +
        (Eig.ellFn χ G w₁ - Complex.exp (Eig.lam χ G * t₁) * runCoef χ G w₀ h t₁) := by
  let g : ℝ → ℂ := fun v =>
    Complex.exp (-(Eig.lam χ G * v)) * Eig.ellFn χ G (forcing χ h v)
  have hcont : ContinuousOn g (Icc 0 T) :=
    (Continuous.continuousOn (by fun_prop)).mul
      (RunCoefShiftAux.continuousOn_ellFn_forcing χ hχ hN hG hh)
  have hI1 : IntervalIntegrable g volume 0 t₁ :=
    (hcont.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc ht₁
  have hI2 : IntervalIntegrable g volume t₁ (t₁ + u') :=
    (hcont.mono (Icc_subset_Icc ht₁ hT)).intervalIntegrable_of_Icc (by linarith)
  have hsplit : ∫ v in (0 : ℝ)..(t₁ + u'), g v =
      (∫ v in (0 : ℝ)..t₁, g v) + ∫ v in t₁..(t₁ + u'), g v :=
    (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
  have hshift : ∫ v in t₁..(t₁ + u'), g v =
      Complex.exp (-(Eig.lam χ G * t₁)) * ∫ v in (0 : ℝ)..u',
        Complex.exp (-(Eig.lam χ G * v)) *
          Eig.ellFn χ G (forcing χ (fun τ => h (t₁ + τ)) v) := by
    have h1 : ∫ v in (0 : ℝ)..u', g (t₁ + v) = ∫ v in (t₁ + 0)..(t₁ + u'), g v :=
      intervalIntegral.integral_comp_add_left g t₁
    rw [add_zero] at h1
    rw [← h1, ← intervalIntegral.integral_const_mul]
    congr 1
    funext v
    have hexp : Complex.exp (-(Eig.lam χ G * ((t₁ + v : ℝ) : ℂ))) =
        Complex.exp (-(Eig.lam χ G * t₁)) * Complex.exp (-(Eig.lam χ G * v)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    show Complex.exp (-(Eig.lam χ G * ((t₁ + v : ℝ) : ℂ))) *
        Eig.ellFn χ G (forcing χ h (t₁ + v)) = _
    rw [hexp, mul_assoc]
    rfl
  have hexp1 : Complex.exp (Eig.lam χ G * t₁) * Complex.exp (-(Eig.lam χ G * t₁)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hsplit' := hsplit
  rw [hshift] at hsplit'
  unfold runCoef
  change Eig.ellFn χ G w₁ + _ =
    Complex.exp (Eig.lam χ G * t₁) * (Eig.ellFn χ G w₀ + ∫ v in (0 : ℝ)..(t₁ + u'), g v) +
      (Eig.ellFn χ G w₁ - Complex.exp (Eig.lam χ G * t₁) *
        (Eig.ellFn χ G w₀ + ∫ v in (0 : ℝ)..t₁, g v))
  rw [hsplit']
  linear_combination (-(∫ v in (0 : ℝ)..u', Complex.exp (-(Eig.lam χ G * v)) *
    Eig.ellFn χ G (forcing χ (fun τ => h (t₁ + τ)) v))) * hexp1

end OneRing

end NonUniqueEuler
