import NonUniqueEuler.H.Sec5.Energy.FieldBounds.Local
import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Infra.Polar.RadialDeriv

/-!
# Helper for `P/Sec5/Energy/FieldBounds`: the background field `Ω(|x|;G)x^⊥` is divergence free

Step 1 of the proof of `lem:energy` (`05_single_ring.tex:333-337`):
`div(f(|x|)x^⊥) = f'(|x|) (x/|x|)·x^⊥ = 0`. Here, with `g(x) = Ω(|x|;G)` (smooth on `ℂ \ {0}`):
`div(g x^⊥) = Dg(x)(x^⊥) + g div(x^⊥) = Dg(x)(x^⊥)`, and `Dg(x)(x^⊥) = 0` because `g` is
constant along the circle `t ↦ e^{it}x`, whose velocity at `t = 0` is `ix = x^⊥`. The classical
divergence is the weak one on `N₁` (`FieldBoundsAux.weakDivOn_eq_divergence`).

* `FieldBoundsAux.omegaField_contDiffOn`: `Ω(|x|;G)x^⊥` is smooth on `ℂ \ {0}` (as in
  `P/Sec5/Lambda.lean`, from `SectorSetting.contDiffOn_Omega`, `ringPhiSetting_valid`,
  `Polar.contDiffOn_comp_norm`);
* `FieldBoundsAux.fderiv_radial_perp`: `D(f∘|·|)(x)(ix) = 0`;
* `FieldBoundsAux.weakDivOn_omegaField`: `div(Ω(|x|;G)x^⊥) = 0` a.e. on `N₁`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.OneRing.FieldBoundsAux

open RingData

theorem a_pos : 0 < a := Real.exp_pos _

theorem annN1_subset_compl_zero : annN1 ⊆ ({0} : Set ℂ)ᶜ := by
  intro x hx
  have hx' : a / 4 < ‖x‖ := hx.1
  have : 0 < ‖x‖ := lt_trans (by have := a_pos; positivity) hx'
  simpa [norm_pos_iff] using this

/-- `Ω(|x|;G)x^⊥` is smooth on `ℂ \ {0}`. -/
theorem omegaField_contDiffOn {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (G : ℝ) :
    ContDiffOn ℝ ∞ (omegaField χ G) ({0} : Set ℂ)ᶜ := by
  have hΩ : ContDiffOn ℝ ∞ (Lin.Omega χ G) (Ioi 0) :=
    SectorSetting.contDiffOn_Omega _ (ringPhiSetting_valid hχ) G
  have hr : ContDiffOn ℝ ∞ (fun x : ℂ => Lin.Omega χ G ‖x‖) ({0} : Set ℂ)ᶜ :=
    Polar.contDiffOn_comp_norm hΩ
  have hc : ContDiffOn ℝ ∞ (fun x : ℂ => ((Lin.Omega χ G ‖x‖ : ℝ) : ℂ)) ({0} : Set ℂ)ᶜ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hr
  have hI : ContDiffOn ℝ ∞ (fun x : ℂ => Complex.I * x) ({0} : Set ℂ)ᶜ :=
    (contDiff_const.mul contDiff_id).contDiffOn
  exact hc.mul hI

/-- A radial function has zero derivative along `x^⊥ = ix`. -/
theorem fderiv_radial_perp {f : ℝ → ℝ} {x : ℂ}
    (hd : DifferentiableAt ℝ (fun y : ℂ => f ‖y‖) x) :
    fderiv ℝ (fun y : ℂ => f ‖y‖) x (Complex.I * x) = 0 := by
  have hc : HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I) * x) (Complex.I * x) 0 := by
    have e : HasDerivAt (fun z : ℂ => Complex.exp (z * Complex.I) * x)
        (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) * (1 * Complex.I) * x) ((0 : ℝ) : ℂ) :=
      (((hasDerivAt_id _).mul_const Complex.I).cexp).mul_const x
    have := e.comp_ofReal
    simpa using this
  have h1 : HasDerivAt ((fun y : ℂ => f ‖y‖) ∘ fun t : ℝ => Complex.exp (t * Complex.I) * x)
      (fderiv ℝ (fun y : ℂ => f ‖y‖) x (Complex.I * x)) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (by simp)
  have h2 : ((fun y : ℂ => f ‖y‖) ∘ fun t : ℝ => Complex.exp (t * Complex.I) * x) =
      fun _ => f ‖x‖ := by
    funext t
    simp only [Function.comp, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const _ _)

/-- `div(Ω(|x|;G)x^⊥) = 0` classically on `ℂ \ {0}`. -/
theorem divergence_omegaField {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (G : ℝ) {x : ℂ}
    (hx : x ≠ 0) : Prelim.divergence (omegaField χ G) x = 0 := by
  set h : ℂ → ℝ := fun y => Lin.Omega χ G ‖y‖ with hhdef
  have hcd : ContDiffOn ℝ ∞ h ({0} : Set ℂ)ᶜ :=
    Polar.contDiffOn_comp_norm (SectorSetting.contDiffOn_Omega _ (ringPhiSetting_valid hχ) G)
  have hdiff : DifferentiableAt ℝ h x :=
    (hcd.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp)
  set h' := fderiv ℝ h x with hh'def
  have hD : HasFDerivAt h h' x := hdiff.hasFDerivAt
  have hrot : h' (Complex.I * x) = 0 := fderiv_radial_perp hdiff
  have hlin : h' (Complex.I * x) = -x.im * h' 1 + x.re * h' Complex.I := by
    have e : Complex.I * x = (-x.im : ℝ) • (1 : ℂ) + (x.re : ℝ) • Complex.I := by
      apply Complex.ext <;> simp
    rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hc : HasFDerivAt (fun y => ((h y : ℝ) : ℂ)) (Complex.ofRealCLM.comp h') x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hD
  have hI : HasFDerivAt (fun y : ℂ => Complex.I * id y)
      (Complex.I • ContinuousLinearMap.id ℝ ℂ) x :=
    (hasFDerivAt_id x).const_mul Complex.I
  have hΩ := hc.mul hI
  have hfun : omegaField χ G = (fun y => ((h y : ℝ) : ℂ)) * fun y : ℂ => Complex.I * id y := rfl
  rw [Prelim.divergence_eq, hfun, hΩ.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    smul_eq_mul, id, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
    Complex.one_im]
  linarith

/-- `div(Ω(|x|;G)x^⊥) = 0` weakly, a.e. on `N₁`. -/
theorem weakDivOn_omegaField {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (G : ℝ) :
    ∀ᵐ x ∂(volume.restrict annN1), Sob.weakDivOn annN1 (omegaField χ G) x = 0 := by
  have hc : ContDiffOn ℝ 1 (omegaField χ G) annN1 :=
    ((omegaField_contDiffOn hχ G).mono annN1_subset_compl_zero).of_le
      (by exact_mod_cast le_top)
  filter_upwards [Sob.FieldBoundsAux.weakDivOn_eq_divergence isOpen_annN1 hc,
    ae_restrict_mem isOpen_annN1.measurableSet] with x hx hxV
  rw [hx]
  exact divergence_omegaField hχ G (annN1_subset_compl_zero hxV)

end NonUniqueEuler.OneRing.FieldBoundsAux
