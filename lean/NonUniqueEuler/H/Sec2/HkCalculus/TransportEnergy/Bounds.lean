import Mathlib.MeasureTheory.Integral.Bochner.Basic
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `P/Sec2/HkCalculus/TransportEnergy`: Hölder-type bounds

`L^∞ × L² × L²` bounds for the integrals in the density argument of
`lem:Hk-calculus`(1), second claim (`02_prelim.tex:735-745`):
* `ae_norm_le_toReal_eLpNorm_top`: `|U(x)| ≤ ‖U‖_{L^∞}` a.e.;
* `integral_norm_mul_norm_le_l2`: `∫ |f| |h| ≤ ‖f‖₂ ‖h‖₂` (Cauchy–Schwarz);
* `norm_integral_le_of_ae_le`: if `|F| ≤ M |f| |h|` a.e. with `f, h ∈ L²`, then `F` is integrable
  and `|∫ F| ≤ M ‖f‖₂ ‖h‖₂`;
* `dotGrad_mul_conj_bound`: `|∫ (U·∇f) h̄| ≤ M (‖∂₁f‖₂ + ‖∂₂f‖₂) ‖h‖₂` for `|U| ≤ M` a.e.

All fully proved.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

namespace NonUniqueEuler.Sob.TransportEnergyAux

/-- `‖f x‖ ≤ ‖f‖_{L^∞}` almost everywhere. -/
theorem ae_norm_le_toReal_eLpNorm_top {f : ℂ → ℂ} (hf : MemLp f ⊤ volume) :
    ∀ᵐ x, ‖f x‖ ≤ (eLpNorm f ⊤ volume).toReal := by
  have h := ae_le_eLpNormEssSup (μ := (volume : Measure ℂ)) (f := f)
  filter_upwards [h] with x hx
  have hlt : eLpNormEssSup f volume ≠ ⊤ := by
    have := hf.2
    rw [eLpNorm_exponent_top] at this
    exact this.ne
  have := ENNReal.toReal_mono hlt hx
  rw [eLpNorm_exponent_top]
  simpa using this

/-- `‖f‖_{L²}` as the square root of `∫ |f|²`. -/
theorem l2_eq_integral_rpow {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    l2 f = (∫ x, ‖f x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  rw [l2, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  norm_num

/-- Cauchy–Schwarz: `∫ |f| |h| ≤ ‖f‖₂ ‖h‖₂`. -/
theorem integral_norm_mul_norm_le_l2 {f h : ℂ → ℂ} (hf : MemLp f 2 volume)
    (hh : MemLp h 2 volume) : ∫ x, ‖f x‖ * ‖h x‖ ≤ l2 f * l2 h := by
  have h1 := integral_mul_norm_le_Lp_mul_Lq (μ := (volume : Measure ℂ)) Real.HolderConjugate.two_two
    (f := f) (g := h) (by simpa using hf) (by simpa using hh)
  rw [l2_eq_integral_rpow hf, l2_eq_integral_rpow hh]
  exact h1

/-- Integrability of `|f| |h|` for `f, h ∈ L²`. -/
theorem integrable_norm_mul_norm {f h : ℂ → ℂ} (hf : MemLp f 2 volume)
    (hh : MemLp h 2 volume) : Integrable (fun x => ‖f x‖ * ‖h x‖) volume := by
  have : Integrable ((fun x => ‖f x‖) * fun x => ‖h x‖) volume :=
    MemLp.integrable_mul (p := 2) (q := 2) hf.norm hh.norm
  exact this

/-- If `|F| ≤ M |f| |h|` a.e. with `f, h ∈ L²` and `M ≥ 0`, then `F` is integrable and
`|∫ F| ≤ M ‖f‖₂ ‖h‖₂`. -/
theorem norm_integral_le_of_ae_le {F f h : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hF : AEStronglyMeasurable F volume) (hf : MemLp f 2 volume) (hh : MemLp h 2 volume)
    (hb : ∀ᵐ x, ‖F x‖ ≤ M * (‖f x‖ * ‖h x‖)) :
    Integrable F volume ∧ ‖∫ x, F x‖ ≤ M * (l2 f * l2 h) := by
  have hi : Integrable (fun x => M * (‖f x‖ * ‖h x‖)) volume :=
    (integrable_norm_mul_norm hf hh).const_mul M
  refine ⟨hi.mono' hF hb, ?_⟩
  calc ‖∫ x, F x‖ ≤ ∫ x, M * (‖f x‖ * ‖h x‖) := norm_integral_le_of_norm_le hi hb
    _ = M * ∫ x, ‖f x‖ * ‖h x‖ := integral_const_mul M _
    _ ≤ M * (l2 f * l2 h) := mul_le_mul_of_nonneg_left (integral_norm_mul_norm_le_l2 hf hh) hM

/-- `|∫ (U·∇f) h̄| ≤ M (‖∂₁f‖₂ + ‖∂₂f‖₂) ‖h‖₂` for `|U| ≤ M` a.e., with integrability. -/
theorem dotGrad_mul_conj_bound {U f h : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hU : AEStronglyMeasurable U volume) (hUb : ∀ᵐ x, ‖U x‖ ≤ M)
    (h1 : MemLp (weakPartial (1, 0) f) 2 volume) (h2 : MemLp (weakPartial (0, 1) f) 2 volume)
    (hh : MemLp h 2 volume) :
    Integrable (fun x => dotGrad U f x * conj (h x)) volume ∧
      ‖∫ x, dotGrad U f x * conj (h x)‖ ≤
        M * (l2 (weakPartial (1, 0) f) + l2 (weakPartial (0, 1) f)) * l2 h := by
  have hre : AEStronglyMeasurable (fun x => ((U x).re : ℂ)) volume :=
    (Complex.continuous_ofReal.comp Complex.continuous_re).comp_aestronglyMeasurable hU
  have him : AEStronglyMeasurable (fun x => ((U x).im : ℂ)) volume :=
    (Complex.continuous_ofReal.comp Complex.continuous_im).comp_aestronglyMeasurable hU
  have hc : AEStronglyMeasurable (fun x => conj (h x)) volume :=
    Complex.continuous_conj.comp_aestronglyMeasurable hh.1
  obtain ⟨hA, hAb⟩ := norm_integral_le_of_ae_le (F := fun x =>
      ((U x).re : ℂ) * weakPartial (1, 0) f x * conj (h x)) hM ((hre.mul h1.1).mul hc) h1 hh
    (by
      filter_upwards [hUb] with x hx
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      have := (Complex.abs_re_le_norm (U x)).trans hx
      have h0 : 0 ≤ ‖weakPartial (1, 0) f x‖ * ‖h x‖ := by positivity
      nlinarith [norm_nonneg (weakPartial (1, 0) f x), norm_nonneg (h x)])
  obtain ⟨hB, hBb⟩ := norm_integral_le_of_ae_le (F := fun x =>
      ((U x).im : ℂ) * weakPartial (0, 1) f x * conj (h x)) hM ((him.mul h2.1).mul hc) h2 hh
    (by
      filter_upwards [hUb] with x hx
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      have := (Complex.abs_im_le_norm (U x)).trans hx
      have h0 : 0 ≤ ‖weakPartial (0, 1) f x‖ * ‖h x‖ := by positivity
      nlinarith [norm_nonneg (weakPartial (0, 1) f x), norm_nonneg (h x)])
  have heq : (fun x => dotGrad U f x * conj (h x)) = fun x =>
      ((U x).re : ℂ) * weakPartial (1, 0) f x * conj (h x) +
        ((U x).im : ℂ) * weakPartial (0, 1) f x * conj (h x) := by
    funext x
    simp only [dotGrad]
    ring
  rw [heq]
  refine ⟨hA.add hB, ?_⟩
  rw [integral_add hA hB]
  calc _ ≤ ‖∫ x, ((U x).re : ℂ) * weakPartial (1, 0) f x * conj (h x)‖ +
        ‖∫ x, ((U x).im : ℂ) * weakPartial (0, 1) f x * conj (h x)‖ := norm_add_le _ _
    _ ≤ M * (l2 (weakPartial (1, 0) f) * l2 h) + M * (l2 (weakPartial (0, 1) f) * l2 h) :=
        add_le_add hAb hBb
    _ = _ := by ring

end NonUniqueEuler.Sob.TransportEnergyAux
