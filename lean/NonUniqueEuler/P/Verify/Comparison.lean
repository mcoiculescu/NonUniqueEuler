import NonUniqueEuler.Defs.Verify.Profile
import NonUniqueEuler.I.Verify.IntGronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Proof: the comparison estimate (variation of constants + integral Grönwall)

Proof of `NonUniqueEuler/I/Verify/Comparison.lean` (manuscript: proof of Lemma A.1(2),
`A_verification.tex:172-190`, reused in Lemma A.2).

* The `cmpSol` lemmas: derivatives of `cosh`/`sinh` (`HasDerivAt.cosh`, `HasDerivAt.sinh`,
  `HasDerivAt.ofReal_comp`) and `cosh + sinh = exp` (`Real.cosh_add_sinh`).
* `comparison_estimate` (restructuring T2): with `D₁ = ψ - ψ₀`, `D₂ = ψ' - ψ₀'`
  the scalar combinations `e_± = D₂ ± ℓD₁` satisfy `e_±' = ±ℓ e_± + δψ`, `e_±(α) = 0`, so
  `e_±(ξ) = ∫_α^ξ e^{±ℓ(ξ-t)} δψ dt` (FTC for `x ↦ e^{∓ℓ(ξ-x)} e_±(x)`, lemma
  `eq_integral_of_hasDeriv`), whence `|Y - Y₀|_w(ξ) ≤ ∫_α^ξ e^{ℓ(ξ-t)} |δψ| dt`
  (`wnorm_le_integral`). With `|ψ| ≤ (e^{ℓ(t-α)} c + |Y - Y₀|_w)/ℓ` this is
  `u ≤ ∫_α^ξ b (c + u)` for `u = e^{-ℓ(ξ-α)} |Y - Y₀|_w`, `b = |δ|/ℓ`, and `int_gronwall`
  (`I/Verify/IntGronwall.lean`) concludes.
-/

noncomputable section

open Set

namespace NonUniqueEuler

namespace AppA

private lemma hasDerivAt_lin (ℓ α ξ : ℝ) : HasDerivAt (fun x : ℝ => ℓ * (x - α)) ℓ ξ := by
  simpa using ((hasDerivAt_id ξ).sub_const α).const_mul ℓ

private lemma hasDerivAt_ccosh (ℓ α ξ : ℝ) :
    HasDerivAt (fun x : ℝ => ((Real.cosh (ℓ * (x - α)) : ℝ) : ℂ))
      (((Real.sinh (ℓ * (ξ - α)) * ℓ : ℝ) : ℂ)) ξ :=
  (hasDerivAt_lin ℓ α ξ).cosh.ofReal_comp

private lemma hasDerivAt_csinh (ℓ α ξ : ℝ) :
    HasDerivAt (fun x : ℝ => ((Real.sinh (ℓ * (x - α)) : ℝ) : ℂ))
      (((Real.cosh (ℓ * (ξ - α)) * ℓ : ℝ) : ℂ)) ξ :=
  (hasDerivAt_lin ℓ α ξ).sinh.ofReal_comp

theorem hasDerivAt_cmpSol {ℓ : ℝ} (hℓ : ℓ ≠ 0) (α : ℝ) (u v : ℂ) (ξ : ℝ) :
    HasDerivAt (cmpSol ℓ α u v) (cmpSol' ℓ α u v ξ) ξ := by
  have hℓc : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ
  have h := ((hasDerivAt_ccosh ℓ α ξ).const_mul u).add
    ((hasDerivAt_csinh ℓ α ξ).const_mul (v / (ℓ : ℂ)))
  refine h.congr_deriv ?_
  simp only [cmpSol', Complex.ofReal_mul]
  field_simp

theorem hasDerivAt_cmpSol' {ℓ : ℝ} (hℓ : ℓ ≠ 0) (α : ℝ) (u v : ℂ) (ξ : ℝ) :
    HasDerivAt (cmpSol' ℓ α u v) ((ℓ : ℂ) ^ 2 * cmpSol ℓ α u v ξ) ξ := by
  have hℓc : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ
  have h := ((hasDerivAt_csinh ℓ α ξ).const_mul (u * (ℓ : ℂ))).add
    ((hasDerivAt_ccosh ℓ α ξ).const_mul v)
  refine h.congr_deriv ?_
  simp only [cmpSol, Complex.ofReal_mul]
  field_simp

/-- `|Y₀(ξ)|_w ≤ e^{ℓ(ξ-α)} |Y₀(α)|_w` for `ξ ≥ α`. -/
theorem wnorm_cmpSol_le {ℓ : ℝ} (hℓ : 0 < ℓ) {α ξ : ℝ} (hξ : α ≤ ξ) (u v : ℂ) :
    wnorm ℓ (cmpSol ℓ α u v ξ) (cmpSol' ℓ α u v ξ) ≤ Real.exp (ℓ * (ξ - α)) * wnorm ℓ u v := by
  set x := ℓ * (ξ - α) with hx
  have hx0 : 0 ≤ x := mul_nonneg hℓ.le (sub_nonneg.mpr hξ)
  have hs : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx0
  have hc : 0 ≤ Real.cosh x := (Real.cosh_pos x).le
  have hexp : Real.exp x = Real.cosh x + Real.sinh x := (Real.cosh_add_sinh x).symm
  set c := wnorm ℓ u v
  have hu : ℓ * ‖u‖ ≤ c := le_max_left _ _
  have hv : ‖v‖ ≤ c := le_max_right _ _
  have hℓc : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ.ne'
  have hnℓ : ‖(ℓ : ℂ)‖ = ℓ := by simp [abs_of_pos hℓ]
  apply max_le
  · -- `ℓ|u cosh + (v/ℓ) sinh| ≤ ℓ|u| cosh + |v| sinh`
    have h1 : ‖cmpSol ℓ α u v ξ‖ ≤ ‖u‖ * Real.cosh x + ‖v‖ / ℓ * Real.sinh x := by
      unfold cmpSol
      rw [← hx]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_div, hnℓ, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hc, Real.norm_of_nonneg hs]
    calc ℓ * ‖cmpSol ℓ α u v ξ‖ ≤ ℓ * (‖u‖ * Real.cosh x + ‖v‖ / ℓ * Real.sinh x) :=
          mul_le_mul_of_nonneg_left h1 hℓ.le
      _ = (ℓ * ‖u‖) * Real.cosh x + ‖v‖ * Real.sinh x := by field_simp
      _ ≤ c * Real.cosh x + c * Real.sinh x := by gcongr
      _ = Real.exp x * c := by rw [hexp]; ring
  · have h1 : ‖cmpSol' ℓ α u v ξ‖ ≤ (ℓ * ‖u‖) * Real.sinh x + ‖v‖ * Real.cosh x := by
      unfold cmpSol'
      rw [← hx]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, hnℓ, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hc, Real.norm_of_nonneg hs]
      ring_nf
      exact le_rfl
    calc ‖cmpSol' ℓ α u v ξ‖ ≤ (ℓ * ‖u‖) * Real.sinh x + ‖v‖ * Real.cosh x := h1
      _ ≤ c * Real.sinh x + c * Real.cosh x := by gcongr
      _ = Real.exp x * c := by rw [hexp]; ring

/-- `(ψ₀' + ℓψ₀)(ξ) = e^{ℓ(ξ-α)} (ψ₀'(α) + ℓψ₀(α))`. -/
theorem cmpSol'_add_mul_cmpSol {ℓ : ℝ} (hℓ : ℓ ≠ 0) (α : ℝ) (u v : ℂ) (ξ : ℝ) :
    cmpSol' ℓ α u v ξ + (ℓ : ℂ) * cmpSol ℓ α u v ξ =
      ((Real.exp (ℓ * (ξ - α)) : ℝ) : ℂ) * (v + (ℓ : ℂ) * u) := by
  have hℓc : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ
  rw [← Real.cosh_add_sinh, Complex.ofReal_add]
  simp only [cmpSol, cmpSol']
  field_simp
  ring

/-- With the data `(1, ℓ)` (the Evans data at `ξL`), `ψ₀(ξ) = e^{ℓ(ξ-α)}` and
`ψ₀'(ξ) = ℓe^{ℓ(ξ-α)}`. -/
theorem cmpSol_one_ell {ℓ : ℝ} (hℓ : ℓ ≠ 0) (α ξ : ℝ) :
    cmpSol ℓ α 1 (ℓ : ℂ) ξ = ((Real.exp (ℓ * (ξ - α)) : ℝ) : ℂ) ∧
      cmpSol' ℓ α 1 (ℓ : ℂ) ξ = (ℓ : ℂ) * ((Real.exp (ℓ * (ξ - α)) : ℝ) : ℂ) := by
  have hℓc : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ
  rw [← Real.cosh_add_sinh, Complex.ofReal_add]
  simp only [cmpSol, cmpSol']
  constructor
  · field_simp
  · ring

/-! ### Variation of constants for the scalar combinations `e_±` -/

/-- Variation of constants for `e' = k e + g`, `e(α) = 0`: `e(ξ) = ∫_α^ξ e^{k(ξ-t)} g(t) dt`
(FTC applied to `x ↦ e^{k(ξ-x)} e(x)`). -/
private lemma eq_integral_of_hasDeriv {k α β ξ : ℝ} {e g : ℝ → ℂ}
    (he : ∀ x ∈ Icc α β, HasDerivWithinAt e ((k : ℂ) * e x + g x) (Icc α β) x)
    (hg : ContinuousOn g (Icc α β)) (he0 : e α = 0) (hξ : ξ ∈ Icc α β) :
    e ξ = ∫ t in α..ξ, ((Real.exp (k * (ξ - t)) : ℝ) : ℂ) * g t := by
  have hαξ : α ≤ ξ := hξ.1
  have hsub : Icc α ξ ⊆ Icc α β := Icc_subset_Icc_right hξ.2
  have hec : ContinuousOn e (Icc α β) := fun x hx => (he x hx).continuousWithinAt
  have hexpc : Continuous (fun x : ℝ => ((Real.exp (k * (ξ - x)) : ℝ) : ℂ)) := by fun_prop
  have hcont : ContinuousOn (fun x : ℝ => ((Real.exp (k * (ξ - x)) : ℝ) : ℂ) * e x)
      (Icc α ξ) := hexpc.continuousOn.mul (hec.mono hsub)
  have hderiv : ∀ x ∈ Ioo α ξ, HasDerivAt
      (fun x : ℝ => ((Real.exp (k * (ξ - x)) : ℝ) : ℂ) * e x)
      (((Real.exp (k * (ξ - x)) : ℝ) : ℂ) * g x) x := by
    intro x hx
    have hxI : x ∈ Icc α β := ⟨hx.1.le, hx.2.le.trans hξ.2⟩
    have hnhds : Icc α β ∈ nhds x := Icc_mem_nhds hx.1 (hx.2.trans_le hξ.2)
    have h1 : HasDerivAt e ((k : ℂ) * e x + g x) x := (he x hxI).hasDerivAt hnhds
    have hlin : HasDerivAt (fun x : ℝ => k * (ξ - x)) (-k) x := by
      simpa using ((hasDerivAt_id x).const_sub ξ).const_mul k
    have h2 : HasDerivAt (fun x : ℝ => ((Real.exp (k * (ξ - x)) : ℝ) : ℂ))
        (((Real.exp (k * (ξ - x)) * -k : ℝ) : ℂ)) x := hlin.exp.ofReal_comp
    refine (h2.mul h1).congr_deriv ?_
    push_cast
    ring
  have hint : IntervalIntegrable (fun t : ℝ => ((Real.exp (k * (ξ - t)) : ℝ) : ℂ) * g t)
      MeasureTheory.volume α ξ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hαξ]
    exact hexpc.continuousOn.mul (hg.mono hsub)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hαξ hcont hderiv hint]
  simp [he0]

/-- The bound `|e(ξ)| ≤ ∫_α^ξ e^{k(ξ-t)} |g(t)| dt` for `e' = k e + g`, `e(α) = 0`. -/
private lemma norm_le_integral_of_hasDeriv {k α β ξ : ℝ} {e g : ℝ → ℂ}
    (he : ∀ x ∈ Icc α β, HasDerivWithinAt e ((k : ℂ) * e x + g x) (Icc α β) x)
    (hg : ContinuousOn g (Icc α β)) (he0 : e α = 0) (hξ : ξ ∈ Icc α β) :
    ‖e ξ‖ ≤ ∫ t in α..ξ, Real.exp (k * (ξ - t)) * ‖g t‖ := by
  rw [eq_integral_of_hasDeriv he hg he0 hξ]
  refine (intervalIntegral.norm_integral_le_integral_norm hξ.1).trans_eq ?_
  congr 1
  funext t
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

/-- The variation-of-constants inequality: if `D₁' = D₂`, `D₂' = ℓ² D₁ + g` on `[α, β]` and
`D₁(α) = D₂(α) = 0`, then `|(D₁, D₂)|_w(ξ) ≤ ∫_α^ξ e^{ℓ(ξ-t)} |g(t)| dt`. -/
private lemma wnorm_le_integral {ℓ α β ξ : ℝ} (hℓ : 0 < ℓ) {D₁ D₂ g : ℝ → ℂ}
    (h1 : ∀ x ∈ Icc α β, HasDerivWithinAt D₁ (D₂ x) (Icc α β) x)
    (h2 : ∀ x ∈ Icc α β, HasDerivWithinAt D₂ ((ℓ : ℂ) ^ 2 * D₁ x + g x) (Icc α β) x)
    (hg : ContinuousOn g (Icc α β)) (h10 : D₁ α = 0) (h20 : D₂ α = 0) (hξ : ξ ∈ Icc α β) :
    wnorm ℓ (D₁ ξ) (D₂ ξ) ≤ ∫ t in α..ξ, Real.exp (ℓ * (ξ - t)) * ‖g t‖ := by
  have hαξ : α ≤ ξ := hξ.1
  have hsub : Icc α ξ ⊆ Icc α β := Icc_subset_Icc_right hξ.2
  -- `e₊ = D₂ + ℓ D₁` and `e₋ = D₂ - ℓ D₁`
  have hp : ∀ x ∈ Icc α β, HasDerivWithinAt (fun y => D₂ y + (ℓ : ℂ) * D₁ y)
      ((ℓ : ℂ) * (D₂ x + (ℓ : ℂ) * D₁ x) + g x) (Icc α β) x := by
    intro x hx
    refine ((h2 x hx).add ((h1 x hx).const_mul (ℓ : ℂ))).congr_deriv ?_
    ring
  have hm : ∀ x ∈ Icc α β, HasDerivWithinAt (fun y => D₂ y - (ℓ : ℂ) * D₁ y)
      (((-ℓ : ℝ) : ℂ) * (D₂ x - (ℓ : ℂ) * D₁ x) + g x) (Icc α β) x := by
    intro x hx
    refine ((h2 x hx).sub ((h1 x hx).const_mul (ℓ : ℂ))).congr_deriv ?_
    push_cast
    ring
  have hp0 : D₂ α + (ℓ : ℂ) * D₁ α = 0 := by simp [h10, h20]
  have hm0 : D₂ α - (ℓ : ℂ) * D₁ α = 0 := by simp [h10, h20]
  have bp := norm_le_integral_of_hasDeriv hp hg hp0 hξ
  have bm := norm_le_integral_of_hasDeriv hm hg hm0 hξ
  set I := ∫ t in α..ξ, Real.exp (ℓ * (ξ - t)) * ‖g t‖
  have hgc : ContinuousOn (fun t => ‖g t‖) (Icc α ξ) := (hg.mono hsub).norm
  have bm' : ‖D₂ ξ - (ℓ : ℂ) * D₁ ξ‖ ≤ I := by
    refine bm.trans (intervalIntegral.integral_mono_on hαξ ?_ ?_ ?_)
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hαξ]
      exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-ℓ * (ξ - t)))).continuousOn.mul hgc
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hαξ]
      exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (ℓ * (ξ - t)))).continuousOn.mul hgc
    · intro t ht
      have hts : 0 ≤ ξ - t := sub_nonneg.mpr ht.2
      gcongr
      nlinarith
  have hnℓ : ‖(ℓ : ℂ)‖ = ℓ := by simp [abs_of_pos hℓ]
  apply max_le
  · have : (2 : ℝ) * (ℓ * ‖D₁ ξ‖) ≤ 2 * I := by
      have heq : (2 : ℂ) * ((ℓ : ℂ) * D₁ ξ) =
          (D₂ ξ + (ℓ : ℂ) * D₁ ξ) - (D₂ ξ - (ℓ : ℂ) * D₁ ξ) := by ring
      have hn : ‖(2 : ℂ) * ((ℓ : ℂ) * D₁ ξ)‖ = 2 * (ℓ * ‖D₁ ξ‖) := by
        rw [norm_mul, norm_mul, hnℓ]; norm_num
      rw [← hn, heq]
      refine (norm_sub_le _ _).trans ?_
      linarith
    linarith
  · have : (2 : ℝ) * ‖D₂ ξ‖ ≤ 2 * I := by
      have heq : (2 : ℂ) * D₂ ξ =
          (D₂ ξ + (ℓ : ℂ) * D₁ ξ) + (D₂ ξ - (ℓ : ℂ) * D₁ ξ) := by ring
      have hn : ‖(2 : ℂ) * D₂ ξ‖ = 2 * ‖D₂ ξ‖ := by
        rw [norm_mul]; norm_num
      rw [← hn, heq]
      refine (norm_add_le _ _).trans ?_
      linarith
    linarith

/-! ### The comparison estimate -/

/-- **The comparison estimate.** If `ψ'' = (ℓ² + δ)ψ` on `[α, β]` and `∫_α^β |δ|/ℓ ≤ ε`, then
`|Y(ξ) - Y₀(ξ)|_w ≤ e^{ℓ(ξ-α)} |Y(α)|_w (e^ε - 1)` on `[α, β]`, where `Y = (ψ, ψ')` and `Y₀`
is the solution of `ψ₀'' = ℓ²ψ₀` with the same data at `α`. -/
theorem comparison_estimate {ℓ : ℝ} (hℓ : 0 < ℓ) {α β ε : ℝ} {ψ ψ' δ : ℝ → ℂ}
    (hψ : ∀ ξ ∈ Icc α β, HasDerivWithinAt ψ (ψ' ξ) (Icc α β) ξ)
    (hψ' : ∀ ξ ∈ Icc α β, HasDerivWithinAt ψ' (((ℓ : ℂ) ^ 2 + δ ξ) * ψ ξ) (Icc α β) ξ)
    (hδ : ContinuousOn δ (Icc α β)) (hε : ∫ t in α..β, ‖δ t‖ / ℓ ≤ ε) :
    ∀ ξ ∈ Icc α β,
      wnorm ℓ (ψ ξ - cmpSol ℓ α (ψ α) (ψ' α) ξ) (ψ' ξ - cmpSol' ℓ α (ψ α) (ψ' α) ξ) ≤
        Real.exp (ℓ * (ξ - α)) * wnorm ℓ (ψ α) (ψ' α) * (Real.exp ε - 1) := by
  intro ξ hξ
  have hαβ : α ≤ β := hξ.1.trans hξ.2
  have hαI : α ∈ Icc α β := ⟨le_rfl, hαβ⟩
  have hℓ0 : ℓ ≠ 0 := hℓ.ne'
  set ψ₀ := cmpSol ℓ α (ψ α) (ψ' α) with hψ₀
  set ψ₀' := cmpSol' ℓ α (ψ α) (ψ' α) with hψ₀'
  set c := wnorm ℓ (ψ α) (ψ' α) with hc
  have hc0 : 0 ≤ c := le_max_of_le_right (norm_nonneg _)
  -- the differences `D₁ = ψ - ψ₀`, `D₂ = ψ' - ψ₀'`
  set D₁ : ℝ → ℂ := fun x => ψ x - ψ₀ x with hD₁
  set D₂ : ℝ → ℂ := fun x => ψ' x - ψ₀' x with hD₂
  have h1 : ∀ x ∈ Icc α β, HasDerivWithinAt D₁ (D₂ x) (Icc α β) x := fun x hx =>
    (hψ x hx).sub (hasDerivAt_cmpSol hℓ0 α (ψ α) (ψ' α) x).hasDerivWithinAt
  have h2 : ∀ x ∈ Icc α β, HasDerivWithinAt D₂ ((ℓ : ℂ) ^ 2 * D₁ x + δ x * ψ x)
      (Icc α β) x := by
    intro x hx
    refine ((hψ' x hx).sub
      (hasDerivAt_cmpSol' hℓ0 α (ψ α) (ψ' α) x).hasDerivWithinAt).congr_deriv ?_
    simp only [hD₁]
    ring
  have hψc : ContinuousOn ψ (Icc α β) := fun x hx => (hψ x hx).continuousWithinAt
  have hψc' : ContinuousOn ψ' (Icc α β) := fun x hx => (hψ' x hx).continuousWithinAt
  have hgc : ContinuousOn (fun x => δ x * ψ x) (Icc α β) := hδ.mul hψc
  have h10 : D₁ α = 0 := by simp [hD₁, hψ₀, cmpSol_self]
  have h20 : D₂ α = 0 := by simp [hD₂, hψ₀', cmpSol'_self]
  -- `W = |Y - Y₀|_w`, `u = e^{-ℓ(ξ-α)} W`, `b = |δ|/ℓ`
  set W : ℝ → ℝ := fun x => wnorm ℓ (D₁ x) (D₂ x) with hW
  set u : ℝ → ℝ := fun x => Real.exp (-(ℓ * (x - α))) * W x with hu
  set b : ℝ → ℝ := fun x => ‖δ x‖ / ℓ with hb
  have hψ₀c : Continuous ψ₀ := continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_cmpSol hℓ0 α (ψ α) (ψ' α) x).differentiableAt.continuousAt
  have hψ₀c' : Continuous ψ₀' := continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_cmpSol' hℓ0 α (ψ α) (ψ' α) x).differentiableAt.continuousAt
  have hD₁c : ContinuousOn D₁ (Icc α β) := hψc.sub hψ₀c.continuousOn
  have hD₂c : ContinuousOn D₂ (Icc α β) := hψc'.sub hψ₀c'.continuousOn
  have hWc : ContinuousOn W (Icc α β) :=
    ContinuousOn.sup (continuousOn_const.mul hD₁c.norm) hD₂c.norm
  have huc : ContinuousOn u (Icc α β) :=
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (-(ℓ * (x - α))))).continuousOn.mul hWc
  have hbc : ContinuousOn b (Icc α β) := hδ.norm.div_const ℓ
  have hb0 : ∀ x ∈ Icc α β, 0 ≤ b x := fun x _ => div_nonneg (norm_nonneg _) hℓ.le
  -- the key inequality `u ≤ ∫ b (c + u)`
  have hkey : ∀ x ∈ Icc α β, u x ≤ ∫ t in α..x, b t * (c + u t) := by
    intro x hx
    have hαx : α ≤ x := hx.1
    have hsub : Icc α x ⊆ Icc α β := Icc_subset_Icc_right hx.2
    have hvc := wnorm_le_integral hℓ h1 h2 hgc h10 h20 hx
    -- pointwise bound of the integrand
    have hpt : ∀ t ∈ Icc α x, Real.exp (ℓ * (x - t)) * ‖δ t * ψ t‖ ≤
        Real.exp (ℓ * (x - α)) * (b t * (c + u t)) := by
      intro t ht
      have htI : t ∈ Icc α β := hsub ht
      have hY₀ := wnorm_cmpSol_le hℓ ht.1 (ψ α) (ψ' α)
      have hψt : ℓ * ‖ψ t‖ ≤ Real.exp (ℓ * (t - α)) * c + W t := by
        have hsplit : ψ t = ψ₀ t + D₁ t := by simp [hD₁]
        have h3 : ℓ * ‖ψ₀ t‖ ≤ Real.exp (ℓ * (t - α)) * c :=
          (le_max_left _ _).trans hY₀
        have h4 : ℓ * ‖D₁ t‖ ≤ W t := le_max_left _ _
        rw [hsplit]
        nlinarith [norm_add_le (ψ₀ t) (D₁ t)]
      have hexp1 : Real.exp (ℓ * (x - t)) * Real.exp (ℓ * (t - α)) =
          Real.exp (ℓ * (x - α)) := by rw [← Real.exp_add]; ring_nf
      have hexp2 : Real.exp (ℓ * (x - t)) =
          Real.exp (ℓ * (x - α)) * Real.exp (-(ℓ * (t - α))) := by
        rw [← Real.exp_add]; ring_nf
      have hE : 0 < Real.exp (ℓ * (x - t)) := Real.exp_pos _
      have hδn : 0 ≤ ‖δ t‖ := norm_nonneg _
      calc Real.exp (ℓ * (x - t)) * ‖δ t * ψ t‖
          = Real.exp (ℓ * (x - t)) * (‖δ t‖ / ℓ) * (ℓ * ‖ψ t‖) := by
            rw [norm_mul]; field_simp
        _ ≤ Real.exp (ℓ * (x - t)) * (‖δ t‖ / ℓ) * (Real.exp (ℓ * (t - α)) * c + W t) := by
            gcongr
        _ = Real.exp (ℓ * (x - α)) * (b t * (c + u t)) := by
            simp only [hb, hu]
            linear_combination (‖δ t‖ / ℓ * c) * hexp1 + (‖δ t‖ / ℓ * W t) * hexp2
    have hint1 : IntervalIntegrable (fun t => Real.exp (ℓ * (x - t)) * ‖δ t * ψ t‖)
        MeasureTheory.volume α x := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hαx]
      exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (ℓ * (x - t)))).continuousOn.mul
        (hgc.mono hsub).norm
    have hint2 : IntervalIntegrable (fun t => Real.exp (ℓ * (x - α)) * (b t * (c + u t)))
        MeasureTheory.volume α x := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hαx]
      exact continuousOn_const.mul ((hbc.mono hsub).mul (continuousOn_const.add (huc.mono hsub)))
    have hle := hvc.trans (intervalIntegral.integral_mono_on hαx hint1 hint2 hpt)
    rw [intervalIntegral.integral_const_mul] at hle
    have hEpos : 0 < Real.exp (ℓ * (x - α)) := Real.exp_pos _
    have hinv : Real.exp (-(ℓ * (x - α))) * Real.exp (ℓ * (x - α)) = 1 := by
      rw [← Real.exp_add]; simp
    calc u x = Real.exp (-(ℓ * (x - α))) * W x := rfl
      _ ≤ Real.exp (-(ℓ * (x - α))) *
          (Real.exp (ℓ * (x - α)) * ∫ t in α..x, b t * (c + u t)) :=
          mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
      _ = ∫ t in α..x, b t * (c + u t) := by rw [← mul_assoc, hinv, one_mul]
  -- Grönwall
  have hgr := int_gronwall huc hbc hb0 hkey ξ hξ
  have hbint : ∫ t in α..ξ, b t ≤ ε := by
    have hi1 : IntervalIntegrable b MeasureTheory.volume α ξ := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hξ.1]
      exact hbc.mono (Icc_subset_Icc_right hξ.2)
    have hi2 : IntervalIntegrable b MeasureTheory.volume ξ β := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hξ.2]
      exact hbc.mono (Icc_subset_Icc_left hξ.1)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hnn : 0 ≤ ∫ t in ξ..β, b t :=
      intervalIntegral.integral_nonneg hξ.2 (fun t ht => hb0 t ⟨hξ.1.trans ht.1, ht.2⟩)
    have : ∫ t in α..β, b t ≤ ε := hε
    linarith
  have hu_le : u ξ ≤ c * (Real.exp ε - 1) := by
    have := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbint) hc0
    nlinarith
  have hEpos : 0 < Real.exp (ℓ * (ξ - α)) := Real.exp_pos _
  have hWeq : W ξ = Real.exp (ℓ * (ξ - α)) * u ξ := by
    simp only [hu]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  calc wnorm ℓ (ψ ξ - ψ₀ ξ) (ψ' ξ - ψ₀' ξ) = W ξ := rfl
    _ = Real.exp (ℓ * (ξ - α)) * u ξ := hWeq
    _ ≤ Real.exp (ℓ * (ξ - α)) * (c * (Real.exp ε - 1)) :=
        mul_le_mul_of_nonneg_left hu_le hEpos.le
    _ = Real.exp (ℓ * (ξ - α)) * c * (Real.exp ε - 1) := by ring

end AppA

end NonUniqueEuler
