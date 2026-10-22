import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Proof: interpolation of `L^p` norms (P-LPINT)

Proof of `NonUniqueEuler/I/Infra/LpInterp/Interp.lean` (same declarations, same statements).

* Log-convexity (`eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow`). The endpoint cases `θ = 0`, `θ = 1`
  reduce to `q = p`, `q = r`. For `0 < θ < 1` write `‖f‖ = ‖f‖^{1-θ} ‖f‖^θ` and apply Mathlib's
  generalized Hölder inequality `eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm` with the exponents
  `a = ((1-θ) p⁻¹)⁻¹`, `b = (θ r⁻¹)⁻¹` (so `a⁻¹ + b⁻¹ = q⁻¹`), then
  `eLpNorm (‖f‖^s) a = ‖f‖_{a s}^s = ‖f‖_p^s` (`eLpNorm_norm_rpow`). No case analysis on zero or
  infinite norms or exponents is needed: the identity `(s p⁻¹)⁻¹ s = p` holds in `ℝ≥0∞` for every
  `p` once `0 < s < ∞`.
* The additive form: for `p < q < r` take `θ = (1/p - 1/q)/(1/p - 1/r)` and bound
  `A^{1-θ} B^θ ≤ (A+B)^{1-θ} (A+B)^θ = A + B`.
* The two special cases are instances with `(p, r, θ) = (1, 2, 2 - 2/q)` and `(1, ∞, 1 - 1/q)`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NonUniqueEuler.LpInterp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*} [NormedAddCommGroup E]

/-- `(s p⁻¹)⁻¹ s = p` in `ℝ≥0∞` for every `p`, when `0 < s`. -/
private lemma inv_ofReal_mul_inv_mul_ofReal {s : ℝ} (hs : 0 < s) (p : ℝ≥0∞) :
    (ENNReal.ofReal s * p⁻¹)⁻¹ * ENNReal.ofReal s = p := by
  have h0 : ENNReal.ofReal s ≠ 0 := by simpa using hs
  have htop : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.mul_inv (Or.inl h0) (Or.inl htop), inv_inv, mul_right_comm,
    ENNReal.inv_mul_cancel h0 htop, one_mul]

/-- The interior case `0 < θ < 1` of log-convexity. -/
private lemma interp_of_pos_of_lt_one {f : α → E} (hf : AEStronglyMeasurable f μ)
    {p q r : ℝ≥0∞} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hθ : q⁻¹ = ENNReal.ofReal (1 - θ) * p⁻¹ + ENNReal.ofReal θ * r⁻¹) :
    eLpNorm f q μ ≤ eLpNorm f p μ ^ (1 - θ) * eLpNorm f r μ ^ θ := by
  have h1θ : 0 < 1 - θ := by linarith
  have : ENNReal.HolderTriple (ENNReal.ofReal (1 - θ) * p⁻¹)⁻¹ (ENNReal.ofReal θ * r⁻¹)⁻¹ q :=
    ⟨by rw [inv_inv, inv_inv]; exact hθ.symm⟩
  have hg : AEStronglyMeasurable (fun x => ‖f x‖) μ := hf.norm
  have hu : AEStronglyMeasurable (fun x => ‖f x‖ ^ (1 - θ)) μ :=
    (Real.continuous_rpow_const h1θ.le).comp_aestronglyMeasurable hg
  have hv : AEStronglyMeasurable (fun x => ‖f x‖ ^ θ) μ :=
    (Real.continuous_rpow_const hθ0.le).comp_aestronglyMeasurable hg
  have hsplit : (fun x => ‖f x‖) = fun x => ‖f x‖ ^ (1 - θ) * ‖f x‖ ^ θ := by
    funext x
    rw [← Real.rpow_add' (norm_nonneg _) (by norm_num : (1 - θ) + θ ≠ 0)]
    norm_num
  calc eLpNorm f q μ = eLpNorm (fun x => ‖f x‖ ^ (1 - θ) * ‖f x‖ ^ θ) q μ := by
        rw [← hsplit, eLpNorm_norm]
    _ ≤ ((1 : NNReal) : ℝ≥0∞) * eLpNorm (fun x => ‖f x‖ ^ (1 - θ))
          (ENNReal.ofReal (1 - θ) * p⁻¹)⁻¹ μ *
          eLpNorm (fun x => ‖f x‖ ^ θ) (ENNReal.ofReal θ * r⁻¹)⁻¹ μ :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hu hv (fun x y : ℝ => x * y) 1
          (Filter.Eventually.of_forall fun x => by
            rw [one_mul]; exact nnnorm_mul_le _ _)
    _ = eLpNorm f p μ ^ (1 - θ) * eLpNorm f r μ ^ θ := by
        rw [eLpNorm_norm_rpow f h1θ, eLpNorm_norm_rpow f hθ0,
          inv_ofReal_mul_inv_mul_ofReal h1θ, inv_ofReal_mul_inv_mul_ofReal hθ0,
          ENNReal.coe_one, one_mul]

/-- Log-convexity of `L^p` norms: `‖f‖_q ≤ ‖f‖_p^{1-θ} ‖f‖_r^θ` when
`1/q = (1-θ)/p + θ/r`, `θ ∈ [0,1]`. -/
theorem eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow {f : α → E} (hf : AEStronglyMeasurable f μ)
    {p q r : ℝ≥0∞} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hθ : q⁻¹ = ENNReal.ofReal (1 - θ) * p⁻¹ + ENNReal.ofReal θ * r⁻¹) :
    eLpNorm f q μ ≤ eLpNorm f p μ ^ (1 - θ) * eLpNorm f r μ ^ θ := by
  rcases hθ0.eq_or_lt with rfl | hθ0'
  · have hqp : q = p := by simpa using hθ
    subst hqp
    simp
  rcases hθ1.eq_or_lt with rfl | hθ1'
  · have hqr : q = r := by simpa using hθ
    subst hqr
    simp
  exact interp_of_pos_of_lt_one hf hθ0' hθ1' hθ

/-- `‖f‖_q ≤ ‖f‖_p + ‖f‖_r` for `0 < p ≤ q ≤ r` (e.g. `‖ω‖_q ≤ ‖ω‖_{L¹ ∩ L²}`). -/
theorem eLpNorm_le_eLpNorm_add_eLpNorm {f : α → E} (hf : AEStronglyMeasurable f μ)
    {p q r : ℝ≥0∞} (hp : 0 < p) (hpq : p ≤ q) (hqr : q ≤ r) :
    eLpNorm f q μ ≤ eLpNorm f p μ + eLpNorm f r μ := by
  rcases hpq.eq_or_lt with rfl | hpq'
  · exact le_self_add
  rcases hqr.eq_or_lt with rfl | hqr'
  · exact le_add_self
  -- Now `0 < p < q < r`; all inverses are finite.
  have hp0 : p ≠ 0 := hp.ne'
  have hq0 : q ≠ 0 := (hp.trans hpq').ne'
  have hr0 : r ≠ 0 := (hp.trans (hpq'.trans hqr')).ne'
  have hPt : p⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hp0
  have hQt : q⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hq0
  have hRt : r⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hr0
  set P := p⁻¹.toReal with hP
  set Q := q⁻¹.toReal with hQ
  set R := r⁻¹.toReal with hR
  have hR0 : 0 ≤ R := ENNReal.toReal_nonneg
  have hQP : Q < P := (ENNReal.toReal_lt_toReal hQt hPt).2 (ENNReal.inv_lt_inv.2 hpq')
  have hRQ : R < Q := (ENNReal.toReal_lt_toReal hRt hQt).2 (ENNReal.inv_lt_inv.2 hqr')
  set θ : ℝ := (P - Q) / (P - R) with hθdef
  have hPR : 0 < P - R := by linarith
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hPR.le
  have hθ1 : θ ≤ 1 := (div_le_one hPR).2 (by linarith)
  have hθlin : (1 - θ) * P + θ * R = Q := by
    have : θ * (P - R) = P - Q := by rw [hθdef]; field_simp
    linarith
  have hθ : q⁻¹ = ENNReal.ofReal (1 - θ) * p⁻¹ + ENNReal.ofReal θ * r⁻¹ := by
    rw [← ENNReal.ofReal_toReal hPt, ← ENNReal.ofReal_toReal hQt, ← ENNReal.ofReal_toReal hRt,
      ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hθ0,
      ← ENNReal.ofReal_add (mul_nonneg (by linarith) ENNReal.toReal_nonneg)
        (mul_nonneg hθ0 ENNReal.toReal_nonneg)]
    exact congrArg ENNReal.ofReal hθlin.symm
  calc eLpNorm f q μ ≤ eLpNorm f p μ ^ (1 - θ) * eLpNorm f r μ ^ θ :=
        eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow hf hθ0 hθ1 hθ
    _ ≤ (eLpNorm f p μ + eLpNorm f r μ) ^ (1 - θ) * (eLpNorm f p μ + eLpNorm f r μ) ^ θ := by
        gcongr
        · exact le_self_add
        · exact le_add_self
    _ = eLpNorm f p μ + eLpNorm f r μ := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) hθ0, sub_add_cancel,
          ENNReal.rpow_one]

/-- `L^p ∩ L^r ⊆ L^q` for `0 < p ≤ q ≤ r`. -/
theorem memLp_of_memLp_of_memLp {f : α → E} {p q r : ℝ≥0∞} (hp : 0 < p) (hpq : p ≤ q)
    (hqr : q ≤ r) (hfp : MemLp f p μ) (hfr : MemLp f r μ) : MemLp f q μ :=
  ⟨hfp.1, (eLpNorm_le_eLpNorm_add_eLpNorm hfp.1 hp hpq hqr).trans_lt
    (ENNReal.add_lt_top.2 ⟨hfp.2, hfr.2⟩)⟩

/-- The `L¹`–`L²` case (`03_compactness.tex:291-293`): `‖f‖_q ≤ ‖f‖₁^{2/q-1} ‖f‖₂^{2-2/q}`,
`q ∈ [1,2]`. -/
theorem eLpNorm_le_of_one_two {f : α → E} (hf : AEStronglyMeasurable f μ) {q : ℝ}
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    eLpNorm f (ENNReal.ofReal q) μ ≤ eLpNorm f 1 μ ^ (2 / q - 1) * eLpNorm f 2 μ ^ (2 - 2 / q) := by
  have hq0 : 0 < q := by linarith
  have h2q : 2 / q ≤ 2 := by rw [div_le_iff₀ hq0]; linarith
  have h1q : 1 ≤ 2 / q := by rw [le_div_iff₀ hq0]; linarith
  have hexp : (1 : ℝ) - (2 - 2 / q) = 2 / q - 1 := by ring
  have hθ : (ENNReal.ofReal q)⁻¹ =
      ENNReal.ofReal (1 - (2 - 2 / q)) * (1 : ℝ≥0∞)⁻¹ + ENNReal.ofReal (2 - 2 / q) * 2⁻¹ := by
    have h2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal 2⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    rw [inv_one, mul_one, h2, ← ENNReal.ofReal_inv_of_pos hq0,
      ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_add (by linarith) (mul_nonneg (by linarith) (by norm_num))]
    congr 1
    field_simp
    ring
  have key := eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow (μ := μ) (p := 1) (r := 2)
    (θ := 2 - 2 / q) hf (by linarith) (by linarith) hθ
  rwa [hexp] at key

/-- The `L¹`–`L^∞` case: `‖f‖_q ≤ ‖f‖₁^{1/q} ‖f‖_∞^{1-1/q}`, `q ≥ 1`. -/
theorem eLpNorm_le_of_one_top {f : α → E} (hf : AEStronglyMeasurable f μ) {q : ℝ}
    (hq : 1 ≤ q) :
    eLpNorm f (ENNReal.ofReal q) μ ≤ eLpNorm f 1 μ ^ (1 / q) * eLpNorm f ⊤ μ ^ (1 - 1 / q) := by
  have hq0 : 0 < q := by linarith
  have h1q : 1 / q ≤ 1 := by rw [div_le_one hq0]; exact hq
  have h1q0 : 0 ≤ 1 / q := by positivity
  have hexp : (1 : ℝ) - (1 - 1 / q) = 1 / q := by ring
  have hθ : (ENNReal.ofReal q)⁻¹ =
      ENNReal.ofReal (1 - (1 - 1 / q)) * (1 : ℝ≥0∞)⁻¹ + ENNReal.ofReal (1 - 1 / q) * (⊤ : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.inv_top, mul_zero, add_zero, inv_one, mul_one, hexp, one_div,
      ENNReal.ofReal_inv_of_pos hq0]
  have key := eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow (μ := μ) (p := 1) (r := ⊤)
    (θ := 1 - 1 / q) hf (by linarith) (by linarith) hθ
  rwa [hexp] at key

end NonUniqueEuler.LpInterp
