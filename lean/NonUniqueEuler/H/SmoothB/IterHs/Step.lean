import NonUniqueEuler.H.SmoothB.IterHs.Commutator
import NonUniqueEuler.H.SmoothB.IterHs.Gronwall

/-!
# Helper for `lem:iter-Hs`: the induction step `s - 1 → s` (`s ≥ 2`)

Helper of `P/SmoothB/IterHs.lean` (`B_global_smooth.tex:320-348`). Assume
`‖ω^{[i]}(t)‖_{H^{s-1}} ≤ 𝓜 = 𝓜_{s-1}(T)` for all `i` and `|t| ≤ T` (`s = n + 2`).

* `j = 0`: `𝓜_s(T) ≥ ‖ω₀‖_{H^s}` (`normH_datum_le_calM`).
* `j + 1`: with `𝓗(t) = ∑_{|α| = s} ‖∂^α ω^{[j+1]}(t)‖²_{L²}` and `Z(t) = ‖ω^{[j+1]}(t)‖_{H^s}`,
  `𝓗' = 2 Re ∑_α ∫ ∂^α ω^{[j+1]} ∂^α ∂_t ω^{[j+1]}` (`hasDerivAt_topEnergy`), each term is at most
  `Z · 2^{s+1}[(V + 𝓜)Z + 𝓜Ψ]` (`abs_re_energy_term_le`), so
  `|𝓗'| ≤ (s+1) 2^{s+2}[(V + 𝓜)Z + 𝓜Ψ]Z ≤ 𝓑_s(Z² + 1) ≤ 𝓑_s(𝓗 + 𝓜² + 1)` since `Z ≤ Z² + 1`
  and `Z² = 𝓗 + ‖ω^{[j+1]}(t)‖²_{H^{s-1}} ≤ 𝓗 + 𝓜²` (`abs_deriv_topEnergy_le`); Grönwall
  (`le_mul_exp_of_abs_deriv_le`) and `𝓗(0) ≤ ‖ω₀‖²_{H^s}` conclude.
-/

noncomputable section

open MeasureTheory Set Metric Filter ComplexConjugate
open scoped ContDiff ENNReal Topology

namespace NonUniqueEuler.Smooth.IterHsH

open Sob

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

theorem calB_nonneg (ω₀ : ℂ → ℝ) (R₀ : ℝ) (s : ℕ) (T : ℝ) : 0 ≤ calB ω₀ R₀ s T := by
  simp only [calB, calBof]
  have hV := Vbd_nonneg ω₀ T
  have hM := calM_nonneg ω₀ R₀ (s - 1) T
  have hP := Psi_nonneg ω₀ T
  have h1 : 0 ≤ Vbd ω₀ T + calM ω₀ R₀ (s - 1) T + calM ω₀ R₀ (s - 1) T * Psi ω₀ T := by
    have := mul_nonneg hM hP
    linarith
  exact mul_nonneg (by positivity) h1

/-- `𝓜_s(T) ≥ ‖ω₀‖_{H^s}` (the case `j = 0`). -/
theorem normH_datum_le_calM (n : ℕ) {T : ℝ} (hT : 0 < T) :
    normH (n + 2) (fun x => (ω₀ x : ℂ)) ≤ calM ω₀ R₀ (n + 2) T := by
  rw [calM_succ_succ]
  apply Real.le_sqrt_of_sq_le
  have he : 1 ≤ Real.exp (calB ω₀ R₀ (n + 2) T * T) :=
    Real.one_le_exp (mul_nonneg (calB_nonneg ω₀ R₀ _ T) hT.le)
  have hpos : 0 ≤ normH (n + 2) (fun x => (ω₀ x : ℂ)) ^ 2 + calM ω₀ R₀ (n + 1) T ^ 2 + 1 := by
    positivity
  have h1 := mul_le_mul_of_nonneg_left he hpos
  nlinarith [sq_nonneg (calM ω₀ R₀ (n + 1) T)]

/-- The elementary inequality `2(s+1) Z · 2^{s+1}[(V + M)Z + MΨ] ≤ 𝓑_s (Z² + 1)`. -/
theorem energy_ineq (n : ℕ) {V M P Z : ℝ} (hV : 0 ≤ V) (hM : 0 ≤ M) (hP : 0 ≤ P) :
    2 * (((n + 2 : ℕ) : ℝ) + 1) * (Z * (2 ^ (n + 3) * ((V + M) * Z + M * P))) ≤
      calBof (n + 2) V M P * (Z ^ 2 + 1) := by
  simp only [calBof]
  have hZ1 : Z ≤ Z ^ 2 + 1 := by nlinarith [sq_nonneg (Z - 1)]
  have hMP : 0 ≤ M * P := mul_nonneg hM hP
  have key : (V + M) * Z ^ 2 + M * P * Z ≤ (V + M + M * P) * (Z ^ 2 + 1) := by
    have h1 : M * P * Z ≤ M * P * (Z ^ 2 + 1) := mul_le_mul_of_nonneg_left hZ1 hMP
    nlinarith
  have hc : (0 : ℝ) ≤ (((n + 2 : ℕ) : ℝ) + 1) * 2 ^ (n + 2 + 2) := by positivity
  have e : 2 * (((n + 2 : ℕ) : ℝ) + 1) * (Z * (2 ^ (n + 3) * ((V + M) * Z + M * P))) =
      (((n + 2 : ℕ) : ℝ) + 1) * 2 ^ (n + 2 + 2) * ((V + M) * Z ^ 2 + M * P * Z) := by
    ring
  rw [e, mul_assoc _ (V + M + M * P)]
  exact mul_le_mul_of_nonneg_left key hc

/-- The bound `|𝓗'(t)| ≤ 𝓑_s(T)(𝓗(t) + 𝓜² + 1)` for `|t| ≤ T`. -/
theorem abs_deriv_topEnergy_le (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (n : ℕ) {T : ℝ}
    (ih : ∀ i : ℕ, ∀ t : ℝ, |t| ≤ T →
      normH (n + 1) (fun x => (iter ω₀ i t x : ℂ)) ≤ calM ω₀ R₀ (n + 1) T)
    (j : ℕ) {t : ℝ} (ht : |t| ≤ T) :
    |2 * (∑ α ∈ Finset.antidiagonal (n + 2),
        ∫ x, conj (partialD α (fun z => (iter ω₀ (j + 1) t z : ℂ)) x) *
          partialD α (fun x => deriv (fun s => (iter ω₀ (j + 1) s x : ℂ)) t) x).re| ≤
      calB ω₀ R₀ (n + 2) T *
        (∑ α ∈ Finset.antidiagonal (n + 2),
          l2 (partialD α (fun z => (iter ω₀ (j + 1) t z : ℂ))) ^ 2 +
          calM ω₀ R₀ (n + 1) T ^ 2 + 1) := by
  set M := calM ω₀ R₀ (n + 1) T with hMdef
  set W : ℂ → ℂ := fun z => (iter ω₀ (j + 1) t z : ℂ) with hW
  set Z := normH (n + 2) W with hZdef
  set K := 2 ^ (n + 3) * ((Vbd ω₀ T + M) * Z + M * Psi ω₀ T) with hK
  have hWs := contDiff_iter_sliceC h hne (j + 1) t
  have hWc := hasCompactSupport_iter_sliceC h hne (j + 1) t
  -- each term
  have hterm : ∀ α ∈ Finset.antidiagonal (n + 2),
      |(∫ x, conj (partialD α W x) *
          partialD α (fun x => deriv (fun s => (iter ω₀ (j + 1) s x : ℂ)) t) x).re| ≤ Z * K :=
    fun α hα => abs_re_energy_term_le h hne n j ht (ih j t ht) hα
  have hsum : |2 * (∑ α ∈ Finset.antidiagonal (n + 2), ∫ x, conj (partialD α W x) *
        partialD α (fun x => deriv (fun s => (iter ω₀ (j + 1) s x : ℂ)) t) x).re| ≤
      2 * (((n + 2 : ℕ) : ℝ) + 1) * (Z * K) := by
    rw [Complex.re_sum, abs_mul, abs_two, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ zero_le_two
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans_eq ?_
    rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    push_cast
    ring
  refine hsum.trans ?_
  -- `2(s+1) Z K ≤ 𝓑 (Z² + 1) ≤ 𝓑 (𝓗 + 𝓜² + 1)`
  have hV := Vbd_nonneg ω₀ T
  have hM0 : 0 ≤ M := calM_nonneg ω₀ R₀ (n + 1) T
  have hP := Psi_nonneg ω₀ T
  have h1 := energy_ineq n (Z := Z) hV hM0 hP
  have hB : calB ω₀ R₀ (n + 2) T = calBof (n + 2) (Vbd ω₀ T) M (Psi ω₀ T) := rfl
  rw [hB]
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by rw [← hB]; exact calB_nonneg ω₀ R₀ _ T))
  have hsplit := normH_succ_sq_eq hWs hWc (n + 1)
  have hlow : normH (n + 1) W ≤ M := ih (j + 1) t ht
  have hlow2 : normH (n + 1) W ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ (normH_nonneg _ _) hlow 2
  have hZsq : Z ^ 2 = normH (n + 1) W ^ 2 +
      ∑ α ∈ Finset.antidiagonal (n + 2), l2 (partialD α W) ^ 2 := hsplit
  linarith

/-- The induction step of `lem:iter-Hs`: the bound at level `s - 1 = n + 1` for all iterates
gives the bound at level `s = n + 2`. -/
theorem iter_Hs_step (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (n : ℕ) {T : ℝ} (hT : 0 < T)
    (ih : ∀ i : ℕ, ∀ t : ℝ, |t| ≤ T →
      normH (n + 1) (fun x => (iter ω₀ i t x : ℂ)) ≤ calM ω₀ R₀ (n + 1) T)
    (j : ℕ) {t : ℝ} (ht : |t| ≤ T) :
    normH (n + 2) (fun x => (iter ω₀ j t x : ℂ)) ≤ calM ω₀ R₀ (n + 2) T := by
  cases j with
  | zero => exact normH_datum_le_calM n hT
  | succ j =>
    set M := calM ω₀ R₀ (n + 1) T with hMdef
    set B := calB ω₀ R₀ (n + 2) T with hBdef
    set N := normH (n + 2) (fun x => (ω₀ x : ℂ)) with hNdef
    set Hf : ℝ → ℝ := fun s => ∑ α ∈ Finset.antidiagonal (n + 2),
      l2 (partialD α (fun z => (iter ω₀ (j + 1) s z : ℂ))) ^ 2 with hHf
    set D : ℝ → ℝ := fun s => 2 * (∑ α ∈ Finset.antidiagonal (n + 2),
      ∫ x, conj (partialD α (fun z => (iter ω₀ (j + 1) s z : ℂ)) x) *
        partialD α (fun x => deriv (fun τ => (iter ω₀ (j + 1) τ x : ℂ)) s) x).re with hD
    have hws : ContDiff ℝ ∞ (fun p : ℝ × ℂ => (iter ω₀ (j + 1) p.1 p.2 : ℂ)) := by
      have h1 : ContDiff ℝ ∞
          (fun p : ℝ × ℂ => Complex.ofRealCLM (Function.uncurry (iter ω₀ (j + 1)) p)) :=
        Complex.ofRealCLM.contDiff.comp (iterates_smooth_support h hne (j + 1)).1
      simpa only [Complex.ofRealCLM_apply, Function.uncurry] using h1
    obtain ⟨R₀', -, hR⟩ := exists_iter_support h hne
    have hU := Ustar_nonneg ω₀
    -- `𝓗' = D`
    have hderiv : ∀ τ, HasDerivAt Hf (D τ) τ := by
      intro τ
      refine hasDerivAt_topEnergy (n + 1) hws
        (isCompact_closedBall (0 : ℂ) (R₀' + Ustar ω₀ * (|τ| + 1)))
        (I := Ioo (-(|τ| + 1)) (|τ| + 1)) isOpen_Ioo ?_ ?_
      · intro s hs x hx
        have hs' : |s| ≤ |τ| + 1 := abs_le.2 ⟨hs.1.le, hs.2.le⟩
        have hx1 : R₀' + Ustar ω₀ * (|τ| + 1) < ‖x‖ := by
          simpa [mem_closedBall, dist_zero_right, not_le] using hx
        have hx' : R₀' + Ustar ω₀ * |s| < ‖x‖ := by
          nlinarith [mul_le_mul_of_nonneg_left hs' hU]
        simp [hR (j + 1) s x hx']
      · constructor <;> linarith [neg_abs_le τ, le_abs_self τ]
    -- `|𝓗'| ≤ 𝓑 (𝓗 + 𝓜² + 1)` on `[-T, T]`
    have hbd : ∀ τ, |τ| ≤ T → |D τ| ≤ B * (Hf τ + M ^ 2 + 1) :=
      fun τ hτ => abs_deriv_topEnergy_le h hne n ih j hτ
    have hHf0 : ∀ τ, 0 ≤ Hf τ := fun τ => Finset.sum_nonneg fun α _ => sq_nonneg _
    have hB0 : 0 ≤ B := calB_nonneg ω₀ R₀ _ T
    -- Grönwall
    have hG := le_mul_exp_of_abs_deriv_le (G := fun τ => Hf τ + M ^ 2 + 1) (G' := D) (B := B)
      (T := T) (fun τ => ((hderiv τ).add_const (M ^ 2)).add_const 1)
      (fun τ _ => by have := hHf0 τ; positivity) hbd ht
    -- `𝓗(0) ≤ ‖ω₀‖²_{H^s}`
    have hinit : iter ω₀ (j + 1) 0 = ω₀ := (iterates_flow h hne j).2.2.2.1
    have hH0 : Hf 0 ≤ N ^ 2 := by
      have hsp := normH_succ_sq_eq (contDiff_iter_sliceC h hne (j + 1) 0)
        (hasCompactSupport_iter_sliceC h hne (j + 1) 0) (n + 1)
      have e : (fun z => (iter ω₀ (j + 1) 0 z : ℂ)) = fun z => (ω₀ z : ℂ) := by
        rw [hinit]
      rw [e] at hsp
      have : Hf 0 = ∑ α ∈ Finset.antidiagonal (n + 2),
          l2 (partialD α (fun z => (ω₀ z : ℂ))) ^ 2 := by
        simp only [hHf, e]
      rw [this]
      nlinarith [sq_nonneg (normH (n + 1) (fun z => (ω₀ z : ℂ)))]
    -- conclusion
    have hexp : Real.exp (B * |t|) ≤ Real.exp (B * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht hB0)
    have hM0 : 0 ≤ M := calM_nonneg ω₀ R₀ (n + 1) T
    have h2 : (Hf 0 + M ^ 2 + 1) * Real.exp (B * |t|) ≤ (N ^ 2 + M ^ 2 + 1) * Real.exp (B * T) :=
      mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by positivity)
    have hsp := normH_succ_sq_eq (contDiff_iter_sliceC h hne (j + 1) t)
      (hasCompactSupport_iter_sliceC h hne (j + 1) t) (n + 1)
    have hlow : normH (n + 1) (fun z => (iter ω₀ (j + 1) t z : ℂ)) ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (normH_nonneg _ _) (ih (j + 1) t ht) 2
    rw [calM_succ_succ]
    apply Real.le_sqrt_of_sq_le
    have hHt : Hf t = ∑ α ∈ Finset.antidiagonal (n + 2),
        l2 (partialD α (fun z => (iter ω₀ (j + 1) t z : ℂ))) ^ 2 := rfl
    rw [← hHt] at hsp
    nlinarith

end NonUniqueEuler.Smooth.IterHsH
