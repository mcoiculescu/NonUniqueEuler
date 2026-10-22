import NonUniqueEuler.H.Sec5.Active.Basic

/-!
# Helpers for `thm:active`: elementary inequalities for the transient and the window

Helper of `P/Sec5/Active.lean` (fully proved). Manuscript `05_single_ring.tex:876-880`,
`:951-956` (`eq:A-t1`), `:1003-1010`, `:1037-1047`.

* `rhoHatOf_nonneg`; `rho_layer`: `C₀κ⟨u⟩^pe^{σ'u} ≤ â(u)ρ̂(u)` for `0 ≤ u ≤ t₁`;
* `small_after_t1` (`eq:A-t1`): `C₀⟨v⟩^pe^{-σv} ≤ 1` for `v ≥ t₁`;
* `ahat_le_of_le_That`: `â(u) ≤ δ₀` for `u ≤ T̂`; `That_shift`: `T̂₁ = T̂ - t₁` for
  `κ₁ = â(t₁)`;
* `varsigma_le`: `0 ≤ ς(κ₁) ≤ ς(κ)` for `0 < κ ≤ κ₁ ≤ 1`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.ActiveH

open RingData

theorem rhoHatOf_nonneg {σ σ' C₀ : ℝ} (hC₀ : 0 ≤ C₀) (u : ℝ) : 0 ≤ rhoHatOf σ σ' C₀ u := by
  unfold rhoHatOf
  have := Prelim.jap_nonneg u
  have := Prelim.jap_nonneg (u - tOneOf σ σ' C₀)
  split_ifs <;> positivity

theorem le_one_of_two_rpow_mul {X : ℝ} (hX : 0 ≤ X)
    (h : (2 : ℝ) ^ ((pW : ℝ) / 2) * X ≤ 1) : X ≤ 1 := by
  have h2 := one_lt_two_rpow
  nlinarith

theorem exp_sig_mul (σ σ' u : ℝ) :
    Real.exp (σ * u) * Real.exp (-((σ - σ') * u)) = Real.exp (σ' * u) := by
  rw [← Real.exp_add]; congr 1; ring

/-- `C₀κ⟨u⟩^pe^{σ'u} ≤ â(u)ρ̂(u)` for `0 ≤ u ≤ t₁` (`05_single_ring.tex:1003-1006`). -/
theorem rho_layer {σ σ' C₀ κ u : ℝ} (hσ : σ' < σ) (hC₀ : 1 ≤ C₀) (hκ : 0 < κ) (_hu : 0 ≤ u)
    (hut : u ≤ tOneOf σ σ' C₀) :
    C₀ * κ * Prelim.jap u ^ pW * Real.exp (σ' * u) ≤ ahat κ σ u * rhoHatOf σ σ' C₀ u := by
  rcases hut.lt_or_eq with hlt | heq
  · rw [rhoHatOf_of_lt hlt, ahat, ← exp_sig_mul σ σ' u]
    apply le_of_eq; ring
  · rw [rhoHatOf_of_le heq.ge, heq, sub_self, Prelim.jap_zero, one_pow, mul_zero, neg_zero,
      Real.exp_zero, mul_one, ahat]
    obtain ⟨-, hprop, -⟩ := tOneOf_spec hσ hC₀
    have h1 := hprop (tOneOf σ σ' C₀) le_rfl
    set t := tOneOf σ σ' C₀
    have h2 := one_lt_two_rpow
    have hj := Prelim.jap_nonneg t
    have hA : C₀ * Prelim.jap t ^ pW * Real.exp (-((σ - σ') * t)) ≤ 1 := by
      have h0 : 0 ≤ C₀ * Prelim.jap t ^ pW * Real.exp (-((σ - σ') * t)) := by positivity
      exact le_one_of_two_rpow_mul h0 (by
        calc _ = (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t ^ pW *
              Real.exp (-((σ - σ') * t)) := by ring
          _ ≤ 1 := h1)
    calc C₀ * κ * Prelim.jap t ^ pW * Real.exp (σ' * t)
        = κ * Real.exp (σ * t) * (C₀ * Prelim.jap t ^ pW * Real.exp (-((σ - σ') * t))) := by
          rw [← exp_sig_mul σ σ' t]; ring
      _ ≤ κ * Real.exp (σ * t) * 1 := by gcongr

/-- At `u = t₁`: `C₀κ⟨t₁⟩^pe^{σ't₁} ≤ â(t₁)` (`05_single_ring.tex:1004-1006`). -/
theorem rho_layer_t1 {σ σ' C₀ κ : ℝ} (hσ : σ' < σ) (hC₀ : 1 ≤ C₀) (hκ : 0 < κ) :
    C₀ * κ * Prelim.jap (tOneOf σ σ' C₀) ^ pW * Real.exp (σ' * tOneOf σ σ' C₀) ≤
      ahat κ σ (tOneOf σ σ' C₀) := by
  have h := rho_layer hσ hC₀ hκ (tOneOf_spec hσ hC₀).1.le le_rfl
  rwa [rhoHatOf_of_le le_rfl, sub_self, Prelim.jap_zero, one_pow, mul_zero, neg_zero,
    Real.exp_zero, mul_one, mul_one] at h

/-- `eq:A-t1`: `C₀⟨v⟩^pe^{-σv} ≤ 1` for `v ≥ t₁` (`05_single_ring.tex:953-956`). -/
theorem small_after_t1 {σ σ' C₀ v : ℝ} (hσ : σ' < σ) (hσ' : 0 ≤ σ') (hC₀ : 1 ≤ C₀)
    (hv : tOneOf σ σ' C₀ ≤ v) : C₀ * Prelim.jap v ^ pW * Real.exp (-(σ * v)) ≤ 1 := by
  obtain ⟨hpos, hprop, -⟩ := tOneOf_spec hσ hC₀
  have h1 := hprop v hv
  have hv0 : 0 ≤ v := hpos.le.trans hv
  have h2 := one_lt_two_rpow
  have hj := Prelim.jap_nonneg v
  have he : Real.exp (-(σ * v)) ≤ Real.exp (-((σ - σ') * v)) := by
    apply Real.exp_le_exp.2; nlinarith
  have h0 : 0 ≤ C₀ * Prelim.jap v ^ pW * Real.exp (-((σ - σ') * v)) := by positivity
  calc C₀ * Prelim.jap v ^ pW * Real.exp (-(σ * v))
      ≤ C₀ * Prelim.jap v ^ pW * Real.exp (-((σ - σ') * v)) := by gcongr
    _ ≤ 1 := le_one_of_two_rpow_mul h0 (by
        calc _ = (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap v ^ pW *
              Real.exp (-((σ - σ') * v)) := by ring
          _ ≤ 1 := h1)

/-- `â(u) ≤ δ₀` for `u ≤ T̂ = σ⁻¹log(δ₀/κ)`. -/
theorem ahat_le_of_le_That {σ δ₀ κ u : ℝ} (hσ : 0 < σ) (hδ₀ : 0 < δ₀) (hκ : 0 < κ)
    (hu : u ≤ That σ δ₀ κ) : ahat κ σ u ≤ δ₀ := by
  unfold That at hu
  unfold ahat
  have h1 : σ * u ≤ Real.log (δ₀ / κ) := by
    have := mul_le_mul_of_nonneg_left hu hσ.le
    rwa [← mul_assoc, mul_inv_cancel₀ hσ.ne', one_mul] at this
  have h2 : Real.exp (σ * u) ≤ δ₀ / κ := by
    calc Real.exp (σ * u) ≤ Real.exp (Real.log (δ₀ / κ)) := Real.exp_le_exp.2 h1
      _ = δ₀ / κ := Real.exp_log (div_pos hδ₀ hκ)
  rw [le_div_iff₀ hκ] at h2
  linarith

/-- `T̂₁ = σ⁻¹log(δ₀/κ₁) = T̂ - t₁` for `κ₁ = â(t₁) = κe^{σt₁}`. -/
theorem That_shift {σ δ₀ κ t : ℝ} (hσ : 0 < σ) (hδ₀ : 0 < δ₀) (hκ : 0 < κ) :
    That σ δ₀ (ahat κ σ t) = That σ δ₀ κ - t := by
  unfold That ahat
  rw [Real.log_div hδ₀.ne' (mul_pos hκ (Real.exp_pos _)).ne', Real.log_mul hκ.ne'
    (Real.exp_pos _).ne', Real.log_exp, Real.log_div hδ₀.ne' hκ.ne']
  field_simp
  ring

/-- `0 ≤ ς(κ₁) ≤ ς(κ)` for `0 < κ ≤ κ₁ ≤ 1` (`ς` is decreasing). -/
theorem varsigma_le (χ : ℝ → ℝ) (hσb : 0 < Eig.sigb χ) {κ κ₁ : ℝ} (hκ : 0 < κ) (hκκ₁ : κ ≤ κ₁)
    (hκ₁ : κ₁ ≤ 1) : 0 ≤ varsigma χ κ₁ ∧ varsigma χ κ₁ ≤ varsigma χ κ := by
  unfold varsigma
  have hκ₁0 : 0 < κ₁ := hκ.trans_le hκκ₁
  have hl : 0 ≤ Real.log (1 / κ₁) := Real.log_nonneg (by rw [le_div_iff₀ hκ₁0]; linarith)
  have hll : Real.log (1 / κ₁) ≤ Real.log (1 / κ) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hκ hκκ₁)
  have hinv := inv_pos.2 hσb
  constructor
  · positivity
  · nlinarith

end NonUniqueEuler.OneRing.ActiveH
