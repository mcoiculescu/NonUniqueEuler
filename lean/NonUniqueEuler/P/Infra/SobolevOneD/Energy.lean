import NonUniqueEuler.Defs.Infra.SobolevOneD
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.H.Infra.SobolevOneD.Energy.Higher

/-!
# Proof: the energy identity for `ψ'' - ℓ²ψ = f` on `ℝ` (library I-SOB1, restructuring R4)

Proves `NonUniqueEuler/I/Infra/SobolevOneD/Energy.lean` (`yukawa_energy`, `yukawa_higher`).

Structure (helpers in `H/Infra/SobolevOneD/Energy/`):
* `Kernel`: `k0 = e^{-L|z|}`, `k1 = sgn(z) e^{-L|z|}` and their distributional derivatives tested
  against `C¹` functions with integrable derivative (half-line FTC);
* `Conv`: `psi0 = k0 ⋆ f`, `psi1 = k1 ⋆ f`; `psi0' = -L psi1` classically; bounds
  `≤ C e^{-L|x-a|}`; Fubini identities;
* `Yukawa`: `ψ = yukawa ℓ f`, `ψ' = Y1 = psi1/2` (classical and weak), `Y1' = Y2 = ℓ²ψ + f`
  (weak, also against `φ = conj ψ`); the energy identity
  `∫|f|² = ℓ⁴∫|ψ|² + 2ℓ²∫|ψ'|² + ∫|ψ''|²` from `∫ ψ'' conj ψ = -∫|ψ'|²`;
* `Commute`: `∂(yukawa g) = yukawa (∂g)` for compactly supported `g ∈ W^{1,1}` (smoothness of
  `k0 ⋆ φ` for test functions `φ` and a bump function cut-off);
* `Higher`: bookkeeping of the weak derivatives of `f ∈ H^k` and of `yukawa ℓ f`.
The weight computation giving the constant `6` is below (`yukawa_higher`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Sob

namespace EnergyAux

theorem ae_eq_of_weak {g h : ℝ → ℂ} {j : ℕ} (hh : MemLp h 2 volume)
    (w : HasWeakDerivOn univ (derivList j) g h) : weakDeriv1On univ j g =ᵐ[volume] h := by
  have := weakDerivOn_ae_eq isOpen_univ (locallyIntegrableOn_of_memLp hh univ) w
  filter_upwards [this] with x hx using hx (mem_univ x)

theorem l2_congr {g h : ℝ → ℂ} (hgh : g =ᵐ[volume] h) : l2 g = l2 h := by
  unfold l2
  rw [eLpNorm_congr_ae hgh]

theorem integral_norm_sq_congr {g h : ℝ → ℂ} (hgh : g =ᵐ[volume] h) :
    ∫ x, ‖g x‖ ^ 2 = ∫ x, ‖h x‖ ^ 2 :=
  integral_congr_ae (hgh.mono fun x hx => by simp only [hx])

theorem one_le_sq_of_ne {ℓ : ℤ} (hℓ : ℓ ≠ 0) : 1 ≤ (ℓ : ℝ) ^ 2 := by
  have h1 : (1 : ℝ) ≤ |(ℓ : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hℓ
  have := sq_abs (ℓ : ℝ)
  nlinarith

/-- The energy identity for the derivatives, in the form used for the weights. -/
theorem energy_le {ℓ : ℤ} (hℓ : ℓ ≠ 0) {f : ℝ → ℂ} (hf : MemLp f 2 volume) {a b : ℝ}
    (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0) :
    (ℓ : ℝ) ^ 4 * (∫ x, ‖yukawa ℓ f x‖ ^ 2) + 2 * (ℓ : ℝ) ^ 2 * (∫ x, ‖Y1 ℓ f x‖ ^ 2) ≤
        ∫ x, ‖f x‖ ^ 2 ∧
      ∫ x, ‖Y2 ℓ f x‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 := by
  have hE := energy_integral hℓ hf hfab
  have h0 : 0 ≤ ∫ x, ‖yukawa ℓ f x‖ ^ 2 := integral_nonneg fun _ => by positivity
  have h1 : 0 ≤ ∫ x, ‖Y1 ℓ f x‖ ^ 2 := integral_nonneg fun _ => by positivity
  have h2 : 0 ≤ ∫ x, ‖Y2 ℓ f x‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hl4 : 0 ≤ (ℓ : ℝ) ^ 4 := by positivity
  have hl2 : 0 ≤ (ℓ : ℝ) ^ 2 := by positivity
  constructor
  · rw [hE]; linarith
  · rw [hE]; nlinarith [mul_nonneg hl4 h0, mul_nonneg hl2 h1]

end EnergyAux

open EnergyAux

/-- `ψ = yukawa ℓ f ∈ H²(ℝ)` solves `ψ'' - ℓ²ψ = f` and satisfies the energy identity. -/
theorem yukawa_energy {ℓ : ℤ} (hℓ : ℓ ≠ 0) {f : ℝ → ℂ} (hf : MemLp f 2 volume) {a b : ℝ}
    (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0) :
    MemH1On 2 univ (yukawa ℓ f) ∧
      (∀ᵐ x, weakDeriv1On univ 2 (yukawa ℓ f) x - ((ℓ : ℂ) ^ 2) * yukawa ℓ f x = f x) ∧
      (ℓ : ℝ) ^ 4 * l2 (yukawa ℓ f) ^ 2 + 2 * (ℓ : ℝ) ^ 2 * l2 (weakDeriv1On univ 1 (yukawa ℓ f)) ^ 2 +
          l2 (weakDeriv1On univ 2 (yukawa ℓ f)) ^ 2 = l2 f ^ 2 := by
  have hfi := integrable_of_memLp_two hf hfab
  have hψ := memLp_yukawa hℓ hfi hfab
  have h1 := memLp_Y1 hℓ hfi hfab
  have h2 := memLp_Y2 hℓ hf hfab
  have w1 := hasWeakDerivOn_yukawa_one hℓ hfi
  have w2 := hasWeakDerivOn_yukawa_two hℓ hfi hfab
  have e1 := ae_eq_of_weak h1 w1
  have e2 := ae_eq_of_weak h2 w2
  refine ⟨⟨memLp_restrict_univ_iff.2 hψ, fun j hj => ?_⟩, ?_, ?_⟩
  · interval_cases j
    · exact ⟨yukawa ℓ f, memLp_restrict_univ_iff.2 hψ, fun φ _ => by simp [derivList]⟩
    · exact ⟨Y1 ℓ f, memLp_restrict_univ_iff.2 h1, w1⟩
    · exact ⟨Y2 ℓ f, memLp_restrict_univ_iff.2 h2, w2⟩
  · filter_upwards [e2] with x hx
    rw [hx]
    unfold Y2
    ring
  · rw [l2_congr e1, l2_congr e2, l2_sq_eq_integral hψ, l2_sq_eq_integral h1,
      l2_sq_eq_integral h2, l2_sq_eq_integral hf, energy_integral hℓ hf hfab]

/-- Higher regularity: `f ∈ H^k(ℝ)` gives `ψ ∈ H^{k+2}(ℝ)`, `∂^j ψ = yukawa ℓ (∂^j f)`, and
`|ψ|²_{k+2,ℓ} ≤ 6 |f|²_{k,ℓ}`. -/
theorem yukawa_higher {ℓ : ℤ} (hℓ : ℓ ≠ 0) {k : ℕ} {f : ℝ → ℂ} (hf : MemH1On k univ f) {a b : ℝ}
    (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0) :
    MemH1On (k + 2) univ (yukawa ℓ f) ∧
      (∀ j ≤ k, weakDeriv1On univ j (yukawa ℓ f) =ᵐ[volume] yukawa ℓ (weakDeriv1On univ j f)) ∧
      logNormSq (k + 2) ℓ (yukawa ℓ f) ≤ 6 * logNormSq k ℓ f := by
  have hf2 : MemLp f 2 volume := memLp_restrict_univ_iff.1 hf.memLp
  have hfi := integrable_of_memLp_two hf2 hfab
  have hD : ∀ j ≤ k, MemLp (weakDeriv1On univ j f) 2 volume :=
    fun j hj => (memLp_weakDeriv1On hf hj).1
  have hZ : ∀ j ≤ k, ∀ᵐ x, x ∉ Icc a b → weakDeriv1On univ j f x = 0 :=
    fun j hj => weakDeriv1On_eq_zero_outside hf hfab hj
  have hI : ∀ j ≤ k, Integrable (weakDeriv1On univ j f) :=
    fun j hj => integrable_weakDeriv1On hf hfab hj
  have hYj : ∀ j ≤ k, MemLp (yukawa ℓ (weakDeriv1On univ j f)) 2 volume :=
    fun j hj => memLp_yukawa hℓ (hI j hj) (hZ j hj)
  have hY1k : MemLp (Y1 ℓ (weakDeriv1On univ k f)) 2 volume :=
    memLp_Y1 hℓ (hI k le_rfl) (hZ k le_rfl)
  have hY2 : ∀ i ≤ k, MemLp (Y2 ℓ (weakDeriv1On univ i f)) 2 volume :=
    fun i hi => memLp_Y2 hℓ (hD i hi) (hZ i hi)
  have hψ := memLp_yukawa hℓ hfi hfab
  have hMem : MemH1On (k + 2) univ (yukawa ℓ f) := by
    refine ⟨memLp_restrict_univ_iff.2 hψ, fun j hj => ?_⟩
    rcases le_or_gt j k with hjk | hjk
    · exact ⟨_, memLp_restrict_univ_iff.2 (hYj j hjk), hasWeakDerivOn_yukawa_iter hℓ hf hfab hjk⟩
    · rcases (show j = k + 1 ∨ j = k + 2 by omega) with rfl | rfl
      · exact ⟨_, memLp_restrict_univ_iff.2 hY1k, hasWeakDerivOn_yukawa_top1 hℓ hf hfab⟩
      · exact ⟨_, memLp_restrict_univ_iff.2 (hY2 k le_rfl),
          hasWeakDerivOn_yukawa_add_two hℓ hf hfab le_rfl⟩
  refine ⟨hMem, fun j hj => ae_eq_of_weak (hYj j hj) (hasWeakDerivOn_yukawa_iter hℓ hf hfab hj),
    ?_⟩
  -- the weighted bound
  set W : ℝ := 1 + (ℓ : ℝ) ^ 2 with hW
  have hl1 := one_le_sq_of_ne hℓ
  have hW0 : 0 ≤ W := by positivity
  set F : ℕ → ℝ := fun j =>
    secWeight (k + 2) j ℓ * ∫ x, ‖weakDeriv1On univ j (yukawa ℓ f) x‖ ^ 2 with hF
  set G : ℕ → ℝ := fun j => secWeight k j ℓ * ∫ x, ‖weakDeriv1On univ j f x‖ ^ 2 with hG
  have hlogψ : logNormSq (k + 2) ℓ (yukawa ℓ f) = ∑ j ∈ Finset.range (k + 2 + 1), F j := by
    simp [logNormSq, logNormSqOn, hF]
  have hlogf : logNormSq k ℓ f = ∑ j ∈ Finset.range (k + 1), G j := by
    simp [logNormSq, logNormSqOn, hG]
  have hG0 : ∀ j, 0 ≤ G j := fun j =>
    mul_nonneg (secWeight_nonneg _ _ _) (integral_nonneg fun _ => by positivity)
  -- the terms `j = i + 2`
  have hhigh : ∀ i ∈ Finset.range (k + 1), F (i + 1 + 1) ≤ G i := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hw : secWeight (k + 2) (i + 1 + 1) ℓ = secWeight k i ℓ := by
      unfold secWeight; congr 1; omega
    have he : weakDeriv1On univ (i + 1 + 1) (yukawa ℓ f) =ᵐ[volume]
        Y2 ℓ (weakDeriv1On univ i f) :=
      ae_eq_of_weak (hY2 i hik) (hasWeakDerivOn_yukawa_add_two hℓ hf hfab hik)
    simp only [hF, hG]
    rw [hw, integral_norm_sq_congr he]
    exact mul_le_mul_of_nonneg_left (energy_le hℓ (hD i hik) (hZ i hik)).2
      (secWeight_nonneg _ _ _)
  -- the terms `j = 0, 1`
  have hlow : F (0 + 1) + F 0 ≤ 4 * G 0 := by
    have e0 : weakDeriv1On univ 0 (yukawa ℓ f) =ᵐ[volume] yukawa ℓ f := weakDeriv1On_zero_ae hψ
    have e1 : weakDeriv1On univ 1 (yukawa ℓ f) =ᵐ[volume] Y1 ℓ f :=
      ae_eq_of_weak (memLp_Y1 hℓ hfi hfab) (hasWeakDerivOn_yukawa_one hℓ hfi)
    have ef : weakDeriv1On univ 0 f =ᵐ[volume] f := weakDeriv1On_zero_ae hf2
    have hE := energy_le hℓ hf2 hfab
    simp only [hF, hG, zero_add]
    rw [integral_norm_sq_congr e0, integral_norm_sq_congr e1, integral_norm_sq_congr ef]
    have s0 : secWeight (k + 2) 0 ℓ = W ^ k * W ^ 2 := by
      simp [secWeight, hW, pow_add]
    have s1 : secWeight (k + 2) 1 ℓ = W ^ k * W := by
      simp only [secWeight, hW]
      rw [show k + 2 - 1 = k + 1 by omega, pow_succ]
    have sk : secWeight k 0 ℓ = W ^ k := by simp [secWeight, hW]
    rw [s0, s1, sk]
    set T0 := ∫ x, ‖yukawa ℓ f x‖ ^ 2
    set T1 := ∫ x, ‖Y1 ℓ f x‖ ^ 2
    set S := ∫ x, ‖f x‖ ^ 2
    have hT0 : 0 ≤ T0 := integral_nonneg fun _ => by positivity
    have hT1 : 0 ≤ T1 := integral_nonneg fun _ => by positivity
    have hWk : 0 ≤ W ^ k := pow_nonneg hW0 k
    have hW1 : W ≤ 2 * (ℓ : ℝ) ^ 2 := by rw [hW]; linarith
    have hW2 : W ^ 2 ≤ 4 * (ℓ : ℝ) ^ 4 := by
      have : W ^ 2 ≤ (2 * (ℓ : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hW0 hW1 2
      nlinarith
    have hl2 : 0 ≤ (ℓ : ℝ) ^ 2 := by positivity
    have hin : W * T1 + W ^ 2 * T0 ≤ 4 * S := by
      have a1 : W * T1 ≤ 2 * (ℓ : ℝ) ^ 2 * T1 := mul_le_mul_of_nonneg_right hW1 hT1
      have a2 : W ^ 2 * T0 ≤ 4 * (ℓ : ℝ) ^ 4 * T0 := mul_le_mul_of_nonneg_right hW2 hT0
      nlinarith [hE.1, mul_nonneg hl2 hT1]
    calc W ^ k * W * T1 + W ^ k * W ^ 2 * T0 = W ^ k * (W * T1 + W ^ 2 * T0) := by ring
      _ ≤ W ^ k * (4 * S) := mul_le_mul_of_nonneg_left hin hWk
      _ = 4 * (W ^ k * S) := by ring
  -- summation
  have hsum0 : G 0 ≤ ∑ j ∈ Finset.range (k + 1), G j :=
    Finset.single_le_sum (fun j _ => hG0 j) (Finset.mem_range.2 (Nat.succ_pos k))
  have hsumG : 0 ≤ ∑ j ∈ Finset.range (k + 1), G j := Finset.sum_nonneg fun j _ => hG0 j
  rw [hlogψ, hlogf, Finset.sum_range_succ', Finset.sum_range_succ']
  have := Finset.sum_le_sum hhigh
  linarith

end NonUniqueEuler.Sob
