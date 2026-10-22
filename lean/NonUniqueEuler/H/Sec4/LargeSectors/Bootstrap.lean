import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Order.Compact
import NonUniqueEuler.I.Infra.SectorSpace.BanachExp
import NonUniqueEuler.I.Infra.Ip.Ip

/-!
# Helpers for `P/Sec4/LargeSectors`: the abstract bootstrap of `prop:large-sectors`

The argument of `prop:large-sectors` (`04_ring.tex:1023-1040`) for bounded operators `A`, `B` on
a complex Banach space `E` (`A = -iℓΩ`, `B = k_ℓ𝒢_ℓ`): if `‖exp(tA)‖ ≤ C(1+t)^s` for `t ≥ 0`,
`‖B‖ ≤ κ`, `(1+t)^s e^{-γt} ≤ c` for `t ≥ 0` and `Cκ I_s(γ) ≤ 1/2`, then
`‖exp(t(A+B))‖ ≤ 2Cc e^{γt}` for `t ≥ 0`. Proof: first Duhamel formula
(`BanachExp.exp_add_eq_duhamel`) and the maximum `Y_T` of `e^{-γt}‖exp(t(A+B))‖` on `[0, T]`
(finite by continuity and compactness), `Y_T ≤ Cc + Y_T/2`.

Also: the explicit `c_s(γ) ≤ s! e^γ / γ^s` and the choice of a `γ` with `K I_s(γ) ≤ 1/2`
(used for the finitely many small sectors).
-/

noncomputable section

open Set MeasureTheory
open scoped Nat

namespace NonUniqueEuler.LargeSectorsH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem continuous_exp_smul (A : E →L[ℂ] E) :
    Continuous fun t : ℝ => NormedSpace.exp ((t : ℂ) • A) :=
  continuous_iff_continuousAt.2 fun t => (BanachExp.hasDerivAt_exp_smul A t).1.continuousAt

/-- `c_s(γ) = sup_{t ≥ 0} (1+t)^s e^{-γt} ≤ s! e^γ / γ^s`. -/
theorem one_add_pow_mul_exp_neg_le (s : ℕ) {γ : ℝ} (hγ : 0 < γ) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ s * Real.exp (-γ * t) ≤ s ! * Real.exp γ / γ ^ s := by
  have h := Real.pow_div_factorial_le_exp (x := γ * (1 + t)) (by positivity) s
  have hs : (0 : ℝ) < s ! := by exact_mod_cast Nat.factorial_pos s
  have hγs : 0 < γ ^ s := pow_pos hγ s
  rw [div_le_iff₀ hs, mul_pow] at h
  rw [le_div_iff₀ hγs]
  have he : Real.exp (γ * (1 + t)) = Real.exp γ * Real.exp (γ * t) := by
    rw [← Real.exp_add]; ring_nf
  have hexp : Real.exp (-γ * t) * Real.exp (γ * t) = 1 := by
    rw [← Real.exp_add]; simp
  calc (1 + t) ^ s * Real.exp (-γ * t) * γ ^ s
      = (γ ^ s * (1 + t) ^ s) * Real.exp (-γ * t) := by ring
    _ ≤ (Real.exp (γ * (1 + t)) * s !) * Real.exp (-γ * t) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = s ! * Real.exp γ * (Real.exp (-γ * t) * Real.exp (γ * t)) := by rw [he]; ring
    _ = s ! * Real.exp γ := by rw [hexp, mul_one]

/-- For every `K ≥ 0` there is `γ ≥ 1` with `K I_s(γ) ≤ 1/2` (`I_s(γ) = O(1/γ)`, from the closed
form `Ip_eq_sum`). -/
theorem exists_Ip_small (s : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ γ : ℝ, 1 ≤ γ ∧ K * Ip s γ ≤ 1 / 2 := by
  set Q : ℝ := ∑ j ∈ Finset.range (s + 1), (s ! : ℝ) / ((s - j)! : ℝ) with hQdef
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun j _ => by positivity
  have hKQ : 0 ≤ K * Q := mul_nonneg hK hQ
  refine ⟨1 + 2 * (K * Q), by linarith, ?_⟩
  set γ := 1 + 2 * (K * Q) with hγdef
  have hγ : 1 ≤ γ := by linarith
  have hγ0 : 0 < γ := by linarith
  have hIp : Ip s γ ≤ Q / γ := by
    rw [Ip_eq_sum s hγ0, hQdef, Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [div_div]
    have hf : (0 : ℝ) < ((s - j)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : γ ≤ γ ^ (j + 1) := by
      calc γ = γ ^ 1 := (pow_one γ).symm
        _ ≤ γ ^ (j + 1) := pow_le_pow_right₀ hγ (by omega)
    exact mul_le_mul_of_nonneg_left this hf.le
  calc K * Ip s γ ≤ K * (Q / γ) := mul_le_mul_of_nonneg_left hIp hK
    _ = (K * Q) / γ := by ring
    _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hγ0]
        linarith

/-- **The bootstrap of `prop:large-sectors`** (`04_ring.tex:1023-1040`), for bounded operators. -/
theorem norm_exp_add_le (A B : E →L[ℂ] E) (s : ℕ) {C κ γ c : ℝ}
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hγ : 0 < γ)
    (hA : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : ℂ) • A)‖ ≤ C * (1 + t) ^ s)
    (hB : ‖B‖ ≤ κ)
    (hc : ∀ t : ℝ, 0 ≤ t → (1 + t) ^ s * Real.exp (-γ * t) ≤ c)
    (hsmall : C * κ * Ip s γ ≤ 1 / 2) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp ((t : ℂ) • (A + B))‖ ≤ 2 * C * c * Real.exp (γ * t) := by
  set L := A + B with hL
  set f : ℝ → ℝ := fun τ => Real.exp (-γ * τ) * ‖NormedSpace.exp ((τ : ℂ) • L)‖ with hfdef
  have hfc : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_exp_smul L).norm
  obtain ⟨t₀, ht₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 ht) hfc.continuousOn
  have hmax' : ∀ τ ∈ Icc (0 : ℝ) t, f τ ≤ f t₀ := fun τ hτ => isMaxOn_iff.1 hmax τ hτ
  set Y := f t₀ with hYdef
  have hY0 : 0 ≤ Y := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have key : ∀ u ∈ Icc (0 : ℝ) t, f u ≤ C * c + Y / 2 := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1
    have hbound : ∀ τ ∈ Icc (0 : ℝ) u,
        ‖NormedSpace.exp (((u - τ : ℝ) : ℂ) • A) * B * NormedSpace.exp ((τ : ℂ) • L)‖ ≤
          (C * κ * Y * Real.exp (γ * u)) * ((1 + (u - τ)) ^ s * Real.exp (-γ * (u - τ))) := by
      intro τ hτ
      have h1 := hA (u - τ) (by linarith [hτ.2])
      have h2 : ‖NormedSpace.exp ((τ : ℂ) • L)‖ ≤ Real.exp (γ * τ) * Y := by
        have hτY : f τ ≤ Y := hmax' τ ⟨hτ.1, hτ.2.trans hu.2⟩
        have hpos := Real.exp_pos (γ * τ)
        calc ‖NormedSpace.exp ((τ : ℂ) • L)‖
            = Real.exp (γ * τ) * f τ := by
              rw [hfdef, ← mul_assoc, ← Real.exp_add]
              simp
          _ ≤ Real.exp (γ * τ) * Y := mul_le_mul_of_nonneg_left hτY hpos.le
      have hexpτ : Real.exp (γ * τ) = Real.exp (γ * u) * Real.exp (-γ * (u - τ)) := by
        rw [← Real.exp_add]; ring_nf
      calc ‖NormedSpace.exp (((u - τ : ℝ) : ℂ) • A) * B * NormedSpace.exp ((τ : ℂ) • L)‖
          ≤ ‖NormedSpace.exp (((u - τ : ℝ) : ℂ) • A)‖ * ‖B‖ *
              ‖NormedSpace.exp ((τ : ℂ) • L)‖ :=
            (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ (C * (1 + (u - τ)) ^ s) * κ * (Real.exp (γ * τ) * Y) := by
            have h1t : 0 ≤ 1 + (u - τ) := by linarith [hτ.2]
            have hCp : 0 ≤ C * (1 + (u - τ)) ^ s := mul_nonneg hC (pow_nonneg h1t s)
            gcongr
        _ = (C * κ * Y * Real.exp (γ * u)) * ((1 + (u - τ)) ^ s * Real.exp (-γ * (u - τ))) := by
            rw [hexpτ]; ring
    have hint1 : IntervalIntegrable (fun τ : ℝ =>
        ‖NormedSpace.exp (((u - τ : ℝ) : ℂ) • A) * B * NormedSpace.exp ((τ : ℂ) • L)‖)
        volume 0 u := by
      refine Continuous.intervalIntegrable ?_ _ _
      have hc1 : Continuous fun τ : ℝ => NormedSpace.exp (((u - τ : ℝ) : ℂ) • A) :=
        (continuous_exp_smul A).comp (continuous_const.sub continuous_id)
      exact ((hc1.mul continuous_const).mul (continuous_exp_smul L)).norm
    have hint2 : IntervalIntegrable (fun τ : ℝ =>
        (C * κ * Y * Real.exp (γ * u)) * ((1 + (u - τ)) ^ s * Real.exp (-γ * (u - τ))))
        volume 0 u := by
      refine Continuous.intervalIntegrable ?_ _ _
      fun_prop
    have hsub : ∫ τ in (0 : ℝ)..u, (1 + (u - τ)) ^ s * Real.exp (-γ * (u - τ)) =
        ∫ x in (0 : ℝ)..u, (1 + x) ^ s * Real.exp (-γ * x) := by
      rw [intervalIntegral.integral_comp_sub_left (fun x => (1 + x) ^ s * Real.exp (-γ * x)) u]
      simp
    have hint_le : ‖∫ τ in (0 : ℝ)..u,
        NormedSpace.exp (((u - τ : ℝ) : ℂ) • A) * B * NormedSpace.exp ((τ : ℂ) • L)‖ ≤
          C * κ * Y * Real.exp (γ * u) * Ip s γ := by
      refine (intervalIntegral.norm_integral_le_integral_norm hu0).trans ?_
      refine (intervalIntegral.integral_mono_on hu0 hint1 hint2 hbound).trans ?_
      rw [intervalIntegral.integral_const_mul, hsub]
      exact mul_le_mul_of_nonneg_left (intervalIntegral_le_Ip s hγ hu0) (by positivity)
    have hnorm : ‖NormedSpace.exp ((u : ℂ) • L)‖ ≤
        C * (1 + u) ^ s + C * κ * Y * Real.exp (γ * u) * Ip s γ := by
      rw [hL, BanachExp.exp_add_eq_duhamel A B u]
      exact (norm_add_le _ _).trans (add_le_add (hA u hu0) hint_le)
    have hcu := hc u hu0
    have hexp : Real.exp (-γ * u) * Real.exp (γ * u) = 1 := by
      rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (-γ * u)
    calc f u = Real.exp (-γ * u) * ‖NormedSpace.exp ((u : ℂ) • L)‖ := rfl
      _ ≤ Real.exp (-γ * u) * (C * (1 + u) ^ s + C * κ * Y * Real.exp (γ * u) * Ip s γ) :=
          mul_le_mul_of_nonneg_left hnorm hpos.le
      _ = C * ((1 + u) ^ s * Real.exp (-γ * u)) +
            (C * κ * Ip s γ) * Y * (Real.exp (-γ * u) * Real.exp (γ * u)) := by ring
      _ ≤ C * c + (1 / 2) * Y * 1 := by
          rw [hexp]
          exact add_le_add (mul_le_mul_of_nonneg_left hcu hC)
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsmall hY0) zero_le_one)
      _ = C * c + Y / 2 := by ring
  have hY : Y ≤ 2 * C * c := by
    have := key t₀ ht₀
    linarith
  have hft : f t ≤ Y := hmax' t (right_mem_Icc.2 ht)
  have hexp : Real.exp (γ * t) * Real.exp (-γ * t) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖NormedSpace.exp ((t : ℂ) • L)‖
      = Real.exp (γ * t) * f t := by
        rw [hfdef]
        simp only
        rw [← mul_assoc, hexp, one_mul]
    _ ≤ Real.exp (γ * t) * (2 * C * c) :=
        mul_le_mul_of_nonneg_left (hft.trans hY) (Real.exp_pos _).le
    _ = 2 * C * c * Real.exp (γ * t) := by ring

end NonUniqueEuler.LargeSectorsH
