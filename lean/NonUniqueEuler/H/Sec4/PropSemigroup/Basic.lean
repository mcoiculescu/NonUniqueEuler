import NonUniqueEuler.Defs.Sec4.Eigendata
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition
import NonUniqueEuler.I.Infra.SectorSpace.Projection

/-!
# Helpers for `P/Sec4/PropSemigroup`: generic lemmas

* `exists_norm_le_of_secProj_le`: on `Y^s` of an annulus, sector-wise bounds
  `‖P_ℓ v‖ ≤ K‖P_ℓ w‖` (all `ℓ`) give `‖v‖ ≤ B K ‖w‖`, with `B` depending only on `s` and the
  annulus (`exists_norm_equiv_Y`, the norm equivalence of `lem:norm-equiv`);
* `exists_uniform_of_large`: a property `Q ℓ C`, monotone in `C`, that holds for each `ℓ` with
  some `C` and for all `|ℓ| ≥ M` with one `C₀`, holds for all `ℓ` with one `C` (finitely many
  remaining sectors);
* `secProj_eq_zero_of_memX`: `P_ℓ w = 0` for `w ∈ X^s` and `3 ∤ ℓ`.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace PropSemigroupH

open Sect

/-- Sector-wise bounds give a bound in `Y^s` (norm equivalence). -/
theorem exists_norm_le_of_secProj_le (s : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) :
    ∃ B : ℝ, 0 < B ∧ ∀ (v w : Y s (closedAnnulus ρm ρp)) (K : ℝ), 0 ≤ K →
      (∀ ℓ : ℤ, ‖secProj s _ ℓ v‖ ≤ K * ‖secProj s _ ℓ w‖) → ‖v‖ ≤ B * K * ‖w‖ := by
  obtain ⟨c, C, hc, hC, h⟩ := exists_norm_equiv_Y s hρm hρ
  refine ⟨Real.sqrt (C / c), Real.sqrt_pos.2 (div_pos hC hc), fun v w K hK hvw => ?_⟩
  obtain ⟨hvs, -, hv⟩ := h v
  obtain ⟨hws, hw, -⟩ := h w
  have hsq : ∀ ℓ : ℤ, ‖secProj s _ ℓ v‖ ^ 2 ≤ K ^ 2 * ‖secProj s _ ℓ w‖ ^ 2 := by
    intro ℓ
    have := pow_le_pow_left₀ (norm_nonneg _) (hvw ℓ) 2
    rwa [mul_pow] at this
  have hsum : ∑' ℓ : ℤ, ‖secProj s _ ℓ v‖ ^ 2 ≤ K ^ 2 * ∑' ℓ : ℤ, ‖secProj s _ ℓ w‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hsq hvs (hws.mul_left _)
  have hw' : ∑' ℓ : ℤ, ‖secProj s _ ℓ w‖ ^ 2 ≤ ‖w‖ ^ 2 / c := by
    rw [le_div_iff₀ hc]
    linarith
  have hB : Real.sqrt (C / c) ^ 2 = C / c := Real.sq_sqrt (div_nonneg hC.le hc.le)
  have key : ‖v‖ ^ 2 ≤ (Real.sqrt (C / c) * K * ‖w‖) ^ 2 := by
    calc ‖v‖ ^ 2 ≤ C * ∑' ℓ : ℤ, ‖secProj s _ ℓ v‖ ^ 2 := hv
      _ ≤ C * (K ^ 2 * (‖w‖ ^ 2 / c)) := by
          gcongr
          exact hsum.trans (mul_le_mul_of_nonneg_left hw' (sq_nonneg K))
      _ = (Real.sqrt (C / c) * K * ‖w‖) ^ 2 := by
          rw [mul_pow, mul_pow, hB]
          field_simp
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 key

/-- Finitely many sectors: a monotone property holding sector-wise and uniformly for large `|ℓ|`
holds uniformly. -/
theorem exists_uniform_of_large (Q : ℤ → ℝ → Prop)
    (hmono : ∀ ℓ C C', C ≤ C' → Q ℓ C → Q ℓ C')
    (hsec : ∀ ℓ, ∃ C, 0 < C ∧ Q ℓ C) {M C₀ : ℝ} (hC₀ : 0 < C₀)
    (hlarge : ∀ ℓ : ℤ, M ≤ |(ℓ : ℝ)| → Q ℓ C₀) :
    ∃ C, 0 < C ∧ ∀ ℓ, Q ℓ C := by
  choose Cf hCf hQ using hsec
  set N : ℕ := ⌈M⌉₊
  set F : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  refine ⟨C₀ + ∑ ℓ ∈ F, Cf ℓ, ?_, fun ℓ => ?_⟩
  · have : 0 ≤ ∑ ℓ ∈ F, Cf ℓ := Finset.sum_nonneg fun ℓ _ => (hCf ℓ).le
    linarith
  · have hsum0 : 0 ≤ ∑ ℓ ∈ F, Cf ℓ := Finset.sum_nonneg fun ℓ _ => (hCf ℓ).le
    by_cases hℓ : M ≤ |(ℓ : ℝ)|
    · exact hmono ℓ _ _ (by linarith) (hlarge ℓ hℓ)
    · replace hℓ := not_le.1 hℓ
      have hmem : ℓ ∈ F := by
        have h1 : |(ℓ : ℝ)| ≤ (N : ℝ) := hℓ.le.trans (Nat.le_ceil M)
        have h2 : |ℓ| ≤ (N : ℤ) := by exact_mod_cast h1
        rw [Finset.mem_Icc]
        exact abs_le.1 h2
      have hle : Cf ℓ ≤ ∑ ℓ ∈ F, Cf ℓ :=
        Finset.single_le_sum (f := Cf) (fun ℓ _ => (hCf ℓ).le) hmem
      exact hmono ℓ _ _ (by linarith) (hQ ℓ)

/-- `P_ℓ w = 0` for `w ∈ X^s` and `3 ∤ ℓ` (`X^s = Y^s_{3ℤ}`). -/
theorem secProj_eq_zero_of_memX {s : ℕ} {w : Y s RingData.annN} (hw : Lin.MemX w) {ℓ : ℤ}
    (hℓ : ¬ (3 : ℤ) ∣ ℓ) : secProj s RingData.annN ℓ w = 0 := by
  have h1 : (w : Sob.SobTuple s) ∈ YZSub s RingData.annN {ℓ : ℤ | ((3 : ℕ) : ℤ) ∣ ℓ} := by
    rw [← YsymSub_eq_YZSub RingData.isRotInvariant_annN (by norm_num : 0 < 3)]
    exact hw
  exact (mem_YZSub_iff RingData.isRotInvariant_annN _ w).1 h1 ℓ hℓ

end PropSemigroupH

end NonUniqueEuler
