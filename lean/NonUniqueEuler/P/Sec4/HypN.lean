import NonUniqueEuler.Defs.Sec4.Eigendata

/-!
# Proof: the remarks after Hypothesis (N)

Proof of `I/Sec4/HypN.lean` (`04_ring.tex:1153-1156`). Same declarations, statements copied
verbatim.

* `hypN_lamC`: (N1) gives the zero `z₀`; its uniqueness gives `∃!`, so `lamC χ G = z₀`
  (`Eig.lamC_eq_of_existsUnique`); (N2) excludes `Re z₀ ≤ 211/2500`.
* `hypN_Θ_pos`: `0 < π ℓ d < π` for `ℓ ∈ {6, 9}` since `0 < 9d < 1` (`d = 5764607523034235/2⁵⁸`),
  so `sin(π ℓ d) > 0` and `Θ_ℓ > 0`.
-/

noncomputable section

open Set

namespace NonUniqueEuler

open RingData

/-- `04_ring.tex:1153-1154`: under (N1) and (N2), for `G ∈ [0, 1/50]`, `λ_*^c(G) = Eig.lamC χ G` is
the zero of (N1) (simple, unique in `{Re λ ≥ 9/200}`), and `Re λ_*^c(G) > 211/2500`. -/
theorem hypN_lamC (χ : ℝ → ℝ) (h1 : N1 χ) (h2 : N2 χ) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) (1 / 50)) :
    211 / 2500 < (Eig.lamC χ G).re ∧ evans χ 3 (Eig.lamC χ G) G = 0 ∧
      deriv (fun z => evans χ 3 z G) (Eig.lamC χ G) ≠ 0 ∧
      ∀ z : ℂ, 9 / 200 ≤ z.re → evans χ 3 z G = 0 → z = Eig.lamC χ G := by
  obtain ⟨z₀, hre, hzero, hderiv, huniq⟩ := h1 G hG
  have hex : ∃! z : ℂ, 9 / 200 ≤ z.re ∧ evans χ 3 z G = 0 :=
    ⟨z₀, ⟨hre, hzero⟩, fun z hz => huniq z hz.1 hz.2⟩
  have hlam : Eig.lamC χ G = z₀ := Eig.lamC_eq_of_existsUnique hex ⟨hre, hzero⟩
  rw [hlam]
  refine ⟨?_, hzero, hderiv, huniq⟩
  by_contra hle
  exact h2 G hG z₀ hre (not_lt.mp hle) hzero

/-- `0 < Θ ℓ` whenever `0 < ℓ d < 1`. -/
private theorem Θ_pos_of {ℓ : ℕ} (h0 : 0 < (ℓ : ℝ) * d) (h1 : (ℓ : ℝ) * d < 1) : 0 < Θ ℓ := by
  have hx0 : 0 < Real.pi * ℓ * d := by
    rw [mul_assoc]; exact mul_pos Real.pi_pos h0
  have hxpi : Real.pi * ℓ * d < Real.pi := by
    rw [mul_assoc]; exact mul_lt_of_lt_one_right Real.pi_pos h1
  exact div_pos hx0 (Real.sin_pos_of_pos_of_lt_pi hx0 hxpi)

/-- `04_ring.tex:1155-1156`: `Θ_6` and `Θ_9` are finite positive numbers (`6d < 1`, `9d < 1`). -/
theorem hypN_Θ_pos : 0 < Θ 6 ∧ 0 < Θ 9 := by
  refine ⟨Θ_pos_of ?_ ?_, Θ_pos_of ?_ ?_⟩ <;> · simp only [d]; norm_num

end NonUniqueEuler
