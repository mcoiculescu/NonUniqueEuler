import NonUniqueEuler.Defs.Verify.NPrime
import NonUniqueEuler.I.Verify.ArgPrinciple
import NonUniqueEuler.I.Verify.APriori
import NonUniqueEuler.I.Evans.ODE

/-!
# Proof: Lemma A.6 (`lem:Nprime-N`): (N1′) ⇒ (N1), and (N1) ∧ (N2′) ⇒ (N2)

Proof of `I/Verify/NPrimeN.lean`. Manuscript `A_verification.tex:536-560`.

Black boxes: `argument_principle_rect_one` (`I/Verify/ArgPrinciple.lean`),
`AppA.apriori_zero_mem_RA` (`I/Verify/APriori.lean`), `evans_differentiableOn`
(`I/Evans/ODE.lean`). The argument is the manuscript's.
-/

namespace NonUniqueEuler

open RingData

namespace NPrimeNAux

/-- `[0, 1/50] ⊆ [0, d]`, since `d > 1/50`. -/
theorem mem_Icc_d_of_mem {G : ℝ} (hG : G ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    G ∈ Set.Icc (0 : ℝ) d := by
  refine ⟨hG.1, hG.2.trans ?_⟩
  norm_num [d]

/-- The open right half-plane is open. -/
theorem isOpen_re_pos : IsOpen {z : ℂ | 0 < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem RA_nondeg : RA.Nondeg := by
  unfold QRect.Nondeg RA
  norm_num

theorem RA_closedSet_subset : RA.closedSet ⊆ {z : ℂ | 0 < z.re} :=
  QRect.closedSet_subset_re_pos (by unfold RA; norm_num)

/-- Every zero of `E_3(·; G)` with `Re z ≥ 9/200` lies in `R_A` (Lemma A.2). -/
theorem mem_RA_of_zero {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {G : ℝ}
    (hG : G ∈ Set.Icc (0 : ℝ) d) {z : ℂ} (hre : 9 / 200 ≤ z.re) (h0 : evans χ 3 z G = 0) :
    z ∈ RA.closedSet := by
  obtain ⟨h1, h2, h3⟩ := AppA.apriori_zero_mem_RA hχ hG hre h0
  rw [QRect.mem_closedSet]
  simp only [RA]
  push_cast
  refine ⟨hre, ?_, ?_, ?_⟩ <;> linarith

end NPrimeNAux

open NPrimeNAux

/-- **Lemma A.6, first part**: (N1′) implies (N1). -/
theorem N1_of_N1' {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (h : N1' χ) : N1 χ := by
  intro G hG
  have hGd := mem_Icc_d_of_mem hG
  obtain ⟨z₀, hz₀, hf0, hd0, huniq⟩ :=
    argument_principle_rect_one (f := fun z => evans χ 3 z G) RA_nondeg isOpen_re_pos
      RA_closedSet_subset (evans_differentiableOn χ hχ 3 G) (h G hGd)
  rw [QRect.mem_openSet] at hz₀
  have hre : (9 / 200 : ℝ) < z₀.re := by
    have := hz₀.1
    simp only [RA] at this
    push_cast at this
    exact this
  refine ⟨z₀, hre.le, hf0, hd0, fun z hz hz0 => huniq z (mem_RA_of_zero hχ hGd hz hz0) hz0⟩

/-- **Lemma A.6, second part**: (N1) and (N2′) imply (N2). -/
theorem N2_of_N1_N2' {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (h1 : N1 χ) (h2 : N2' χ) :
    N2 χ := by
  intro G hG z hz1 hz2 hz0
  have hGd := mem_Icc_d_of_mem hG
  obtain ⟨cells, hcov, hrect, hwind⟩ := h2
  obtain ⟨c, hc, hGc⟩ := hcov G hGd
  have hok := hrect c hc
  have hx₀ : (c.rect.x₀ : ℝ) = 211 / 2500 := by
    rw [hok.left]; push_cast; ring
  have hsub : c.rect.closedSet ⊆ {z : ℂ | 0 < z.re} :=
    QRect.closedSet_subset_re_pos (by rw [hok.left]; norm_num)
  obtain ⟨w, hw, hfw, -, -⟩ :=
    argument_principle_rect_one (f := fun z => evans χ 3 z G) hok.nondeg isOpen_re_pos hsub
      (evans_differentiableOn χ hχ 3 G) (hwind c hc G hGc hGd)
  rw [QRect.mem_openSet, hx₀] at hw
  obtain ⟨z₀, -, -, -, huniq⟩ := h1 G hG
  have hwz : w = z₀ := huniq w (by linarith [hw.1]) hfw
  have hzz : z = z₀ := huniq z hz1 hz0
  have : z.re = w.re := by rw [hwz, hzz]
  linarith [hw.1]

/-- **Lemma A.6**: (N1′) and (N2′) imply (N1) and (N2). -/
theorem N1_N2_of_N1'_N2' {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (h1 : N1' χ) (h2 : N2' χ) :
    N1 χ ∧ N2 χ :=
  ⟨N1_of_N1' hχ h1, N2_of_N1_N2' hχ (N1_of_N1' hχ h1) h2⟩

end NonUniqueEuler
