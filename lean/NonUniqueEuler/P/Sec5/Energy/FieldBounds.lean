import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.Lambda
import NonUniqueEuler.H.Sec5.Energy.FieldBounds.Local
import NonUniqueEuler.H.Sec5.Energy.FieldBounds.Omega
import NonUniqueEuler.H.Sec5.Energy.FieldBounds.Velocity

/-!
# Proof (step of `I/Sec5/Energy`): the transporting field `U` on `N₁`

Proof of `I/Sec5/Energy/FieldBounds.lean` (step 2 of the proof of `lem:energy`,
`05_single_ring.tex:333-346`). Same declaration, statement copied verbatim.

Let `U = Ω(|x|;G)x^⊥ + h + K_BS*Re w` on `N₁`.
1. `Ω(|x|;G)x^⊥`: membership and `‖·‖_{W^{1,∞}(N₁)} + ‖·‖_{H^s(N₁)} ≤ C_Ω` from `lambda_consts`
   (`le_csSup`); divergence free (`FieldBoundsAux.weakDivOn_omegaField`,
   `H/Sec5/Energy/FieldBounds/Omega.lean`).
2. `h`: membership and `‖h‖_{W^{1,∞}(N₁)} + ‖h‖_{H^s(N₁)} ≤ C_{N'}‖h‖_{C^s(N')} ≤ C_{N'}` from
   `lambda_consts` (`IsLeast` of `C_{N'}`); divergence free since `div h = 0` classically on
   `O ⊇ N₁` and `h` is smooth there (`Sob.FieldBoundsAux.weakDivOn_eq_divergence`).
3. `K_BS*Re w`: `‖·‖_{H^s(N₁)} ≤ C^el_s`, `‖·‖_{W^{1,∞}(N₁)} ≤ 3C^el_2 ≤ 6C^el_2`, divergence free
   (`H/Sec5/Energy/FieldBounds/Velocity.lean`).
4. Sums: Minkowski for `‖·‖_{W^{1,∞}(N₁)}`, `‖·‖_{H^s(N₁)}` and additivity of the weak divergence
   (`H/Sec5/Energy/FieldBounds/Local.lean`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- **The field `U = Ω(|x|;G)x^⊥ + h + K_BS*w` on `N₁`** (proof of `lem:energy`,
`05_single_ring.tex:333-346`): `U ∈ W^{1,∞}(N₁) ∩ H^s(N₁)`, `div U = 0` on `N₁`, and
`‖U‖_{W^{1,∞}(N₁)} + ‖U‖_{H^s(N₁)} ≤ A_s`. -/
theorem energy_field (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 3 ≤ s) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {hf : ℂ → ℂ} {O : Set ℂ}
    (hO : IsOpen O) (hNO : annN' ⊆ O) (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) hf O)
    (hdiv : ∀ x ∈ O, Prelim.divergence hf x = 0) (hhf : MemCk s annN' hf)
    (hhf1 : normCk s annN' hf ≤ 1) {w : ℂ → ℂ} (hw : Sob.MemH s w)
    (hwN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → w x = 0) (hw1 : Sob.normH s w ≤ 1) :
    Sob.MemW1infOn annN1 (omegaField χ G + hf + BS.velocityRe w) ∧
      Sob.MemHOn s annN1 (omegaField χ G + hf + BS.velocityRe w) ∧
      (∀ᵐ x ∂(volume.restrict annN1),
        Sob.weakDivOn annN1 (omegaField χ G + hf + BS.velocityRe w) x = 0) ∧
      Sob.normW1infOn annN1 (omegaField χ G + hf + BS.velocityRe w) +
          Sob.normHOn s annN1 (omegaField χ G + hf + BS.velocityRe w) ≤ As χ s := by
  have _unusedO := hO
  obtain ⟨hΩmem, hΩbdd, hCk, hleast, -⟩ := lambda_consts χ hχ hN hs
  -- 1. the background field
  obtain ⟨hΩW, hΩH⟩ := hΩmem G hG
  have hΩle : Sob.normW1infOn annN1 (omegaField χ G) + Sob.normHOn s annN1 (omegaField χ G) ≤
      COmega χ s :=
    le_csSup hΩbdd ⟨G, hG, rfl⟩
  have hdΩ := FieldBoundsAux.weakDivOn_omegaField hχ G
  -- 2. the field `h`
  obtain ⟨hhW, hhH⟩ := hCk hf hhf
  have hhle : Sob.normW1infOn annN1 hf + Sob.normHOn s annN1 hf ≤ CNprime s := by
    have h := hleast.1.2 hf hhf
    have h0 := hleast.1.1
    calc _ ≤ CNprime s * normCk s annN' hf := h
      _ ≤ CNprime s * 1 := mul_le_mul_of_nonneg_left hhf1 h0
      _ = CNprime s := mul_one _
  have hdh : ∀ᵐ x ∂(volume.restrict annN1), Sob.weakDivOn annN1 hf x = 0 := by
    have hc : ContDiffOn ℝ 1 hf annN1 :=
      (hsm.mono (annN1_subset_annN'.trans hNO)).of_le (by exact_mod_cast le_top)
    filter_upwards [Sob.FieldBoundsAux.weakDivOn_eq_divergence isOpen_annN1 hc,
      ae_restrict_mem isOpen_annN1.measurableSet] with x hx hxV
    rw [hx]
    exact hdiv x (hNO (annN1_subset_annN' hxV))
  -- 3. the Biot–Savart field
  obtain ⟨hWH, hWHle⟩ := FieldBoundsAux.velocityRe_memHOn hw hwN hw1
  obtain ⟨hWW, hWWle⟩ := FieldBoundsAux.velocityRe_memW1infOn (by omega) hw hwN hw1
  have hdW := FieldBoundsAux.weakDivOn_velocityRe hw hwN hw1
  -- 4. sums
  obtain ⟨hW1, hW1le⟩ := Sob.FieldBoundsAux.memW1infOn_add isOpen_annN1 hΩW hhW
  obtain ⟨hW2, hW2le⟩ := Sob.FieldBoundsAux.memW1infOn_add isOpen_annN1 hW1 hWW
  obtain ⟨hH1, hH1le⟩ := Sob.FieldBoundsAux.memHOn_add isOpen_annN1 hΩH hhH
  obtain ⟨hH2, hH2le⟩ := Sob.FieldBoundsAux.memHOn_add isOpen_annN1 hH1 hWH
  have hd1 := Sob.FieldBoundsAux.weakDivOn_add isOpen_annN1 hΩW hhW
  have hd2 := Sob.FieldBoundsAux.weakDivOn_add isOpen_annN1 hW1 hWW
  refine ⟨hW2, hH2, ?_, ?_⟩
  · filter_upwards [hd1, hd2, hdΩ, hdh, hdW] with x h1 h2 h3 h4 h5
    rw [h2, h1, h3, h4, h5]
    norm_num
  · have hCel := Cel_pos 2
    unfold As
    linarith

end OneRing

end NonUniqueEuler
