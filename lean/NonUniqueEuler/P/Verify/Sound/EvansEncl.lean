import NonUniqueEuler.Defs.Verify.Encl
import NonUniqueEuler.I.Verify.Sound.Grid
import NonUniqueEuler.I.Verify.Sound.MidStep
import NonUniqueEuler.I.Verify.Sound.EndBoxes
import NonUniqueEuler.I.Evans.ODE

/-!
# Proof: Proposition A.3 (`prop:enclosure`), the soundness of `evansEncl`

Proof of the interface `I/Verify/Sound/EvansEncl.lean` (same declarations, same statements).

**Manuscript.** Proposition A.3 and its proof (`A_verification.tex:339-455`).

The proof is an assembly of the stage lemmas: unfold `evansEncl`, split its guards, and chain
* `evansEncl_re_pos` (`Re λ > 0`), `exists_global_evansSolution` (`I/Evans/ODE`);
* `eps_sound`, `UB.leDy_sound` (the end-region tolerance `ε ∈ [ε_end, 1]`);
* `leftEnd_mem` (`I/Verify/Sound/EndBoxes`), step (ii);
* `midLoop_sound` (`I/Verify/Sound/MidStep`), step (iii);
* `rightEnd_mem` (`I/Verify/Sound/EndBoxes`), step (iv).
For the grids of the code, `grid_sound` (`I/Verify/Sound/Grid`) supplies `GridSound`.
-/

noncomputable section

open Set

namespace NonUniqueEuler.Verify

open AppA RingData

/-- An upper bound passes `UB.leDy` only if it is finite (`leDy` is `false` on `inf`). -/
private theorem isFin_of_leDy_evansEncl {U : UB} {c : Dy} (h : U.leDy c = true) :
    U.isFin = true := by
  cases U with
  | inf => simp [UB.leDy] at h
  | fin m e => rfl

/-- **Proposition A.3** for a sound grid: if `evansEncl` returns a box `B` for the `λ`-box `lam`
and the `G`-ball `Gb`, then `B` contains `E_ℓ(λ; G)` for every `λ ∈ lam` and every real
`G ∈ Gb`. -/
theorem evansEncl_sound_of_gridSound {p ℓ : ℕ} (hℓ : 1 ≤ ℓ) {χ : ℝ → ℝ}
    (hχ : IsAdmissibleCutoff χ) {gr : Grid} (hgr : GridSound χ gr) (hN : 1 ≤ gr.N)
    {lam B : CBox} {Gb : Ball} (h : evansEncl p gr ℓ lam Gb = some B) {z : ℂ} (hz : z ∈ lam)
    {G : ℝ} (hG : G ∈ Gb) : evans χ ℓ z G ∈ B := by
  have hz0 : 0 < z.re := evansEncl_re_pos h hz
  obtain ⟨ψ, hψ, hode, -, -, hsol, -⟩ := exists_global_evansSolution χ hχ ℓ z hz0 G
  unfold evansEncl at h
  split at h
  · simp at h
  · split at h
    · rename_i relo tv hrelo htv
      split at h
      · simp at h
      · rename_i hpos
        dsimp only at h
        split at h
        · simp at h
        · rename_i hle
          split at h
          · simp at h
          · rename_i psi dpsi hmid
            split at h
            · cases h
              have hle' : ((UB.ofDyUp tv).div (UB.ofDyExact relo)).leDy Dy.one = true := by
                simpa using hle
              have hposT : relo.isPos = true := by simpa using hpos
              have hfinε := isFin_of_leDy_evansEncl hle'
              have hε := eps_sound htv hposT (Ball.lower?_le hrelo hz.1) hfinε
              have hε1 : ((UB.ofDyUp tv).div (UB.ofDyExact relo)).toReal ≤ 1 := by
                have := UB.leDy_sound (UB.bounds_of_isFin hfinε le_rfl) hle'
                rwa [Dy.toReal_one] at this
              obtain ⟨hl1, hl2⟩ := leftEnd_mem (p := p) hℓ hχ hz0 hsol hfinε hε hε1
                (mem_expPoint_endL p ℓ)
              obtain ⟨hm1, hm2⟩ := midLoop_sound hχ hℓ hN hz hz0 hG hψ hode gr.steps ξa _ _
                (psi, dpsi) hgr.chain hgr.steps hl1 hl2 hmid
              exact rightEnd_mem hℓ hχ hz0 hsol hfinε hε hε1 (mem_expPoint_endR p ℓ)
                (mem_expPoint_nrm p ℓ) hm1 hm2
            · simp at h
    · simp at h

/-- **Proposition A.3** (`prop:enclosure`): if `evansEncl` on the grid `Grid.build q hpow N`
(`N ≥ 1`) returns a box `B` for the `λ`-box `lam` and the `G`-ball `Gb`, then
`E_ℓ(λ; G) ∈ B` for every `λ ∈ lam`, every real `G ∈ Gb` and every admissible cutoff `χ`. -/
theorem evansEncl_sound {p q hpow N ℓ : ℕ} (hN : 1 ≤ N) (hℓ : 1 ≤ ℓ) {χ : ℝ → ℝ}
    (hχ : IsAdmissibleCutoff χ) {lam B : CBox} {Gb : Ball}
    (h : evansEncl p (Grid.build q hpow N) ℓ lam Gb = some B) {z : ℂ} (hz : z ∈ lam) {G : ℝ}
    (hG : G ∈ Gb) : evans χ ℓ z G ∈ B :=
  evansEncl_sound_of_gridSound hℓ hχ (grid_sound hχ (evansEncl_grid_ok h))
    (by rw [Grid.build_N]; exact hN) h hz hG

end NonUniqueEuler.Verify
