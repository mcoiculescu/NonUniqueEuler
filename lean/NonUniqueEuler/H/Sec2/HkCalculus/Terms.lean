import NonUniqueEuler.H.Sec2.HkCalculus.Basic

/-!
# Helper for `P/Sec2/HkCalculus`: bounds on the terms of the Leibniz formulas

* `prodTerm_bound` (proof of `lem:Hk-calculus`(2), `02_prelim.tex:675-685`): for `j ≥ 2`,
  `g, h ∈ H^j`, `|γ| ≤ j`, `β ≤ γ`: `‖∂^β g ∂^{γ-β} h‖_{L²} ≤ ‖g‖_{H^j} ‖h‖_{H^j}` (end terms by
  (E2), middle terms by Hölder and (E1));
* `commTerm_bound` (proof of `lem:Hk-calculus`(1), `02_prelim.tex:716-731`): for `k ≥ 3`,
  `G ∈ H^k` with first derivatives bounded by `M` in `L^∞`, `w ∈ H^{k+1}`, `|α| ≤ k`,
  `0 < β ≤ α`, `|e| = 1`: `‖∂^β G ∂^{α-β} ∂_e w‖_{L²} ≤ (M + ‖G‖_{H^k}) ‖w‖_{H^k}`
  (`|β| = 1`: `L^∞`; `|β| = |α| ≥ 2`: (E2) on `∂_e w`; otherwise Hölder and (E1)).

Note: a copy of these lemmas in another file (e.g. for `I/Sec2/HkCalculus/ProductLeibniz.lean`)
must change the namespace `HkCalcAux` (and the instance names), otherwise the
full library declares the same names twice.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Sob.HkCalcAux

theorem prodTerm_bound {j : ℕ} (hj : 2 ≤ j) {g h : ℂ → ℂ} (hg : MemH j g) (hh : MemH j h)
    {γ β : ℕ × ℕ} (hγ : γ ∈ multiIdx j) (hβ : β ∈ leIdx γ) :
    MemLp (fun x => weakPartial β g x * weakPartial (γ.1 - β.1, γ.2 - β.2) h x) 2 volume ∧
      l2 (fun x => weakPartial β g x * weakPartial (γ.1 - β.1, γ.2 - β.2) h x) ≤
        normH j g * normH j h := by
  rw [mem_multiIdx] at hγ
  rw [mem_leIdx] at hβ
  have hgn := normH_nonneg j g
  have hhn := normH_nonneg j h
  by_cases hb : β.1 + β.2 = 0
  · -- `β = 0`: (E2) on `∂^β g`
    have hg2 : MemH (2 + (β.1 + β.2)) g := hg.mono_order (by omega)
    obtain ⟨h1, h2⟩ := MemH.weakPartial (k := 2) (γ := β) hg2
    have h3 : normH (2 + (β.1 + β.2)) g ≤ normH j g := hg.normH_mono (by omega)
    have hγβ : (γ.1 - β.1, γ.2 - β.2) ∈ multiIdx j := mem_multiIdx.2 (by simp only; omega)
    obtain ⟨h4, -⟩ := hh.memLp_weakPartial hγβ
    have h5 := hh.l2_weakPartial_le hγβ
    obtain ⟨h6, h7⟩ := l2_mul_le_of_H2_left h1 h4
    refine ⟨h6, h7.trans ?_⟩
    exact mul_le_mul (h2.trans h3) h5 (l2_nonneg _) hgn
  by_cases hc : (γ.1 - β.1) + (γ.2 - β.2) = 0
  · -- `β = γ`: (E2) on `∂^{γ-β} h`
    have hh2 : MemH (2 + ((γ.1 - β.1, γ.2 - β.2).1 + (γ.1 - β.1, γ.2 - β.2).2)) h :=
      hh.mono_order (by simp only; omega)
    obtain ⟨h1, h2⟩ := MemH.weakPartial (k := 2) (γ := (γ.1 - β.1, γ.2 - β.2)) hh2
    have h3 : normH (2 + ((γ.1 - β.1, γ.2 - β.2).1 + (γ.1 - β.1, γ.2 - β.2).2)) h ≤
        normH j h := hh.normH_mono (by simp only; omega)
    have hβ' : β ∈ multiIdx j := mem_multiIdx.2 (by omega)
    obtain ⟨h4, -⟩ := hg.memLp_weakPartial hβ'
    have h5 := hg.l2_weakPartial_le hβ'
    obtain ⟨h6, h7⟩ := l2_mul_le_of_H2_right h4 h1
    refine ⟨h6, h7.trans ?_⟩
    exact mul_le_mul h5 (h2.trans h3) (normH_nonneg _ _) hgn
  · -- middle terms: Hölder and (E1)
    have hg1 : MemH (1 + (β.1 + β.2)) g := hg.mono_order (by omega)
    obtain ⟨h1, h2⟩ := MemH.weakPartial (k := 1) (γ := β) hg1
    have h3 : normH (1 + (β.1 + β.2)) g ≤ normH j g := hg.normH_mono (by omega)
    have hh1 : MemH (1 + ((γ.1 - β.1, γ.2 - β.2).1 + (γ.1 - β.1, γ.2 - β.2).2)) h :=
      hh.mono_order (by simp only; omega)
    obtain ⟨h4, h5⟩ := MemH.weakPartial (k := 1) (γ := (γ.1 - β.1, γ.2 - β.2)) hh1
    have h6 : normH (1 + ((γ.1 - β.1, γ.2 - β.2).1 + (γ.1 - β.1, γ.2 - β.2).2)) h ≤
        normH j h := hh.normH_mono (by simp only; omega)
    obtain ⟨h7, h8⟩ := l2_mul_le_of_H1 h1 h4
    refine ⟨h7, h8.trans ?_⟩
    exact mul_le_mul (h2.trans h3) (h5.trans h6) (normH_nonneg _ _) hgn

theorem commTerm_bound {k : ℕ} (hk : 3 ≤ k) {G w : ℂ → ℂ} (hG : MemH k G) {M : ℝ}
    (hM : 0 ≤ M)
    (hGinf : ∀ β : ℕ × ℕ, β.1 + β.2 = 1 → eLpNorm (weakPartial β G) ⊤ volume ≤ ENNReal.ofReal M)
    (hw : MemH (k + 1) w) {e : ℕ × ℕ} (he : e.1 + e.2 = 1) {α β : ℕ × ℕ}
    (hα : α ∈ multiIdx k) (hβ : β ∈ leIdx α) (hβ0 : β ≠ (0, 0)) :
    MemLp (fun x => weakPartial β G x *
        weakPartial (α.1 - β.1, α.2 - β.2) (weakPartial e w) x) 2 volume ∧
      l2 (fun x => weakPartial β G x *
        weakPartial (α.1 - β.1, α.2 - β.2) (weakPartial e w) x) ≤
        (M + normH k G) * normH k w := by
  rw [mem_multiIdx] at hα
  rw [mem_leIdx] at hβ
  have hb1 : 1 ≤ β.1 + β.2 := by
    by_contra hcon
    exact hβ0 (Prod.ext (by simp only; omega) (by simp only; omega))
  have hGn := normH_nonneg k G
  have hwk : MemH k w := hw.mono_order (by omega)
  have hwn := normH_nonneg k w
  set δ : ℕ × ℕ := (α.1 - β.1, α.2 - β.2) with hδ
  have hδ1 : δ.1 = α.1 - β.1 := rfl
  have hδ2 : δ.2 = α.2 - β.2 := rfl
  by_cases hb : β.1 + β.2 = 1
  · -- `|β| = 1`: `L^∞` bound on `∂^β G`
    have hβk : β ∈ multiIdx k := mem_multiIdx.2 (by omega)
    obtain ⟨h1, -⟩ := hG.memLp_weakPartial hβk
    have hwF : MemH (0 + (δ.1 + δ.2) + (e.1 + e.2)) w := hw.mono_order (by omega)
    obtain ⟨h2, h3⟩ := memH_weakPartial_weakPartial hwF
    have h4 : normH (0 + (δ.1 + δ.2) + (e.1 + e.2)) w ≤ normH k w :=
      hwk.normH_mono (by omega)
    obtain ⟨h5, h6⟩ := l2_mul_le_of_top h1.1 hM (hGinf β hb) (memLp_of_memH h2)
    refine ⟨h5, h6.trans ?_⟩
    have h7 := h2.l2_le
    calc M * l2 (weakPartial δ (weakPartial e w)) ≤ M * normH k w :=
          mul_le_mul_of_nonneg_left (h7.trans (h3.trans h4)) hM
      _ ≤ (M + normH k G) * normH k w := by nlinarith
  by_cases hc : δ.1 + δ.2 = 0
  · -- `|β| = |α| ≥ 2`: (E2) on `∂_e w`
    have hβk : β ∈ multiIdx k := mem_multiIdx.2 (by omega)
    obtain ⟨h1, -⟩ := hG.memLp_weakPartial hβk
    have h1' := hG.l2_weakPartial_le hβk
    have hwF : MemH (2 + (δ.1 + δ.2) + (e.1 + e.2)) w := hw.mono_order (by omega)
    obtain ⟨h2, h3⟩ := memH_weakPartial_weakPartial hwF
    have h4 : normH (2 + (δ.1 + δ.2) + (e.1 + e.2)) w ≤ normH k w :=
      hwk.normH_mono (by omega)
    obtain ⟨h5, h6⟩ := l2_mul_le_of_H2_right h1 h2
    refine ⟨h5, h6.trans ?_⟩
    calc l2 (weakPartial β G) * normH 2 (weakPartial δ (weakPartial e w)) ≤
          normH k G * normH k w :=
          mul_le_mul h1' (h3.trans h4) (normH_nonneg _ _) hGn
      _ ≤ (M + normH k G) * normH k w := by nlinarith
  · -- `2 ≤ |β| ≤ |α| - 1`: Hölder and (E1)
    have hG1 : MemH (1 + (β.1 + β.2)) G := hG.mono_order (by omega)
    obtain ⟨h1, h2⟩ := MemH.weakPartial (k := 1) (γ := β) hG1
    have h2' : normH (1 + (β.1 + β.2)) G ≤ normH k G := hG.normH_mono (by omega)
    have hwF : MemH (1 + (δ.1 + δ.2) + (e.1 + e.2)) w := hw.mono_order (by omega)
    obtain ⟨h3, h4⟩ := memH_weakPartial_weakPartial hwF
    have h4' : normH (1 + (δ.1 + δ.2) + (e.1 + e.2)) w ≤ normH k w :=
      hwk.normH_mono (by omega)
    obtain ⟨h5, h6⟩ := l2_mul_le_of_H1 h1 h3
    refine ⟨h5, h6.trans ?_⟩
    calc normH 1 (weakPartial β G) * normH 1 (weakPartial δ (weakPartial e w)) ≤
          normH k G * normH k w :=
          mul_le_mul (h2.trans h2') (h4.trans h4') (normH_nonneg _ _) hGn
      _ ≤ (M + normH k G) * normH k w := by nlinarith

end NonUniqueEuler.Sob.HkCalcAux
