import NonUniqueEuler.H.Sec5.Energy.ToY
import NonUniqueEuler.I.Sec5.Bilinear
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.Sobolev.Leibniz
import NonUniqueEuler.I.Infra.Sobolev.Smooth

/-!
# Helpers for `lem:energy`: the transport term and the ring `Φ`

Helper of `P/Sec5/Energy.lean`.
* `EnergyH.weakPartialOn_ae_eq`: for `F ∈ H^s` and `V` open, the local weak derivative
  `∂^γ F` on `V` is the global one a.e. on `V`;
* `EnergyH.abs_re_inner_dotGrad_le`: **the transport bound** of `05_single_ring.tex:345-350`:
  for real `U ∈ W^{1,∞}(N₁) ∩ H^s(N₁)` with `div U = 0` on `N₁` and `v ∈ H^{s+1}` supported in
  `N`, `|Re ⟪v, U·∇v⟫_{H^s}| ≤ n_s C_HK (‖U‖_{W^{1,∞}(N₁)} + ‖U‖_{H^s(N₁)}) ‖v‖²_{H^s}`, from
  `lem:Hk-calculus`(1) (`CP_isHkCalcConst`) summed over `|α| ≤ s`;
* `EnergyH.memXFn_PhiC`: `Φ ∈ X^k` for every `k` (`lem:ring-facts`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate

namespace NonUniqueEuler.OneRing.EnergyH

open Sect Sob RingData

/-- The local weak derivative of an `H^s` function on an open set is its global weak derivative
(a.e. on the set). -/
theorem weakPartialOn_ae_eq {s : ℕ} {F : ℂ → ℂ} (hF : MemH s F) {V : Set ℂ} (hV : IsOpen V)
    {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx s) :
    ∀ᵐ x ∂(volume : Measure ℂ), x ∈ V → weakPartialOn V γ F x = weakPartial γ F x := by
  obtain ⟨hL, hW⟩ := hF.memLp_weakPartial hγ
  have hloc : LocallyIntegrableOn (weakPartial γ F) V :=
    (hL.locallyIntegrable (by norm_num)).locallyIntegrableOn V
  exact weakDerivOn_ae_eq hV hloc (hW.mono (subset_univ V))

theorem annN_subset_annN1 : annN ⊆ annN1 := exists_chiN.choose_spec.subset

/-- **The transport bound** (`05_single_ring.tex:345-350`, `lem:Hk-calculus`(1) summed over
`|α| ≤ s`). -/
theorem abs_re_inner_dotGrad_le {s : ℕ} (hs : 3 ≤ s) {v U : ℂ → ℂ} (hv : MemH (s + 1) v)
    (hvN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → v x = 0) (hU1 : MemW1infOn annN1 U)
    (hU2 : MemHOn s annN1 U) (hdiv : ∀ᵐ x ∂(volume.restrict annN1), weakDivOn annN1 U x = 0)
    (hD : MemH s (dotGrad U v)) (hDN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → dotGrad U v x = 0) :
    |(inner ℂ (toY s annN v) (toY s annN (dotGrad U v))).re| ≤
      nIdx s * CHK s * (normW1infOn annN1 U + normHOn s annN1 U) * normH s v ^ 2 := by
  have hcalc : IsHkCommConst s annN annN1 (CP s) := by
    have h := (CP_isHkCalcConst s).1
    rwa [max_eq_left hs] at h
  have hKm : MeasurableSet annN := (isClosed_closedAnnulus _ _).measurableSet
  have hvs : MemH s v := hv.mono_order (Nat.le_succ s)
  rw [inner_toY hKm hvs hvN hD hDN, Complex.re_sum]
  set A := normW1infOn annN1 U + normHOn s annN1 U with hA
  have hterm : ∀ γ : SobIdx s,
      |(Prelim.innerL2 (weakPartial γ.1 (dotGrad U v)) (weakPartial γ.1 v)).re| ≤
        CP s * A * normH s v ^ 2 := by
    intro γ
    have hb := ((hcalc v U hv hvN hU1 hU2 γ.1 γ.2).2.2.2 hdiv).1
    have heq : Prelim.innerL2 (weakPartial γ.1 (dotGrad U v)) (weakPartial γ.1 v) =
        Prelim.innerL2 (annN1.indicator (weakPartialOn annN1 γ.1 (dotGrad U v)))
          (weakPartial γ.1 v) := by
      unfold Prelim.innerL2
      refine integral_congr_ae ?_
      filter_upwards [weakPartialOn_ae_eq hD isOpen_annN1 γ.2,
        hvs.weakPartial_eq_zero_outside (isClosed_closedAnnulus _ _) hvN γ.2] with x h1 h2
      by_cases hx : x ∈ annN1
      · rw [indicator_of_mem hx, h1 hx]
      · have hxN : x ∉ annN := fun h => hx (annN_subset_annN1 h)
        rw [h2 hxN]
        simp
    rw [heq]
    exact hb
  calc |∑ γ : SobIdx s, (Prelim.innerL2 (weakPartial γ.1 (dotGrad U v)) (weakPartial γ.1 v)).re|
      ≤ ∑ γ : SobIdx s, |(Prelim.innerL2 (weakPartial γ.1 (dotGrad U v))
          (weakPartial γ.1 v)).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _γ : SobIdx s, CP s * A * normH s v ^ 2 := Finset.sum_le_sum fun γ _ => hterm γ
    _ = nIdx s * CHK s * A * normH s v ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe, CHK_eq, nIdx]
      ring

/-- **`Φ ∈ X^k`** for every `k` (`lem:ring-facts`: `Φ ∈ C_c^∞` is radial with
`supp Φ ⊆ {a ≤ |y| ≤ 1} ⊆ N`). -/
theorem memXFn_PhiC {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (k : ℕ) : Lin.MemXFn k (PhiC χ) := by
  obtain ⟨hsm, hcs, hrad, -, -, hts, ha, -⟩ := ringFacts_of_admissible hχ
  have hsm' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (PhiC χ) := Complex.ofRealCLM.contDiff.comp hsm
  have hcs' : HasCompactSupport (PhiC χ) := hcs.comp_left Complex.ofReal_zero
  refine ⟨(memH_of_contDiff_hasCompactSupport hsm' hcs' k).1, ?_, ?_⟩
  · refine Eventually.of_forall fun x hx => ?_
    have hxt : x ∉ tsupport (ringPhi χ) := by
      intro h
      obtain ⟨h1, h2⟩ := hts h
      exact hx ⟨by linarith, by linarith⟩
    simp [PhiC, image_eq_zero_of_notMem_tsupport hxt]
  · exact Eventually.of_forall fun x => by simp [PhiC, hrad _ x]

end NonUniqueEuler.OneRing.EnergyH
