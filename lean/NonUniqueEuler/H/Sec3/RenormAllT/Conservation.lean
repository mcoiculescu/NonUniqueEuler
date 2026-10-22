import NonUniqueEuler.H.Sec3.RenormAllT.Basic
import NonUniqueEuler.I.Sec3.Transport
import NonUniqueEuler.I.Sec3.WeakCont
import NonUniqueEuler.I.Sec3.VelocityField
import NonUniqueEuler.I.Sec3.WeakContRep

/-!
# Helpers for `lem:renorm-all-t`: conservation at every time

Helper file of `P/Sec3/RenormAllT.lean` (fully proved).

Restructured argument (deviation from `03_compactness.tex:601-656`).
With the `(a,b) = (2,2)` version of `lem:transport` (R7), the transport lemma applies to `ω`
itself, so the bounded truncations `U_k` of the manuscript are not needed:

* `solvesTE_restart`: by `lem:weak-cont`(c) (with `u = ω`) and the uniqueness of weakly
  continuous representatives, `ω` satisfies `(te)` on `[t₀,T)` with datum `ω(t₀)`, for every
  `t₀ ∈ [0,T)`;
* `conservation`: `lem:transport`(ii) on `[0,T)` (datum `ω^in`) and on `[t₀,T)` (datum
  `ω(t₀)`), compared at a time `t ∈ (t₀,T)` that is exceptional for neither, gives
  `∫β(ω(t₀)) = ∫β(ω^in)` for every `t₀ ∈ [0,T)` and `β ∈ Lip₀` (eq:conservation; this is
  eq:Uk for `ω` in place of `U_k`).

Only the weak-solution property in `X₂(T)` is used.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Weak.RenormAllTH

/-- `ω` satisfies `(te)` on `[t₀,T)` with field `v` and datum `ω(t₀)` for every `t₀ ∈ [0,T)`
(`lem:weak-cont`(c) and the uniqueness of the weakly continuous representative). -/
theorem solvesTE_restart {T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsWeakSolution 2 T ωin ω) (hc : IsWeakContL2On (Icc 0 T) ω) :
    ∀ t₀ ∈ Ico 0 T, SolvesTE t₀ T ω (velocityField ω) (ω t₀) := by
  have hT := h.T_pos
  obtain ⟨-, h2⟩ := memLinfLp_of_isWeakSolution h
  obtain ⟨N, hN0, hN⟩ := exists_ae_eLpNorm_le h2
  have hw : ∀ R : ℝ, 0 < R → Prelim.MemLinfLp (Ioo 0 T) (ball (0 : ℂ) R) 2 (velocityField ω) :=
    fun R hR => (h.memLinfLp_velocityField hR).1
  have hin : LocallyIntegrable ωin volume :=
    (memLp_one_iff_integrable.1 h.datum_memLp_one).locallyIntegrable
  obtain ⟨ũ, -, hũc, -, hũae, -, -, -, -, -, -, hres⟩ :=
    weakCont hT hN0 hw h2 hin h.solvesTE hN
  have hrep := ae_eq_of_isWeakContL2On hT hũc hc hũae
  intro t₀ ht₀
  exact SolvesTE.congr_datum (hres t₀ ht₀) (hrep t₀ ⟨ht₀.1, ht₀.2.le⟩)

/-- eq:conservation for weak solutions in `X₂(T)` that are weakly continuous on `[0,T]`. -/
theorem conservation {T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsWeakSolution 2 T ωin ω) (hc : IsWeakContL2On (Icc 0 T) ω) :
    ∀ t ∈ Ico 0 T, ∀ β : ℝ → ℝ, Equimeas.IsLipO β →
      Integrable (fun x => β (ω t x)) volume ∧ ∫ x, β (ω t x) = ∫ x, β (ωin x) := by
  have hT := h.T_pos
  obtain ⟨h1, h2⟩ := memLinfLp_of_isWeakSolution h
  have hw := isBddH1DivFreeField_velocityField h1 h2
  have huw := h.integrable_smul_velocityField
  have hin1 := h.datum_memLp_one
  have hin2 := datum_memLp_two h
  obtain ⟨M, hM⟩ := h.bound_of_isWeakContL2On hc
  have hres := solvesTE_restart h hc
  intro t₀ ht₀ β hβ
  have ht₀' : t₀ ∈ Icc 0 T := ⟨ht₀.1, ht₀.2.le⟩
  have hm1 : MemLp (ω t₀) 1 volume := (hM t₀ ht₀').1
  have hm2 : MemLp (ω t₀) 2 volume := hc.memLp t₀ ht₀'
  refine ⟨integrable_comp_of_isLipO hβ hm1, ?_⟩
  have H0 := transport_conservation hT ⟨le_rfl, hT⟩ hw h1 h2 huw hin1 hin2 h.solvesTE β hβ
  have H1 := transport_conservation hT ht₀ hw h1 h2 huw hm1 hm2 (hres t₀ ht₀) β hβ
  have H0' := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left ht₀.1) H0
  have hne : (ae (volume.restrict (Ioo t₀ T))).NeBot := by
    rw [ae_restrict_neBot, Real.volume_Ioo, Ne, ENNReal.ofReal_eq_zero, not_le]
    linarith [ht₀.2]
  obtain ⟨t, ht1, ht0⟩ := (H1.and H0').exists
  rw [← ht1.2, ht0.2]

end NonUniqueEuler.Weak.RenormAllTH
