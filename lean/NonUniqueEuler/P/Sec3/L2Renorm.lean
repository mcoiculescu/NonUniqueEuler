import NonUniqueEuler.Defs.Sec2.Spaces
import NonUniqueEuler.I.Sec3.Transport
import NonUniqueEuler.I.Sec3.WeakCont
import NonUniqueEuler.I.Sec3.VelocityField
import NonUniqueEuler.I.Infra.Equimeasurable.Lipschitz

/-!
# Proof: `cor:L2-renorm` (weak solutions in `L^∞(0,T;L²)` are renormalized)

Proof of `I/Sec3/L2Renorm.lean` (`03_compactness.tex:549-574`).

**Proof.** `ω ∈ L^∞(0,T;L¹)` by `memX_iff`, `ω ∈ L^∞(0,T;L²)` by hypothesis; the field
`v = K∗ω` is in `L^∞(0,T;W^{1,2}_loc)` and divergence-free
(`isBddH1DivFreeField_velocityField`); `ωv ∈ L¹((0,T)×ℝ²)`
(`integrable_smul_velocityField`); `ω^in ∈ L¹`, and `ω^in ∈ L²` by `weakCont` (`b = 2`, with
`w = v ∈ L^∞(0,T;L²(B_R))`, `memLinfLp_velocityField`, and the datum `ω^in ∈ L¹ ⊂ L¹_loc`).
`transport_renorm` with `t₀ = 0` then gives `(te)` for `Υ(ω)` with datum `Υ(ω^in)` for every
`Υ ∈ Lip₀`, in particular for every renormalization (`IsRenormalization.isLipO`); this is
`(renorm)` (`solvesTE_zero_iff`).

**Deviation (D9).** The manuscript obtains `ω^in ∈ L²` from the weakly continuous representative
of `ω` in `L^q` (`lem:weak-cont` with `b = q`, `03_compactness.tex:563-570`). Here
`lem:weak-cont` with `b = 2`, stated for a locally integrable datum and concluding `u₀ ∈ L²`
(`I/Sec3/WeakCont.lean`), is applied with `u = ω`, `w = v`, `u₀ = ω^in`.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.Weak

/-- An essential bound for `‖u(t)‖_{L²}` in the form required by `weakCont`, extracted from
`u ∈ L^∞(I;L²)`. -/
private theorem exists_nonneg_ae_eLpNorm_two_le {I : Set ℝ} {u : ℝ → ℂ → ℝ}
    (hu : Prelim.MemLinfLp I univ 2 u) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ᵐ t ∂(volume.restrict I), eLpNorm (u t) 2 volume ≤ ENNReal.ofReal N := by
  obtain ⟨M, hM⟩ := hu.essBounded
  refine ⟨max M 0, le_max_right M 0, hM.mono fun t ht => ?_⟩
  rw [Measure.restrict_univ] at ht
  obtain ⟨hmem, hle⟩ := ht
  calc eLpNorm (u t) 2 volume = ENNReal.ofReal (eLpNorm (u t) 2 volume).toReal :=
        (ENNReal.ofReal_toReal hmem.eLpNorm_ne_top).symm
    _ ≤ ENNReal.ofReal (max M 0) := ENNReal.ofReal_le_ofReal (hle.trans (le_max_left M 0))

/-- `cor:L2-renorm` (`03_compactness.tex:549-554`): a weak solution in `X_q(T)`, `4/3 < q < ∞`,
with `ω ∈ L^∞(0,T;L²)` is a renormalized weak solution. -/
theorem _root_.NonUniqueEuler.IsWeakSolution.isRenormalized_of_memLinfLp_two {q T : ℝ}
    {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ} (h : IsWeakSolution q T ωin ω)
    (h2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 ω) :
    IsRenormalizedWeakSolution q T ωin ω := by
  have hT : 0 < T := h.T_pos
  -- `ω ∈ L^∞(0,T;L¹)`
  have h1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 ω := (Prelim.memX_iff.1 h.memX).1
  -- the field `v = K ∗ ω`
  have hw : IsBddH1DivFreeField (Ioo 0 T) (velocityField ω) :=
    isBddH1DivFreeField_velocityField h1 h2
  have huw := h.integrable_smul_velocityField
  have hte : SolvesTE 0 T ω (velocityField ω) ωin := h.solvesTE
  -- the datum: `ω^in ∈ L¹`, and `ω^in ∈ L²` by `lem:weak-cont` (`b = 2`)
  have hin1 : MemLp ωin 1 volume := h.datum_memLp_one
  have hinloc : LocallyIntegrable ωin volume :=
    (memLp_one_iff_integrable.1 hin1).locallyIntegrable
  obtain ⟨N, hN0, hN⟩ := exists_nonneg_ae_eLpNorm_two_le h2
  have hwR : ∀ R : ℝ, 0 < R →
      Prelim.MemLinfLp (Ioo 0 T) (Metric.ball (0 : ℂ) R) 2 (velocityField ω) :=
    fun R hR => (h.memLinfLp_velocityField hR).1
  obtain ⟨_, _, _, _, _, hin2, -⟩ := weakCont hT hN0 hwR h2 hinloc hte hN
  -- `lem:transport`(i) with `t₀ = 0`, `a = b = 2`
  have hren := transport_renorm hT ⟨le_rfl, hT⟩ hw h1 h2 huw hin1 hin2 hte
  exact ⟨h, fun Υ hΥ => solvesTE_zero_iff.1 (hren Υ hΥ.isLipO)⟩

end NonUniqueEuler.Weak
