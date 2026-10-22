import NonUniqueEuler.Defs.Sec3.Paths
import NonUniqueEuler.Defs.Sec3.Solutions
import NonUniqueEuler.Defs.Sec3.Auxiliary
import NonUniqueEuler.Defs.SmoothB.Iteration
import NonUniqueEuler.H.Sec3.RenormAllT.Conservation
import NonUniqueEuler.H.Sec3.RenormAllT.Flux
import NonUniqueEuler.H.Sec3.RenormAllT.Continuity
import NonUniqueEuler.H.Sec3.RenormAllT.Tail
import NonUniqueEuler.H.Sec3.RenormAllT.LqCont
import NonUniqueEuler.I.Infra.Equimeasurable.Lipschitz
import NonUniqueEuler.I.Infra.Equimeasurable.Norms
import NonUniqueEuler.I.Sec3.WeakContRep
import NonUniqueEuler.I.Sec3.VelocityField

/-!
# Proof of `lem:renorm-all-t` (conservation at every time, strong continuity, tail bound)

Proof of the interface `I/Sec3/RenormAllT.lean` (`03_compactness.tex:576-689`): same
declarations, statements copied verbatim.

**Restructured argument** (deviation from the manuscript's proof, `03_compactness.tex:601-656`;
correct, and shorter). With `lem:transport` in its `(a,b) = (2,2)` form (R7), the transport lemma
applies to `ω` itself, so the bounded truncations `U_k = T_k(ω)` and their identification are not
needed:
1. eq:conservation (`H/Sec3/RenormAllT/Conservation.lean`): `lem:weak-cont`(c) for `u = ω` and
   the uniqueness of weakly continuous representatives give `(te)` on `[t₀,T)` with datum `ω(t₀)`;
   `lem:transport`(ii) on `[0,T)` and on `[t₀,T)`, compared at a common good time `t > t₀`, give
   `∫β(ω(t₀)) = ∫β(ω^in)` for every `t₀ ∈ [0,T)` and `β ∈ Lip₀`.
2. Equimeasurability (I-EQM `of_integral_lipO_eq`) and hence equal `L^q` norms
   (`Equimeasurable.eLpNorm_eq`), in place of the monotone convergence with `Υ_{q,k}` and
   `min{1,(z-s)₊/δ}` (which is what I-EQM proves).
3. Strong continuity into `L²` on `[0,T)` (`H/Sec3/RenormAllT/Continuity.lean`): weak continuity
   and `‖ω(t)‖₂ = ‖ω^in‖₂` with `lem:RR` (`radonRiesz_filter`); this replaces the Cauchy argument
   for `ω(t_j)` in `L¹(B_R)` through `U_k`.
4. eq:tail (`H/Sec3/RenormAllT/Tail.lean`) exactly as in the manuscript (`|ω|`, `lem:weak-cont`(b)
   with `ψ = ς_R`), the identification of the representative of `|ω|` with `|ω(t)|` using step 3.
5. `C([0,T);L^q)`, `q ∈ [1,2)` (`H/Sec3/RenormAllT/LqCont.lean`): `L²` continuity plus the uniform
   tails give `L¹` continuity; interpolation (I-LPINT) gives `q ∈ (1,2)`.
6. The flux bound (`H/Sec3/RenormAllT/Flux.lean`): `lem:velocity`(a) slice-wise and Tonelli.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Weak

namespace RenormAllTH

/-- Equimeasurability at every `t ∈ [0,T)` (from eq:conservation and I-EQM). -/
theorem equimeasurable_of_conservation {T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsRenormalizedWeakSolution 2 T ωin ω) (hc : IsWeakContL2On (Icc 0 T) ω) :
    ∀ t ∈ Ico 0 T, Equimeasurable (ω t) ωin := by
  intro t ht
  obtain ⟨M, hM⟩ := h.toIsWeakSolution.bound_of_isWeakContL2On hc
  exact Equimeasurable.of_integral_lipO_eq (hM t ⟨ht.1, ht.2.le⟩).1 h.datum_memLp_one
    fun β hβ => (conservation h.toIsWeakSolution hc t ht β hβ).2

theorem eLpNorm_two_eq {T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsRenormalizedWeakSolution 2 T ωin ω) (hc : IsWeakContL2On (Icc 0 T) ω) :
    ∀ t ∈ Ico 0 T, eLpNorm (ω t) 2 volume = eLpNorm ωin 2 volume :=
  fun t ht => (equimeasurable_of_conservation h hc t ht).eLpNorm_eq 2

/-- `ω ∈ C([0,T);L²)` (weak continuity, constant norm, `lem:RR`). -/
theorem tendsto_eLpNorm_two {T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsRenormalizedWeakSolution 2 T ωin ω) (hc : IsWeakContL2On (Icc 0 T) ω) :
    ∀ t₀ ∈ Ico 0 T,
      Tendsto (fun t => eLpNorm (ω t - ω t₀) 2 volume) (𝓝[Ico 0 T] t₀) (𝓝 0) :=
  tendsto_eLpNorm_two_of_norm_eq hc (eLpNorm_two_eq h hc)

theorem tail_of_renorm {T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsRenormalizedWeakSolution 2 T ωin ω) (hc : IsWeakContL2On (Icc 0 T) ω) :
    ∀ R : ℝ, 0 < R → ∀ t ∈ Ico 0 T,
      ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖ω t x‖ₑ ≤
        (∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖ωin x‖ₑ) +
          ENNReal.ofReal (Smooth.gradSup sigmaCut / R) *
            ∫⁻ p in slab T, ‖ω p.1 p.2 • velocityField ω p.1 p.2‖ₑ :=
  tail h hc (conservation h.toIsWeakSolution hc) (tendsto_eLpNorm_two h hc)

end RenormAllTH

/-- `lem:renorm-all-t`, eq:conservation (`03_compactness.tex:576-583`): for a renormalized weak
solution in `X₂(T)`, weakly continuous on `[0,T]`, for every `t ∈ [0,T)` and every `Υ ∈ Lip₀`,
`Υ(ω(t))` is integrable and `∫Υ(ω(t)) = ∫Υ(ω^in)`. -/
theorem renormAllT_conservation {T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsRenormalizedWeakSolution 2 T ωin ω) (hc : IsWeakContL2On (Icc 0 T) ω) :
    ∀ t ∈ Ico 0 T, ∀ β : ℝ → ℝ, Equimeas.IsLipO β →
      Integrable (fun x => β (ω t x)) volume ∧ ∫ x, β (ω t x) = ∫ x, β (ωin x) :=
  RenormAllTH.conservation h.toIsWeakSolution hc

/-- `lem:renorm-all-t` (`03_compactness.tex:584-585`): `‖ω(t)‖_{L^q} = ‖ω^in‖_{L^q}` for every
`t ∈ [0,T)` and `q ∈ [1,2]`. -/
theorem renormAllT_eLpNorm_eq {T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsRenormalizedWeakSolution 2 T ωin ω) (hc : IsWeakContL2On (Icc 0 T) ω) :
    ∀ t ∈ Ico 0 T, ∀ q : ℝ, 1 ≤ q → q ≤ 2 →
      eLpNorm (ω t) (ENNReal.ofReal q) volume = eLpNorm ωin (ENNReal.ofReal q) volume :=
  fun t ht _ _ _ => (RenormAllTH.equimeasurable_of_conservation h hc t ht).eLpNorm_eq _

/-- `lem:renorm-all-t` (`03_compactness.tex:585`): `ω(t)` is equimeasurable with `ω^in` for every
`t ∈ [0,T)`. -/
theorem renormAllT_equimeasurable {T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsRenormalizedWeakSolution 2 T ωin ω) (hc : IsWeakContL2On (Icc 0 T) ω) :
    ∀ t ∈ Ico 0 T, Equimeasurable (ω t) ωin :=
  RenormAllTH.equimeasurable_of_conservation h hc

/-- `lem:renorm-all-t` (`03_compactness.tex:586`): `ω ∈ C([0,T);L^q(ℝ²))` for every
`q ∈ [1,2)`. -/
theorem renormAllT_continuousIntoLpOn {T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsRenormalizedWeakSolution 2 T ωin ω) (hc : IsWeakContL2On (Icc 0 T) ω) :
    ∀ q : ℝ, 1 ≤ q → q < 2 → ContinuousIntoLpOn (ENNReal.ofReal q) (Ico 0 T) ω := by
  have hws := h.toIsWeakSolution
  obtain ⟨M, hM⟩ := hws.bound_of_isWeakContL2On hc
  have hm1 : ∀ t ∈ Ico 0 T, MemLp (ω t) 1 volume := fun t ht => (hM t ⟨ht.1, ht.2.le⟩).1
  have hm2 : ∀ t ∈ Ico 0 T, MemLp (ω t) 2 volume := fun t ht => hc.memLp t ⟨ht.1, ht.2.le⟩
  have hΦ : (∫⁻ p in slab T, ‖ω p.1 p.2 • velocityField ω p.1 p.2‖ₑ) ≠ ⊤ :=
    hws.integrable_smul_velocityField.2.ne
  have hL1 := RenormAllTH.tendsto_eLpNorm_one hm2 hws.datum_memLp_one hΦ
    (RenormAllTH.tendsto_eLpNorm_two h hc) (RenormAllTH.tail_of_renorm h hc)
  exact RenormAllTH.continuousIntoLpOn_of_one_two (RenormAllTH.datum_memLp_two hws).eLpNorm_ne_top
    hm1 hm2 (fun t ht => (RenormAllTH.eLpNorm_two_eq h hc t ht).le) hL1

/-- `lem:renorm-all-t`, the flux bound after eq:tail (`03_compactness.tex:592-593`, `:597-600`;
`C_v = C(2,1)` of `lem:velocity`(a), `:37-41`): there is `C_v > 0` such that for every weak
solution in `X₂(T)`, weakly continuous on `[0,T]`, with `‖ω(t)‖_{L¹∩L²} ≤ M` on `[0,T]`,
`‖ωv‖_{L¹((0,T)×ℝ²)} ≤ C_v T M²`. -/
theorem renormAllT_flux_bound :
    ∃ Cv : ℝ, 0 < Cv ∧ ∀ (T M : ℝ) (ωin : ℂ → ℝ) (ω : ℝ → ℂ → ℝ),
      IsWeakSolution 2 T ωin ω → IsWeakContL2On (Icc 0 T) ω →
      (∀ t ∈ Icc 0 T, normL1LpE 2 (ω t) ≤ ENNReal.ofReal M) →
      ∫⁻ p in slab T, ‖ω p.1 p.2 • velocityField ω p.1 p.2‖ₑ ≤
        ENNReal.ofReal (Cv * T * M ^ 2) :=
  RenormAllTH.flux_bound

/-- `lem:renorm-all-t`, eq:tail (`03_compactness.tex:587-592`): for every `R > 0` and
`t ∈ [0,T)`,
`∫_{|x|≥2R}|ω(t)| ≤ ∫_{|x|≥R}|ω^in| + (‖∇ς‖_∞/R) ‖ωv‖_{L¹((0,T)×ℝ²)}`. -/
theorem renormAllT_tail {T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsRenormalizedWeakSolution 2 T ωin ω) (hc : IsWeakContL2On (Icc 0 T) ω) :
    ∀ R : ℝ, 0 < R → ∀ t ∈ Ico 0 T,
      ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖ω t x‖ₑ ≤
        (∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖ωin x‖ₑ) +
          ENNReal.ofReal (Smooth.gradSup sigmaCut / R) *
            ∫⁻ p in slab T, ‖ω p.1 p.2 • velocityField ω p.1 p.2‖ₑ :=
  RenormAllTH.tail_of_renorm h hc

end NonUniqueEuler.Weak
