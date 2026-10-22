import NonUniqueEuler.Defs.Sec3.Transport
import NonUniqueEuler.Defs.Sec3.Commutator
import NonUniqueEuler.Defs.Sec2.Spaces
import NonUniqueEuler.I.Sec3.LipRenorm
import NonUniqueEuler.H.Sec3.Transport.Renorm
import NonUniqueEuler.H.Sec3.Transport.Conservation

/-!
# Proof: `lem:transport` (renormalization, conservation and uniqueness for `(te)`), `a = b = 2`

Proof of `I/Sec3/Transport.lean` (`03_compactness.tex:463-547`). Same declarations, same
statements.

**(i)** (`transport_renorm`). By `lem:lip-renorm` (`I/Sec3/LipRenorm.lean`) it suffices to treat
renormalizations `Υ` (`C¹`, `Υ'` bounded, `Υ(0) = 0`), under the standing assumptions `IsTEData`
of `(te)` (`TransportH.isTEData_of_transport`: `u ∈ L^∞(0,T;L¹)`, `w ∈ L^∞(0,T;L²(B_R))`,
`uw ∈ L¹`, `u₀ ∈ L¹`). For a renormalization (`TransportH.solvesTE_renormalization`,
`H/Sec3/Transport/Renorm.lean`): the mollified identity
`∫∫Υ(u_ε)(∂_tφ + w·∇φ) + ∫Υ(u₀,ε)φ(t₀) = -∫∫ φΥ'(u_ε)C_ε[u,w]`
(`I/Sec3/Transport/Mollified.lean`) is passed to the limit along `ε_n = 1/(n+1)`
(`H/Sec3/Transport/Limit.lean`): `u_ε(t) → u(t)` in `L²` (`I/Sec3/Transport/MollifyLp.lean`),
and `C_ε[u,w] → 0` in `L¹((t₀,T')×B_R)` (`lem:commutator`, applied on `(-1,T)` to the
extension by `0`, `H/Sec3/Transport/CommSlab.lean`).

**(ii)** (`transport_conservation`, `H/Sec3/Transport/Conservation.lean`). Test (i) with
`α(t)ς_{n+1}(x)`, let `n → ∞` (dominated convergence; the flux term is
`≤ L‖α‖_∞‖∇ς‖_∞ (n+1)⁻¹ ‖uw‖_{L¹}`), and apply `lem:dbr` to `B(t) = ∫β(u(t))`.

**(iii)** (`transport_eq_zero`). (ii) with `β = |·|` gives `∫|u(t)| = ∫|u₀| = 0` for a.e.
`t ∈ (t₀,T)`; Tonelli on the slab.

**Deviations.** The manuscript extends `u, w` to `(t₀-1,T)` and recovers the datum by testing
with `κ₀φ`; here the datum is kept throughout (the mollified identity is derived on `[t₀,T)`
with its datum), and the extension (by `0` below `t = 0`) is used only to apply
`lem:commutator` on an open interval. Exponents `a = b = 2` (R7).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak

/-- `lem:transport`(i) with `a = b = 2` (`03_compactness.tex:463-474`): under the hypotheses of
the lemma, for every `Υ ∈ Lip₀`, `Υ(u)` satisfies `(te)` on `[t₀,T)` with field `w` and datum
`Υ(u₀)`. -/
theorem transport_renorm {T t₀ : ℝ} (hT : 0 < T) (ht₀ : t₀ ∈ Ico 0 T) {w : ℝ → ℂ → ℂ}
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) {u : ℝ → ℂ → ℝ} {u₀ : ℂ → ℝ}
    (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u) (hu2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    (hu₀1 : MemLp u₀ 1 volume) (hu₀2 : MemLp u₀ 2 volume) (hte : SolvesTE t₀ T u w u₀) :
    ∀ β : ℝ → ℝ, Equimeas.IsLipO β →
      SolvesTE t₀ T (fun t x => β (u t x)) w (fun x => β (u₀ x)) :=
  lipRenorm hT ht₀ (TransportH.isTEData_of_transport ht₀ hw hu1 huw hu₀1)
    fun _ hΥ => TransportH.solvesTE_renormalization hT ht₀ hw hu1 hu2 huw hu₀1 hu₀2 hte hΥ

/-- `lem:transport`(ii) with `a = b = 2` (`03_compactness.tex:475-476`): under the hypotheses
of the lemma, for every `Υ ∈ Lip₀` and a.e. `t ∈ (t₀,T)`, `Υ(u(t))` is integrable and
`∫Υ(u(t)) = ∫Υ(u₀)`. -/
theorem transport_conservation {T t₀ : ℝ} (hT : 0 < T) (ht₀ : t₀ ∈ Ico 0 T) {w : ℝ → ℂ → ℂ}
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) {u : ℝ → ℂ → ℝ} {u₀ : ℂ → ℝ}
    (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u) (hu2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    (hu₀1 : MemLp u₀ 1 volume) (hu₀2 : MemLp u₀ 2 volume) (hte : SolvesTE t₀ T u w u₀) :
    ∀ β : ℝ → ℝ, Equimeas.IsLipO β →
      ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)),
        Integrable (fun x => β (u t x)) volume ∧ ∫ x, β (u t x) = ∫ x, β (u₀ x) :=
  fun β hβ => TransportH.conservation_of_solvesTE ht₀ hw hu1 huw hu₀1 hβ
    (transport_renorm hT ht₀ hw hu1 hu2 huw hu₀1 hu₀2 hte β hβ)

/-- `lem:transport`(iii) with `a = b = 2` (`03_compactness.tex:477`): under the hypotheses of
the lemma, if `u₀ = 0` a.e., then `u = 0` a.e. on `(t₀,T) × ℝ²`. -/
theorem transport_eq_zero {T t₀ : ℝ} (hT : 0 < T) (ht₀ : t₀ ∈ Ico 0 T) {w : ℝ → ℂ → ℂ}
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) {u : ℝ → ℂ → ℝ} {u₀ : ℂ → ℝ}
    (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u) (hu2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    (hu₀1 : MemLp u₀ 1 volume) (hu₀2 : MemLp u₀ 2 volume) (hte : SolvesTE t₀ T u w u₀)
    (hzero : u₀ =ᵐ[volume] 0) :
    Function.uncurry u =ᵐ[volume.restrict (slabFrom t₀ T)] 0 := by
  have h := transport_conservation hT ht₀ hw hu1 hu2 huw hu₀1 hu₀2 hte (fun s => |s|)
    Equimeas.isLipO_abs
  have h0 : ∫ x, |u₀ x| = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hzero] with x hx
    simp [hx]
  -- for a.e. `t`, `∫ |u(t)| = 0`
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∫⁻ x, ‖u t x‖ₑ = 0 := by
    filter_upwards [h] with t ⟨hi, he⟩
    rw [h0] at he
    have hz : (fun x => |u t x|) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg _) hi).1 he
    rw [← lintegral_zero (μ := (volume : Measure ℂ))]
    refine lintegral_congr_ae ?_
    filter_upwards [hz] with x hx
    have hx' : u t x = 0 := abs_eq_zero.1 hx
    simp [hx']
  -- Tonelli on the slab
  have hm : AEStronglyMeasurable (Function.uncurry u) (volume.restrict (slabFrom t₀ T)) :=
    hu1.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono (TransportH.slabFrom_subset_prod ht₀.1) le_rfl)
  have hl : ∫⁻ p, ‖Function.uncurry u p‖ₑ ∂(volume.restrict (slabFrom t₀ T)) = 0 := by
    have hm' := hm
    rw [TransportH.restrict_slabFrom_eq_prod] at hm' ⊢
    rw [lintegral_prod _ hm'.enorm, ← lintegral_zero (μ := volume.restrict (Ioo t₀ T))]
    exact lintegral_congr_ae hae
  have hz := (lintegral_eq_zero_iff' hm.enorm).1 hl
  filter_upwards [hz] with p hp
  simpa using hp

end NonUniqueEuler.Weak
