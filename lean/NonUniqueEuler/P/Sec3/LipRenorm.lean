import NonUniqueEuler.Defs.Sec3.Transport
import NonUniqueEuler.H.Sec3.LipRenorm.Steklov
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Proof: `lem:lip-renorm` (renormalization extends from `C¹` to `Lip₀`)

Proof of `I/Sec3/LipRenorm.lean` (`lem:lip-renorm`, `03_compactness.tex:92-118`).

**Argument.** Let `β ∈ Lip₀` with constant `K`. By `exists_seq_isRenormalization_tendsto`
(`H/Sec3/LipRenorm/Steklov.lean`) there are renormalizations `Υ_n` with `|Υ_n(s)| ≤ K|s|` and
`Υ_n → β` pointwise. The identity renormalization gives the integrability of `u(∂_tφ + w·∇φ)`
on the slab and of `u₀ φ(t₀)` (they are conjuncts of `SolvesTE`, decision D5). Then
`|Υ_n(u)(∂_tφ + w·∇φ)| ≤ K|u(∂_tφ + w·∇φ)|`, and dominated convergence passes from the identity
`(te)` for `Υ_n(u)` to the identity for `β(u)`; the same domination gives the integrability of
`β(u)(∂_tφ + w·∇φ)` and `β(u₀)φ(t₀)`.

**Deviation.** The manuscript uses the mollifications `Υ ⋆ ρ^t_{1/j} - (Υ ⋆ ρ^t_{1/j})(0)` and
the uniform bound `|Υ_j - Υ| ≤ 2L/j`, and gets integrability of `Υ(u)` from the standing
assumptions `IsTEData`. We use Steklov averages (which are `C¹`) and dominated convergence with
the dominating function `K |u (∂_tφ + w·∇φ)|`, integrable by `(te)` for `Υ = id`. The standing
assumptions `hdata` (and `hT`, `ht₀`) are therefore not needed: the core statement is
`lipRenorm_core`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace NonUniqueEuler.Weak

namespace LipRenormAux

/-- The identity is a renormalization. -/
theorem isRenormalization_id : IsRenormalization id :=
  ⟨contDiff_id, ⟨1, fun s => by simp⟩, rfl⟩

/-- Dominated convergence in the form used for `(te)`: if `|F_n| ≤ C|G|`, `|f| ≤ C|G|`,
`G` and `F_n` are integrable and `F_n → f` pointwise, then `f` is integrable and
`∫ F_n → ∫ f`. -/
theorem integrable_and_tendsto_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {f G : α → ℝ} {C : ℝ} (hG : Integrable G μ)
    (hF : ∀ n, Integrable (F n) μ) (hFb : ∀ n p, |F n p| ≤ C * |G p|)
    (hfb : ∀ p, |f p| ≤ C * |G p|) (hlim : ∀ p, Tendsto (fun n => F n p) atTop (𝓝 (f p))) :
    Integrable f μ ∧ Tendsto (fun n => ∫ p, F n p ∂μ) atTop (𝓝 (∫ p, f p ∂μ)) := by
  have hbound : Integrable (fun p => C * ‖G p‖) μ := hG.norm.const_mul C
  refine ⟨?_, ?_⟩
  · refine hbound.mono' (aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hF n).1)
      (ae_of_all _ hlim)) (ae_of_all _ fun p => ?_)
    simpa [Real.norm_eq_abs] using hfb p
  · refine tendsto_integral_of_dominated_convergence _ (fun n => (hF n).1) hbound
      (fun n => ae_of_all _ fun p => ?_) (ae_of_all _ hlim)
    simpa [Real.norm_eq_abs] using hFb n p

theorem abs_mul_le_of_abs_le {a b c C : ℝ} (h : |a| ≤ C * |b|) : |a * c| ≤ C * |b * c| := by
  rw [abs_mul, abs_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h (abs_nonneg c)

/-- Passage to the limit in `(te)`: if `u` and every `Υ_n(u)` satisfy `(te)`, `|Υ_n(s)| ≤ C|s|`,
`|β(s)| ≤ C|s|` and `Υ_n → β` pointwise, then `β(u)` satisfies `(te)`. -/
theorem solvesTE_of_tendsto {t₀ T : ℝ} {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {u₀ : ℂ → ℝ}
    (hu : SolvesTE t₀ T u w u₀) {Υ : ℕ → ℝ → ℝ} {β : ℝ → ℝ} {C : ℝ}
    (hΥ : ∀ n, SolvesTE t₀ T (fun t x => Υ n (u t x)) w (fun x => Υ n (u₀ x)))
    (hbound : ∀ n s, |Υ n s| ≤ C * |s|) (hβ : ∀ s, |β s| ≤ C * |s|)
    (hlim : ∀ s, Tendsto (fun n => Υ n s) atTop (𝓝 (β s))) :
    SolvesTE t₀ T (fun t x => β (u t x)) w (fun x => β (u₀ x)) := by
  -- the slab term
  have hS : ∀ φ, IsTestFunction T φ →
      IntegrableOn (transportIntegrand (fun t x => β (u t x)) w φ) (slabFrom t₀ T) ∧
      Tendsto (fun n => ∫ p in slabFrom t₀ T,
          transportIntegrand (fun t x => Υ n (u t x)) w φ p) atTop
        (𝓝 (∫ p in slabFrom t₀ T, transportIntegrand (fun t x => β (u t x)) w φ p)) :=
    fun φ hφ => integrable_and_tendsto_integral (hu.integrableOn φ hφ)
      (fun n => (hΥ n).integrableOn φ hφ)
      (fun n p => abs_mul_le_of_abs_le (hbound n (u p.1 p.2)))
      (fun p => abs_mul_le_of_abs_le (hβ (u p.1 p.2)))
      (fun p => (hlim (u p.1 p.2)).mul_const _)
  -- the datum term
  have hD : ∀ φ, IsTestFunction T φ →
      Integrable (fun x : ℂ => β (u₀ x) * φ (t₀, x)) ∧
      Tendsto (fun n => ∫ x : ℂ, Υ n (u₀ x) * φ (t₀, x)) atTop
        (𝓝 (∫ x : ℂ, β (u₀ x) * φ (t₀, x))) :=
    fun φ hφ => integrable_and_tendsto_integral (hu.datum_integrable φ hφ)
      (fun n => (hΥ n).datum_integrable φ hφ)
      (fun n x => abs_mul_le_of_abs_le (hbound n (u₀ x)))
      (fun x => abs_mul_le_of_abs_le (hβ (u₀ x)))
      (fun x => (hlim (u₀ x)).mul_const _)
  refine ⟨fun φ hφ => (hS φ hφ).1, fun φ hφ => (hD φ hφ).1, fun φ hφ => ?_⟩
  have hzero : ∀ n, (∫ p in slabFrom t₀ T,
      transportIntegrand (fun t x => Υ n (u t x)) w φ p) +
        ∫ x : ℂ, Υ n (u₀ x) * φ (t₀, x) = 0 := fun n => by
    rw [← integral_Ioo_integral_eq ((hΥ n).integrableOn φ hφ)]
    exact (hΥ n).identity φ hφ
  have ht := (hS φ hφ).2.add (hD φ hφ).2
  simp only [hzero] at ht
  rw [integral_Ioo_integral_eq (hS φ hφ).1]
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- `lem:lip-renorm` without the standing assumptions (which are not needed once `(te)`
includes the integrability of its integrands, decision D5). -/
theorem lipRenorm_core {t₀ T : ℝ} {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {u₀ : ℂ → ℝ}
    (hren : ∀ Υ : ℝ → ℝ, IsRenormalization Υ →
      SolvesTE t₀ T (fun t x => Υ (u t x)) w (fun x => Υ (u₀ x))) :
    ∀ β : ℝ → ℝ, Equimeas.IsLipO β →
      SolvesTE t₀ T (fun t x => β (u t x)) w (fun x => β (u₀ x)) := by
  intro β ⟨⟨K, hK⟩, h0⟩
  obtain ⟨Υ, hΥ, hbound, hlim⟩ := exists_seq_isRenormalization_tendsto hK h0
  have hu : SolvesTE t₀ T u w u₀ := hren id isRenormalization_id
  have hβ : ∀ s, |β s| ≤ K * |s| := fun s => by
    have := hK.dist_le_mul s 0
    rwa [Real.dist_eq, Real.dist_eq, h0, sub_zero, sub_zero] at this
  exact solvesTE_of_tendsto hu (fun n => hren (Υ n) (hΥ n)) hbound hβ hlim

end LipRenormAux

open LipRenormAux

set_option linter.unusedVariables false in
/-- `lem:lip-renorm` (`03_compactness.tex:92-99`): under the standing assumptions of `(te)`, if
`Υ(u)` satisfies `(te)` on `[t₀,T)` with field `w` and datum `Υ(u₀)` for every renormalization
`Υ` (`C¹`, `Υ'` bounded, `Υ(0) = 0`), then the same holds for every `β ∈ Lip₀`.
(The hypotheses `hT`, `ht₀`, `hdata` of the manuscript statement are not needed by the proof;
see `lipRenorm_core`.) -/
theorem lipRenorm {t₀ T : ℝ} (hT : 0 < T) (ht₀ : t₀ ∈ Ico 0 T) {u : ℝ → ℂ → ℝ}
    {w : ℝ → ℂ → ℂ} {u₀ : ℂ → ℝ} (hdata : IsTEData t₀ T u w u₀)
    (hren : ∀ Υ : ℝ → ℝ, IsRenormalization Υ →
      SolvesTE t₀ T (fun t x => Υ (u t x)) w (fun x => Υ (u₀ x))) :
    ∀ β : ℝ → ℝ, Equimeas.IsLipO β →
      SolvesTE t₀ T (fun t x => β (u t x)) w (fun x => β (u₀ x)) := by
  exact lipRenorm_core hren

/-- `lem:lip-renorm` for renormalized weak solutions (`03_compactness.tex:607-608`, `:677-678`,
`:740-742`): if `ω` is a renormalized weak solution in `X_q(T)` with datum `ωin`, then for every
`β ∈ Lip₀`, `β(ω)` satisfies `(te)` on `[0,T)` with field `v = K ∗ ω` and datum `β(ωin)`. -/
theorem _root_.NonUniqueEuler.IsRenormalizedWeakSolution.solvesTE_lipO {q T : ℝ}
    {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ} (h : IsRenormalizedWeakSolution q T ωin ω) :
    ∀ β : ℝ → ℝ, Equimeas.IsLipO β →
      SolvesTE 0 T (fun t x => β (ω t x)) (velocityField ω) (fun x => β (ωin x)) := by
  exact lipRenorm_core fun Υ hΥ => h.solvesTE_renormalized hΥ

end NonUniqueEuler.Weak
