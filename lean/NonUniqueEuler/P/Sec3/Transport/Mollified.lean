import NonUniqueEuler.Defs.Sec3.Transport
import NonUniqueEuler.Defs.Sec3.Commutator
import NonUniqueEuler.Defs.Sec2.Spaces
import NonUniqueEuler.H.Sec3.Transport.Mollified.Integrable
import NonUniqueEuler.H.Sec3.Transport.Mollified.Space
import NonUniqueEuler.I.Sec3.Transport.Mollified.TimeEq
import NonUniqueEuler.I.Sec3.Transport.Mollified.ChainRule

/-!
# Proof of `I/Sec3/Transport/Mollified.lean` (the mollified renormalized identity)

The proof of `lem:transport`(i) (`03_compactness.tex:494-510`) at a fixed `ε > 0`, with the datum
kept from the start (deviation recorded in the I file). With `U = u ⋆ ρ_ε`,
`D = (div(wu)) ⋆ ρ_ε`, `G = w·∇(u ⋆ ρ_ε)` (so `C_ε[u,w] = G - D`) and `μ = volume.restrict (t₀,T)`:

* **time part** (steps 1–2): for every `x`, `U(·,x)` satisfies `U' = -D(·,x)` weakly on
  `[t₀,T)` with datum `U₀(x)` (`mollify_timeEq`, `I/Sec3/Transport/Mollified/TimeEq.lean`); the
  one-dimensional chain rule (`renorm_timeEq`, `I/Sec3/Transport/Mollified/ChainRule.lean`) with
  `α = φ(·,x)` gives `∫ Υ(U) ∂_tφ = ∫ φ Υ'(U) D - Υ(U₀(x)) φ(t₀,x)`;
* **space part** (step 3): for a.e. `t`, `∫ Υ(U) w·∇φ = -∫ φ Υ'(U) G`
  (`MollifiedH.integral_renorm_spaceDeriv`, `H/Sec3/Transport/Mollified/Space.lean`);
* **assembly** (step 4): the four integrands are integrable on `μ ⊗ volume`
  (`H/Sec3/Transport/Mollified/Integrable.lean`); integrate the time part in `x` and the space
  part in `t` (Fubini, `integral_prod`, `integral_prod_symm`) and add.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak

set_option linter.unusedVariables false in
open MollifiedH in
/-- The mollified renormalized identity of the proof of `lem:transport`(i)
(`03_compactness.tex:494-510`), with `a = b = 2`, at a fixed `ε > 0`: with
`u_ε(t) = u(t) ⋆ ρ_ε` and `u₀,ε = u₀ ⋆ ρ_ε`, for every renormalization `Υ` and `φ ∈ 𝒟_T`, the
functions `Υ(u_ε)(∂_tφ + w·∇φ)` and `φ Υ'(u_ε) C_ε[u,w]` are integrable on `(t₀,T)×ℝ²` and
`∫_{t₀}^T∫ Υ(u_ε)(∂_tφ + w·∇φ) + ∫ Υ(u₀,ε)φ(t₀) = -∫_{t₀}^T∫ φ Υ'(u_ε) C_ε[u,w]`. -/
theorem transport_mollified_identity {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {T t₀ : ℝ} (hT : 0 < T) (ht₀ : t₀ ∈ Ico 0 T) {w : ℝ → ℂ → ℂ}
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) {u : ℝ → ℂ → ℝ} {u₀ : ℂ → ℝ}
    (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u) (hu2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    (hu₀1 : MemLp u₀ 1 volume) (hu₀2 : MemLp u₀ 2 volume) (hte : SolvesTE t₀ T u w u₀)
    {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    IntegrableOn (transportIntegrand (fun t x => Υ (mollify ρ ε (u t) x)) w φ)
        (slabFrom t₀ T) ∧
      IntegrableOn (fun p : ℝ × ℂ =>
          φ p * deriv Υ (mollify ρ ε (u p.1) p.2) * commEps ρ ε u w p.1 p.2) (slabFrom t₀ T) ∧
      (∫ t in Ioo t₀ T, ∫ x : ℂ,
          transportIntegrand (fun t x => Υ (mollify ρ ε (u t) x)) w φ (t, x)) +
          ∫ x : ℂ, Υ (mollify ρ ε u₀ x) * φ (t₀, x) =
        -∫ t in Ioo t₀ T, ∫ x : ℂ,
          φ (t, x) * deriv Υ (mollify ρ ε (u t) x) * commEps ρ ε u w t x := by
  have ht₀0 : 0 ≤ t₀ := ht₀.1
  have htT : t₀ < T := ht₀.2
  have hF1 := integrable_F1 hρ hε ht₀0 hw hu1 huw hΥ hφ
  have hF2 := integrable_F2 hρ hε ht₀0 hw hu1 huw hΥ hφ
  have hF3 := integrable_F3 hρ hε ht₀0 hw hu1 huw hΥ hφ
  have hF4 := integrable_F4 hρ hε ht₀0 hw hu1 huw hΥ hφ
  have hsplitT : transportIntegrand (fun t x => Υ (mollify ρ ε (u t) x)) w φ =
      fun p => Υ (mollify ρ ε (u p.1) p.2) * timeDeriv φ p.1 p.2 +
        Υ (mollify ρ ε (u p.1) p.2) * spaceDeriv φ p.1 p.2 (w p.1 p.2) := by
    funext p
    simp only [transportIntegrand, mul_add]
  have hsplitC : (fun p : ℝ × ℂ =>
      φ p * deriv Υ (mollify ρ ε (u p.1) p.2) * commEps ρ ε u w p.1 p.2) =
      fun p => φ p * deriv Υ (mollify ρ ε (u p.1) p.2) * dotGradMollify ρ ε u w p.1 p.2 -
        φ p * deriv Υ (mollify ρ ε (u p.1) p.2) * mollifyDiv ρ ε u w p.1 p.2 := by
    funext p
    simp only [commEps, mul_sub]
  have hTint : Integrable (transportIntegrand (fun t x => Υ (mollify ρ ε (u t) x)) w φ)
      ((volume.restrict (Ioo t₀ T)).prod volume) := by
    rw [hsplitT]; exact hF1.add hF2
  have hCint : Integrable (fun p : ℝ × ℂ =>
      φ p * deriv Υ (mollify ρ ε (u p.1) p.2) * commEps ρ ε u w p.1 p.2)
      ((volume.restrict (Ioo t₀ T)).prod volume) := by
    rw [hsplitC]; exact hF4.sub hF3
  refine ⟨?_, ?_, ?_⟩
  · rw [IntegrableOn, restrict_slabFrom_eq_prod]; exact hTint
  · rw [IntegrableOn, restrict_slabFrom_eq_prod]; exact hCint
  -- The identity.
  -- Time part, for a.e. `x`.
  have htime : ∀ᵐ x : ℂ,
      ∫ s, Υ (mollify ρ ε (u s) x) * timeDeriv φ s x ∂(volume.restrict (Ioo t₀ T)) =
        (∫ s, φ (s, x) * deriv Υ (mollify ρ ε (u s) x) * mollifyDiv ρ ε u w s x
          ∂(volume.restrict (Ioo t₀ T))) - Υ (mollify ρ ε u₀ x) * φ (t₀, x) := by
    filter_upwards [hF1.prod_left_ae, hF3.prod_left_ae] with x h1 h3
    have key := renorm_timeEq htT (memLp_top_mollify_slice hρ hε ht₀0 hw hu1 huw x)
      (integrable_mollifyDiv_slice hρ hε ht₀0 hw hu1 huw x)
      (fun α hα => mollify_timeEq hρ hε ht₀ hu1 huw hte x hα) hΥ.contDiff
      (isTimeTestFn_slice hφ x)
    have h1' : Integrable (fun s => deriv (fun s => φ (s, x)) s * Υ (mollify ρ ε (u s) x))
        (volume.restrict (Ioo t₀ T)) := by
      refine h1.congr (ae_of_all _ fun s => ?_)
      simp only [timeDeriv, mul_comm]
    have e1 : ∫ s, Υ (mollify ρ ε (u s) x) * timeDeriv φ s x ∂(volume.restrict (Ioo t₀ T)) =
        ∫ s, deriv (fun s => φ (s, x)) s * Υ (mollify ρ ε (u s) x)
          ∂(volume.restrict (Ioo t₀ T)) := by
      refine integral_congr_ae (ae_of_all _ fun s => ?_)
      simp only [timeDeriv, mul_comm]
    rw [integral_sub h1' h3] at key
    rw [e1]
    linarith
  -- Space part, for a.e. `t`.
  obtain ⟨M₁, -, hgood⟩ := ae_good ht₀0 hw hu1 huw
  have hspace : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)),
      ∫ x, Υ (mollify ρ ε (u t) x) * spaceDeriv φ t x (w t x) =
        -∫ x, φ (t, x) * deriv Υ (mollify ρ ε (u t) x) * dotGradMollify ρ ε u w t x := by
    filter_upwards [hgood] with t ht
    exact integral_renorm_spaceDeriv hρ hε ht.1.locallyIntegrable ht.2.2.2.1 ht.2.2.2.2 hΥ hφ
  -- Fubini.
  have eL : (∫ t in Ioo t₀ T, ∫ x : ℂ,
      transportIntegrand (fun t x => Υ (mollify ρ ε (u t) x)) w φ (t, x)) =
      ∫ p, transportIntegrand (fun t x => Υ (mollify ρ ε (u t) x)) w φ p
        ∂((volume.restrict (Ioo t₀ T)).prod volume) :=
    (integral_prod _ hTint).symm
  have eR : (∫ t in Ioo t₀ T, ∫ x : ℂ,
      φ (t, x) * deriv Υ (mollify ρ ε (u t) x) * commEps ρ ε u w t x) =
      ∫ p, φ p * deriv Υ (mollify ρ ε (u p.1) p.2) * commEps ρ ε u w p.1 p.2
        ∂((volume.restrict (Ioo t₀ T)).prod volume) :=
    (integral_prod _ hCint).symm
  have e1 : ∫ p, Υ (mollify ρ ε (u p.1) p.2) * timeDeriv φ p.1 p.2
      ∂((volume.restrict (Ioo t₀ T)).prod volume) =
      (∫ p, φ p * deriv Υ (mollify ρ ε (u p.1) p.2) * mollifyDiv ρ ε u w p.1 p.2
        ∂((volume.restrict (Ioo t₀ T)).prod volume)) -
        ∫ x, Υ (mollify ρ ε u₀ x) * φ (t₀, x) := by
    rw [integral_prod_symm _ hF1, integral_prod_symm _ hF3,
      ← integral_sub hF3.integral_prod_right (integrable_datum hρ hε hu₀1 hΥ hφ t₀)]
    exact integral_congr_ae htime
  have e2 : ∫ p, Υ (mollify ρ ε (u p.1) p.2) * spaceDeriv φ p.1 p.2 (w p.1 p.2)
      ∂((volume.restrict (Ioo t₀ T)).prod volume) =
      -∫ p, φ p * deriv Υ (mollify ρ ε (u p.1) p.2) * dotGradMollify ρ ε u w p.1 p.2
        ∂((volume.restrict (Ioo t₀ T)).prod volume) := by
    rw [integral_prod _ hF2, integral_prod _ hF4, ← integral_neg]
    exact integral_congr_ae hspace
  rw [eL, eR, hsplitT, hsplitC, integral_add hF1 hF2, integral_sub hF4 hF3, e1, e2]
  ring

end NonUniqueEuler.Weak
