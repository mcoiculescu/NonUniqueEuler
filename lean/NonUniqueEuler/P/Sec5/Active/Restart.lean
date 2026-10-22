import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.SmoothB.SmoothCovariance
import NonUniqueEuler.I.SmoothB.SmoothFlow
import NonUniqueEuler.I.Sec5.Setting
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Proof: restarting a configuration of `lem:reduction` at a later time

Proof of `I/Sec5/Active/Restart.lean` (`05_single_ring.tex:1022-1031`, "We restart at `t₁`").

The restarted configuration is `c' = ⟨ω_r(t₁), ω_i(t₁), ω_o(t₁)⟩`. Its datum is `ω(t₁)`
(`setting_sol_eq_parts`), an admissible datum by `Smooth.sol_timeShift`, whose flow is
`Φ̃_τ = Φ_{t₁+τ} ∘ Φ_{t₁}⁻¹`. Since `Φ̃_τ⁻¹` is the two-sided inverse of `Φ̃_τ`
(`Smooth.flow_diffeo` for the datum `ω(t₁)`), `Φ̃_τ⁻¹ = Φ_{t₁} ∘ Φ_{t₁+τ}⁻¹` and the transported
parts of `c'` are `ω_•(t₁ + ·)`. The hypotheses of `lem:reduction` on `[0, T - t₁]` follow from
those of `c` on `[0, T]` (supports at `t₁ + τ`), from `setting_tsupport_parts` and the injectivity
of `Φ_{t₁}` (disjoint supports) and from `setting_symmetric` (symmetry); the circulation is the
same by `setting_integral_innerPart`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

namespace RingConfig

/-- The restarted configuration `⟨ω_r(t₁), ω_i(t₁), ω_o(t₁)⟩`. -/
private def restartCfg (c : RingConfig) (t₁ : ℝ) : RingConfig :=
  ⟨c.ringPart t₁, c.innerPart t₁, c.outerPart t₁⟩

/-- Pointwise symmetry gives the almost-everywhere form `IsMFoldSymmetric 3`. -/
private theorem isMFoldSymmetric_three_of_forall {g : ℂ → ℝ}
    (hg : ∀ x, g (rot (2 * Real.pi / 3) x) = g x) : IsMFoldSymmetric 3 g := by
  unfold IsMFoldSymmetric
  refine Filter.Eventually.of_forall (fun x => ?_)
  simp only [Nat.cast_ofNat]
  exact hg x

/-- **Restart at `t₁`** (`05_single_ring.tex:1022-1031`): the configuration `c'` with
`c'.ring0 = ω_r(t₁)` satisfies the hypotheses of `lem:reduction` on `[0, T - t₁]`, has the same
`G`, field `h(t₁ + ·)`, perturbation `w(t₁ + ·)`, and flow `Φ_{t₁+τ} ∘ Φ_{t₁}⁻¹`. -/
theorem active_restart {c : RingConfig} {T t₁ : ℝ} (hc : c.Hyp T) (ht₁ : 0 ≤ t₁)
    (ht₁T : t₁ < T) :
    ∃ c' : RingConfig, c'.Hyp (T - t₁) ∧ c'.G = c.G ∧ c'.ring0 = c.ringPart t₁ ∧
      (∀ τ : ℝ, c'.h τ = c.h (t₁ + τ)) ∧
      (∀ (χ : ℝ → ℝ) (τ : ℝ), c'.w χ τ = c.w χ (t₁ + τ)) ∧
      (∀ χ : ℝ → ℝ, c'.pert0 χ = c.w χ t₁) ∧
      ∀ (τ : ℝ) (y : ℂ), c'.flow τ (c.flow t₁ y) = c.flow (t₁ + τ) y := by
  set c' := restartCfg c t₁ with hc'
  -- the datum of `c` is admissible for `thm:smooth`
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, tsupport c.datum ⊆ ball 0 R₀ :=
    (isBounded_iff_subset_ball (0 : ℂ)).1 hc.datum_hasCompactSupport.isCompact.isBounded
  have hdat : Smooth.IsSmoothDatum c.datum R₀ := ⟨hc.datum_contDiff, hR₀⟩
  obtain ⟨hdat', -, -, hflow'⟩ := Smooth.sol_timeShift hdat t₁
  obtain ⟨hsum, hFI, hIF, -, -, -⟩ := setting_sol_eq_parts hc
  -- the datum of `c'` is `ω(t₁)`
  have hdatum' : c'.datum = Smooth.sol c.datum t₁ := by
    funext x
    exact (hsum t₁ x).symm
  have hdat'' : Smooth.IsSmoothDatum c'.datum (Smooth.suppRadius c.datum R₀ t₁) := by
    rw [hdatum']; exact hdat'
  -- the flow of `c'`
  have hflowc' : ∀ (τ : ℝ) (y : ℂ), c'.flow τ y = c.flow (t₁ + τ) (c.flowInv t₁ y) := by
    intro τ y
    change Smooth.flow c'.datum τ y = _
    rw [hdatum']
    exact hflow' τ y
  have hflow_main : ∀ (τ : ℝ) (y : ℂ), c'.flow τ (c.flow t₁ y) = c.flow (t₁ + τ) y := by
    intro τ y
    rw [hflowc', hIF]
  -- the inverse flow of `c'`
  have hflowInvc' : ∀ (τ : ℝ) (x : ℂ),
      c'.flowInv τ x = c.flow t₁ (c.flowInv (t₁ + τ) x) := by
    intro τ x
    have hL := (Smooth.flow_diffeo hdat'' τ).1
    have hx : c'.flow τ (c.flow t₁ (c.flowInv (t₁ + τ) x)) = x := by
      rw [hflow_main, hFI]
    calc c'.flowInv τ x
        = c'.flowInv τ (c'.flow τ (c.flow t₁ (c.flowInv (t₁ + τ) x))) := by rw [hx]
      _ = c.flow t₁ (c.flowInv (t₁ + τ) x) := hL _
  -- the transported parts of `c'`
  have hring : ∀ τ : ℝ, c'.ringPart τ = c.ringPart (t₁ + τ) := by
    intro τ; funext x
    change c.ring0 (c.flowInv t₁ (c'.flowInv τ x)) = c.ring0 (c.flowInv (t₁ + τ) x)
    rw [hflowInvc', hIF]
  have hinner : ∀ τ : ℝ, c'.innerPart τ = c.innerPart (t₁ + τ) := by
    intro τ; funext x
    change c.inner0 (c.flowInv t₁ (c'.flowInv τ x)) = c.inner0 (c.flowInv (t₁ + τ) x)
    rw [hflowInvc', hIF]
  have houter : ∀ τ : ℝ, c'.outerPart τ = c.outerPart (t₁ + τ) := by
    intro τ; funext x
    change c.outer0 (c.flowInv t₁ (c'.flowInv τ x)) = c.outer0 (c.flowInv (t₁ + τ) x)
    rw [hflowInvc', hIF]
  -- the circulation
  have hG : c'.G = c.G := by
    change (2 * Real.pi)⁻¹ * ∫ x, c.innerPart t₁ x = c.G
    rw [setting_integral_innerPart hc t₁]
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    field_simp
  -- supports and symmetry at `t₁`
  have hinj : Function.Injective (c.flow t₁) := Function.LeftInverse.injective (hIF t₁)
  obtain ⟨hsr, hsi, hso⟩ := setting_tsupport_parts hc t₁
  obtain ⟨-, -, hsymr, hsymi, hsymo⟩ := setting_symmetric hc
  have hTime : ∀ τ ∈ Icc (0 : ℝ) (T - t₁), t₁ + τ ∈ Icc (0 : ℝ) T := by
    intro τ hτ
    exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hHyp : c'.Hyp (T - t₁) :=
    { datum_contDiff := hdat''.contDiff
      datum_hasCompactSupport := hdat''.hasCompactSupport
      disjoint_ring_inner := by
        change Disjoint (tsupport (c.ringPart t₁)) (tsupport (c.innerPart t₁))
        rw [hsr, hsi, disjoint_image_iff hinj]
        exact hc.disjoint_ring_inner
      disjoint_ring_outer := by
        change Disjoint (tsupport (c.ringPart t₁)) (tsupport (c.outerPart t₁))
        rw [hsr, hso, disjoint_image_iff hinj]
        exact hc.disjoint_ring_outer
      disjoint_inner_outer := by
        change Disjoint (tsupport (c.innerPart t₁)) (tsupport (c.outerPart t₁))
        rw [hsi, hso, disjoint_image_iff hinj]
        exact hc.disjoint_inner_outer
      sym_ring := isMFoldSymmetric_three_of_forall (hsymr t₁)
      sym_inner := isMFoldSymmetric_three_of_forall (hsymi t₁)
      sym_outer := isMFoldSymmetric_three_of_forall (hsymo t₁)
      T_pos := sub_pos.2 ht₁T
      inner_tsupport := by
        intro τ hτ
        rw [hinner τ]
        exact hc.inner_tsupport _ (hTime τ hτ)
      outer_tsupport := by
        intro τ hτ
        rw [houter τ]
        exact hc.outer_tsupport _ (hTime τ hτ) }
  refine ⟨c', hHyp, hG, rfl, ?_, ?_, ?_, hflow_main⟩
  · intro τ
    funext x
    simp only [h, hinner τ, houter τ, hG]
  · intro χ τ
    funext x
    simp only [w, hring τ]
  · intro χ
    rfl

end RingConfig

end OneRing

end NonUniqueEuler
