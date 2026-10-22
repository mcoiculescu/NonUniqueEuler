import NonUniqueEuler.Defs.Sec4.Linear
import NonUniqueEuler.I.Sec4.SemigroupLaw
import NonUniqueEuler.I.Sec4.RingFacts

/-!
# Helper for `lem:running`: the Duhamel integrand is continuous

Helper of `P/Sec5/Running.lean`. For `g ∈ C([0,u]; Y^s(N))`, the integrand
`v ↦ e^{(u-v)L(G)} g(v)` of the Duhamel integral is continuous on `[0,u]` (strong continuity of
the semigroup and its local uniform bound, `semigroup_continuousOn`, `semigroup_bound`), hence
interval integrable (`RunningAux.intervalIntegrable_S_comp`).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.RunningAux

open Sect RingData

/-- `v ↦ e^{(u-v)L(G)} g(v)` is continuous on `[0,u]` for `g` continuous on `[0,u]`. -/
theorem continuousOn_S_comp (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (s : ℕ) (G : ℝ) {u : ℝ}
    {g : ℝ → Y s annN} (hg : ContinuousOn g (Icc 0 u)) :
    ContinuousOn (fun v => Lin.S χ s G (u - v) (g v)) (Icc 0 u) := by
  obtain ⟨B, hB⟩ :=
    (ringPhiSetting χ).semigroup_bound (ringPhiSetting_valid hχ) s (abs_nonneg G) u
  intro v₀ hv₀
  have hmaps : MapsTo (fun v => u - v) (Icc 0 u) (Icc 0 u) := fun v hv =>
    ⟨by linarith [hv.2], by linarith [hv.1]⟩
  have h2 : ContinuousWithinAt (fun v => Lin.S χ s G (u - v) (g v₀)) (Icc 0 u) v₀ := by
    have hc := (ringPhiSetting χ).semigroup_continuousOn (ringPhiSetting_valid hχ) s G (g v₀)
    have h3 : ContinuousWithinAt (fun t => Lin.S χ s G t (g v₀)) (Icc 0 u) (u - v₀) :=
      (hc (u - v₀) (show (0 : ℝ) ≤ u - v₀ by linarith [hv₀.2])).mono Icc_subset_Ici_self
    exact h3.comp (continuousWithinAt_const.sub continuousWithinAt_id) hmaps
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero] at h2 ⊢
  have h1 : Tendsto (fun v => ‖g v - g v₀‖) (𝓝[Icc 0 u] v₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hg v₀ hv₀)
  have hlim : Tendsto (fun v => B * ‖g v - g v₀‖ +
      ‖Lin.S χ s G (u - v) (g v₀) - Lin.S χ s G (u - v₀) (g v₀)‖) (𝓝[Icc 0 u] v₀) (𝓝 0) := by
    simpa using (h1.const_mul B).add h2
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall fun v hv => ?_) hlim
  have hsplit : Lin.S χ s G (u - v) (g v) - Lin.S χ s G (u - v₀) (g v₀) =
      Lin.S χ s G (u - v) (g v - g v₀) +
        (Lin.S χ s G (u - v) (g v₀) - Lin.S χ s G (u - v₀) (g v₀)) := by
    rw [map_sub]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  have hop : ‖Lin.S χ s G (u - v)‖ ≤ B := hB G le_rfl (u - v) (hmaps hv)
  calc ‖Lin.S χ s G (u - v) (g v - g v₀)‖ ≤ ‖Lin.S χ s G (u - v)‖ * ‖g v - g v₀‖ :=
        (Lin.S χ s G (u - v)).le_opNorm _
    _ ≤ B * ‖g v - g v₀‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)

/-- The Duhamel integrand is interval integrable on `[0,u]`. -/
theorem intervalIntegrable_S_comp (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (s : ℕ) (G : ℝ)
    {u : ℝ} (hu : 0 ≤ u) {g : ℝ → Y s annN} (hg : ContinuousOn g (Icc 0 u)) :
    IntervalIntegrable (fun v => Lin.S χ s G (u - v) (g v)) volume 0 u :=
  (continuousOn_S_comp χ hχ s G hg).intervalIntegrable_of_Icc hu

end NonUniqueEuler.OneRing.RunningAux
