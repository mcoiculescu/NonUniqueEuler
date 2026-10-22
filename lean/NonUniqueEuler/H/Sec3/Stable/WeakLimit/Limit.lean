import NonUniqueEuler.H.Sec3.Stable.WeakLimit.TE

/-!
# Helpers for `prop:stable`, step 1a: the weak limit satisfies `(te)`

Helper file of `P/Sec3/Stable/WeakLimit.lean` (`03_compactness.tex:755-763`).

`solvesTE_of_weak`: if `γ ∈ Lip₀` is bounded by `B` and `γ(ωₙ) ⇀ G` weakly in
`L²((0,T) × ℝ²)`, then `G` satisfies `(te)` on `[0,T)` with field `v = K ∗ ω` and datum `γ(g)`.
For `φ ∈ 𝒟_T`, with `Iₙ = ∫∫ γ(ωₙ)(∂_tφ + vₙ·∇φ) = -∫ γ(gₙ)φ(0)` and
`Jₙ = ∫∫ γ(ωₙ)(∂_tφ + v·∇φ)`: `Jₙ → ∫∫ G(∂_tφ + v·∇φ)` (weak convergence),
`Iₙ - Jₙ → 0` (`enorm_integral_transport_sub_le`, `tendsto_lintegral_velocity_sub`) and
`∫ γ(gₙ)φ(0) → ∫ γ(g)φ(0)` (`tendsto_datum`).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.WeakLimitAux

open Weak

variable {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ} {ω : ℝ → ℂ → ℝ}

/-- **Passage to the limit in `(te)`** (`03_compactness.tex:755-763`). -/
theorem solvesTE_of_weak (hseq : IsCompactSeq T M gs g ωs) (hlim : IsCompactLimit T g ωs ω)
    (hstrong : Tendsto (fun n => normL1LpE 2 (gs n - g)) atTop (𝓝 0))
    (hren : ∀ n, IsRenormalizedWeakSolution 2 T (gs n) (ωs n))
    {γ : ℝ → ℝ} (hγ : Equimeas.IsLipO γ) {B : ℝ} (hγB : ∀ s, |γ s| ≤ B)
    {G : ℝ × ℂ → ℝ} (hG2 : MemLp G 2 (volume.restrict (slab T)))
    (hw : ∀ Φ : ℝ × ℂ → ℝ, MemLp Φ 2 (volume.restrict (slab T)) →
      Tendsto (fun n => ∫ p in slab T, γ (ωs n p.1 p.2) * Φ p) atTop
        (𝓝 (∫ p in slab T, G p * Φ p))) :
    SolvesTE 0 T (fun t x => G (t, x)) (velocityField ω) (fun x => γ (g x)) := by
  obtain ⟨L, hL0, hLs, -⟩ := isLipO_exists_abs_le hγ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hγB 0)
  have hint : ∀ φ, IsTestFunction T φ →
      IntegrableOn (transportIntegrand (fun t x => G (t, x)) (velocityField ω) φ)
        (slabFrom 0 T) :=
    fun φ hφ => hG2.integrable_mul (memLp_testIntegrand hlim.weakSolution hφ)
  refine ⟨hint, fun φ hφ => integrable_datum hγ hseq.memLp_one hφ, fun φ hφ => ?_⟩
  have hΨ := memLp_testIntegrand hlim.weakSolution hφ
  obtain ⟨R, hR, b, -, hsupp⟩ := exists_ball_of_isTestFunction hφ
  obtain ⟨D, -, hD⟩ := exists_bound_fderiv_of_isTestFunction hφ
  have hsupp' : ∀ p ∈ tsupport φ, p.2 ∈ ball (0 : ℂ) R := fun p hp => (hsupp p hp).2
  have hTE : ∀ n, SolvesTE 0 T (fun t x => γ (ωs n t x)) (velocityField (ωs n))
      (fun x => γ (gs n x)) := fun n => (hren n).solvesTE_lipO γ hγ
  -- `Iₙ = -∫ γ(gₙ) φ(0)`
  have hIeq : (fun n => ∫ p in slab T,
      transportIntegrand (fun t x => γ (ωs n t x)) (velocityField (ωs n)) φ p) =
      fun n => -∫ x, γ (gs n x) * φ (0, x) := by
    funext n
    have h := (hTE n).identity φ hφ
    rw [integral_Ioo_integral_eq ((hTE n).integrableOn φ hφ)] at h
    change (∫ p in slab T, _) + _ = 0 at h
    linarith
  -- `Jₙ → J`
  have hJn : Tendsto (fun n => ∫ p in slab T,
      transportIntegrand (fun t x => γ (ωs n t x)) (velocityField ω) φ p) atTop
      (𝓝 (∫ p in slab T, transportIntegrand (fun t x => G (t, x)) (velocityField ω) φ p)) :=
    hw _ hΨ
  have hJnint : ∀ n, IntegrableOn
      (transportIntegrand (fun t x => γ (ωs n t x)) (velocityField ω) φ) (slab T) :=
    fun n => (memLp_two_seq hseq n (isLipO_continuous hγ) hL0 hLs hγB).integrable_mul hΨ
  -- `Iₙ - Jₙ → 0`
  have hdiff : Tendsto (fun n =>
      (∫ p in slab T, transportIntegrand (fun t x => γ (ωs n t x)) (velocityField (ωs n)) φ p) -
        ∫ p in slab T, transportIntegrand (fun t x => γ (ωs n t x)) (velocityField ω) φ p)
      atTop (𝓝 0) := by
    refine tendsto_of_enorm_sub_le (e := fun n => ENNReal.ofReal (B * D) *
      ∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R,
        ‖velocityField (ωs n) p.1 p.2 - velocityField ω p.1 p.2‖ₑ) (fun n => ?_) ?_
    · rw [sub_zero]
      exact enorm_integral_transport_sub_le hφ hsupp' hD hB0 (fun t x => hγB _)
        ((hTE n).integrableOn φ hφ) (hJnint n)
    · simpa using ENNReal.Tendsto.const_mul (tendsto_lintegral_velocity_sub hseq hlim hR)
        (Or.inr ENNReal.ofReal_ne_top)
  have hI := hdiff.add hJn
  simp only [sub_add_cancel, zero_add] at hI
  rw [hIeq] at hI
  have hI' := (tendsto_datum hseq hstrong hγ hφ).neg
  have hJeq := tendsto_nhds_unique hI hI'
  rw [integral_Ioo_integral_eq (hint φ hφ)]
  change (∫ p in slab T, _) + _ = 0
  rw [hJeq]
  ring

end NonUniqueEuler.Compact.WeakLimitAux
