import NonUniqueEuler.Defs.Infra.Dunford
import NonUniqueEuler.I.Infra.Dunford.Integral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Algebra

/-!
# Proof of `I/Infra/Dunford/Uniform.lean` (I-DUNF (D3), (D4), uniform spectral gap)

Exponential bounds from the spectrum, uniformly for continuous families of bounded operators on a
compact parameter set (library I-DUNF; restructuring R2; used by
`prop:semigroup`, `04_ring.tex:1431-1500`).

* (D3) `exists_norm_resolvent_le_of_isCompact`: `(k, z) ↦ Ring.inverse (z - A k)` is continuous on
  the compact `K ×ˢ Z` (continuity of `Ring.inverse` at units), hence bounded.
* (D4) `exists_ball_of_re_le`: elementary planar geometry with `ρ₀ = |a| + |R| + R²/ε + 1`.
* Spectral gap `exists_re_le_of_isCompact`: the set `T = {(k, z) : k ∈ K, z ∈ σ(A k)}` is compact
  (relatively closed in `K ×ˢ closedBall 0 (R ‖1‖)`, as the preimage of the closed set of
  non-units); `Re` attains its maximum on `T` (if `T ≠ ∅`), which is `< σ`.
* Exponential bounds: gap + (D4) put all spectra in one disc `ball (σ - ρ) ρ`; (D3) on its
  boundary circle and the circle bound `norm_exp_le_of_spectrum_subset_ball`
  (`I/Infra/Dunford/Integral.lean`) conclude. The single-operator case is the constant family on
  `Unit`.
-/

noncomputable section

open Filter Topology Metric Set

namespace NonUniqueEuler.Dunford

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- The family `(k, z) ↦ z - A k` is continuous on `K ×ˢ Z`. -/
private theorem continuousOn_sub_family {κ : Type*} [TopologicalSpace κ] {K : Set κ}
    {A : κ → X →L[ℂ] X} (hA : ContinuousOn A K) (Z : Set ℂ) :
    ContinuousOn (fun p : κ × ℂ => algebraMap ℂ (X →L[ℂ] X) p.2 - A p.1) (K ×ˢ Z) := by
  have h1 : ContinuousOn (fun p : κ × ℂ => A p.1) (K ×ˢ Z) :=
    hA.comp continuousOn_fst (fun p hp => hp.1)
  have h2 : Continuous (fun p : κ × ℂ => algebraMap ℂ (X →L[ℂ] X) p.2) :=
    (continuous_algebraMap ℂ (X →L[ℂ] X)).comp continuous_snd
  exact h2.continuousOn.sub h1

/-- **(D3) Uniform resolvent bound** for a continuous family on a compact set, on a compact set
of spectral parameters contained in all the resolvent sets. -/
theorem exists_norm_resolvent_le_of_isCompact {κ : Type*} [TopologicalSpace κ] {K : Set κ}
    (hK : IsCompact K) {A : κ → X →L[ℂ] X} (hA : ContinuousOn A K) {Z : Set ℂ}
    (hZ : IsCompact Z) (hres : ∀ k ∈ K, ∀ z ∈ Z, z ∈ resolventSet ℂ (A k)) :
    ∃ M : ℝ, ∀ k ∈ K, ∀ z ∈ Z, ‖resolvent (A k) z‖ ≤ M := by
  have hfc := continuousOn_sub_family hA Z
  have hg : ContinuousOn (fun p : κ × ℂ => resolvent (A p.1) p.2) (K ×ˢ Z) := by
    intro p hp
    obtain ⟨u, hu⟩ := (spectrum.mem_resolventSet_iff).1 (hres p.1 hp.1 p.2 hp.2)
    have hinv := NormedRing.inverse_continuousAt u
    rw [hu] at hinv
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun p : κ × ℂ => algebraMap ℂ (X →L[ℂ] X) p.2 - A p.1) (g := Ring.inverse)
      hinv (hfc p hp)
  obtain ⟨M, hM⟩ := (hK.prod hZ).exists_bound_of_continuousOn hg
  exact ⟨M, fun k hk z hz => hM (k, z) ⟨hk, hz⟩⟩

/-- **(D4) Geometry**: a set in `{Re z ≤ a - ε} ∩ closedBall 0 R` lies in the open disc of centre
`a - ρ` and radius `ρ` for every sufficiently large `ρ`. -/
theorem exists_ball_of_re_le {S : Set ℂ} {a ε R : ℝ} (hε : 0 < ε)
    (hS : ∀ z ∈ S, z.re ≤ a - ε ∧ ‖z‖ ≤ R) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → S ⊆ ball ((a - ρ : ℝ) : ℂ) ρ := by
  refine ⟨|a| + |R| + R ^ 2 / ε + 1, by positivity, fun ρ hρ z hz => ?_⟩
  obtain ⟨hre, hnorm⟩ := hS z hz
  have hρpos : 0 < ρ := lt_of_lt_of_le (by positivity) hρ
  set q : ℝ := R ^ 2 / ε with hq
  have hq0 : 0 ≤ q := by positivity
  have hqε : q * ε = R ^ 2 := by rw [hq]; field_simp
  set u : ℝ := a - z.re with hu
  have huε : ε ≤ u := by rw [hu]; linarith
  have hu0 : 0 < u := lt_of_lt_of_le hε huε
  have hxR : -R ≤ z.re := by
    have := (abs_le.1 ((Complex.abs_re_le_norm z).trans hnorm)).1
    linarith
  have haa : a ≤ |a| := le_abs_self a
  have hRR : R ≤ |R| := le_abs_self R
  have huR : u ≤ |a| + R := by rw [hu]; linarith
  have hy : z.im ^ 2 ≤ R ^ 2 := by
    have h0 : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans hnorm
    have : |z.im| ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h0 2
    simpa [sq_abs] using this
  -- `u² + y² ≤ u (|a| + R + q) < 2 ρ u`.
  have h1 : u ^ 2 ≤ u * (|a| + R) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left huR hu0.le
  have h2 : R ^ 2 ≤ q * u := by
    rw [← hqε]; exact mul_le_mul_of_nonneg_left huε hq0
  have h3 : |a| + R + q < 2 * ρ := by linarith
  have h4 : u * (|a| + R + q) < u * (2 * ρ) := mul_lt_mul_of_pos_left h3 hu0
  have key : ‖z - ((a - ρ : ℝ) : ℂ)‖ ^ 2 < ρ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    have e : (z.re - (a - ρ)) = ρ - u := by rw [hu]; ring
    rw [e]
    nlinarith
  rw [mem_ball, Complex.dist_eq]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hρpos.le two_ne_zero).1 key

/-- **Uniform spectral gap** for a continuous family on a compact set. -/
theorem exists_re_le_of_isCompact {κ : Type*} [TopologicalSpace κ] {K : Set κ}
    (hK : IsCompact K) {A : κ → X →L[ℂ] X} (hA : ContinuousOn A K) {σ : ℝ}
    (h : ∀ k ∈ K, ∀ z ∈ spectrum ℂ (A k), z.re < σ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k ∈ K, ∀ z ∈ spectrum ℂ (A k), z.re ≤ σ - ε := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hA
  set B : Set ℂ := closedBall 0 (R * ‖(1 : X →L[ℂ] X)‖) with hB
  have hfc := continuousOn_sub_family hA (univ : Set ℂ)
  obtain ⟨w, hw, hweq⟩ := (continuousOn_iff_isClosed.1 hfc) {x : X →L[ℂ] X | IsUnit x}ᶜ
    Units.isOpen.isClosed_compl
  set T : Set (κ × ℂ) := w ∩ (K ×ˢ B) with hT
  have hTc : IsCompact T := (hK.prod (isCompact_closedBall _ _)).inter_left hw
  have memT : ∀ k ∈ K, ∀ z ∈ spectrum ℂ (A k), (k, z) ∈ T := by
    intro k hk z hz
    have hzB : z ∈ B := by
      rw [hB, mem_closedBall, dist_zero_right]
      exact (spectrum.norm_le_norm_mul_of_mem hz).trans
        (mul_le_mul_of_nonneg_right (hR k hk) (norm_nonneg _))
    have hmem : (k, z) ∈ (fun p : κ × ℂ => algebraMap ℂ (X →L[ℂ] X) p.2 - A p.1) ⁻¹'
        {x : X →L[ℂ] X | IsUnit x}ᶜ ∩ (K ×ˢ (univ : Set ℂ)) :=
      ⟨spectrum.mem_iff.1 hz, hk, mem_univ _⟩
    rw [hweq] at hmem
    exact ⟨hmem.1, hk, hzB⟩
  have Tmem : ∀ p ∈ T, p.1 ∈ K ∧ p.2 ∈ spectrum ℂ (A p.1) := by
    intro p hp
    have hmem : p ∈ w ∩ (K ×ˢ (univ : Set ℂ)) := ⟨hp.1, hp.2.1, mem_univ _⟩
    rw [← hweq] at hmem
    exact ⟨hmem.2.1, spectrum.mem_iff.2 hmem.1⟩
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · refine ⟨1, one_pos, fun k hk z hz => ?_⟩
    have := memT k hk z hz
    rw [hTe] at this
    exact absurd this (notMem_empty _)
  · obtain ⟨p, hp, hmax⟩ := hTc.exists_isMaxOn hTne
      (Complex.continuous_re.comp continuous_snd).continuousOn
    obtain ⟨hpK, hps⟩ := Tmem p hp
    refine ⟨σ - p.2.re, sub_pos.2 (h _ hpK _ hps), fun k hk z hz => ?_⟩
    have hle : z.re ≤ p.2.re := hmax (memT k hk z hz)
    linarith

/-- The uniform exponential bound (shared proof of the last two statements). -/
private theorem uniform_exp_bound {κ : Type*} [TopologicalSpace κ]
    {K : Set κ} (hK : IsCompact K) {A : κ → X →L[ℂ] X} (hA : ContinuousOn A K) {σ : ℝ}
    (h : ∀ k ∈ K, ∀ z ∈ spectrum ℂ (A k), z.re < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ∈ K, ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((t : ℂ) • A k)‖ ≤ C * Real.exp (σ * t) := by
  obtain ⟨ε, hε, hgap⟩ := exists_re_le_of_isCompact hK hA h
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hA
  set S : Set ℂ := ⋃ k ∈ K, spectrum ℂ (A k) with hS
  have hSb : ∀ z ∈ S, z.re ≤ σ - ε ∧ ‖z‖ ≤ R * ‖(1 : X →L[ℂ] X)‖ := by
    intro z hz
    rw [hS, mem_iUnion₂] at hz
    obtain ⟨k, hk, hzk⟩ := hz
    exact ⟨hgap k hk z hzk, (spectrum.norm_le_norm_mul_of_mem hzk).trans
      (mul_le_mul_of_nonneg_right (hR k hk) (norm_nonneg _))⟩
  obtain ⟨ρ, hρ, hball⟩ := exists_ball_of_re_le hε hSb
  have hsub : ∀ k ∈ K, spectrum ℂ (A k) ⊆ ball ((σ - ρ : ℝ) : ℂ) ρ := fun k hk z hz =>
    hball ρ le_rfl (mem_iUnion₂.2 ⟨k, hk, hz⟩)
  have hres : ∀ k ∈ K, ∀ z ∈ sphere ((σ - ρ : ℝ) : ℂ) ρ, z ∈ resolventSet ℂ (A k) := by
    intro k hk z hz
    by_contra hz'
    have hzb := hsub k hk (show z ∈ spectrum ℂ (A k) from hz')
    rw [mem_sphere] at hz
    rw [mem_ball] at hzb
    linarith
  obtain ⟨M, hM⟩ := exists_norm_resolvent_le_of_isCompact hK hA (isCompact_sphere _ _) hres
  refine ⟨max (ρ * M) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun k hk t ht => ?_⟩
  have hb := norm_exp_le_of_spectrum_subset_ball (A k) hρ (hsub k hk) (hM k hk) ht
  rw [Complex.ofReal_re, sub_add_cancel] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

/-- **Exponential bound from the spectrum**: `spectrum ℂ A ⊆ {Re < σ}` implies
`‖exp(tA)‖ ≤ C e^{σt}` for `t ≥ 0`. -/
theorem exists_norm_exp_le_of_spectrum_re_lt (A : X →L[ℂ] X) {σ : ℝ}
    (h : ∀ z ∈ spectrum ℂ A, z.re < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((t : ℂ) • A)‖ ≤ C * Real.exp (σ * t) := by
  obtain ⟨C, hC, hb⟩ := uniform_exp_bound (κ := Unit) (K := univ) isCompact_univ
    (A := fun _ => A) continuousOn_const (fun _ _ => h)
  exact ⟨C, hC, fun t ht => hb () (mem_univ _) t ht⟩

/-- **Uniform exponential bound** for a continuous family on a compact set with spectra in
`{Re < σ}`. -/
theorem exists_norm_exp_le_of_spectrum_re_lt_uniform {κ : Type*} [TopologicalSpace κ]
    {K : Set κ} (hK : IsCompact K) {A : κ → X →L[ℂ] X} (hA : ContinuousOn A K) {σ : ℝ}
    (h : ∀ k ∈ K, ∀ z ∈ spectrum ℂ (A k), z.re < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ∈ K, ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((t : ℂ) • A k)‖ ≤ C * Real.exp (σ * t) :=
  uniform_exp_bound hK hA h

end NonUniqueEuler.Dunford
