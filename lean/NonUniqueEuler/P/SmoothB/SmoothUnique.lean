import NonUniqueEuler.Defs.SmoothB.Solution
import NonUniqueEuler.H.SmoothB.SmoothUnique.Energy
import NonUniqueEuler.H.SmoothB.SmoothUnique.Transport

/-!
# Proof: thm:smooth (5) for any function with (1)–(3) (uniqueness among `C¹` solutions)

Proof of `I/SmoothB/SmoothUnique.lean` (`thm:smooth`(5), `02_prelim.tex:580-585`; proof
`B_global_smooth.tex:494-513`).

Fix `t ∈ I`, `t ≠ 0`, and `J = [a, b] = [min 0 t, max 0 t] ⊆ I`. Choose `ρ > 0` with `ω(s)`,
`ω̃(s)` vanishing outside `B_ρ` for `s ∈ J`, and `L` bounding `Dω̃` on `J × B̄_ρ` (continuity of
the derivative within `J × ℝ²` on a compact set). Put `δ = ω̃ - ω` and `E(s) = ∫ δ(s)²`.

* `E` is continuous on `J` (`continuousOn_integral_sq`), `E ≥ 0`, `E(0) = 0`;
* at `s ∈ (a, b)`: `E'(s) = ∫ 2δ ∂_tδ` (`hasDerivAt_integral_sq`), and
  `∂_tδ = -v·∇δ - (K ∗ δ)·∇ω̃` (the two transport equations, the chain rule
  `fderiv_uncurry_apply_one`, linearity `velocity_sub`); so `|E'(s)| ≤ L(1 + 4ρ²)E(s)`
  (`abs_integral_le_of_transport`: the transport term vanishes because `div v = 0`, and
  `lem:BS-basic`(c));
* Grönwall (`eq_zero_of_abs_deriv_le_mul`) gives `E(t) = 0`, so `δ(t) = 0` by continuity.

Deviation: the Cauchy–Schwarz step `|∫ δ (K∗δ)·∇ω̃| ≤
L‖δ‖₂‖K∗δ‖_{L²(B_ρ)}` is replaced by the pointwise `2|δ||w| ≤ δ² + |w|²`, which gives the
constant `L(1 + 4ρ²)` instead of `4ρL`; only finiteness of the constant matters.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler.Smooth

namespace UniqueAux

/-- For `s` between `0` and `t`, `|s| ≤ |t|`. -/
theorem abs_le_of_mem_Icc_min_max {s t : ℝ} (hs : s ∈ Icc (min 0 t) (max 0 t)) : |s| ≤ |t| := by
  rcases le_total 0 t with h | h
  · rw [min_eq_left h, max_eq_right h] at hs
    rw [abs_of_nonneg hs.1, abs_of_nonneg h]
    exact hs.2
  · rw [min_eq_right h, max_eq_left h] at hs
    rw [abs_of_nonpos hs.2, abs_of_nonpos h]
    linarith [hs.1]

/-- A slice `x ↦ u(s, x)` of a function `C¹` near `{s} × ℝ²` is `C¹`. -/
theorem contDiff_slice {u : ℝ → ℂ → ℝ} {U : Set (ℝ × ℂ)} (hu : ContDiffOn ℝ 1 (Function.uncurry u) U)
    {s : ℝ} (hs : ∀ x, U ∈ 𝓝 (s, x)) : ContDiff ℝ 1 (u s) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have h1 : ContDiffAt ℝ 1 (fun y : ℂ => (s, y)) x :=
    (contDiff_const.prodMk contDiff_id).contDiffAt
  exact (hu.contDiffAt (hs x)).comp x h1

/-- **The energy inequality at a time `s ∈ (a, b)`.** -/
theorem energy_step {ω ω' : ℝ → ℂ → ℝ} {a b ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hωs : ContDiff ℝ 1 (Function.uncurry ω))
    (hv : ∀ s, ContDiff ℝ 1 (velocityField ω s))
    (hdiv : ∀ s x, Prelim.divergence (velocityField ω s) x = 0)
    (htr : ∀ s x, deriv (fun r => ω r x) s + fderiv ℝ (ω s) x (velocityField ω s x) = 0)
    (hω' : ContDiffOn ℝ 1 (Function.uncurry ω') (Ioo a b ×ˢ univ))
    (htr' : ∀ s ∈ Ioo a b, ∀ x,
      fderiv ℝ (Function.uncurry ω') (s, x) (1, velocity (ω' s) x) = 0)
    (hvan' : ∀ s ∈ Ioo a b, ∀ x, x ∉ ball (0 : ℂ) ρ → ω' s x = 0)
    (hvan : ∀ s ∈ Ioo a b, ∀ x, x ∉ ball (0 : ℂ) ρ → ω s x = 0)
    (hD : ∀ s ∈ Ioo a b, ∀ x ∈ ball (0 : ℂ) ρ, ∀ w, |fderiv ℝ (ω' s) x w| ≤ L * ‖w‖)
    {s : ℝ} (hs : s ∈ Ioo a b) :
    HasDerivAt (fun r => ∫ x, (ω' r x - ω r x) ^ 2)
        (∫ x, 2 * (ω' s x - ω s x) * deriv (fun r => ω' r x - ω r x) s) s ∧
      |∫ x, 2 * (ω' s x - ω s x) * deriv (fun r => ω' r x - ω r x) s| ≤
        L * (1 + 4 * ρ ^ 2) * ∫ x, (ω' s x - ω s x) ^ 2 := by
  set δ : ℝ → ℂ → ℝ := fun r x => ω' r x - ω r x with hδdef
  have hU : IsOpen (Ioo a b ×ˢ (univ : Set ℂ)) := isOpen_Ioo.prod isOpen_univ
  have hδC1 : ContDiffOn ℝ 1 (Function.uncurry δ) (Ioo a b ×ˢ univ) :=
    hω'.sub hωs.contDiffOn
  have hδvan : ∀ r ∈ Ioo a b, ∀ x, x ∉ ball (0 : ℂ) ρ → δ r x = 0 := by
    intro r hr x hx
    simp [hδdef, hvan' r hr x hx, hvan r hr x hx]
  obtain ⟨hint, hder⟩ := hasDerivAt_integral_sq hδC1 hδvan hs
  refine ⟨hder, ?_⟩
  -- regularity of the slices
  have hnhds : ∀ x, Ioo a b ×ˢ (univ : Set ℂ) ∈ 𝓝 (s, x) := fun x =>
    hU.mem_nhds ⟨hs, trivial⟩
  have hω's : ContDiff ℝ 1 (ω' s) := contDiff_slice hω' hnhds
  have hωss : ContDiff ℝ 1 (ω s) := contDiff_slice hωs.contDiffOn (fun _ => univ_mem)
  have hδs : ContDiff ℝ 1 (δ s) := hω's.sub hωss
  have hdω' : ∀ x, DifferentiableAt ℝ (Function.uncurry ω') (s, x) := fun x =>
    (hω'.contDiffAt (hnhds x)).differentiableAt one_ne_zero
  have hdω : ∀ x, DifferentiableAt ℝ (Function.uncurry ω) (s, x) := fun x =>
    (hωs.differentiable one_ne_zero) (s, x)
  apply abs_integral_le_of_transport (δ := δ s) (v := velocityField ω s)
    (D := fun x => fderiv ℝ (ω' s) x) hρ hL hδs (hδvan s hs) (hv s) (hdiv s) (hD s hs) hint
  intro x
  -- the equation for `δ`
  have h1 : deriv (fun r => δ r x) s = deriv (fun r => ω' r x) s - deriv (fun r => ω r x) s :=
    deriv_fun_sub (hasDerivAt_uncurry_left (hdω' x)).differentiableAt
      (hasDerivAt_uncurry_left (hdω x)).differentiableAt
  have h2 : deriv (fun r => ω' r x) s = -fderiv ℝ (ω' s) x (velocity (ω' s) x) := by
    have := htr' s hs x
    rw [fderiv_uncurry_apply_one (hdω' x)] at this
    linarith
  have h3 : deriv (fun r => ω r x) s = -fderiv ℝ (ω s) x (velocityField ω s x) := by
    have := htr s x
    linarith
  have h4 : fderiv ℝ (δ s) x = fderiv ℝ (ω' s) x - fderiv ℝ (ω s) x :=
    fderiv_fun_sub ((hω's.differentiable one_ne_zero) x) ((hωss.differentiable one_ne_zero) x)
  have h5 : velocity (δ s) x = velocity (ω' s) x - velocityField ω s x :=
    (velocity_sub hω's.continuous hωss.continuous (hvan' s hs) (hvan s hs) x).symm
  rw [h1, h2, h3, h4, h5]
  simp only [sub_apply, map_sub]
  ring

end UniqueAux

open UniqueAux

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

/-- thm:smooth (5) for any `ω` with (1)–(3): if `I ∋ 0` is an interval and `ω̃ ∈ C¹(I × ℝ²)`
satisfies `ω̃(0) = ω₀`, `∂_t ω̃ + (K_BS ∗ ω̃)·∇ω̃ = 0` on `I × ℝ²`, and has supports in one disk on
each compact subinterval of `I`, then `ω̃ = ω` on `I × ℝ²`. -/
theorem isC1SolOn_eq_of_isSmoothSol (h : IsSmoothDatum ω₀ R₀) {ω : ℝ → ℂ → ℝ}
    (hω : IsSmoothSol ω₀ R₀ ω) {I : Set ℝ} (hI : I.OrdConnected) (h0 : 0 ∈ I)
    {ω' : ℝ → ℂ → ℝ} (hω' : IsC1SolOn I ω₀ ω') :
    ∀ t ∈ I, ω' t = ω t := by
  intro t ht
  by_cases ht0 : t = 0
  · subst ht0
    rw [hω'.init, hω.init]
  -- the interval `J = [a, b]`
  set a : ℝ := min 0 t with ha
  set b : ℝ := max 0 t with hb
  have hab : a < b := min_lt_max.2 (Ne.symm ht0)
  have hJ : Icc a b ⊆ I := hI.uIcc_subset h0 ht
  have h0J : (0 : ℝ) ∈ Icc a b := ⟨min_le_left _ _, le_max_left _ _⟩
  have htJ : t ∈ Icc a b := ⟨min_le_right _ _, le_max_right _ _⟩
  -- the radius `ρ`
  obtain ⟨R, hR⟩ := hω'.tsupport_bounded a b hJ
  set ρ : ℝ := max (max R (suppRadius ω₀ R₀ t)) 0 + 1 with hρdef
  have hρ : 0 < ρ := by positivity
  have hRρ : R ≤ ρ := by
    have := le_max_left R (suppRadius ω₀ R₀ t)
    have := le_max_left (max R (suppRadius ω₀ R₀ t)) 0
    linarith
  have hSρ : suppRadius ω₀ R₀ t ≤ ρ := by
    have := le_max_right R (suppRadius ω₀ R₀ t)
    have := le_max_left (max R (suppRadius ω₀ R₀ t)) 0
    linarith
  have hvan' : ∀ s ∈ Icc a b, ∀ x, x ∉ ball (0 : ℂ) ρ → ω' s x = 0 := by
    intro s hs x hx
    refine image_eq_zero_of_notMem_tsupport (fun hx' => hx ?_)
    exact ball_subset_ball hRρ (hR s hs hx')
  have hvan : ∀ s ∈ Icc a b, ∀ x, x ∉ ball (0 : ℂ) ρ → ω s x = 0 := by
    intro s hs x hx
    refine image_eq_zero_of_notMem_tsupport (fun hx' => hx ?_)
    refine ball_subset_ball ?_ (hω.tsupport_subset s hx')
    exact (suppRadius_mono_abs ω₀ R₀ (abs_le_of_mem_Icc_min_max hs)).trans hSρ
  -- regularity
  have hωs : ContDiff ℝ 1 (Function.uncurry ω) := hω.contDiff.of_le (by exact_mod_cast le_top)
  have hv : ∀ s, ContDiff ℝ 1 (velocityField ω s) := by
    intro s
    have hV : ContDiff ℝ 1 (Function.uncurry (velocityField ω)) :=
      hω.velocity_contDiff.of_le (by exact_mod_cast le_top)
    have hcomp : velocityField ω s = Function.uncurry (velocityField ω) ∘ (fun y : ℂ => (s, y)) :=
      rfl
    rw [hcomp]
    exact hV.comp ((contDiff_const (c := s)).prodMk contDiff_id)
  have hC1 : ContDiffOn ℝ 1 (Function.uncurry ω') (Icc a b ×ˢ univ) :=
    hω'.contDiffOn.mono (prod_mono hJ subset_rfl)
  have hnhds : ∀ s ∈ Ioo a b, ∀ x : ℂ, Icc a b ×ˢ (univ : Set ℂ) ∈ 𝓝 (s, x) := fun s hs x =>
    prod_mem_nhds (Icc_mem_nhds hs.1 hs.2) univ_mem
  -- the bound `L` on `Dω̃` over `J × B̄_ρ`
  have huniq : UniqueDiffOn ℝ (Icc a b ×ˢ (univ : Set ℂ)) :=
    (uniqueDiffOn_Icc hab).prod uniqueDiffOn_univ
  have hcont := hC1.continuousOn_fderivWithin huniq le_rfl
  obtain ⟨L₀, hL₀⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : ℂ) ρ)).exists_bound_of_continuousOn
    (hcont.mono (prod_mono subset_rfl (subset_univ _)))
  set L : ℝ := max L₀ 0 with hLdef
  have hL : 0 ≤ L := le_max_right _ _
  have hdω' : ∀ s ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (Function.uncurry ω') (s, x) :=
    fun s hs x => (hC1.contDiffAt (hnhds s hs x)).differentiableAt one_ne_zero
  have hD : ∀ s ∈ Ioo a b, ∀ x ∈ ball (0 : ℂ) ρ, ∀ w, |fderiv ℝ (ω' s) x w| ≤ L * ‖w‖ := by
    intro s hs x hx w
    rw [fderiv_uncurry_right (hdω' s hs x)]
    have hle := hL₀ (s, x) ⟨Ioo_subset_Icc_self hs, ball_subset_closedBall hx⟩
    rw [fderivWithin_of_mem_nhds (hnhds s hs x)] at hle
    calc |fderiv ℝ (Function.uncurry ω') (s, x) (0, w)|
        = ‖fderiv ℝ (Function.uncurry ω') (s, x) (0, w)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (Function.uncurry ω') (s, x)‖ * ‖((0 : ℝ), w)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * ‖w‖ := by
          have hn : ‖((0 : ℝ), w)‖ = ‖w‖ := by simp [Prod.norm_def]
          rw [hn]
          exact mul_le_mul_of_nonneg_right (hle.trans (le_max_left _ _)) (norm_nonneg _)
  have htr' : ∀ s ∈ Ioo a b, ∀ x,
      fderiv ℝ (Function.uncurry ω') (s, x) (1, velocity (ω' s) x) = 0 := by
    intro s hs x
    have := hω'.transport s (hJ (Ioo_subset_Icc_self hs)) x
    rwa [fderivWithin_of_mem_nhds (mem_of_superset (hnhds s hs x)
      (prod_mono hJ subset_rfl))] at this
  -- the energy
  set E : ℝ → ℝ := fun r => ∫ x, (ω' r x - ω r x) ^ 2 with hEdef
  set E' : ℝ → ℝ := fun s => ∫ x, 2 * (ω' s x - ω s x) * deriv (fun r => ω' r x - ω r x) s
    with hE'def
  have hstep : ∀ s ∈ Ioo a b, HasDerivAt E (E' s) s ∧
      |E' s| ≤ L * (1 + 4 * ρ ^ 2) * E s := fun s hs =>
    energy_step hρ hL hωs hv hω.divergence_eq_zero hω.transport
      (hC1.mono (prod_mono Ioo_subset_Icc_self subset_rfl)) htr'
      (fun r hr => hvan' r (Ioo_subset_Icc_self hr)) (fun r hr => hvan r (Ioo_subset_Icc_self hr))
      hD hs
  have hδcont : ContinuousOn (Function.uncurry fun r x => ω' r x - ω r x) (Icc a b ×ˢ univ) :=
    hC1.continuousOn.sub hωs.continuous.continuousOn
  have hEcont : ContinuousOn E (Icc a b) := by
    refine continuousOn_integral_sq (ρ := ρ) hδcont (fun r hr x hx => ?_)
    simp [hvan' r hr x hx, hvan r hr x hx]
  have hEnn : ∀ s ∈ Icc a b, 0 ≤ E s := fun s _ => integral_nonneg (fun x => sq_nonneg _)
  have hE0 : E 0 = 0 := by
    simp [hEdef, hω'.init, hω.init]
  have hEt := eq_zero_of_abs_deriv_le_mul h0J hEcont hEnn (fun s hs => (hstep s hs).1)
    (fun s hs => (hstep s hs).2) hE0 t htJ
  -- `δ(t) = 0`
  have hδt : Continuous (fun x => ω' t x - ω t x) :=
    hδcont.comp_continuous (Continuous.prodMk_right t) (fun x => ⟨htJ, trivial⟩)
  have hδtv : ∀ x, x ∉ ball (0 : ℂ) ρ → ω' t x - ω t x = 0 := fun x hx => by
    simp [hvan' t htJ x hx, hvan t htJ x hx]
  have hint : Integrable (fun x => (ω' t x - ω t x) ^ 2) :=
    (memLp_of_vanish hδt hδtv 2).integrable_sq
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint).1 hEt
  have heq : (fun x => (ω' t x - ω t x) ^ 2) = fun _ => (0 : ℝ) :=
    (Continuous.ae_eq_iff_eq volume (hδt.pow 2) continuous_const).1 hae
  funext x
  have := congrFun heq x
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at this
  linarith

end NonUniqueEuler.Smooth
