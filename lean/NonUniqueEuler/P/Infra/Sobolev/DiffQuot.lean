import NonUniqueEuler.H.Infra.Sobolev.DiffQuot.Core
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Proof: the difference-quotient bound for `H¹` functions on balls (library I-HK)

Proves `I/Infra/Sobolev/DiffQuot.lean`: for `f ∈ H¹(B_r)` and `R + |h| < r`,
`‖f - f(· - h)‖_{L²(B_R)} ≤ |h| ‖f‖_{H¹(B_r)}`.

**Proof.** Take `L²(B_r)` weak derivatives `g₁ = ∂₁ f`, `g₂ = ∂₂ f` on `B_r`, and replace `f`,
`g₁`, `g₂` by strongly measurable modifications supported in `B_r` (they agree a.e. on `B_r`,
so the weak-derivative relations and the left side are unchanged; they are integrable on the
plane because `B_r` has finite measure). The core bound
`DiffQuotAux.eLpNorm_sub_comp_sub_le_of_integrable` (`H/Infra/Sobolev/DiffQuot/Core.lean`)
gives `‖f - f(·-h)‖_{L²(B_R)} ≤ ‖h.re g₁ + h.im g₂‖_{L²(B_r)}`; the triangle inequality and
Cauchy–Schwarz give `≤ |h| (‖g₁‖² + ‖g₂‖²)^{1/2} ≤ |h| ‖f‖_{H¹(B_r)}`, where
`‖g_i‖_{L²(B_r)}` is the norm of the chosen weak derivative `weakPartialOn` by uniqueness
(`weakDerivOn_ae_eq`).

**Deviation from the interface sketch.** No mollification: the identity
`f(x) - f(x-h) = ∫_0^1 ∂_h f(x - s h) ds` (a.e. on `B_R`) is proved directly in the weak form,
by testing against `ψ ∈ C_c^∞(B_R)` and using the fundamental lemma of the calculus of
variations; the `L²` bound is Minkowski's integral inequality.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Sob

namespace DiffQuotAux

/-- `L²` on a ball implies integrable on the ball. -/
theorem integrableOn_ball_of_memLp {r : ℝ} {g : ℂ → ℂ}
    (hg : MemLp g 2 (volume.restrict (ball (0 : ℂ) r))) : IntegrableOn g (ball (0 : ℂ) r) := by
  have : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  exact hg.integrable one_le_two

/-- A strongly measurable modification supported in the ball, integrable on the plane, equal to
`g` a.e. on the ball. -/
theorem exists_good_modification {r : ℝ} {g : ℂ → ℂ}
    (hg : MemLp g 2 (volume.restrict (ball (0 : ℂ) r))) :
    ∃ g' : ℂ → ℂ, StronglyMeasurable g' ∧ Integrable g' ∧
      ∀ᵐ x, x ∈ ball (0 : ℂ) r → g x = g' x := by
  refine ⟨(ball (0 : ℂ) r).indicator (hg.1.mk g),
    hg.1.stronglyMeasurable_mk.indicator measurableSet_ball, ?_, ?_⟩
  · rw [integrable_indicator_iff measurableSet_ball]
    exact integrableOn_ball_of_memLp (hg.ae_eq hg.1.ae_eq_mk)
  · have := hg.1.ae_eq_mk
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball] at this
    filter_upwards [this] with x hx hxB
    rw [indicator_of_mem hxB]
    exact hx hxB

/-- The `L²(B_r)` norm of a weak derivative is that of the chosen one. -/
theorem eLpNorm_eq_ofReal_l2On {r : ℝ} {f g g' : ℂ → ℂ} {γ : ℕ × ℕ}
    (hg : MemLp g 2 (volume.restrict (ball (0 : ℂ) r)))
    (hfg : HasWeakDerivOn (ball (0 : ℂ) r) (pdList γ) f g)
    (hgg' : ∀ᵐ x, x ∈ ball (0 : ℂ) r → g x = g' x) :
    eLpNorm g' 2 (volume.restrict (ball (0 : ℂ) r)) =
      ENNReal.ofReal (l2On (ball (0 : ℂ) r) (weakPartialOn (ball (0 : ℂ) r) γ f)) := by
  have hae := weakDerivOn_ae_eq isOpen_ball (integrableOn_ball_of_memLp hg).locallyIntegrableOn
    hfg
  have h1 : eLpNorm g' 2 (volume.restrict (ball (0 : ℂ) r)) =
      eLpNorm (weakPartialOn (ball (0 : ℂ) r) γ f) 2 (volume.restrict (ball (0 : ℂ) r)) := by
    apply eLpNorm_congr_ae
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
    filter_upwards [hae, hgg'] with x hx1 hx2 hxB
    rw [← hx2 hxB, ← hx1 hxB]
    rfl
  have h2 : eLpNorm (weakPartialOn (ball (0 : ℂ) r) γ f) 2 (volume.restrict (ball (0 : ℂ) r))
      ≠ ⊤ := by
    rw [← h1, ← eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_ball).2 hgg')]
    exact hg.2.ne
  rw [h1, l2On, ENNReal.ofReal_toReal h2]

/-- Cauchy–Schwarz: `|h.re| a + |h.im| b ≤ |h| (a² + b²)^{1/2}`. -/
theorem abs_re_mul_add_le (h : ℂ) (a b : ℝ) :
    |h.re| * a + |h.im| * b ≤ ‖h‖ * Real.sqrt (a ^ 2 + b ^ 2) := by
  have hn : ‖h‖ ^ 2 = |h.re| ^ 2 + |h.im| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, sq_abs, sq_abs]
    ring
  have hsq : (|h.re| * a + |h.im| * b) ^ 2 ≤ ‖h‖ ^ 2 * (a ^ 2 + b ^ 2) := by
    rw [hn]
    nlinarith [sq_nonneg (|h.re| * b - |h.im| * a)]
  calc |h.re| * a + |h.im| * b ≤ |(|h.re| * a + |h.im| * b)| := le_abs_self _
    _ ≤ Real.sqrt (‖h‖ ^ 2 * (a ^ 2 + b ^ 2)) := Real.abs_le_sqrt hsq
    _ = ‖h‖ * Real.sqrt (a ^ 2 + b ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- `(‖∂₁ f‖² + ‖∂₂ f‖²)^{1/2} ≤ ‖f‖_{H¹(V)}`. -/
theorem sqrt_l2On_sq_add_le (V : Set ℂ) (f : ℂ → ℂ) :
    Real.sqrt (l2On V (weakPartialOn V (1, 0) f) ^ 2 + l2On V (weakPartialOn V (0, 1) f) ^ 2) ≤
      normHOn 1 V f := by
  unfold normHOn
  apply Real.sqrt_le_sqrt
  have hsub : ({(1, 0), (0, 1)} : Finset (ℕ × ℕ)) ⊆ multiIdx 1 := by
    intro γ hγ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
    rcases hγ with rfl | rfl <;> simp [mem_multiIdx]
  have hne : ((1, 0) : ℕ × ℕ) ≠ (0, 1) := by decide
  calc l2On V (weakPartialOn V (1, 0) f) ^ 2 + l2On V (weakPartialOn V (0, 1) f) ^ 2
      = ∑ γ ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ)), l2On V (weakPartialOn V γ f) ^ 2 := by
        rw [Finset.sum_pair hne]
    _ ≤ ∑ γ ∈ multiIdx 1, l2On V (weakPartialOn V γ f) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)

end DiffQuotAux

/-- The difference-quotient bound: for `f ∈ H¹(B_r)` and `R + |h| < r`,
`‖f - f(· - h)‖_{L²(B_R)} ≤ |h| ‖f‖_{H¹(B_r)}`. -/
theorem MemHOn.eLpNorm_sub_comp_sub_le {r : ℝ} {f : ℂ → ℂ}
    (hf : MemHOn 1 (ball (0 : ℂ) r) f) {R : ℝ} {h : ℂ} (hRr : R + ‖h‖ < r) :
    eLpNorm (fun x => f x - f (x - h)) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
      ENNReal.ofReal (‖h‖ * normHOn 1 (ball (0 : ℂ) r) f) := by
  -- the weak derivatives `∂₁ f`, `∂₂ f` in `L²(B_r)`
  obtain ⟨g₁, hg₁, hfg₁⟩ := hf.deriv (1, 0) (by simp [mem_multiIdx])
  obtain ⟨g₂, hg₂, hfg₂⟩ := hf.deriv (0, 1) (by simp [mem_multiIdx])
  have hfg₁' : HasWeakDerivOn (ball (0 : ℂ) r) [1] f g₁ := by simpa [pdList] using hfg₁
  have hfg₂' : HasWeakDerivOn (ball (0 : ℂ) r) [Complex.I] f g₂ := by simpa [pdList] using hfg₂
  -- strongly measurable, integrable modifications
  obtain ⟨f', -, hf'i, hff'⟩ := DiffQuotAux.exists_good_modification hf.memLp
  obtain ⟨g₁', hg₁'m, hg₁'i, hgg₁'⟩ := DiffQuotAux.exists_good_modification hg₁
  obtain ⟨g₂', hg₂'m, hg₂'i, hgg₂'⟩ := DiffQuotAux.exists_good_modification hg₂
  have h₁ : HasWeakDerivOn (ball (0 : ℂ) r) [1] f' g₁' := hfg₁'.congr_ae hff' hgg₁'
  have h₂ : HasWeakDerivOn (ball (0 : ℂ) r) [Complex.I] f' g₂' := hfg₂'.congr_ae hff' hgg₂'
  have hcore := DiffQuotAux.eLpNorm_sub_comp_sub_le_of_integrable (R := R) (h := h) hRr.le hf'i
    hg₁'m hg₁'i hg₂'m hg₂'i h₁ h₂
  -- the left side only sees `f` on `B_r`
  have hLHS : eLpNorm (fun x => f x - f (x - h)) 2 (volume.restrict (ball (0 : ℂ) R)) =
      eLpNorm (fun x => f' x - f' (x - h)) 2 (volume.restrict (ball (0 : ℂ) R)) := by
    apply eLpNorm_congr_ae
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
    have hsh : ∀ᵐ x, x - h ∈ ball (0 : ℂ) r → f (x - h) = f' (x - h) :=
      (measurePreserving_sub_right volume h).quasiMeasurePreserving.ae hff'
    filter_upwards [hff', hsh] with x hx1 hx2 hxR
    have hxR' : ‖x‖ < R := mem_ball_zero_iff.1 hxR
    have hxB : x ∈ ball (0 : ℂ) r := mem_ball_zero_iff.2 (by linarith [norm_nonneg h])
    have hxhB : x - h ∈ ball (0 : ℂ) r := by
      rw [mem_ball_zero_iff]
      calc ‖x - h‖ ≤ ‖x‖ + ‖h‖ := norm_sub_le _ _
        _ < r := by linarith
    rw [hx1 hxB, hx2 hxhB]
  rw [hLHS]
  refine hcore.trans ?_
  -- `‖h.re g₁ + h.im g₂‖ ≤ |h.re| ‖g₁‖ + |h.im| ‖g₂‖ ≤ |h| ‖f‖_{H¹}`
  set μ := volume.restrict (ball (0 : ℂ) r)
  set a := l2On (ball (0 : ℂ) r) (weakPartialOn (ball (0 : ℂ) r) (1, 0) f)
  set b := l2On (ball (0 : ℂ) r) (weakPartialOn (ball (0 : ℂ) r) (0, 1) f)
  have ha : eLpNorm g₁' 2 μ = ENNReal.ofReal a :=
    DiffQuotAux.eLpNorm_eq_ofReal_l2On hg₁ hfg₁ hgg₁'
  have hb : eLpNorm g₂' 2 μ = ENNReal.ofReal b :=
    DiffQuotAux.eLpNorm_eq_ofReal_l2On hg₂ hfg₂ hgg₂'
  have htri : eLpNorm (fun y => (h.re : ℂ) * g₁' y + (h.im : ℂ) * g₂' y) 2 μ ≤
      ‖(h.re : ℂ)‖ₑ * eLpNorm g₁' 2 μ + ‖(h.im : ℂ)‖ₑ * eLpNorm g₂' 2 μ := by
    have hfun : (fun y => (h.re : ℂ) * g₁' y + (h.im : ℂ) * g₂' y) =
        ((h.re : ℂ) • g₁') + ((h.im : ℂ) • g₂') := by
      funext y
      simp
    rw [hfun, ← eLpNorm_const_smul, ← eLpNorm_const_smul]
    exact eLpNorm_add_le ((hg₁'m.aestronglyMeasurable).const_smul _)
      ((hg₂'m.aestronglyMeasurable).const_smul _) one_le_two
  refine htri.trans ?_
  rw [ha, hb, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
    ← ENNReal.ofReal_mul (norm_nonneg _),
    ← ENNReal.ofReal_add (mul_nonneg (norm_nonneg _) (l2On_nonneg _ _))
      (mul_nonneg (norm_nonneg _) (l2On_nonneg _ _))]
  apply ENNReal.ofReal_le_ofReal
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |h.re| * a + |h.im| * b ≤ ‖h‖ * Real.sqrt (a ^ 2 + b ^ 2) :=
        DiffQuotAux.abs_re_mul_add_le h a b
    _ ≤ ‖h‖ * normHOn 1 (ball (0 : ℂ) r) f :=
        mul_le_mul_of_nonneg_left (DiffQuotAux.sqrt_l2On_sq_add_le _ f) (norm_nonneg h)

end NonUniqueEuler.Sob
