import NonUniqueEuler.Defs.SmoothB.Iteration
import NonUniqueEuler.I.SmoothB.IterLimit
import NonUniqueEuler.I.SmoothB.Smooth
import NonUniqueEuler.I.SmoothB.OpNormEntry

/-!
# Proof of `lem:smooth-bounds` (explicit bounds on the smooth solution)

Proof of `I/SmoothB/SmoothBounds.lean` (`B_global_smooth.tex:479-491`, joint proof with thm:smooth
`:493-521`).

`iter_limit` gives `ω` with `IsSmoothSolAll ω₀ ω` and the bounds `eq:limit-bounds`. Both `ω` and
`sol ω₀` satisfy `IsSmoothSol ω₀ R₀` (`IsSmoothSolAll.isSmoothSol`, `sol_spec`), so they agree by
the uniqueness in `smooth_existsUnique`. Then `vel ω₀ = velocityField ω`; the first three bounds are
`eq:limit-bounds`, the last follows from the entry bound and
`norm_fderiv_le_two_mul_of_gradEntry_le` (`‖M‖_op ≤ 2 max_{i,l} |M_il|`).
-/

noncomputable section

namespace NonUniqueEuler.Smooth

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

/-- For a nonzero smooth datum, `sol ω₀` is the limit function of `iter_limit`, so it satisfies
the bounds `eq:limit-bounds`. -/
private theorem sol_limit_bounds (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) :
    (∀ t : ℝ, ∀ x : ℂ, ‖fderiv ℝ (sol ω₀ t) x‖ ≤ Psi ω₀ t) ∧
      (∀ t : ℝ, ∀ x : ℂ, ‖vel ω₀ t x‖ ≤ Ustar ω₀) ∧
      (∀ t : ℝ, ∀ x : ℂ, ∀ i l : Fin 2,
        |Prelim.gradEntry (vel ω₀ t) i l x| ≤ Amax ω₀ * (calL ω₀ t + cstar ω₀)) := by
  obtain ⟨ω, -, -, hall, -, -, hgrad, hvel, hentry⟩ := iter_limit h hne
  have hsolAll : IsSmoothSolAll ω₀ (sol ω₀) := sol_spec ⟨ω, hall⟩
  have heq : ω = sol ω₀ :=
    (smooth_existsUnique h).unique (hall.isSmoothSol h.tsupport_subset)
      (hsolAll.isSmoothSol h.tsupport_subset)
  subst heq
  exact ⟨hgrad, hvel, hentry⟩

/-- `lem:smooth-bounds`: for `ω₀ ≢ 0`, for every `t ∈ ℝ` and `x ∈ ℝ²`,
`|∇ω(t, x)| ≤ Ψ(t)`, `|v(t, x)| ≤ U_*`, `max_{i,l} |∂_l v_i(t, x)| ≤ A(𝓛(t) + c_*)` and
`‖∇v(t, x)‖_op ≤ 2A(𝓛(t) + c_*)`. -/
theorem smooth_bounds (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) (x : ℂ) :
    ‖fderiv ℝ (sol ω₀ t) x‖ ≤ Psi ω₀ t ∧
      ‖vel ω₀ t x‖ ≤ Ustar ω₀ ∧
      (∀ i l : Fin 2, |Prelim.gradEntry (vel ω₀ t) i l x| ≤ Amax ω₀ * (calL ω₀ t + cstar ω₀)) ∧
      ‖fderiv ℝ (vel ω₀ t) x‖ ≤ 2 * Amax ω₀ * (calL ω₀ t + cstar ω₀) := by
  obtain ⟨hgrad, hvel, hentry⟩ := sol_limit_bounds h hne
  refine ⟨hgrad t x, hvel t x, hentry t x, ?_⟩
  rw [mul_assoc]
  exact norm_fderiv_le_two_mul_of_gradEntry_le (hentry t x)

end NonUniqueEuler.Smooth
