import NonUniqueEuler.H.Sec5.Energy.Pointwise
import NonUniqueEuler.H.Sec5.Energy.Gronwall

/-!
# Proof of `lem:energy` (the crude energy estimate)

Proof of `I/Sec5/Energy.lean` (`05_single_ring.tex:300-373`). Same declaration, statement
copied verbatim.

Structure (the manuscript's proof, `05_single_ring.tex:317-373`):
1. `v = w - w_app` is a `C¹` path in `Y^s(N)` (`lem:reduction`(3), `reduction_eq`, and the
   hypothesis on `w_app`), with derivative `V' = toY(∂_t w) - toY(∂_t w_app)`; its norm is the
   `H^s` norm (`EnergyH.MemXFn.norm_toY`).
2. `d/dτ ‖v‖²_{H^s} = 2 Re ⟪v, v'⟫_{H^s}` (`HasDerivWithinAt.norm_sq` for the real inner product
   space underlying `Y^s(N)`).
3. The energy inequality at each time, `Re ⟪v, v'⟫ ≤ Λ(s)‖v‖² + ‖R_app‖‖v‖`
   (`EnergyH.energy_pointwise`, `H/Sec5/Energy/Pointwise.lean`, from the step interfaces
   `I/Sec5/Energy/{VEquation,FieldBounds,RappPath}.lean`, `lem:bilinear` and
   `lem:Hk-calculus`(1)).
4. `τ ↦ ‖R_app(τ)‖_{H^s}` is continuous (`rapp_pathC`), `Λ(s) > 0` (`lambda_ge`), and the
   Grönwall comparison for `y_ε = (‖v‖² + ε²)^{1/2}` (`EnergyH.le_of_hasDerivWithinAt_sq`,
   `H/Sec5/Energy/Gronwall.lean`) concludes.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- **`lem:energy`** (`05_single_ring.tex:300-316`). Assume (N1)–(N3). Let `s ≥ 3`, let the
assumptions of `lem:reduction`(3) hold on `[0,t]` with `G = c.G ∈ [0,G₁]` and `w = ω_r - Φ`, let
`w_app ∈ C([0,t];X^{s+1}) ∩ C¹([0,t];X^s)` be real valued with time derivative `w_app'`, and
assume `‖w‖_{H^s} ≤ 1`, `‖w_app‖_{H^{s+1}} ≤ 1`, `‖h‖_{C^{s+1}(N')} ≤ 1` on `[0,t]`. Then for
`τ ∈ [0,t]`, `‖(w - w_app)(τ)‖_{H^s} ≤ e^{Λ(s)τ}‖(w - w_app)(0)‖_{H^s} +
∫₀^τ e^{Λ(s)(τ-τ')}‖R_app(τ')‖_{H^s} dτ'`. -/
theorem energy (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 3 ≤ s) {c : RingConfig} {t : ℝ} (hc : c.Hyp t)
    (hG : c.G ∈ Icc (0 : ℝ) Gbar) (hsupp : c.RingSupportedIn t annN)
    {wapp wapp' : ℝ → ℂ → ℂ} (happ : PathC (s + 1) t wapp) (happ' : PathC1 s t wapp wapp')
    (hreal : ∀ τ ∈ Icc (0 : ℝ) t, ∀ᵐ x ∂(volume : Measure ℂ), (wapp τ x).im = 0)
    (hw : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH s (c.w χ τ) ≤ 1)
    (hwapp : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH (s + 1) (wapp τ) ≤ 1)
    (hh : ∀ τ ∈ Icc (0 : ℝ) t, normCk (s + 1) annN' (c.h τ) ≤ 1) :
    ∀ τ ∈ Icc (0 : ℝ) t,
      Sob.normH s (c.w χ τ - wapp τ) ≤
        Real.exp (Lam χ s * τ) * Sob.normH s (c.w χ 0 - wapp 0) +
          ∫ τ' in (0 : ℝ)..τ, Real.exp (Lam χ s * (τ - τ')) *
            Sob.normH s (Rapp χ c.G c.h wapp wapp' τ') := by
  -- `w_app` real valued is not needed: the energy identity of `lem:Hk-calculus`(1) is used in
  -- its real-part form, valid for complex `v`.
  have _unused := hreal
  have hKm : MeasurableSet annN := (Sect.isClosed_closedAnnulus _ _).measurableSet
  obtain ⟨-, hΛpos⟩ := lambda_ge χ hχ hN hs
  obtain ⟨-, hpert⟩ := reduction_eq χ hχ hc hsupp
  have hR := rapp_pathC χ hχ hN hs hc happ happ'
  -- the path `v` in `Y^s(N)` and its derivative
  set V : ℝ → Sect.Y s annN := fun τ => Sect.toY s annN (c.w χ τ - wapp τ) with hVdef
  set V' : ℝ → Sect.Y s annN := fun τ =>
    Sect.toY s annN (ringRHS χ c.G (c.h τ) (c.w χ τ)) - Sect.toY s annN (wapp' τ) with hV'def
  have hmem : ∀ τ ∈ Icc (0 : ℝ) t, Lin.MemXFn s (c.w χ τ - wapp τ) := fun τ hτ =>
    EnergyH.MemXFn.sub ((hpert s).1.1 τ hτ) (happ'.1.1 τ hτ)
  have hVsub : ∀ τ ∈ Icc (0 : ℝ) t,
      V τ = Sect.toY s annN (c.w χ τ) - Sect.toY s annN (wapp τ) := fun τ hτ =>
    EnergyH.toY_sub hKm ((hpert s).1.1 τ hτ).1 ((hpert s).1.1 τ hτ).2.1 (happ'.1.1 τ hτ).1
      (happ'.1.1 τ hτ).2.1
  have hVd : ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt V (V' τ) (Icc 0 t) τ := fun τ hτ =>
    (((hpert s).2.2 τ hτ).sub (happ'.2.2 τ hτ)).congr_of_mem (fun σ hσ => hVsub σ hσ) hτ
  -- `d/dτ ‖v‖² = 2 Re ⟪v, v'⟫`
  have hVd2 : ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt (fun σ => ‖V σ‖ ^ 2)
      (2 * (inner ℂ (V τ) (V' τ)).re) (Icc 0 t) τ := by
    intro τ hτ
    let _ : InnerProductSpace ℝ (Sect.Y s annN) := InnerProductSpace.complexToReal
    exact (hVd τ hτ).norm_sq
  have hnorm : ∀ τ ∈ Icc (0 : ℝ) t, ‖V τ‖ = Sob.normH s (c.w χ τ - wapp τ) := fun τ hτ =>
    EnergyH.MemXFn.norm_toY (hmem τ hτ)
  -- the forcing `‖R_app‖_{H^s}` is continuous on `[0,t]`
  set r : ℝ → ℝ := fun τ => Sob.normH s (Rapp χ c.G c.h wapp wapp' τ) with hrdef
  have hrc : ContinuousOn r (Icc 0 t) := by
    have h1 : ContinuousOn (fun τ => ‖Sect.toY s annN (Rapp χ c.G c.h wapp wapp' τ)‖)
        (Icc 0 t) := hR.2.norm
    exact h1.congr fun τ hτ => (EnergyH.MemXFn.norm_toY (hR.1 τ hτ)).symm
  have hr0 : ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ r τ := fun τ _ => Sob.normH_nonneg _ _
  -- the differential inequality
  have hineq : ∀ τ ∈ Icc (0 : ℝ) t,
      2 * (inner ℂ (V τ) (V' τ)).re ≤ 2 * (Lam χ s * ‖V τ‖ ^ 2 + r τ * ‖V τ‖) := by
    intro τ hτ
    have h := EnergyH.energy_pointwise χ hχ hN hs hc hG hsupp happ happ' hw hwapp hh hτ
    rw [hnorm τ hτ]
    simp only [hVdef, hV'def, hrdef]
    linarith
  have key := EnergyH.le_of_hasDerivWithinAt_sq hΛpos.le (fun τ _ => norm_nonneg (V τ)) hVd2
    hineq hrc hr0
  intro τ hτ
  have h := key τ hτ
  rw [hnorm τ hτ, hnorm 0 ⟨le_rfl, hc.T_pos.le⟩] at h
  exact h

end OneRing

end NonUniqueEuler
