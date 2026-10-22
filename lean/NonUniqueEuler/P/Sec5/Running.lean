import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec4.PropSemigroup
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.Duhamel
import NonUniqueEuler.H.Sec5.Running.Bridge
import NonUniqueEuler.H.Sec5.Running.EllCongr
import NonUniqueEuler.H.Sec5.Running.Forcing
import NonUniqueEuler.H.Sec5.Running.Integrand

/-!
# Proof: `lem:running` and `eq:running` (the running coefficient)

Proof of `I/Sec5/Running.lean` (same declaration, statement copied verbatim). Manuscript
`05_single_ring.tex:587-611`.

Steps (as in the manuscript proof):
1. `F(v) = -h(v)·∇Φ` is continuous on `[0,ū]` into `X^s`, real (`RunningAux.forcing_path`,
   `H/Sec5/Running/Forcing.lean`), and `w₀` gives the real element `toY s annN w₀ ∈ X^s`
   (`RunningAux.memX_toY`, `H/Sec5/Running/Bridge.lean`).
2. The integrand `v ↦ e^{(u-v)L}F(v)` is continuous on `[0,u]`, hence integrable
   (`RunningAux.intervalIntegrable_S_comp`, `H/Sec5/Running/Integrand.lean`), with values in
   `X^s` (`Lin.S_memX`) and real (`Lin.S_isReal`); `X^s` and the real elements are closed under
   such integrals (`RunningAux.intervalIntegral_memX`, `RunningAux.intervalIntegral_isReal`).
   So `wlin₀(u) ∈ X^s` is real.
3. `ℓ_*` is a bounded functional (`Eig.exists_ell`), so it commutes with the integral, and
   `prop:semigroup` gives `ℓ_*(e^{τL}f) = e^{λ_*τ}ℓ_*(f)` (`Eig.propSemigroup_formulas`);
   `ℓ_*` on functions sees only the a.e. class (`RunningAux.ellFn_congr_ae`). Hence
   `ℓ_*(wlin₀(u)) = e^{λ_*u}ℓ_*(w₀) + ∫₀ᵘ e^{λ_*(u-v)}ℓ_*(F(v))dv = c(u)e^{λ_*u}`.
4. `wlin₀(u)` is real, so `R(G)wlin₀(u) = 2Re(ℓ_*(wlin₀(u))φ_*)` (`Eig.R_of_isReal`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- **`lem:running`** (`05_single_ring.tex:587-600`), at level `s` (`s = 0` is the manuscript's
`X^0` statement). Assume (N1)–(N3). Let `G ∈ [0,G₁]`, `ū > 0`, `w₀ ∈ X^s` real, and `h`
continuous on `[0,ū]` with values in `C^s(N';ℝ²)`, `3`-fold symmetric. With `F = -h·∇Φ`, the
running coefficient `c(u) = ℓ_*(w₀) + ∫₀ᵘ e^{-λ_* v}ℓ_*(F(v))dv` and
`wlin₀(u) = e^{uL(G)}w₀ + ∫₀ᵘ e^{(u-v)L(G)}F(v)dv`, for `u ∈ [0,ū]`: `wlin₀(u) ∈ X^s` is real,
`ℓ_*(wlin₀(u)) = c(u)e^{λ_* u}` and `R(G)wlin₀(u) = 2Re(c(u)e^{λ_* u}φ_*)`. -/
theorem running (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} {G ubar : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) (hu : 0 < ubar)
    {w₀ : ℂ → ℂ} (hw₀ : Lin.MemXFn s w₀) (hw₀r : ∀ᵐ x ∂(volume : Measure ℂ), (w₀ x).im = 0)
    {h : ℝ → ℂ → ℂ} (hh : CkPathOn s annN' (Icc 0 ubar) h)
    (hsym : ∀ u ∈ Icc (0 : ℝ) ubar, IsSymFieldOn annN' (h u)) :
    ∀ u ∈ Icc (0 : ℝ) ubar,
      Lin.MemX (wlin0 χ s G w₀ h u) ∧ (wlin0 χ s G w₀ h u).IsReal ∧
        Eig.ellFn χ G (wlin0 χ s G w₀ h u).fn =
          runCoef χ G w₀ h u * Complex.exp (Eig.lam χ G * u) ∧
        (Eig.R χ s G (wlin0 χ s G w₀ h u)).fn =ᵐ[volume]
          modeFn χ G (runCoef χ G w₀ h u * Complex.exp (Eig.lam χ G * u)) := by
  intro u hu'
  have hu0 : 0 ≤ u := hu'.1
  -- Step 1: the data in `Y^s(N)`.
  obtain ⟨hgc, hgX⟩ := RunningAux.forcing_path χ hχ hN hh hsym
  obtain ⟨hf₀fn, hf₀X⟩ := RunningAux.memX_toY hw₀
  have hf₀R : (Sect.toY s annN w₀).IsReal := by
    show ∀ᵐ x ∂(volume : Measure ℂ), ((Sect.toY s annN w₀).fn x).im = 0
    filter_upwards [hf₀fn, hw₀r] with x h1 h2
    rw [h1, h2]
  have hvu : ∀ v ∈ Icc (0 : ℝ) u, v ∈ Icc (0 : ℝ) ubar := fun v hv => ⟨hv.1, hv.2.trans hu'.2⟩
  -- Step 2: the integrand.
  have hint : IntervalIntegrable
      (fun v => Lin.S χ s G (u - v) (Sect.toY s annN (forcing χ h v))) volume 0 u :=
    RunningAux.intervalIntegrable_S_comp χ hχ s G hu0 (hgc.mono (Icc_subset_Icc_right hu'.2))
  have hSX : ∀ v ∈ Icc (0 : ℝ) u,
      Lin.MemX (Lin.S χ s G (u - v) (Sect.toY s annN (forcing χ h v))) := fun v hv =>
    Lin.S_memX χ hχ s G (by linarith [hv.2]) (hgX v (hvu v hv)).2.1
  have hSR : ∀ v ∈ Icc (0 : ℝ) u,
      (Lin.S χ s G (u - v) (Sect.toY s annN (forcing χ h v))).IsReal := fun v hv =>
    Lin.S_isReal χ hχ s G (by linarith [hv.2]) (hgX v (hvu v hv)).2.2
  have hW := wlin0_def χ s G w₀ h u
  have hX : Lin.MemX (wlin0 χ s G w₀ h u) := by
    rw [hW]
    show ((Lin.S χ s G u (Sect.toY s annN w₀) +
        ∫ v in (0 : ℝ)..u, Lin.S χ s G (u - v) (Sect.toY s annN (forcing χ h v)) :
          Sect.Y s annN) : Sob.SobTuple s) ∈ Lin.Xsub s
    rw [Submodule.coe_add]
    exact add_mem (Lin.S_memX χ hχ s G hu0 hf₀X) (RunningAux.intervalIntegral_memX hu0 hint hSX)
  have hreal : (wlin0 χ s G w₀ h u).IsReal := by
    rw [hW]
    exact RunningAux.isReal_add (Lin.S_isReal χ hχ s G hu0 hf₀R)
      (RunningAux.intervalIntegral_isReal hu0 hint hSR)
  -- Step 3: the coefficient.
  have hellw : ∀ w : Sect.Y s annN, Eig.ell χ s G w = Eig.ellFn χ G w.fn :=
    Eig.ell_spec_of_exists (Eig.exists_ell χ hχ hN hG s)
  have hform : ∀ t : ℝ, 0 ≤ t → ∀ w : Sect.Y s annN, Lin.MemX w →
      Eig.ell χ s G (Lin.S χ s G t w) = Complex.exp (Eig.lam χ G * (t : ℂ)) * Eig.ell χ s G w :=
    fun t ht => (Eig.propSemigroup_formulas χ hχ hN s hG ht).2
  have hE : Eig.ellFn χ G (wlin0 χ s G w₀ h u).fn =
      runCoef χ G w₀ h u * Complex.exp (Eig.lam χ G * u) := by
    rw [← hellw, hW, map_add, hform u hu0 _ hf₀X,
      ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    have hcongr : ∀ v ∈ uIcc (0 : ℝ) u,
        Eig.ell χ s G (Lin.S χ s G (u - v) (Sect.toY s annN (forcing χ h v))) =
          Complex.exp (-(Eig.lam χ G * v)) * Eig.ellFn χ G (forcing χ h v) *
            Complex.exp (Eig.lam χ G * u) := by
      intro v hv
      rw [uIcc_of_le hu0] at hv
      rw [hform (u - v) (by linarith [hv.2]) _ (hgX v (hvu v hv)).2.1, hellw,
        RunningAux.ellFn_congr_ae χ G (hgX v (hvu v hv)).1]
      have hexp : Complex.exp (Eig.lam χ G * ((u - v : ℝ) : ℂ)) =
          Complex.exp (-(Eig.lam χ G * v)) * Complex.exp (Eig.lam χ G * u) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hexp]
      ring
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_mul_const, hellw,
      RunningAux.ellFn_congr_ae χ G hf₀fn, runCoef]
    ring
  refine ⟨hX, hreal, hE, ?_⟩
  -- Step 4: the Riesz projection.
  have hR := Eig.R_of_isReal χ hχ hN hG s hreal
  rw [hellw, hE] at hR
  exact hR

end OneRing

end NonUniqueEuler
