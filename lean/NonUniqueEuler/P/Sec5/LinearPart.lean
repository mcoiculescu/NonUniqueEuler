import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.Running
import NonUniqueEuler.H.Sec5.LinearPart.Bridge
import NonUniqueEuler.H.Sec5.LinearPart.Bound

/-!
# Proof: `lem:linear-part` (the complementary part of the linear response)

Proof of `I/Sec5/LinearPart.lean` (`05_single_ring.tex:616-649`).

* The decomposition `wlin₀(u) = 2Re(c(u)e^{λu}φ_*) + (1-R)wlin₀(u)` is `lem:running` at level `k`
  (`I/Sec5/Running.lean`, `running`: `R wlin₀(u) = 2Re(c(u)e^{λu}φ_*)` a.e.) together with
  `(w - Rw).fn = w.fn - (Rw).fn` a.e. (`LinearPartH.Y.fn_sub`).
* The bound is `LinearPartH.complement_bound` (`H/Sec5/LinearPart/Bound.lean`): `R` commutes with
  `e^{tL}` (`prop:SU`, `Eig.R_sector`), so
  `(1-R)wlin₀(u) = e^{uL}(1-R)w₀ + (1-R)∫₀ᵘ e^{(u-v)L}F(v)dv`; the first term is bounded by the
  first bound of `IsSemigroupConst`; for the second, `1-R` passes under the integral (when the
  integrand is interval integrable; otherwise the integral is `0`), each
  `(1-R)e^{(u-v)L}F(v) = e^{(u-v)L}(1-R)F(v)` has norm `≤ C_S e^{σ'(u-v)}C_∇(k)‖h(v)‖_{C^k(N')}`
  (`lem:bilinear`(3)), and the elementary integrals give the constant `C_lin(k)`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- **`lem:linear-part`** (`05_single_ring.tex:616-633`). Assume (N1)–(N3). Let
`σ' ∈ (9/200, σ_b)`, `p ≥ 0`, `k ≥ 2`, and let `CS ≥ 0` be a constant `C_S(k,σ')` of
`prop:semigroup`. Let `G ∈ [0,G₁]`, `ū > 0`, `A, κ, η_b ≥ 0`, `w₀ ∈ X^k` real with
`‖w₀‖_{H^k} ≤ A`, and `h` continuous on `[0,ū]` into `C^k(N';ℝ²)`, `3`-fold symmetric, with
`‖h(u)‖_{C^k(N')} ≤ A⟨u⟩^p + η_bκe^{σ(G)u}`. Then for `u ∈ [0,ū]`,
`wlin₀(u) = 2Re(c(u)e^{λ_*u}φ_*) + (1-R)wlin₀(u)` (a.e.) and
`‖(1-R)wlin₀(u)‖_{H^k} ≤ C_lin(k)(A⟨u⟩^pe^{σ'u} + η_bκe^{σ(G)u})`. -/
theorem linear_part (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {σ' : ℝ} (hσ' : σ' ∈ Ioo (9 / 200 : ℝ) (Eig.sigb χ)) (p : ℕ) {k : ℕ} (hk : 2 ≤ k)
    {CS : ℝ} (hCS0 : 0 ≤ CS) (hCS : IsSemigroupConst χ k σ' CS)
    {G ubar A κ ηb : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) (hu : 0 < ubar) (hA : 0 ≤ A) (hκ : 0 ≤ κ)
    (hηb : 0 ≤ ηb) {w₀ : ℂ → ℂ} (hw₀ : Lin.MemXFn k w₀)
    (hw₀r : ∀ᵐ x ∂(volume : Measure ℂ), (w₀ x).im = 0) (hw₀A : Sob.normH k w₀ ≤ A)
    {h : ℝ → ℂ → ℂ} (hh : CkPathOn k annN' (Icc 0 ubar) h)
    (hsym : ∀ u ∈ Icc (0 : ℝ) ubar, IsSymFieldOn annN' (h u))
    (hbd : ∀ u ∈ Icc (0 : ℝ) ubar,
      normCk k annN' (h u) ≤ A * Prelim.jap u ^ p + ηb * κ * Real.exp (Eig.sigma χ G * u)) :
    ∀ u ∈ Icc (0 : ℝ) ubar,
      (wlin0 χ k G w₀ h u).fn =ᵐ[volume]
          (fun x => modeFn χ G (runCoef χ G w₀ h u * Complex.exp (Eig.lam χ G * u)) x +
            (wlin0 χ k G w₀ h u - Eig.R χ k G (wlin0 χ k G w₀ h u)).fn x) ∧
        ‖wlin0 χ k G w₀ h u - Eig.R χ k G (wlin0 χ k G w₀ h u)‖ ≤
          Clin χ k σ' CS * (A * Prelim.jap u ^ p * Real.exp (σ' * u) +
            ηb * κ * Real.exp (Eig.sigma χ G * u)) := by
  intro u hu'
  obtain ⟨-, -, -, hRW⟩ := running χ hχ hN hG hu hw₀ hw₀r hh hsym u hu'
  refine ⟨?_, LinearPartH.complement_bound χ hχ hN hσ' p hk hCS0 hCS hG hA hκ hηb hw₀ hw₀A hh
    hsym hbd hu'⟩
  filter_upwards [LinearPartH.Y.fn_sub (wlin0 χ k G w₀ h u) (Eig.R χ k G (wlin0 χ k G w₀ h u)),
    hRW] with x hx1 hx2
  rw [hx1, Pi.sub_apply, ← hx2]
  ring

end OneRing

end NonUniqueEuler
