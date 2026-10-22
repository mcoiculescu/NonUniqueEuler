import NonUniqueEuler.Defs.Sec8.All
import NonUniqueEuler.I.Sec6.RegionsBasic

/-!
# Helper for `lem:coupling`: the inner and outer fields are `3`-fold symmetric; `ν^in_k`

Helper of `P/Sec8/Coupling.lean` (fully proved, modulo the interface files it imports).
Manuscript `08_kick.tex:95-98` ("`h^in_k(τ)` … is `3`-fold symmetric because `ν^in_k` is") and
`:141-144` (the same for `h^out_k`).

* `biotSavartKernel_rot`, `velocity_rot`: `K_BS(O z) = O K_BS(z)`, hence
  `(K_BS * g)(O x) = O (K_BS * g)(x)` for a rotation `O` and a vorticity with `g ∘ O = g`
  (substitution `y = O y'`, `O` preserves `volume`);
* `nuIn_rot`, `nuOut_rot`: `ν^in_k`, `ν^out_k` are `3`-fold symmetric (`lem:regions-basic`(3));
* `isSymFieldOn_hIn`, `isSymFieldOn_hOut`: `h^in_k(τ)`, `h^out_k(τ)` are symmetric fields
  (`OneRing.IsSymFieldOn`, on all of `ℂ`, in particular on `N'`);
* `nuIn_contDiff`, `nuIn_eq_zero`: `ν^in_k(t)` is smooth and vanishes for `|y| ≥ a/8` when
  `D_{k+1}(t) ⊂ B_{a r_k/8}`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.CouplingAux

open RingData Datum OneRing

/-- `K_BS(e^{iθ} z) = e^{iθ} K_BS(z)`. -/
theorem biotSavartKernel_rot (θ : ℝ) (z : ℂ) :
    biotSavartKernel (rot θ z) = rot θ (biotSavartKernel z) := by
  unfold biotSavartKernel
  rw [Polar.norm_rot]
  simp only [rot]
  ring

/-- Rotations are measurable embeddings. -/
theorem measurableEmbedding_rot (θ : ℝ) : MeasurableEmbedding (rot θ) := by
  rw [Polar.rot_eq_rotation]
  have h := (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding
  rwa [LinearIsometryEquiv.coe_toHomeomorph] at h

/-- **Rotation covariance of the Biot–Savart velocity**: if `g ∘ O_θ = g`, then
`(K_BS * g)(O_θ x) = O_θ (K_BS * g)(x)` (no integrability needed). -/
theorem velocity_rot {g : ℂ → ℝ} {θ : ℝ} (hg : ∀ y, g (rot θ y) = g y) (x : ℂ) :
    velocity g (rot θ x) = rot θ (velocity g x) := by
  unfold velocity
  rw [← (Polar.measurePreserving_rot θ).integral_comp (measurableEmbedding_rot θ)
    (fun y => biotSavartKernel (rot θ x - y) * (g y : ℂ))]
  have h : ∀ y, biotSavartKernel (rot θ x - rot θ y) * (g (rot θ y) : ℂ) =
      Complex.exp ((θ : ℂ) * Complex.I) * (biotSavartKernel (x - y) * (g y : ℂ)) := by
    intro y
    have h1 : rot θ x - rot θ y = rot θ (x - y) := by simp only [rot]; ring
    rw [h1, biotSavartKernel_rot, hg]
    simp only [rot]
    ring
  simp_rw [h]
  rw [integral_const_mul]
  rfl

/-- `r O_θ y = O_θ (r y)`. -/
theorem mul_rot (θ : ℝ) (c y : ℂ) : c * rot θ y = rot θ (c * y) := by
  simp only [rot]
  ring

variable (P : Approx)

/-- `ν^in_k(t)` is `3`-fold symmetric (`lem:regions-basic`(3)). -/
theorem nuIn_rot (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < P.n) {t : ℝ} (ht : 0 ≤ t) (y : ℂ) :
    P.nuIn k t (rot (2 * Real.pi / 3) y) = P.nuIn k t y := by
  have hmem : k + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨by omega, hkn⟩
  have hsym := (Approx.regions_basic_three P hP hN hmem ht).2.2.2.2.2.2.2.2.2.2
  show (P.A k)⁻¹ * P.omegaGe (k + 1) t (((P.r k : ℝ) : ℂ) * rot (2 * Real.pi / 3) y) =
    (P.A k)⁻¹ * P.omegaGe (k + 1) t (((P.r k : ℝ) : ℂ) * y)
  rw [mul_rot, hsym]

/-- `ν^out_k(t)` is `3`-fold symmetric (`lem:regions-basic`(3)). -/
theorem nuOut_rot (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) {t : ℝ} (ht : 0 ≤ t) (y : ℂ) :
    P.nuOut k t (rot (2 * Real.pi / 3) y) = P.nuOut k t y := by
  have hmem : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨hk, hkn⟩
  have hsum := (Approx.regions_basic_three P hP hN hmem ht).2.2.2.2.1
  have hring : ∀ i ∈ Finset.Ico 1 k, ∀ x : ℂ,
      P.omegaRing i t (rot (2 * Real.pi / 3) x) = P.omegaRing i t x := by
    intro i hi x
    have hi' : i ∈ Finset.Icc 1 P.n := by
      rw [Finset.mem_Ico] at hi
      exact Finset.mem_Icc.2 ⟨hi.1, by omega⟩
    exact (Approx.regions_basic_three P hP hN hi' ht).2.2.2.2.2.2.1.2.2.2 x
  show (P.A k)⁻¹ * P.omegaOut k t (((P.r k : ℝ) : ℂ) * rot (2 * Real.pi / 3) y) =
    (P.A k)⁻¹ * P.omegaOut k t (((P.r k : ℝ) : ℂ) * y)
  rw [hsum, mul_rot]
  congr 1
  exact Finset.sum_congr rfl fun i hi => hring i hi _

/-- **`h^in_k(τ)` is a `3`-fold symmetric field** (`08_kick.tex:95-98`), for `τ ≥ 0`. -/
theorem isSymFieldOn_hIn (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < P.n) {τ : ℝ} (hτ : 0 ≤ τ) (U : Set ℂ) : IsSymFieldOn U (P.hIn k τ) := by
  intro x _
  have ht : 0 ≤ τ / P.A k := div_nonneg hτ (hP.A_pos k).le
  show velocity (P.nuIn k (τ / P.A k)) (rot (2 * Real.pi / 3) x) -
      (P.G k : ℂ) * (Complex.I * rot (2 * Real.pi / 3) x) /
        ((‖rot (2 * Real.pi / 3) x‖ ^ 2 : ℝ) : ℂ) =
    rot (2 * Real.pi / 3) (velocity (P.nuIn k (τ / P.A k)) x -
      (P.G k : ℂ) * (Complex.I * x) / ((‖x‖ ^ 2 : ℝ) : ℂ))
  rw [velocity_rot (fun y => nuIn_rot P hP hN hk hkn ht y), Polar.norm_rot]
  simp only [rot]
  ring

/-- **`h^out_k(τ)` is a `3`-fold symmetric field** (`08_kick.tex:141-144`), for `τ ≥ 0`. -/
theorem isSymFieldOn_hOut (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) {τ : ℝ} (hτ : 0 ≤ τ) (U : Set ℂ) : IsSymFieldOn U (P.hOut k τ) := by
  intro x _
  have ht : 0 ≤ τ / P.A k := div_nonneg hτ (hP.A_pos k).le
  show velocity (P.nuOut k (τ / P.A k)) (rot (2 * Real.pi / 3) x) =
    rot (2 * Real.pi / 3) (velocity (P.nuOut k (τ / P.A k)) x)
  exact velocity_rot (fun y => nuOut_rot P hP hN hk hkn ht y) x

/-- `ν^in_k(t)` is smooth (`lem:regions-basic`(3)). -/
theorem nuIn_contDiff (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < P.n) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.nuIn k t) := by
  have hmem : k + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨by omega, hkn⟩
  have h8 := (Approx.regions_basic_three P hP hN hmem ht).2.2.2.2.2.2.2.1
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun y : ℂ => (P.A k)⁻¹ * P.omegaGe (k + 1) t (((P.r k : ℝ) : ℂ) * y))
  exact contDiff_const.mul (h8.comp (contDiff_const.mul contDiff_id))

/-- If `D_{k+1}(t) ⊂ B_{a r_k/8}`, then `ν^in_k(t)` vanishes for `|y| ≥ a/8`. -/
theorem nuIn_eq_zero (hP : P.Valid) {k : ℕ} {t : ℝ} (hin : P.HInDefined k t) {y : ℂ}
    (hy : a / 8 ≤ ‖y‖) : P.nuIn k t y = 0 := by
  show (P.A k)⁻¹ * (P.D (k + 1) t).indicator (P.om t) (((P.r k : ℝ) : ℂ) * y) = 0
  rw [Set.indicator_of_notMem, mul_zero]
  intro hmem
  have h1 := hin hmem
  rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hP.r_pos k)] at h1
  have hr := hP.r_pos k
  nlinarith

end NonUniqueEuler.CouplingAux
