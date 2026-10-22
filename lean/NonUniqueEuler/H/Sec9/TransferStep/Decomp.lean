import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.H.Sec9.TransferStep.Radial
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Helper for `lem:transfer-step`(1): the decomposition of `ω_{≥i+1}(t)`

Helper of `P/Sec9/TransferStep.lean` (`09_relay.tex:198-206`). In physical units
`ω_{≥i+1}(t) = A_{i+1}Φ(·/r_{i+1}) + A_{i+1}w_{i+1}(t,·/r_{i+1}) + ω_{≥i+2}(t)`; the first term is
radial and supported in `\bar B_{r_{i+1}}`, so it has no non-monopole field at `|x| ≥ 2r_{i+1}`
(`Radial.lean`); the second has zero integral (`lem:regions-basic`(4)). Hence, at `|x| ≥ 2r_{i+1}`,
the non-monopole field of `ω_{≥i+1}(t)` is the velocity of the second term plus the non-monopole
field of `ω_{≥i+2}(t)` (`extField_omegaGe_split`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.Relay.TransferStepAux

open RingData Datum

/-- `A_i Φ(·/r_i)`, the radial part of ring `i` in physical units. -/
def radialPart (P : Approx) (i : ℕ) (x : ℂ) : ℝ := P.A i * ringPhi P.χ ((P.r i : ℂ)⁻¹ * x)

theorem norm_inv_r_mul (P : Approx) (hP : P.Valid) (i : ℕ) (x : ℂ) :
    ‖((P.r i : ℝ) : ℂ)⁻¹ * x‖ = (P.r i)⁻¹ * ‖x‖ := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hP.r_pos i)]

/-- `A_iΦ(·/r_i)` is in `L¹ ∩ L^∞`, radial, and vanishes outside `\bar B_{r_i}`. -/
theorem radialPart_facts (P : Approx) (hP : P.Valid) (i : ℕ) :
    MemLp (radialPart P i) 1 volume ∧ MemLp (radialPart P i) ⊤ volume ∧
      IsRadialPointwise (radialPart P i) ∧
      ∀ x : ℂ, P.r i < ‖x‖ → radialPart P i x = 0 := by
  obtain ⟨hsm, -, hrad, -, -, hsupp, -, -⟩ := ringFacts_of_admissible hP.admissible
  have hr := hP.r_pos i
  have hcont : Continuous (radialPart P i) :=
    continuous_const.mul (hsm.continuous.comp (continuous_const.mul continuous_id))
  have hzero : ∀ x : ℂ, P.r i < ‖x‖ → radialPart P i x = 0 := by
    intro x hx
    have h0 : ringPhi P.χ (((P.r i : ℝ) : ℂ)⁻¹ * x) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun h => ?_
      have h1 := (hsupp h).2
      rw [norm_inv_r_mul P hP, inv_mul_le_iff₀ hr, mul_one] at h1
      linarith
    simp only [radialPart]
    rw [h0, mul_zero]
  have hcpt : HasCompactSupport (radialPart P i) :=
    HasCompactSupport.intro (isCompact_closedBall 0 (P.r i)) fun x hx => by
      rw [mem_closedBall_zero_iff, not_le] at hx
      exact hzero x hx
  refine ⟨hcont.memLp_of_hasCompactSupport hcpt, hcont.memLp_of_hasCompactSupport hcpt, ?_,
    hzero⟩
  intro θ x
  simp only [radialPart]
  have he : ((P.r i : ℝ) : ℂ)⁻¹ * rot θ x = rot θ (((P.r i : ℝ) : ℂ)⁻¹ * x) := by
    simp only [rot]
    ring
  rw [he, hrad]

/-- `ω(t)1_{S_i(t)} = A_iΦ(·/r_i) + A_iw_i(t,·/r_i)` (definition of `w_i`). -/
theorem omegaRing_eq (P : Approx) (hP : P.Valid) (i : ℕ) (t : ℝ) (x : ℂ) :
    P.omegaRing i t x = radialPart P i x + P.wPhys i t x := by
  have hA := (hP.A_pos i).ne'
  have hr : ((P.r i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hP.r_pos i).ne'
  simp only [radialPart, Approx.wPhys, Approx.wR, Approx.unitsVort, scaleVort]
  rw [mul_inv_cancel_left₀ hr, mul_sub, mul_inv_cancel_left₀ hA]
  ring

/-- `ω(t)1_{S_i(t)} ∈ L¹ ∩ L^∞` (`lem:regions-basic`(3): it is `C_c^∞`). -/
theorem omegaRing_memLp (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 P.n) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (P.omegaRing i t) 1 volume ∧ MemLp (P.omegaRing i t) ⊤ volume := by
  obtain ⟨-, -, -, -, -, -, ⟨hωsm, hωcpt, -, -⟩, -⟩ := Approx.regions_basic_three P hP hN hi ht
  exact ⟨hωsm.continuous.memLp_of_hasCompactSupport hωcpt,
    hωsm.continuous.memLp_of_hasCompactSupport hωcpt⟩

/-- `A_iw_i(t,·/r_i) ∈ L¹ ∩ L^∞`. -/
theorem wPhys_memLp (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 P.n) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (P.wPhys i t) 1 volume ∧ MemLp (P.wPhys i t) ⊤ volume := by
  have he : P.wPhys i t = P.omegaRing i t - radialPart P i := by
    funext x
    rw [Pi.sub_apply, omegaRing_eq P hP i t x]
    ring
  obtain ⟨h1, hinf⟩ := omegaRing_memLp P hP hN hi ht
  obtain ⟨r1, rinf, -, -⟩ := radialPart_facts P hP i
  rw [he]
  exact ⟨h1.sub r1, hinf.sub rinf⟩

/-- `∫ A_iw_i(t,·/r_i) = 0` if `S_i(t) ⊂ N_i` (`lem:regions-basic`(4) and a change of variables). -/
theorem integral_wPhys (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 P.n) {t : ℝ} (ht : 0 ≤ t) (hS : P.PertDefined i t) :
    ∫ x, P.wPhys i t x = 0 := by
  have hw0 := (Approx.regions_basic_four P hP hN hi ht hS).2.2.2.2.2.1
  have hcv : ∫ x, P.wR i t (((P.r i : ℝ) : ℂ)⁻¹ * x) = 0 := by
    have h := Measure.integral_comp_smul (volume : Measure ℂ) (P.wR i t) (P.r i)⁻¹
    simp only [Complex.real_smul, Complex.finrank_real_complex, Complex.ofReal_inv] at h
    rw [h, hw0, smul_zero]
  simp only [Approx.wPhys]
  rw [integral_const_mul, hcv, mul_zero]

/-- `ω_{≥k}(t) = Σ_{j=k}^n ω(t)1_{S_j(t)}` for `1 ≤ k ≤ n + 1` (`eq:omega-ge`; empty sum and
`ω_{≥n+1} = 0` for `k = n + 1`). -/
theorem omegaGe_eq_sum (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ P.n + 1) {t : ℝ} (ht : 0 ≤ t) (x : ℂ) :
    P.omegaGe k t x = ∑ j ∈ Finset.Icc k P.n, P.omegaRing j t x := by
  rcases Nat.lt_or_ge P.n k with h | h
  · have hk' : k = P.n + 1 := by omega
    subst hk'
    rw [Approx.omegaGe_succ_n, Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    rfl
  · have := (Approx.regions_basic_three P hP hN (Finset.mem_Icc.2 ⟨hk, h⟩) ht).2.2.1
    rw [this]

/-- `ω_{≥i+1}(t) = ω(t)1_{S_{i+1}(t)} + ω_{≥i+2}(t)` (`1 ≤ i < n`). -/
theorem omegaGe_succ_split (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {i : ℕ}
    (hin : i < P.n) {t : ℝ} (ht : 0 ≤ t) (x : ℂ) :
    P.omegaGe (i + 1) t x = P.omegaRing (i + 1) t x + P.omegaGe (i + 2) t x := by
  rw [omegaGe_eq_sum P hP hN (by omega) (by omega) ht,
    omegaGe_eq_sum P hP hN (by omega) (by omega) ht,
    Finset.Icc_eq_cons_Ioc (by omega : i + 1 ≤ P.n), Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]
  rfl

/-- `ω_{≥k}(t)` (`2 ≤ k ≤ n + 1`) is in `L¹ ∩ L^∞` and pointwise `3`-fold symmetric. -/
theorem omegaGe_facts (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ P.n + 1) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (P.omegaGe k t) 1 volume ∧ MemLp (P.omegaGe k t) ⊤ volume ∧
      ∀ x, P.omegaGe k t (rot (2 * Real.pi / 3) x) = P.omegaGe k t x := by
  rcases Nat.lt_or_ge P.n k with h | h
  · have hk' : k = P.n + 1 := by omega
    subst hk'
    rw [Approx.omegaGe_succ_n]
    exact ⟨MemLp.zero, MemLp.zero, fun _ => rfl⟩
  · obtain ⟨-, -, -, -, -, -, -, ⟨hsm, hcpt, -, hsym⟩⟩ :=
      Approx.regions_basic_three P hP hN (Finset.mem_Icc.2 ⟨hk, h⟩) ht
    exact ⟨hsm.continuous.memLp_of_hasCompactSupport hcpt,
      hsm.continuous.memLp_of_hasCompactSupport hcpt, hsym⟩

/-- **The decomposition of the non-monopole field of `ω_{≥i+1}(t)`** (`09_relay.tex:198-206`): for
`1 ≤ i < n`, `t ≥ 0`, `S_{i+1}(t) ⊂ N_{i+1}` and `|x| ≥ 2r_{i+1}`,
`E[ω_{≥i+1}(t)](x) = K_BS * (A_{i+1}w_{i+1}(t,·/r_{i+1}))(x) + E[ω_{≥i+2}(t)](x)`. -/
theorem extField_omegaGe_split (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    {i : ℕ} (hin : i < P.n) {t : ℝ} (ht : 0 ≤ t) (hS : P.PertDefined (i + 1) t) {x : ℂ}
    (hx : 2 * P.r (i + 1) ≤ ‖x‖) :
    BS.extField (P.omegaGe (i + 1) t) x =
      velocity (P.wPhys (i + 1) t) x + BS.extField (P.omegaGe (i + 2) t) x := by
  have hi1 : i + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  obtain ⟨ρ1, ρinf, ρrad, ρz⟩ := radialPart_facts P hP (i + 1)
  obtain ⟨w1, winf⟩ := wPhys_memLp P hP hN hi1 ht
  obtain ⟨g1, ginf, -⟩ := omegaGe_facts P hP hN (k := i + 2) (by omega) (by omega) ht
  have hsplit : ∀ y, P.omegaGe (i + 1) t y =
      radialPart P (i + 1) y + P.wPhys (i + 1) t y + P.omegaGe (i + 2) t y := by
    intro y
    rw [omegaGe_succ_split P hP hN hin ht y, omegaRing_eq P hP (i + 1) t y]
  -- integrability of the Biot–Savart integrands at `x`
  have hIρ := (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf ρ1 ρinf x).1
  have hIw := (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf w1 winf x).1
  have hIg := (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf g1 ginf x).1
  -- the velocity splits
  have hv : velocity (P.omegaGe (i + 1) t) x = velocity (radialPart P (i + 1)) x +
      velocity (P.wPhys (i + 1) t) x + velocity (P.omegaGe (i + 2) t) x := by
    have hfun : (fun y => biotSavartKernel (x - y) * ((P.omegaGe (i + 1) t y : ℝ) : ℂ)) =
        fun y => (biotSavartKernel (x - y) * ((radialPart P (i + 1) y : ℝ) : ℂ) +
          biotSavartKernel (x - y) * ((P.wPhys (i + 1) t y : ℝ) : ℂ)) +
          biotSavartKernel (x - y) * ((P.omegaGe (i + 2) t y : ℝ) : ℂ) := by
      funext y
      rw [hsplit y]
      push_cast
      ring
    have h3 := integral_add (hIρ.add hIw) hIg
    simp only [Pi.add_apply] at h3
    simp only [velocity]
    rw [hfun, h3, integral_add hIρ hIw]
  -- the integral splits, and `∫ A_{i+1}w_{i+1} = 0`
  have hI : ∫ y, P.omegaGe (i + 1) t y =
      (∫ y, radialPart P (i + 1) y) + ∫ y, P.omegaGe (i + 2) t y := by
    have hfun : (fun y => P.omegaGe (i + 1) t y) =
        fun y => (radialPart P (i + 1) y + P.wPhys (i + 1) t y) + P.omegaGe (i + 2) t y := by
      funext y
      exact hsplit y
    have iρ := memLp_one_iff_integrable.mp ρ1
    have iw := memLp_one_iff_integrable.mp w1
    have ig := memLp_one_iff_integrable.mp g1
    have h3 := integral_add (iρ.add iw) ig
    simp only [Pi.add_apply] at h3
    rw [hfun, h3, integral_add iρ iw, integral_wPhys P hP hN hi1 ht hS, add_zero]
  -- the radial part has no non-monopole field at `|x| ≥ 2 r_{i+1}`
  have hρ0 := extField_eq_zero_of_radial ρ1 ρrad (hP.r_pos (i + 1)) ρz hx
  simp only [BS.extField, BS.monopole] at hρ0 ⊢
  have hIc : ((∫ y, P.omegaGe (i + 1) t y : ℝ) : ℂ) =
      ((∫ y, radialPart P (i + 1) y : ℝ) : ℂ) + ((∫ y, P.omegaGe (i + 2) t y : ℝ) : ℂ) := by
    rw [hI]
    push_cast
    ring
  rw [hv, hIc]
  linear_combination hρ0

end NonUniqueEuler.Relay.TransferStepAux
