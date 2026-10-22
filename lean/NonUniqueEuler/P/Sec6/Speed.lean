import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import NonUniqueEuler.Defs.Sec6.All
import NonUniqueEuler.I.Sec6.InnerCirc
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec2.LpLinf
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec5.Seed

/-!
# Proof: `lem:speed` (norms and velocity of the inner vorticity)

Proof of `I/Sec6/Speed.lean` (`06_datum.tex:361-393`).

* `eq:conserved` (`conserved`, `F(s) = |s|^q`) and the scaling `x = r_i y` give
  `∫|ω_{≥k}(t)|^q = (∫|Φ|^q) Σ_{i=k}^n A_i^q r_i²` (the seeded term by the measure preservation
  of the seed flow `Y_κ`, `Φ^κ = Φ ∘ Y_κ`, which is the equimeasurability used by the manuscript);
* `∫|Φ|^q ≤ |B̄₁| = π` (`0 ≤ Φ < 1`, `supp Φ ⊂ B̄₁`) and `A_{i+1}^q r_{i+1}² ≤ A_i^q r_i²/8`
  (`0 < q ≤ 4`), so `Σ_{i≥k} A_i^q r_i² ≤ (8/7) A_k^q r_k²`;
* `lem:LpLinf` with `p = 4` for the velocity.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Datum

namespace Approx

open RingData

namespace SpeedP

/-- `‖g‖_{L^q} = (∫ |g|^q)^{1/q}` for `g ∈ L^q`, `q > 0`. -/
theorem eLpNorm_ofReal_eq {g : ℂ → ℝ} {q : ℝ} (hq : 0 < q)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    eLpNorm g (ENNReal.ofReal q) volume = ENNReal.ofReal ((∫ x, |g x| ^ q) ^ q⁻¹) := by
  rw [hg.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le]
  simp only [Real.norm_eq_abs]

/-- The scaling `x = r y`: `∫ |A ψ(x/r)|^q dx = A^q r² ∫ |ψ|^q`. -/
theorem integral_abs_rpow_scale (ψ : ℂ → ℝ) {A r q : ℝ} (hA : 0 ≤ A) (hr : 0 < r) :
    ∫ x : ℂ, |A * ψ (x / ((r : ℝ) : ℂ))| ^ q = A ^ q * r ^ 2 * ∫ y : ℂ, |ψ y| ^ q := by
  have h1 : ∀ x : ℂ, |A * ψ (x / ((r : ℝ) : ℂ))| ^ q = A ^ q * |ψ (r⁻¹ • x)| ^ q := by
    intro x
    rw [abs_mul, abs_of_nonneg hA, Real.mul_rpow hA (abs_nonneg _), Complex.real_smul,
      div_eq_inv_mul, Complex.ofReal_inv]
  simp_rw [h1]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume (fun y : ℂ => |ψ y| ^ q) hr.le,
    Complex.finrank_real_complex, smul_eq_mul]
  ring

/-- Integrals are invariant under a measure-preserving map. -/
theorem integral_comp_of_measurePreserving {T : ℂ → ℂ} (hT : MeasurePreserving T volume volume)
    {h : ℂ → ℝ} (hh : AEStronglyMeasurable h volume) : ∫ y, h (T y) = ∫ y, h y := by
  have hh' : AEStronglyMeasurable h (Measure.map T volume) := by rwa [hT.map_eq]
  rw [← integral_map hT.measurable.aemeasurable hh', hT.map_eq]

/-- `∫ |Φ|^q ≤ π` for `q > 0` (`0 ≤ Φ < 1`, `supp Φ ⊂ B̄₁`). -/
theorem integral_abs_rpow_Phi_le {χ : ℝ → ℝ} (hR : RingFacts χ) {q : ℝ} (hq : 0 < q) :
    ∫ y, |ringPhi χ y| ^ q ≤ Real.pi := by
  obtain ⟨_, _, _, hbd, _, hsupp, _, _⟩ := hR
  have hint : Integrable ((closedBall (0 : ℂ) 1).indicator (fun _ => (1 : ℝ))) volume := by
    refine (integrable_indicator_iff measurableSet_closedBall).mpr ?_
    exact integrableOn_const (by simp [Complex.volume_closedBall]) |>.mono_set subset_rfl
  have hle : (fun y => |ringPhi χ y| ^ q) ≤ᵐ[volume]
      (closedBall (0 : ℂ) 1).indicator (fun _ => (1 : ℝ)) := by
    refine Filter.Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ closedBall (0 : ℂ) 1
    · rw [indicator_of_mem hy]
      exact Real.rpow_le_one (abs_nonneg _)
        (by rw [abs_of_nonneg (hbd y).1]; exact (hbd y).2.le) hq.le
    · rw [indicator_of_notMem hy]
      have hy' : y ∉ tsupport (ringPhi χ) := fun h => hy (by
        have := (hsupp h).2
        simpa [mem_closedBall, dist_zero_right] using this)
      show |ringPhi χ y| ^ q ≤ 0
      rw [image_eq_zero_of_notMem_tsupport hy', abs_zero, Real.zero_rpow hq.ne']
  calc ∫ y, |ringPhi χ y| ^ q
      ≤ ∫ y, (closedBall (0 : ℂ) 1).indicator (fun _ => (1 : ℝ)) y :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity) hint hle
    _ = Real.pi := by
        rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul, mul_one,
          Measure.real, Complex.volume_closedBall]
        simp

/-- The geometric sum: if `b ≥ 0` and `b_{i+1} ≤ b_i/8` for `i ≥ 1`, then
`Σ_{i=k}^n b_i ≤ (8/7) b_k`. -/
theorem sum_Icc_le_of_ratio (b : ℕ → ℝ) (hb0 : ∀ i, 0 ≤ b i)
    (hb : ∀ i, 1 ≤ i → b (i + 1) ≤ b i / 8) (n : ℕ) :
    ∀ d k : ℕ, 1 ≤ k → n + 1 - k = d → ∑ i ∈ Finset.Icc k n, b i ≤ 8 / 7 * b k := by
  intro d
  induction d with
  | zero =>
    intro k _ hd
    have : Finset.Icc k n = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this, Finset.sum_empty]
    have := hb0 k
    positivity
  | succ d ih =>
    intro k hk hd
    have hkn : k ≤ n := by omega
    rw [← Finset.insert_Icc_add_one_left_eq_Icc hkn, Finset.sum_insert (by simp)]
    have h1 := ih (k + 1) (by omega) (by omega)
    have h2 := hb k hk
    linarith

/-- The exponent identity of `lem:speed`:
`(u A r²)^{1/3} (u^{1/4} A r^{1/2})^{2/3} = u^{1/2} A r`. -/
theorem rpow_identity {u A r : ℝ} (hu : 0 < u) (hA : 0 < A) (hr : 0 < r) :
    (u ^ ((1 : ℝ) / 1) * A * r ^ ((2 : ℝ) / 1)) ^ ((1 : ℝ) / 3) *
        (u ^ ((1 : ℝ) / 4) * A * r ^ ((2 : ℝ) / 4)) ^ ((2 : ℝ) / 3) =
      u ^ ((1 : ℝ) / 2) * A * r := by
  have h3 : ∀ x y z e : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → (x * y * z) ^ e = x ^ e * y ^ e * z ^ e :=
    fun x y z e hx hy hz => by rw [Real.mul_rpow (mul_nonneg hx hy) hz, Real.mul_rpow hx hy]
  rw [h3 _ _ _ _ (by positivity) hA.le (by positivity),
    h3 _ _ _ _ (by positivity) hA.le (by positivity), ← Real.rpow_mul hu.le,
    ← Real.rpow_mul hu.le, ← Real.rpow_mul hr.le, ← Real.rpow_mul hr.le]
  calc u ^ ((1 : ℝ) / 1 * (1 / 3)) * A ^ ((1 : ℝ) / 3) * r ^ ((2 : ℝ) / 1 * (1 / 3)) *
        (u ^ ((1 : ℝ) / 4 * (2 / 3)) * A ^ ((2 : ℝ) / 3) * r ^ ((2 : ℝ) / 4 * (2 / 3)))
      = u ^ ((1 : ℝ) / 1 * (1 / 3) + 1 / 4 * (2 / 3)) * A ^ ((1 : ℝ) / 3 + 2 / 3) *
          r ^ ((2 : ℝ) / 1 * (1 / 3) + 2 / 4 * (2 / 3)) := by
        rw [Real.rpow_add hu, Real.rpow_add hA, Real.rpow_add hr]
        ring
    _ = u ^ ((1 : ℝ) / 2) * A * r := by norm_num

/-- `∫ |f^{(n)}_i|^q = A_i^q r_i² ∫ |Φ|^q` for `1 ≤ i ≤ n` (scaling `x = r_i y`; for `i = n`,
`Φ^κ = Φ ∘ Y_κ` with `Y_κ` area preserving, `lem:seed`). -/
theorem integral_abs_rpow_term {P : Approx} (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 P.n) (q : ℝ) :
    ∫ x, |P.term i x| ^ q = P.A i ^ q * P.r i ^ 2 * ∫ y, |ringPhi P.χ y| ^ q := by
  obtain ⟨hi1, hin⟩ := Finset.mem_Icc.mp hi
  have hA := (hP.A_pos i).le
  have hr := hP.r_pos i
  rcases lt_or_eq_of_le hin with hlt | heq
  · have h : P.term i = fun x => P.A i * ringPhi P.χ (x / ((P.r i : ℝ) : ℂ)) := by
      funext x
      exact approxTerm_of_lt hi1 hlt x
    rw [h]
    exact integral_abs_rpow_scale _ hA hr
  · have h : P.term i = fun x => P.A i * OneRing.PhiSeed P.χ P.κs (x / ((P.r i : ℝ) : ℂ)) := by
      funext x
      rw [heq]
      exact approxTerm_self x
    rw [h, integral_abs_rpow_scale _ hA hr]
    congr 1
    have hS := OneRing.seedData_spec (OneRing.seed P.χ hP.admissible hN)
    have hc : Continuous (ringPhi P.χ) := (ringFacts_of_admissible hP.admissible).1.continuous
    simp only [OneRing.PhiSeed_apply]
    exact integral_comp_of_measurePreserving (hS.measurePreserving P.κs)
      (h := fun y => |ringPhi P.χ y| ^ q)
      ((continuous_abs.measurable.comp hc.measurable).pow_const q).aestronglyMeasurable

/-- Step 1 of the proof: `∫ |ω_{≥k}(t)|^q = (∫ |Φ|^q) Σ_{i=k}^n A_i^q r_i²` (`eq:conserved`). -/
theorem integral_abs_rpow_omegaGe {P : Approx} (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 P.n) {t : ℝ} (ht : 0 ≤ t) {q : ℝ} (hq : 0 < q) :
    ∫ x, |P.omegaGe k t x| ^ q =
      (∫ y, |ringPhi P.χ y| ^ q) * ∑ i ∈ Finset.Icc k P.n, P.A i ^ q * P.r i ^ 2 := by
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
  rw [conserved P hP hN (F := fun s => |s| ^ q)
    (continuous_abs.rpow_const fun _ => Or.inr hq.le)
    (by simp only [abs_zero, Real.zero_rpow hq.ne']) hk1 (by omega) ht, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ∈ Finset.Icc 1 P.n := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨le_trans hk1 h1, h2⟩
  rw [integral_abs_rpow_term hP hN hi' q]
  ring

/-- Step 2 of the proof: `A_{i+1}^q r_{i+1}² ≤ A_i^q r_i²/8` for `i ≥ 1`, `q ≤ 4`
(`μ ≤ 2`, `s_i ≤ s̄ ≤ a/16 < 1/16`). -/
theorem ratio_step {P : Approx} (hP : P.Valid) {q : ℝ} (hq4 : q ≤ 4) {i : ℕ}
    (hi : 1 ≤ i) : P.A (i + 1) ^ q * P.r (i + 1) ^ 2 ≤ P.A i ^ q * P.r i ^ 2 / 8 := by
  have hdp := hP.datumParams
  have ha1 : a < 1 := (ringFacts_of_admissible hP.admissible).2.2.2.2.2.2.2
  have hμ1 : 1 ≤ P.μ := hdp.one_lt_μ.le
  have hA := hP.A_pos i
  have hr := hP.r_pos i
  have hs := hP.s_pos i
  have hAs : P.A (i + 1) = P.μ * P.A i := amp_succ P.A₁ P.μ hi
  have hrs : P.r (i + 1) = P.s i * P.r i := radius_succ P.sbar P.μ hi
  have hsle : P.s i ≤ P.sbar :=
    div_le_self hdp.sbar_pos.le (one_le_pow₀ (by linarith))
  have hsb : P.sbar < 1 / 16 := by linarith [hdp.sbar_le]
  have hμq : P.μ ^ q ≤ 16 := by
    calc P.μ ^ q ≤ P.μ ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hμ1 hq4
      _ = P.μ ^ (4 : ℕ) := by exact_mod_cast Real.rpow_natCast P.μ 4
      _ ≤ 2 ^ (4 : ℕ) := pow_le_pow_left₀ (by linarith) hdp.μ_le_two 4
      _ = 16 := by norm_num
  have hs2 : P.s i ^ 2 ≤ 1 / 256 := by
    have : P.s i < 1 / 16 := lt_of_le_of_lt hsle hsb
    nlinarith
  have hμq0 : 0 ≤ P.μ ^ q := Real.rpow_nonneg (by linarith) q
  have hb : 0 ≤ P.A i ^ q * P.r i ^ 2 := by positivity
  rw [hAs, hrs, Real.mul_rpow (by linarith) hA.le]
  have hprod : P.μ ^ q * P.s i ^ 2 ≤ 1 / 8 := by
    calc P.μ ^ q * P.s i ^ 2 ≤ 16 * (1 / 256) :=
          mul_le_mul hμq hs2 (by positivity) (by norm_num)
      _ ≤ 1 / 8 := by norm_num
  calc P.μ ^ q * P.A i ^ q * (P.s i * P.r i) ^ 2
      = (P.μ ^ q * P.s i ^ 2) * (P.A i ^ q * P.r i ^ 2) := by ring
    _ ≤ (1 / 8) * (P.A i ^ q * P.r i ^ 2) := mul_le_mul_of_nonneg_right hprod hb
    _ = P.A i ^ q * P.r i ^ 2 / 8 := by ring

/-- `Σ_{i=k}^n A_i^q r_i² ≤ (8/7) A_k^q r_k²` for `k ≥ 1`, `q ≤ 4`. -/
theorem sum_le {P : Approx} (hP : P.Valid) {q : ℝ} (hq4 : q ≤ 4) {k : ℕ}
    (hk : 1 ≤ k) :
    ∑ i ∈ Finset.Icc k P.n, P.A i ^ q * P.r i ^ 2 ≤ 8 / 7 * (P.A k ^ q * P.r k ^ 2) := by
  refine sum_Icc_le_of_ratio (fun i => P.A i ^ q * P.r i ^ 2) (fun i => ?_)
    (fun i hi => ratio_step hP hq4 hi) P.n _ k hk rfl
  have := hP.A_pos i
  positivity

end SpeedP

open SpeedP in
/-- **`lem:speed`** (`06_datum.tex:361-373`): for `1 ≤ k ≤ n`, `t ≥ 0` and `q ∈ {1, 4}`,
`‖ω_{≥k}(t)‖_{L^q} ≤ M_vort^{1/q}A_kr_k^{2/q}`; `|K_BS * ω_{≥k}(t)(x)| ≤ C_*A_kr_k` at every `x`;
`‖ω_{≥k}(t)‖_{L¹} = ‖Φ‖_{L¹}Σ_{i=k}^n A_ir_i² ≤ 2‖Φ‖_{L¹}A_kr_k²`. -/
theorem speed (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) {t : ℝ} (ht : 0 ≤ t) :
    (∀ q ∈ ({1, 4} : Set ℝ), eLpNorm (P.omegaGe k t) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (Mvort ^ (1 / q) * P.A k * P.r k ^ (2 / q))) ∧
    (∀ x : ℂ, ‖velocity (P.omegaGe k t) x‖ ≤ Cstar * P.A k * P.r k) ∧
    (eLpNorm (P.omegaGe k t) 1 volume).toReal =
      PhiL1 P.χ * ∑ i ∈ Finset.Icc k P.n, P.A i * P.r i ^ 2 ∧
    (eLpNorm (P.omegaGe k t) 1 volume).toReal ≤ 2 * PhiL1 P.χ * P.A k * P.r k ^ 2 := by
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
  have hR := ringFacts_of_admissible hP.admissible
  have hA := hP.A_pos k
  have hr := hP.r_pos k
  have hMv := Mvort_pos
  obtain ⟨hgc, hgs, -, -⟩ := (regions_basic_three P hP hN hk ht).2.2.2.2.2.2.2
  have hmem : ∀ p, MemLp (P.omegaGe k t) p volume := fun p =>
    hgc.continuous.memLp_of_hasCompactSupport hgs
  have hΦmem : MemLp (ringPhi P.χ) 1 volume := hR.1.continuous.memLp_of_hasCompactSupport hR.2.1
  -- `‖h‖_{L¹} = ∫ |h|`
  have hL1 : ∀ h : ℂ → ℝ, MemLp h 1 volume → (eLpNorm h 1 volume).toReal = ∫ x, |h x| := by
    intro h hh
    have e := eLpNorm_ofReal_eq one_pos (by rwa [ENNReal.ofReal_one])
    rw [ENNReal.ofReal_one] at e
    rw [e, ENNReal.toReal_ofReal]
    · simp only [Real.rpow_one, inv_one]
    · simp only [Real.rpow_one, inv_one]
      exact integral_nonneg fun _ => abs_nonneg _
  -- Steps 1–3: `∫ |ω_{≥k}(t)|^q ≤ M_vort A_k^q r_k²`
  have hbound : ∀ q : ℝ, 0 < q → q ≤ 4 →
      ∫ x, |P.omegaGe k t x| ^ q ≤ Mvort * (P.A k ^ q * P.r k ^ 2) := by
    intro q hq hq4
    rw [integral_abs_rpow_omegaGe hP hN hk ht hq]
    have hI0 : 0 ≤ ∫ y, |ringPhi P.χ y| ^ q :=
      integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
    have hS0 : 0 ≤ ∑ i ∈ Finset.Icc k P.n, P.A i ^ q * P.r i ^ 2 :=
      Finset.sum_nonneg fun i _ => by have := hP.A_pos i; positivity
    have hb0 : 0 ≤ P.A k ^ q * P.r k ^ 2 := by positivity
    calc (∫ y, |ringPhi P.χ y| ^ q) * ∑ i ∈ Finset.Icc k P.n, P.A i ^ q * P.r i ^ 2
        ≤ Real.pi * (8 / 7 * (P.A k ^ q * P.r k ^ 2)) :=
          mul_le_mul (integral_abs_rpow_Phi_le hR hq) (sum_le hP hq4 hk1) hS0
            Real.pi_pos.le
      _ ≤ Mvort * (P.A k ^ q * P.r k ^ 2) := by
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ hb0
          unfold Mvort
          linarith [Real.pi_pos]
  -- the `L^q` bounds, `0 < q ≤ 4`
  have hnorm : ∀ q : ℝ, 0 < q → q ≤ 4 → eLpNorm (P.omegaGe k t) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (Mvort ^ (1 / q) * P.A k * P.r k ^ (2 / q)) := by
    intro q hq hq4
    rw [eLpNorm_ofReal_eq hq (hmem _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (∫ x, |P.omegaGe k t x| ^ q) ^ q⁻¹
        ≤ (Mvort * (P.A k ^ q * P.r k ^ 2)) ^ q⁻¹ :=
          Real.rpow_le_rpow (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)
            (hbound q hq hq4) (inv_nonneg.mpr hq.le)
      _ = Mvort ^ (1 / q) * P.A k * P.r k ^ (2 / q) := by
          rw [Real.mul_rpow hMv.le (by positivity), Real.mul_rpow (by positivity) (by positivity),
            Real.rpow_rpow_inv hA.le hq.ne', ← Real.rpow_natCast (P.r k) 2,
            ← Real.rpow_mul hr.le, one_div, div_eq_mul_inv]
          push_cast
          ring
  -- the sum bound with `q = 1`
  have hsum1 : ∑ i ∈ Finset.Icc k P.n, P.A i * P.r i ^ 2 ≤ 8 / 7 * (P.A k * P.r k ^ 2) := by
    simpa only [Real.rpow_one] using sum_le hP (q := 1) (by norm_num) hk1
  -- the `L¹` identity
  have hid : (eLpNorm (P.omegaGe k t) 1 volume).toReal =
      PhiL1 P.χ * ∑ i ∈ Finset.Icc k P.n, P.A i * P.r i ^ 2 := by
    rw [hL1 _ (hmem 1), PhiL1, hL1 _ hΦmem]
    simpa only [Real.rpow_one] using integral_abs_rpow_omegaGe hP hN hk ht one_pos
  refine ⟨?_, ?_, hid, ?_⟩
  · intro q hq
    rcases hq with rfl | hq
    · exact hnorm 1 one_pos (by norm_num)
    · rw [mem_singleton_iff] at hq
      subst hq
      exact hnorm 4 (by norm_num) le_rfl
  · intro x
    have hc : Real.conjExponent 4 = 4 / 3 := by norm_num [Real.conjExponent]
    have hv := (BS.velocity_bound_L1_Lp (p := 4) (by norm_num) (hmem 1) (hmem _) x).2.2
    rw [hc, show (1 : ℝ) - 4 / 3 / 2 = 1 / 3 by norm_num, show (4 : ℝ) / 3 / 2 = 2 / 3 by norm_num]
      at hv
    have hC : 0 ≤ (1 + BS.cLpLinf 4) / (2 * Real.pi) := by
      have : 0 ≤ BS.cLpLinf 4 := by
        unfold BS.cLpLinf
        refine Real.rpow_nonneg (div_nonneg (by positivity) ?_) _
        rw [hc]
        norm_num
      positivity
    have hX1 : (eLpNorm (P.omegaGe k t) 1 volume).toReal ≤
        Mvort ^ ((1 : ℝ) / 1) * P.A k * P.r k ^ ((2 : ℝ) / 1) := by
      have h := hnorm 1 one_pos (by norm_num)
      rw [ENNReal.ofReal_one] at h
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
    have hX4 : (eLpNorm (P.omegaGe k t) (ENNReal.ofReal 4) volume).toReal ≤
        Mvort ^ ((1 : ℝ) / 4) * P.A k * P.r k ^ ((2 : ℝ) / 4) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hnorm 4 (by norm_num) le_rfl)
    calc ‖velocity (P.omegaGe k t) x‖
        ≤ (1 + BS.cLpLinf 4) / (2 * Real.pi) *
            (eLpNorm (P.omegaGe k t) 1 volume).toReal ^ ((1 : ℝ) / 3) *
            (eLpNorm (P.omegaGe k t) (ENNReal.ofReal 4) volume).toReal ^ ((2 : ℝ) / 3) := hv
      _ ≤ (1 + BS.cLpLinf 4) / (2 * Real.pi) *
            (Mvort ^ ((1 : ℝ) / 1) * P.A k * P.r k ^ ((2 : ℝ) / 1)) ^ ((1 : ℝ) / 3) *
            (Mvort ^ ((1 : ℝ) / 4) * P.A k * P.r k ^ ((2 : ℝ) / 4)) ^ ((2 : ℝ) / 3) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow ENNReal.toReal_nonneg hX1 (by norm_num)) hC)
            (Real.rpow_le_rpow ENNReal.toReal_nonneg hX4 (by norm_num))
            (Real.rpow_nonneg ENNReal.toReal_nonneg _) ?_
          exact mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
      _ = Cstar * P.A k * P.r k := by
          rw [mul_assoc ((1 + BS.cLpLinf 4) / (2 * Real.pi)), rpow_identity hMv hA hr, Cstar,
            Real.sqrt_eq_rpow]
          ring
  · rw [hid]
    have hP0 := PhiL1_nonneg P.χ
    calc PhiL1 P.χ * ∑ i ∈ Finset.Icc k P.n, P.A i * P.r i ^ 2
        ≤ PhiL1 P.χ * (8 / 7 * (P.A k * P.r k ^ 2)) := mul_le_mul_of_nonneg_left hsum1 hP0
      _ ≤ 2 * PhiL1 P.χ * P.A k * P.r k ^ 2 := by
          have : 0 ≤ PhiL1 P.χ * (P.A k * P.r k ^ 2) := by positivity
          nlinarith

end Approx

end Datum

end NonUniqueEuler
