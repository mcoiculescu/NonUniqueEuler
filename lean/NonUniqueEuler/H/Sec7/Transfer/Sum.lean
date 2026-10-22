import NonUniqueEuler.Defs.Sec7.All
import NonUniqueEuler.I.Sec2.Hollow
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Infra.Polar.AngularAverage
import NonUniqueEuler.I.Infra.CkNorm.Basic
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.H.Sec7.Transfer.Outer

/-!
# Helper for `lem:transfer`(4): the field of `ω(t)1_{S_1(t)∪…∪S_{k-1}(t)}` on `N'_k`

Helper of `P/Sec7/Transfer.lean` (`07_several_rings.tex:229-237`).
* `velocity_radial_eq_zero`: the field of the radial `A_iΦ(·/r_i)`, supported in `{|x| ≥ ar_i}`,
  vanishes on `B_{ar_i}` (`lem:hollow`, with `angAvg Φ(·/r_i) = Φ(·/r_i)`);
* `velocity_wPhys_eq`: since `ω(t)1_{S_i(t)} = A_iΦ(·/r_i) + A_iw_i(t,·/r_i)`, the two fields
  agree on `B_{ar_i}`;
* `outer_sum_eq_ball`: `ω(t)1_{S_1(t)∪…∪S_{k-1}(t)} = Σ_{i<k} ω(t)1_{S_i(t)}`
  (`lem:regions-basic`(3)), and `B_{4r_k} ⊂ B_{ar_i}` for `i < k` (`r_k/r_i ≤ a/32`), so the
  identity of item (4) holds on the open set `B_4 ⊃ N'` in ring-`k` units;
* `memCk_congr_of_eqOn`, `memCk_sum`: transfer of `C^k(N')` bounds along an identity on an open
  neighbourhood, and the triangle inequality for finite sums.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.Rings.TransferAux

open RingData Datum

/-! ### `C^k` norms -/

/-- `C^k(U)` membership and norm only depend on the values on an open neighbourhood of `U`. -/
theorem memCk_congr_of_eqOn {k : ℕ} {U V : Set ℂ} {f g : ℂ → ℂ} (hV : IsOpen V) (hUV : U ⊆ V)
    (hfg : ∀ y ∈ V, f y = g y) (hf : MemCk k U f) : MemCk k U g ∧ normCk k U g = normCk k U f := by
  have hiter : ∀ q, ∀ x ∈ U, iteratedFDeriv ℝ q f x = iteratedFDeriv ℝ q g x := by
    intro q x hx
    have h : f =ᶠ[𝓝 x] g := Filter.eventually_of_mem (hV.mem_nhds (hUV hx)) hfg
    exact (h.iteratedFDeriv ℝ q).eq_of_nhds
  have hE : normCkE k U g = normCkE k U f := by
    unfold normCkE supIterDerivE
    refine Finset.sum_congr rfl fun q _ => ?_
    refine iSup_congr fun x => iSup_congr fun hx => ?_
    rw [hiter q x hx]
  obtain ⟨W, hW, hUW, hcd⟩ := hf.near
  have hnear : IsCkNear k U g :=
    ⟨W ∩ V, hW.inter hV, subset_inter hUW hUV,
      (hcd.mono inter_subset_left).congr fun y hy => (hfg y hy.2).symm⟩
  refine ⟨⟨hnear, hE ▸ hf.finite⟩, ?_⟩
  unfold normCk
  rw [hE]

/-- The triangle inequality for a finite sum of `C^k(U)` fields. -/
theorem memCk_sum {k : ℕ} {U : Set ℂ} (hU : U.Nonempty) {ι : Type*} (s : Finset ι)
    (f : ι → ℂ → ℂ) (hf : ∀ i ∈ s, MemCk k U (f i)) :
    MemCk k U (fun y => ∑ i ∈ s, f i y) ∧
      normCk k U (fun y => ∑ i ∈ s, f i y) ≤ ∑ i ∈ s, normCk k U (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := memCk_const_and_normCk k hU (0 : ℂ)
    simp only [Finset.sum_empty]
    refine ⟨h.1, ?_⟩
    rw [h.2, norm_zero]
  | insert a s ha ih =>
    have ih' := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a s)
    have hfun : (fun y => ∑ i ∈ insert a s, f i y) = f a + fun y => ∑ i ∈ s, f i y := by
      funext y
      rw [Finset.sum_insert ha, Pi.add_apply]
    rw [hfun, Finset.sum_insert ha]
    have hadd := hfa.add ih'.1
    exact ⟨hadd.1, hadd.2.trans (by linarith [ih'.2])⟩

/-! ### The radial part of a ring has no field inside the ring -/

/-- `A_i Φ(·/r_i)`. -/
def radialPart (P : Approx) (i : ℕ) (x : ℂ) : ℝ := P.A i * ringPhi P.χ ((P.r i : ℂ)⁻¹ * x)

theorem norm_inv_r_mul (P : Approx) (hP : P.Valid) (i : ℕ) (x : ℂ) :
    ‖((P.r i : ℝ) : ℂ)⁻¹ * x‖ = (P.r i)⁻¹ * ‖x‖ := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hP.r_pos i)]

theorem radialPart_facts (P : Approx) (hP : P.Valid) (i : ℕ) :
    MemLp (radialPart P i) 1 volume ∧ MemLp (radialPart P i) ⊤ volume ∧
      IsRadialPointwise (radialPart P i) ∧
      ∀ x : ℂ, ‖x‖ < a * P.r i → radialPart P i x = 0 := by
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
  refine ⟨hcont.memLp_of_hasCompactSupport hcpt, hcont.memLp_of_hasCompactSupport hcpt, ?_, ?_⟩
  · intro θ x
    simp only [radialPart]
    have he : ((P.r i : ℝ) : ℂ)⁻¹ * rot θ x = rot θ (((P.r i : ℝ) : ℂ)⁻¹ * x) := by
      simp only [rot]
      ring
    rw [he, hrad]
  · intro x hx
    have h0 : ringPhi P.χ (((P.r i : ℝ) : ℂ)⁻¹ * x) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun h => ?_
      have h1 := (hsupp h).1
      rw [norm_inv_r_mul P hP, le_inv_mul_iff₀ hr] at h1
      have : a * P.r i ≤ ‖x‖ := by linarith [mul_comm (P.r i) a]
      linarith
    simp only [radialPart]
    rw [h0, mul_zero]

/-- `lem:hollow`: the field of `A_iΦ(·/r_i)` vanishes on `B_{ar_i}`. -/
theorem velocity_radialPart_eq_zero (P : Approx) (hP : P.Valid) (i : ℕ) {x : ℂ}
    (hx : ‖x‖ < a * P.r i) : velocity (radialPart P i) x = 0 := by
  obtain ⟨h1, hinf, hrad, hz⟩ := radialPart_facts P hP i
  have hR : 0 < a * P.r i := by
    have := a_pos'
    have := hP.r_pos i
    positivity
  have hsym : IsMFoldSymmetric 3 (radialPart P i) :=
    Filter.Eventually.of_forall fun y => hrad _ y
  have h := BS.velocity_angAvg_eq_zero_of_hollow (m₀ := 3) (by norm_num) hR h1 hinf hsym
    (Filter.Eventually.of_forall fun y hy => hz y hy) x (mem_ball_zero_iff.mpr hx)
  rwa [Polar.angAvg_of_isRadialPointwise hrad] at h

/-- `ω(t)1_{S_i(t)} = A_iΦ(·/r_i) + A_iw_i(t,·/r_i)` (definition of `w_i`). -/
theorem omegaRing_eq (P : Approx) (hP : P.Valid) (i : ℕ) (t : ℝ) (x : ℂ) :
    P.omegaRing i t x = radialPart P i x + P.wPhys i t x := by
  have hA := (hP.A_pos i).ne'
  have hr : ((P.r i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hP.r_pos i).ne'
  simp only [radialPart, Approx.wPhys, Approx.wR, Approx.unitsVort, scaleVort]
  rw [mul_inv_cancel_left₀ hr, mul_sub, mul_inv_cancel_left₀ hA]
  ring

theorem integrable_omegaRing (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 P.n) {t : ℝ} (ht : 0 ≤ t) (x : ℂ) :
    Integrable (fun y => biotSavartKernel (x - y) * (P.omegaRing i t y : ℂ)) volume := by
  obtain ⟨-, -, -, -, -, -, ⟨hωsm, hωcpt, -, -⟩, -⟩ := Approx.regions_basic_three P hP hN hi ht
  exact (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf
    (hωsm.continuous.memLp_of_hasCompactSupport hωcpt)
    (hωsm.continuous.memLp_of_hasCompactSupport hωcpt) x).1

/-- On `B_{ar_i}` the field of `A_iw_i(t,·/r_i)` is the field of `ω(t)1_{S_i(t)}`. -/
theorem velocity_wPhys_eq (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 P.n) {t : ℝ} (ht : 0 ≤ t) {x : ℂ} (hx : ‖x‖ < a * P.r i) :
    velocity (P.wPhys i t) x = velocity (P.omegaRing i t) x := by
  obtain ⟨h1, hinf, -, -⟩ := radialPart_facts P hP i
  have hIω := integrable_omegaRing P hP hN hi ht x
  have hIρ := (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf h1 hinf x).1
  have hw : (fun y => biotSavartKernel (x - y) * ((P.wPhys i t y : ℝ) : ℂ)) = fun y =>
      biotSavartKernel (x - y) * (P.omegaRing i t y : ℂ) -
        biotSavartKernel (x - y) * (radialPart P i y : ℂ) := by
    funext y
    rw [show P.wPhys i t y = P.omegaRing i t y - radialPart P i y by
      rw [omegaRing_eq P hP i t y]; ring]
    push_cast
    ring
  have h0 := velocity_radialPart_eq_zero P hP i hx
  rw [velocity] at h0 ⊢
  rw [hw, integral_sub hIω hIρ, h0, sub_zero]
  rfl

/-- **`lem:transfer`(4), the identity**, on `B_4 ⊃ N'` in ring-`k` units
(`07_several_rings.tex:229-237`). -/
theorem outer_sum_eq_ball (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ P.n) {t : ℝ} (ht : 0 ≤ t) :
    ∀ y ∈ ball (0 : ℂ) 4, P.unitsField k (velocity (P.omegaOut k t)) y =
      ∑ i ∈ Finset.Ico 1 k, P.unitsField k (velocity (P.wPhys i t)) y := by
  intro y hy
  have hrk := hP.r_pos k
  have hkI : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨hk, hkn⟩
  obtain ⟨-, -, -, -, hout, -, -, -⟩ := Approx.regions_basic_three P hP hN hkI ht
  have hy4 : ‖y‖ < 4 := mem_ball_zero_iff.mp hy
  have hx : ‖(P.r k : ℂ) * y‖ < 4 * P.r k := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrk]
    nlinarith
  have hring : ∀ i ∈ Finset.Ico 1 k, velocity (P.wPhys i t) ((P.r k : ℂ) * y) =
      velocity (P.omegaRing i t) ((P.r k : ℂ) * y) := by
    intro i hi
    have hi1 := (Finset.mem_Ico.mp hi).1
    have hik := (Finset.mem_Ico.mp hi).2
    have hri := hP.r_pos i
    have hσ := r_div_r_le P hP hi1 hik
    have ha := a_pos'
    have hxi : ‖(P.r k : ℂ) * y‖ < a * P.r i := by
      rw [div_le_iff₀ hri] at hσ
      nlinarith
    exact velocity_wPhys_eq P hP hN (Finset.mem_Icc.2 ⟨hi1, by omega⟩) ht hxi
  have hsum : velocity (P.omegaOut k t) ((P.r k : ℂ) * y) =
      ∑ i ∈ Finset.Ico 1 k, velocity (P.omegaRing i t) ((P.r k : ℂ) * y) := by
    rw [hout, velocity]
    simp only [Complex.ofReal_sum, Finset.mul_sum]
    rw [integral_finsetSum]
    · rfl
    · intro i hi
      exact integrable_omegaRing P hP hN
        (Finset.mem_Icc.2 ⟨(Finset.mem_Ico.mp hi).1, by have := (Finset.mem_Ico.mp hi).2; omega⟩)
        ht _
  simp only [Approx.unitsField, scaleField]
  rw [hsum, Finset.sum_div]
  exact Finset.sum_congr rfl fun i hi => by rw [hring i hi]

end NonUniqueEuler.Rings.TransferAux
