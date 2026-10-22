import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Infra.ODE.WeakIBP
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Helpers for `P/Sec4/Resolvent/Reduction`: the reduction of `lem:resolvent` to `eq:bvp`

Elementary facts used in both directions of the reduction (`04_ring.tex:391-410`):
* `integral_exp_comp`, `intervalIntegrable_exp_comp`: the substitution `r = e^t` for interval
  integrals of arbitrary (not necessarily continuous) integrands;
* `integrableOn_Ioi_of_isProfileL2`, `intervalIntegrable_Fres`: integrability of profiles in
  `Y^0_ℓ` and of the forcing `F = e^{2ξ}(M_λ g)(e^ξ)`;
* `norm_Mres_le`, `continuousOn_Mres`, `continuousOn_kcoef`, `kcoef_eq_zero`;
* `exp_sq_mul_Mres`: the algebraic identity `e^{2ξ} M_λ(g + k_ℓ X) = F + (V_ℓ - ℓ²) X` at
  `r = e^ξ` (`04_ring.tex:395-396`: `e^{2ξ} M_λ k_ℓ = V_ℓ - ℓ²`);
* `rmul_deriv_integrated`: `(rψ')' = r g + ℓ²ψ/r` in integrated form, from the integrated radial
  equation (integration by parts against `v(r) = r`, `LinODE.integral_mul_eq_of_integrated`);
* `green_left`, `green_right`: `𝒢_ℓ h = A r^ℓ` on `(0, ρ₋]` and `B r^{-ℓ}` on `[ρ₊, ∞)`;
* `isProfileL2_eta`: `η = M_λ(g + k_ℓ φ(log r)) ∈ Y^0_ℓ`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.ReductionAux

open SectorSetting

/-! ### The substitution `r = e^t` -/

/-- `∫_{e^a}^{e^b} f(r) dr = ∫_a^b e^t f(e^t) dt`, for any `f`. -/
theorem integral_exp_comp (f : ℝ → ℂ) (a b : ℝ) :
    ∫ r in Real.exp a..Real.exp b, f r =
      ∫ t in a..b, ((Real.exp t : ℝ) : ℂ) * f (Real.exp t) := by
  wlog hab : a ≤ b generalizing a b
  · have h := this b a (le_of_not_ge hab)
    rw [intervalIntegral.integral_symm (Real.exp b) (Real.exp a), h,
      intervalIntegral.integral_symm a b, neg_neg]
  rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le (Real.exp_le_exp.2 hab),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  have h := integral_Icc_deriv_smul_of_deriv_nonneg (f := Real.exp) (f' := Real.exp) (g := f)
    Real.continuous_exp.continuousOn (fun x _ => Real.hasDerivAt_exp x)
    (fun x _ => (Real.exp_pos x).le) hab
  rw [← h]
  simp only [Complex.real_smul]

/-- If `f` is integrable on `(0, ∞)`, then `t ↦ e^t f(e^t)` is interval integrable. -/
theorem intervalIntegrable_exp_comp {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) (a b : ℝ) :
    IntervalIntegrable (fun t => ((Real.exp t : ℝ) : ℂ) * f (Real.exp t)) volume a b := by
  wlog hab : a ≤ b generalizing a b
  · exact (this b a (le_of_not_ge hab)).symm
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have h := (integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg (f := Real.exp) (f' := Real.exp)
    (g := f) Real.continuous_exp.continuousOn (fun x _ => Real.hasDerivAt_exp x)
    (fun x _ => (Real.exp_pos x).le) hab).2
    (hf.mono_set fun r hr => lt_of_lt_of_le (Real.exp_pos a) hr.1)
  simpa only [Complex.real_smul] using h

theorem uIcc_subset_Ioi {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : uIcc A B ⊆ Ioi 0 := by
  intro x hx
  rcases mem_uIcc.1 hx with h | h
  · exact hA.trans_le h.1
  · exact hB.trans_le h.1

/-! ### Integrability of profiles -/

/-- A profile in `Y^0_ℓ` is integrable on `(0, ∞)`. -/
theorem integrableOn_Ioi_of_isProfileL2 (S : SectorSetting) {g : ℝ → ℂ}
    (hg : S.IsProfileL2 g) : IntegrableOn g (Ioi 0) := by
  have h1 : IntegrableOn g (Icc S.ρm S.ρp) :=
    memLp_one_iff_integrable.1 (hg.1.mono_exponent (by norm_num))
  have h2 : Integrable (indicator (Icc S.ρm S.ρp) g) :=
    (integrable_indicator_iff measurableSet_Icc).2 h1
  refine (h2.integrableOn (s := Ioi 0)).congr ?_
  filter_upwards [hg.2] with r hr
  by_cases hm : r ∈ Icc S.ρm S.ρp
  · exact indicator_of_mem hm g
  · rw [indicator_of_notMem hm, hr hm]

theorem intervalIntegrable_of_integrableOn {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) : IntervalIntegrable f volume A B :=
  intervalIntegrable_iff.2 (hf.mono_set (uIoc_subset_uIcc.trans (uIcc_subset_Ioi hA hB)))

/-! ### `M_λ` and `k_ℓ` -/

theorem denom_ne_zero (S : SectorSetting) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ) (G r : ℝ) :
    z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- `|M_λ(r)| ≤ 1/Re λ` (`lem:sector`(3): `|λ + iℓΩ| ≥ Re λ`). -/
theorem norm_Mres_le (S : SectorSetting) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ) (G r : ℝ) :
    ‖S.Mres ℓ z G r‖ ≤ 1 / z.re := by
  have hre : (z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)).re = z.re := by simp
  have h1 : z.re ≤ ‖z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)‖ :=
    hre ▸ Complex.re_le_norm _
  rw [Mres, norm_inv, one_div]
  exact inv_anti₀ hz h1

theorem continuousOn_Mres (S : SectorSetting) (hS : S.Valid) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ)
    (G : ℝ) : ContinuousOn (S.Mres ℓ z G) (Ioi 0) := by
  have h1 : ContinuousOn (fun r : ℝ => ((S.Omega G r : ℝ) : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn (contDiffOn_Omega S hS G).continuousOn
  have h2 : ContinuousOn (fun r : ℝ => z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ))
      (Ioi 0) := continuousOn_const.add (continuousOn_const.mul h1)
  exact h2.inv₀ fun r _ => denom_ne_zero S hz ℓ G r

theorem contDiff_omR (S : SectorSetting) (hS : S.Valid) : ContDiff ℝ ∞ S.omR :=
  hS.contDiff.comp Complex.ofRealCLM.contDiff

theorem contDiff_dom (S : SectorSetting) (hS : S.Valid) : ContDiff ℝ ∞ S.dom :=
  (contDiff_infty_iff_deriv.1 (contDiff_omR S hS)).2

theorem continuousOn_kcoef (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) :
    ContinuousOn (S.kcoef ℓ) (Ioi 0) := by
  have h1 : Continuous fun r : ℝ => ((S.dom r : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (contDiff_dom S hS).continuous
  have h2 : ContinuousOn (fun r : ℝ => Complex.I * (ℓ : ℂ) * ((S.dom r : ℝ) : ℂ) / (r : ℂ))
      (Ioi 0) :=
    (continuous_const.mul h1).continuousOn.div Complex.continuous_ofReal.continuousOn
      fun r hr => Complex.ofReal_ne_zero.2 (ne_of_gt (show (0 : ℝ) < r from hr))
  exact h2

theorem kcoef_eq_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) {r : ℝ} (hr : 0 < r)
    (hrI : r ∉ Icc S.r₁ S.r₂) : S.kcoef ℓ r = 0 := by
  simp [kcoef, hS.dom_eq_zero r hr hrI]

/-- The forcing `F(ξ) = e^{2ξ}(M_λ g)(e^ξ)` is interval integrable for `g ∈ Y^0_ℓ`. -/
theorem intervalIntegrable_Fres (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) {g : ℝ → ℂ} (hg : S.IsProfileL2 g) (a b : ℝ) :
    IntervalIntegrable (S.Fres ℓ z G g) volume a b := by
  have h1 := intervalIntegrable_exp_comp (integrableOn_Ioi_of_isProfileL2 S hg) a b
  have h2 : Continuous fun t : ℝ => ((Real.exp t : ℝ) : ℂ) * S.Mres ℓ z G (Real.exp t) :=
    (Complex.continuous_ofReal.comp Real.continuous_exp).mul
      ((continuousOn_Mres S hS hz ℓ G).comp_continuous Real.continuous_exp
        fun t => Real.exp_pos t)
  have h3 := h1.continuousOn_mul h2.continuousOn
  have heq : S.Fres ℓ z G g = fun t => (((Real.exp t : ℝ) : ℂ) * S.Mres ℓ z G (Real.exp t)) *
      (((Real.exp t : ℝ) : ℂ) * g (Real.exp t)) := by
    funext t
    simp only [Fres]
    rw [show (2 : ℝ) * t = t + t by ring, Real.exp_add, Complex.ofReal_mul]
    ring
  rw [heq]
  exact h3

/-! ### The key algebraic identity -/

/-- `e^{2ξ} M_λ(e^ξ) (g(e^ξ) + k_ℓ(e^ξ) X) = F(ξ) + (V_ℓ(ξ) - ℓ²) X` (`04_ring.tex:395-396`:
`e^{2ξ} M_λ k_ℓ = iℓ f_ξ M_λ = V_ℓ - ℓ²`). -/
theorem exp_sq_mul_Mres (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) (g : ℝ → ℂ) (t : ℝ)
    (X : ℂ) :
    ((Real.exp t : ℝ) : ℂ) * ((Real.exp t : ℝ) : ℂ) *
        (S.Mres ℓ z G (Real.exp t) * (g (Real.exp t) + S.kcoef ℓ (Real.exp t) * X)) =
      S.Fres ℓ z G g t + (S.Vric ℓ z G t - (ℓ : ℂ) ^ 2) * X := by
  have hE : ((Real.exp t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos t).ne'
  simp only [Fres, Vric, Mres, kcoef, fxi, Int.cast_natCast, Complex.ofReal_mul]
  rw [show (2 : ℝ) * t = t + t by ring, Real.exp_add, Complex.ofReal_mul]
  generalize ((Real.exp t : ℝ) : ℂ) = E at hE ⊢
  generalize ((S.dom (Real.exp t) : ℝ) : ℂ) = d
  generalize (z + Complex.I * (ℓ : ℂ) * ((S.Omega G (Real.exp t) : ℝ) : ℂ)) = D
  have h1 : E * E⁻¹ = 1 := mul_inv_cancel₀ hE
  simp only [div_eq_mul_inv]
  linear_combination (Complex.I * (ℓ : ℂ) * d * X * D⁻¹ * E) * h1

/-! ### `(rψ')' = r g + ℓ²ψ/r` -/

/-- From the integrated radial equation `ψ'(b) - ψ'(a) = ∫_a^b (g - ψ'/r + ℓ²ψ/r²)`:
`Bψ'(B) - Aψ'(A) = ∫_A^B (r g + ℓ²ψ/r) dr` for `A, B > 0` (integration by parts against
`v(r) = r`). -/
theorem rmul_deriv_integrated {ℓ : ℤ} {g ψ ψ' : ℝ → ℂ}
    (hd : ∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r) (hc : ContinuousOn ψ' (Ioi 0))
    (heq : ∀ a b : ℝ, 0 < a → 0 < b →
      ψ' b - ψ' a = ∫ r in a..b, (g r - ψ' r / (r : ℂ) + (ℓ : ℂ) ^ 2 * ψ r / (r : ℂ) ^ 2))
    (hg : IntegrableOn g (Ioi 0)) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (B : ℂ) * ψ' B - (A : ℂ) * ψ' A =
      ∫ r in A..B, ((r : ℂ) * g r + (ℓ : ℂ) ^ 2 * ψ r / (r : ℂ)) := by
  have hsub := uIcc_subset_Ioi hA hB
  have hψc : ContinuousOn ψ (uIcc A B) := fun r hr =>
    (hd r (hsub hr)).continuousAt.continuousWithinAt
  have hψ'c : ContinuousOn ψ' (uIcc A B) := hc.mono hsub
  have hne : ∀ r ∈ uIcc A B, (r : ℂ) ≠ 0 := fun r hr =>
    Complex.ofReal_ne_zero.2 (ne_of_gt (hsub hr))
  have hrest : ContinuousOn (fun r : ℝ => -(ψ' r / (r : ℂ)) + (ℓ : ℂ) ^ 2 * ψ r / (r : ℂ) ^ 2)
      (uIcc A B) := by
    refine (hψ'c.div Complex.continuous_ofReal.continuousOn hne).neg.add ?_
    exact (continuousOn_const.mul hψc).div (Complex.continuous_ofReal.continuousOn.pow 2)
      fun r hr => pow_ne_zero 2 (hne r hr)
  set H : ℝ → ℂ := fun r => g r - ψ' r / (r : ℂ) + (ℓ : ℂ) ^ 2 * ψ r / (r : ℂ) ^ 2 with hHdef
  have hHI : IntervalIntegrable H volume A B := by
    have := (intervalIntegrable_of_integrableOn hg hA hB).add hrest.intervalIntegrable
    refine this.congr fun r _ => ?_
    simp only [H]
    ring
  have hU : ∀ t ∈ uIcc A B, ψ' t = ψ' A + ∫ s in A..t, H s := fun t ht => by
    rw [← heq A t hA (hsub ht)]
    ring
  have hv : ∀ t ∈ uIcc A B, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := fun t _ => by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hIBP : ∫ t in A..B, (t : ℂ) * H t = (B : ℂ) * ψ' B - (A : ℂ) * ψ' A -
      ∫ t in A..B, (1 : ℂ) * ψ' t :=
    LinODE.integral_mul_eq_of_integrated (v := fun t : ℝ => (t : ℂ)) (v' := fun _ => 1) hHI hU
      hv continuousOn_const
  have hcongr : ∫ r in A..B, ((r : ℂ) * g r + (ℓ : ℂ) ^ 2 * ψ r / (r : ℂ)) =
      ∫ r in A..B, ((r : ℂ) * H r + ψ' r) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hr0 := hne r hr
    simp only [H]
    field_simp
    ring
  rw [hcongr, intervalIntegral.integral_add
    (hHI.continuousOn_mul Complex.continuous_ofReal.continuousOn) hψ'c.intervalIntegrable, hIBP]
  simp only [one_mul]
  ring

/-! ### `𝒢_ℓ h` off the support -/

/-- `𝒢_ℓ h(r) = A r^ℓ` for `r ≤ ρ₋` (`04_ring.tex:229`). -/
theorem green_left (S : SectorSetting) (ℓ : ℕ) {h : ℝ → ℂ} (hh : S.IsProfileL2 h) :
    ∃ A : ℂ, ∀ r : ℝ, r ≤ S.ρm → green ℓ h r = A * ((r ^ ℓ : ℝ) : ℂ) := by
  refine ⟨-((((2 * |((ℓ : ℤ) : ℝ)|)⁻¹ : ℝ)) : ℂ) *
    ∫ ρ in Ioi (0 : ℝ), ((ρ⁻¹ ^ ℓ : ℝ) : ℂ) * h ρ * (ρ : ℂ), fun r hrm => ?_⟩
  have hae : (fun ρ : ℝ => (((min r ρ / max r ρ) ^ ((ℓ : ℤ).natAbs) : ℝ) : ℂ) * h ρ * (ρ : ℂ))
      =ᵐ[volume.restrict (Ioi 0)]
      fun ρ => ((r ^ ℓ : ℝ) : ℂ) * (((ρ⁻¹ ^ ℓ : ℝ) : ℂ) * h ρ * (ρ : ℂ)) := by
    filter_upwards [hh.2] with ρ hρ
    by_cases hm : ρ ∈ Icc S.ρm S.ρp
    · have hrρ : r ≤ ρ := hrm.trans hm.1
      rw [min_eq_left hrρ, max_eq_right hrρ, Int.natAbs_natCast, div_eq_mul_inv, mul_pow,
        Complex.ofReal_mul]
      ring
    · rw [hρ hm]
      simp
  rw [green, integral_congr_ae hae, integral_const_mul]
  ring

/-- `𝒢_ℓ h(r) = B r^{-ℓ}` for `r ≥ ρ₊` (`04_ring.tex:229`). -/
theorem green_right (S : SectorSetting) (ℓ : ℕ) {h : ℝ → ℂ} (hh : S.IsProfileL2 h) :
    ∃ B : ℂ, ∀ r : ℝ, S.ρp ≤ r → green ℓ h r = B * ((r⁻¹ ^ ℓ : ℝ) : ℂ) := by
  refine ⟨-((((2 * |((ℓ : ℤ) : ℝ)|)⁻¹ : ℝ)) : ℂ) *
    ∫ ρ in Ioi (0 : ℝ), ((ρ ^ ℓ : ℝ) : ℂ) * h ρ * (ρ : ℂ), fun r hrp => ?_⟩
  have hae : (fun ρ : ℝ => (((min r ρ / max r ρ) ^ ((ℓ : ℤ).natAbs) : ℝ) : ℂ) * h ρ * (ρ : ℂ))
      =ᵐ[volume.restrict (Ioi 0)]
      fun ρ => ((r⁻¹ ^ ℓ : ℝ) : ℂ) * (((ρ ^ ℓ : ℝ) : ℂ) * h ρ * (ρ : ℂ)) := by
    filter_upwards [hh.2] with ρ hρ
    by_cases hm : ρ ∈ Icc S.ρm S.ρp
    · have hρr : ρ ≤ r := hm.2.trans hrp
      rw [min_eq_right hρr, max_eq_left hρr, Int.natAbs_natCast, div_eq_mul_inv, mul_pow,
        Complex.ofReal_mul]
      ring
    · rw [hρ hm]
      simp
  rw [green, integral_congr_ae hae, integral_const_mul]
  ring

/-! ### The converse profile `η = M_λ(g + k_ℓ φ(log r))` -/

/-- For `g ∈ Y^0_ℓ` and `φ` continuous, `η = M_λ(g + k_ℓ φ(log r))` is in `Y^0_ℓ`
(`04_ring.tex:403-405`): `|M_λ| ≤ 1/Re λ`, `k_ℓ φ(log r)` is continuous on `[ρ₋,ρ₊]` and vanishes
off `[r₁, r₂] ⊆ [ρ₋, ρ₊]`. -/
theorem isProfileL2_eta (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) {z : ℂ} (hz : 0 < z.re)
    (G : ℝ) {g : ℝ → ℂ} (hg : S.IsProfileL2 g) {φ : ℝ → ℂ} (hφc : Continuous φ) :
    S.IsProfileL2 (fun r => S.Mres ℓ z G r * (g r + S.kcoef ℓ r * φ (Real.log r))) := by
  have hsub : Icc S.ρm S.ρp ⊆ Ioi 0 := fun r hr => hS.ρm_pos.trans_le hr.1
  have hk : ContinuousOn (fun r => S.kcoef ℓ r * φ (Real.log r)) (Icc S.ρm S.ρp) :=
    ((continuousOn_kcoef S hS ℓ).mono hsub).mul
      (hφc.comp_continuousOn (Real.continuousOn_log.mono fun r hr => (hsub hr).ne'))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hk
  have hkL : MemLp (fun r => S.kcoef ℓ r * φ (Real.log r)) 2 (volume.restrict (Icc S.ρm S.ρp)) :=
    MemLp.of_bound (hk.aestronglyMeasurable measurableSet_Icc) C
      (ae_restrict_of_forall_mem measurableSet_Icc hC)
  have hsum := hg.1.add hkL
  have hM : ContinuousOn (S.Mres ℓ z G) (Icc S.ρm S.ρp) :=
    (continuousOn_Mres S hS hz ℓ G).mono hsub
  refine ⟨hsum.of_le_mul (c := 1 / z.re)
    ((hM.aestronglyMeasurable measurableSet_Icc).mul hsum.1) (Eventually.of_forall fun r => ?_),
    ?_⟩
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_Mres_le S hz ℓ G r) (norm_nonneg _)
  · filter_upwards [hg.2, ae_restrict_mem measurableSet_Ioi] with r hr hpos hnot
    have hk0 : S.kcoef ℓ r = 0 := kcoef_eq_zero S hS ℓ hpos fun hm =>
      hnot ⟨hS.ρm_lt_r₁.le.trans hm.1, hm.2.trans hS.r₂_lt_ρp.le⟩
    simp [hr hnot, hk0]

end NonUniqueEuler.ReductionAux
