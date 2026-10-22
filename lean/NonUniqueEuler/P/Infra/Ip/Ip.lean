import NonUniqueEuler.Defs.Infra.Ip
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Proof: the integrals `I_p(x) = ∫₀^∞ e^{-xu} (1+u)^p du` (eq:Ip)

Proof of the interface `NonUniqueEuler/I/Infra/Ip/Ip.lean` (`02_prelim.tex:84-92`,
`04_ring.tex:1038`, `lem:pinning` in `08_kick.tex:181-190`).

* Integrability: `(1+u)^p = O(e^{xu/2})` at `+∞` (`isLittleO_pow_exp_pos_mul_atTop`), then
  `integrableOn_exp_neg_mul_of_isBigO_exp`.
* `I_0(x) = 1/x`: `integral_exp_mul_Ioi`.
* Recursion: improper integration by parts `integral_Ioi_mul_deriv_eq_deriv_mul` with
  `U = (1+s)^{p+1}`, `V = -e^{-xs}/x`.
* Closed form: induction with the recursion. Positivity and strict monotonicity follow from the
  closed form (every summand is positive and strictly decreasing in `x > 0`).
* Bounds: `setIntegral_mono_set` (nonnegative integrand), and for `lem:pinning` the
  substitution `s = τ + u` and `1 + τ + u ≤ (1+τ)(1+u)`.
-/

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped Nat Topology

namespace NonUniqueEuler

/-- `(1+u)^p = O(exp(b u))` at `+∞` for every `b > 0`. -/
private lemma one_add_pow_isBigO_exp (p : ℕ) {b : ℝ} (hb : 0 < b) :
    (fun u : ℝ => (1 + u) ^ p) =O[atTop] fun u => Real.exp (b * u) := by
  have h1 : (fun u : ℝ => (1 + u) ^ p) =O[atTop] fun u => Real.exp (b * (1 + u)) :=
    ((isLittleO_pow_exp_pos_mul_atTop p hb).comp_tendsto
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)).isBigO
  refine h1.trans ?_
  have : (fun u : ℝ => Real.exp (b * (1 + u))) = fun u => Real.exp b * Real.exp (b * u) := by
    funext u; rw [← Real.exp_add]; ring_nf
  rw [this]
  exact (isBigO_refl _ _).const_mul_left _

theorem integrableOn_Ip (p : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => Real.exp (-x * u) * (1 + u) ^ p) (Ioi 0) := by
  have h := integrableOn_exp_neg_mul_of_isBigO_exp (c := 0)
    ((by fun_prop : Continuous fun u : ℝ => (1 + u) ^ p).locallyIntegrable.locallyIntegrableOn _)
    (one_add_pow_isBigO_exp p (half_pos hx)) (half_lt_self hx)
  exact h.mono_set Ioi_subset_Ici_self

theorem Ip_zero {x : ℝ} (hx : 0 < x) : Ip 0 x = 1 / x := by
  unfold Ip
  simp only [pow_zero, mul_one]
  rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hx) 0]
  simp

/-- `(1+s)^q e^{-xs} → 0` at `+∞` for `x > 0`. -/
private lemma tendsto_one_add_pow_mul_exp (q : ℕ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s : ℝ => (1 + s) ^ q * Real.exp (-x * s)) atTop (𝓝 0) := by
  have hO : (fun s : ℝ => (1 + s) ^ q * Real.exp (-x * s)) =O[atTop]
      fun s => Real.exp (-(x / 2) * s) := by
    have := (one_add_pow_isBigO_exp q (half_pos hx)).mul
      (isBigO_refl (fun s : ℝ => Real.exp (-x * s)) atTop)
    refine this.congr_right (fun s => ?_)
    rw [← Real.exp_add]
    ring_nf
  have ht : Tendsto (fun s : ℝ => Real.exp (-(x / 2) * s)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 (half_pos hx)))
  exact hO.trans_tendsto ht

/-- `I_{p+1}(x) = 1/x + ((p+1)/x) I_p(x)` (integration by parts). -/
theorem Ip_succ (p : ℕ) {x : ℝ} (hx : 0 < x) :
    Ip (p + 1) x = 1 / x + ((p + 1 : ℝ) / x) * Ip p x := by
  have hx0 : x ≠ 0 := hx.ne'
  have hU : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivAt (fun s : ℝ => (1 + s) ^ (p + 1)) ((p + 1 : ℝ) * (1 + s) ^ p) s := by
    intro s _
    simpa using ((hasDerivAt_id s).const_add 1).fun_pow (p + 1)
  have hV : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivAt (fun s : ℝ => -Real.exp (-x * s) / x) (Real.exp (-x * s)) s := by
    intro s _
    have h1 : HasDerivAt (fun s => Real.exp (-x * s)) (Real.exp (-x * s) * (-x * 1)) s :=
      ((hasDerivAt_id' s).const_mul (-x)).exp
    have h3 : HasDerivAt (fun y => -1 / x * Real.exp (-x * y)) (Real.exp (-x * s)) s :=
      (h1.const_mul (-1 / x)).congr_deriv (by field_simp)
    have hf : (fun s : ℝ => -Real.exp (-x * s) / x) = fun y => -1 / x * Real.exp (-x * y) := by
      funext y
      ring
    rw [hf]
    exact h3
  have huv' : IntegrableOn ((fun s : ℝ => (1 + s) ^ (p + 1)) * fun s => Real.exp (-x * s))
      (Ioi 0) := by
    refine (integrableOn_Ip (p + 1) hx).congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]
    ring
  have hu'v : IntegrableOn ((fun s : ℝ => (p + 1 : ℝ) * (1 + s) ^ p) *
      fun s => -Real.exp (-x * s) / x) (Ioi 0) := by
    refine IntegrableOn.congr_fun ((integrableOn_Ip p hx).const_mul (-(p + 1 : ℝ) / x))
      (fun s _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]
    ring
  have h_zero : Tendsto ((fun s : ℝ => (1 + s) ^ (p + 1)) * fun s => -Real.exp (-x * s) / x)
      (𝓝[>] 0) (𝓝 (-1 / x)) := by
    have hc : Continuous ((fun s : ℝ => (1 + s) ^ (p + 1)) * fun s => -Real.exp (-x * s) / x) :=
      by fun_prop
    have := hc.tendsto 0
    simp only [Pi.mul_apply, add_zero, one_pow, mul_zero, Real.exp_zero, one_mul] at this
    rw [neg_div] at this ⊢
    exact this.mono_left nhdsWithin_le_nhds
  have h_infty : Tendsto ((fun s : ℝ => (1 + s) ^ (p + 1)) * fun s => -Real.exp (-x * s) / x)
      atTop (𝓝 0) := by
    have := (tendsto_one_add_pow_mul_exp (p + 1) hx).const_mul (-1 / x)
    rw [mul_zero] at this
    refine this.congr (fun s => ?_)
    simp only [Pi.mul_apply]
    ring
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hU hV huv' hu'v h_zero h_infty
  have e1 : Ip (p + 1) x = ∫ s in Ioi (0 : ℝ), (1 + s) ^ (p + 1) * Real.exp (-x * s) := by
    unfold Ip
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    ring
  have e2 : ∫ s in Ioi (0 : ℝ), (p + 1 : ℝ) * (1 + s) ^ p * (-Real.exp (-x * s) / x)
      = -((p + 1 : ℝ) / x) * Ip p x := by
    unfold Ip
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    ring
  rw [e1, key, e2]
  ring

/-- The closed form of eq:Ip: `I_p(x) = ∑_{j=0}^p p!/((p-j)! x^{j+1})`. -/
theorem Ip_eq_sum (p : ℕ) {x : ℝ} (hx : 0 < x) :
    Ip p x = ∑ j ∈ Finset.range (p + 1), (p ! : ℝ) / ((p - j)! * x ^ (j + 1)) := by
  have hx0 : x ≠ 0 := hx.ne'
  induction p with
  | zero => rw [Ip_zero hx]; simp
  | succ p ih =>
    rw [Ip_succ p hx, ih, Finset.sum_range_succ' _ (p + 1), Finset.mul_sum, add_comm (1 / x)]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Nat.add_sub_add_right, Nat.factorial_succ]
      push_cast
      have : ((p - j)! : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    · have : ((p + 1)! : ℝ) ≠ 0 := by positivity
      simp only [Nat.sub_zero, zero_add, pow_one]
      field_simp

theorem Ip_pos (p : ℕ) {x : ℝ} (hx : 0 < x) : 0 < Ip p x := by
  rw [Ip_eq_sum p hx]
  refine Finset.sum_pos (fun j _ => ?_) ⟨0, by simp⟩
  positivity

/-- `I_p` is decreasing on `(0, ∞)` (`02_prelim.tex:90`). -/
theorem Ip_strictAntiOn (p : ℕ) : StrictAntiOn (Ip p) (Ioi 0) := by
  intro x hx y hy hxy
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  rw [Ip_eq_sum p hx', Ip_eq_sum p hy']
  refine Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ (fun j _ => ?_)
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hxy hx'.le (Nat.succ_ne_zero j))
    (by positivity)

theorem Ip_antitoneOn (p : ℕ) : AntitoneOn (Ip p) (Ioi 0) := by
  exact (Ip_strictAntiOn p).antitoneOn

/-- `∫₀ᵗ (1+u)^p e^{-xu} du ≤ I_p(x)` for `t ≥ 0` (`04_ring.tex:1038`). -/
theorem intervalIntegral_le_Ip (p : ℕ) {x : ℝ} (hx : 0 < x) {t : ℝ} (ht : 0 ≤ t) :
    ∫ u in (0 : ℝ)..t, (1 + u) ^ p * Real.exp (-x * u) ≤ Ip p x := by
  rw [intervalIntegral.integral_of_le ht]
  have hcomm : ∀ u : ℝ, (1 + u) ^ p * Real.exp (-x * u) = Real.exp (-x * u) * (1 + u) ^ p :=
    fun u => mul_comm _ _
  simp_rw [hcomm]
  unfold Ip
  refine setIntegral_mono_set (integrableOn_Ip p hx) ?_ Ioc_subset_Ioi_self.eventuallyLE
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
  have hu' : 0 ≤ 1 + u := by have : (0 : ℝ) < u := hu; linarith
  exact mul_nonneg (Real.exp_pos _).le (pow_nonneg hu' p)

/-- `∫_τ^{τ'} e^{-xs}(1+s)^p ds ≤ (1+τ)^p e^{-xτ} I_p(x)` for `0 ≤ τ ≤ τ'` (`lem:pinning`). -/
theorem intervalIntegral_le_mul_Ip (p : ℕ) {x : ℝ} (hx : 0 < x) {τ τ' : ℝ} (hτ : 0 ≤ τ)
    (hττ' : τ ≤ τ') :
    ∫ s in τ..τ', Real.exp (-x * s) * (1 + s) ^ p ≤ (1 + τ) ^ p * Real.exp (-x * τ) * Ip p x := by
  have hC0 : 0 ≤ (1 + τ) ^ p * Real.exp (-x * τ) := by
    have : 0 ≤ 1 + τ := by linarith
    positivity
  have hshift : ∫ s in τ..τ', Real.exp (-x * s) * (1 + s) ^ p
      = ∫ u in (0 : ℝ)..(τ' - τ), Real.exp (-x * (τ + u)) * (1 + (τ + u)) ^ p := by
    rw [intervalIntegral.integral_comp_add_left (fun s => Real.exp (-x * s) * (1 + s) ^ p) τ]
    simp
  have hT : (0 : ℝ) ≤ τ' - τ := sub_nonneg.mpr hττ'
  rw [hshift]
  calc ∫ u in (0 : ℝ)..(τ' - τ), Real.exp (-x * (τ + u)) * (1 + (τ + u)) ^ p
      ≤ ∫ u in (0 : ℝ)..(τ' - τ),
          (1 + τ) ^ p * Real.exp (-x * τ) * ((1 + u) ^ p * Real.exp (-x * u)) := by
        refine intervalIntegral.integral_mono_on hT ?_ ?_ (fun u hu => ?_)
        · exact (by fun_prop : Continuous _).intervalIntegrable _ _
        · exact (by fun_prop : Continuous _).intervalIntegrable _ _
        · have hu0 : 0 ≤ u := hu.1
          have h1 : 1 + (τ + u) ≤ (1 + τ) * (1 + u) := by nlinarith
          have h2 : (1 + (τ + u)) ^ p ≤ ((1 + τ) * (1 + u)) ^ p :=
            pow_le_pow_left₀ (by linarith) h1 p
          rw [mul_pow] at h2
          rw [show -x * (τ + u) = -x * τ + -x * u by ring, Real.exp_add]
          calc Real.exp (-x * τ) * Real.exp (-x * u) * (1 + (τ + u)) ^ p
              ≤ Real.exp (-x * τ) * Real.exp (-x * u) * ((1 + τ) ^ p * (1 + u) ^ p) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
            _ = (1 + τ) ^ p * Real.exp (-x * τ) * ((1 + u) ^ p * Real.exp (-x * u)) := by ring
    _ = (1 + τ) ^ p * Real.exp (-x * τ) *
          ∫ u in (0 : ℝ)..(τ' - τ), (1 + u) ^ p * Real.exp (-x * u) :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (1 + τ) ^ p * Real.exp (-x * τ) * Ip p x :=
        mul_le_mul_of_nonneg_left (intervalIntegral_le_Ip p hx hT) hC0

end NonUniqueEuler
