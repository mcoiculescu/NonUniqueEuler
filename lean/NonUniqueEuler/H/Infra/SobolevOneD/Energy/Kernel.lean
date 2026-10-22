import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Helper for `P/Infra/SobolevOneD/Energy`: the kernels `e^{-L|z|}` and `sgn(z) e^{-L|z|}`

For `L > 0` we use the kernels `k0 L z = e^{-L|z|}` and `k1 L z = sgn(z) e^{-L|z|}` (value `-1`
at `z = 0`). Distributionally `k0' = -L k1` and `k1' = -L k0 + 2δ`; tested against a `C¹`
function `φ` with `φ, φ'` integrable and `φ` bounded this reads
* `∫ k0(x-y) φ'(x) dx = L ∫ k1(x-y) φ(x) dx` (`integral_k0_mul_deriv`),
* `∫ k1(x-y) φ'(x) dx = -2 φ(y) + L ∫ k0(x-y) φ(x) dx` (`integral_k1_mul_deriv`).
Proof: split at `y` and apply the fundamental theorem of calculus on the half-lines
(`integral_Ioi_of_hasDerivAt_of_tendsto`, `integral_Iic_of_hasDerivAt_of_tendsto`) to
`e^{∓L(x-y)} φ(x)`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace NonUniqueEuler.Sob.EnergyAux

/-- The kernel `e^{-L|z|}`. -/
def k0 (L z : ℝ) : ℝ := Real.exp (-L * |z|)

/-- The kernel `sgn(z) e^{-L|z|}`, with value `-1` at `0`. -/
def k1 (L z : ℝ) : ℝ := if 0 < z then Real.exp (-L * z) else -Real.exp (L * z)

/-- A `C¹` function on the line with `φ, φ'` integrable and `φ` bounded: the class of
functions the kernels are tested against. -/
structure TestLike (φ φ' : ℝ → ℂ) : Prop where
  deriv : ∀ x, HasDerivAt φ (φ' x) x
  int : Integrable φ
  int' : Integrable φ'
  bdd : ∃ M, ∀ x, ‖φ x‖ ≤ M

theorem k0_pos (L z : ℝ) : 0 < k0 L z := Real.exp_pos _

theorem k0_le_one {L : ℝ} (hL : 0 ≤ L) (z : ℝ) : k0 L z ≤ 1 := by
  unfold k0
  rw [Real.exp_le_one_iff]
  have := abs_nonneg z
  nlinarith

theorem k0_neg (L z : ℝ) : k0 L (-z) = k0 L z := by
  simp [k0, abs_neg]

theorem abs_k1 (L z : ℝ) : |k1 L z| = k0 L z := by
  unfold k1 k0
  split_ifs with h
  · rw [abs_of_pos (Real.exp_pos _), abs_of_pos h]
  · rw [abs_neg, abs_of_pos (Real.exp_pos _), abs_of_nonpos (not_lt.1 h)]
    congr 1
    ring

theorem abs_k1_le_one {L : ℝ} (hL : 0 ≤ L) (z : ℝ) : |k1 L z| ≤ 1 := by
  rw [abs_k1]; exact k0_le_one hL z

theorem continuous_k0 (L : ℝ) : Continuous (k0 L) := by
  unfold k0; fun_prop

theorem measurable_k1 (L : ℝ) : Measurable (k1 L) := by
  unfold k1
  refine Measurable.ite (measurableSet_lt measurable_const measurable_id) ?_ ?_ <;>
    fun_prop

theorem k0_of_pos {L z : ℝ} (hz : 0 < z) : k0 L z = Real.exp (-L * z) := by
  simp [k0, abs_of_pos hz]

theorem k0_of_nonpos {L z : ℝ} (hz : z ≤ 0) : k0 L z = Real.exp (L * z) := by
  simp only [k0, abs_of_nonpos hz]
  congr 1
  ring

theorem k1_of_pos {L z : ℝ} (hz : 0 < z) : k1 L z = Real.exp (-L * z) := by
  simp [k1, hz]

theorem k1_of_nonpos {L z : ℝ} (hz : z ≤ 0) : k1 L z = -Real.exp (L * z) := by
  simp [k1, not_lt.2 hz]

/-- `k0' = -L k1` away from `0`. -/
theorem hasDerivAt_k0 (L : ℝ) {z : ℝ} (hz : z ≠ 0) : HasDerivAt (k0 L) (-L * k1 L z) z := by
  rcases lt_or_gt_of_ne hz with h | h
  · have heq : (fun w => Real.exp (L * w)) =ᶠ[𝓝 z] k0 L := by
      filter_upwards [Iio_mem_nhds h] with w hw
      exact (k0_of_nonpos (le_of_lt hw)).symm
    have hd : HasDerivAt (fun w => Real.exp (L * w)) (Real.exp (L * z) * L) z := by
      simpa using ((hasDerivAt_id z).const_mul L).exp
    refine (hd.congr_of_eventuallyEq heq.symm).congr_deriv ?_
    rw [k1_of_nonpos (le_of_lt h)]
    ring
  · have heq : (fun w => Real.exp (-L * w)) =ᶠ[𝓝 z] k0 L := by
      filter_upwards [Ioi_mem_nhds h] with w hw
      exact (k0_of_pos hw).symm
    have hd : HasDerivAt (fun w => Real.exp (-L * w)) (Real.exp (-L * z) * (-L)) z := by
      simpa using ((hasDerivAt_id z).const_mul (-L)).exp
    refine (hd.congr_of_eventuallyEq heq.symm).congr_deriv ?_
    rw [k1_of_pos h]
    ring

/-- `k1` is continuous away from `0`. -/
theorem continuousAt_k1 (L : ℝ) {z : ℝ} (hz : z ≠ 0) : ContinuousAt (k1 L) z := by
  rcases lt_or_gt_of_ne hz with h | h
  · have heq : (fun w => -Real.exp (L * w)) =ᶠ[𝓝 z] k1 L := by
      filter_upwards [Iio_mem_nhds h] with w hw
      exact (k1_of_nonpos (le_of_lt hw)).symm
    exact ContinuousAt.congr (by fun_prop) heq
  · have heq : (fun w => Real.exp (-L * w)) =ᶠ[𝓝 z] k1 L := by
      filter_upwards [Ioi_mem_nhds h] with w hw
      exact (k1_of_pos hw).symm
    exact ContinuousAt.congr (by fun_prop) heq

/-- `|e^{-u} - e^{-v}| ≤ |u - v|` for `u, v ≥ 0`. -/
theorem abs_exp_neg_sub_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.exp (-u) - Real.exp (-v)| ≤ |u - v| := by
  wlog h : u ≤ v generalizing u v
  · rw [abs_sub_comm, abs_sub_comm u]
    exact this hv hu (le_of_not_ge h)
  have hsplit : Real.exp (-v) = Real.exp (-u) * Real.exp (-(v - u)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : Real.exp (-(v - u)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : -(v - u) + 1 ≤ Real.exp (-(v - u)) := Real.add_one_le_exp _
  have h3 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h4 : 0 < Real.exp (-u) := Real.exp_pos _
  rw [hsplit, abs_of_nonpos (sub_nonpos.2 h)]
  rw [abs_le]
  constructor <;> nlinarith

/-- `k0` is `L`-Lipschitz. -/
theorem abs_k0_sub_le {L : ℝ} (hL : 0 ≤ L) (s t : ℝ) : |k0 L s - k0 L t| ≤ L * |s - t| := by
  unfold k0
  have h := abs_exp_neg_sub_le (mul_nonneg hL (abs_nonneg s)) (mul_nonneg hL (abs_nonneg t))
  rw [neg_mul, neg_mul]
  refine h.trans ?_
  rw [← mul_sub, abs_mul, abs_of_nonneg hL]
  exact mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub s t) hL

/-! ### Integrability of the kernels -/

theorem integrable_k0 {L : ℝ} (hL : 0 < L) : Integrable (k0 L) := by
  have hI : IntegrableOn (fun x : ℝ => Real.exp (-L * x)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact exp_neg_integrableOn_Ioi 0 hL
  have hind : Integrable (Set.indicator (Ici 0) fun x : ℝ => Real.exp (-L * x)) :=
    (integrable_indicator_iff measurableSet_Ici).2 hI
  refine (hind.add hind.comp_neg).mono' (continuous_k0 L).aestronglyMeasurable ?_
  refine Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_pos (k0_pos L x)]
  have hnn : ∀ y : ℝ, 0 ≤ Set.indicator (Ici 0) (fun x : ℝ => Real.exp (-L * x)) y :=
    fun y => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) y
  rcases le_or_gt 0 x with hx | hx
  · have : Set.indicator (Ici 0) (fun x : ℝ => Real.exp (-L * x)) x = k0 L x := by
      rw [Set.indicator_of_mem (mem_Ici.2 hx), k0, abs_of_nonneg hx]
    simp only [Pi.add_apply]
    linarith [hnn (-x)]
  · have : Set.indicator (Ici 0) (fun x : ℝ => Real.exp (-L * x)) (-x) = k0 L x := by
      rw [Set.indicator_of_mem (mem_Ici.2 (by linarith)), k0, abs_of_neg hx]
    simp only [Pi.add_apply]
    linarith [hnn x]

theorem k0_sq (L z : ℝ) : k0 L z ^ 2 = k0 (2 * L) z := by
  unfold k0
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-! ### The half-line identities -/

theorem tendsto_exp_neg_mul_sub_atTop {L : ℝ} (hL : 0 < L) (y : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (-L * (x - y))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => L * (x + -y)) atTop atTop :=
    Tendsto.const_mul_atTop hL (tendsto_atTop_add_const_right _ (-y) tendsto_id)
  have := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  refine this.congr fun x => ?_
  simp only [Function.comp]
  congr 1
  ring

theorem tendsto_exp_mul_sub_atBot {L : ℝ} (hL : 0 < L) (y : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (L * (x - y))) atBot (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => L * (x + -y)) atBot atBot :=
    Tendsto.const_mul_atBot hL (tendsto_atBot_add_const_right _ (-y) tendsto_id)
  have := Real.tendsto_exp_atBot.comp h1
  refine this.congr fun x => ?_
  simp only [Function.comp]
  congr 1

/-- Bounded-factor integrability on a set. -/
theorem integrableOn_ofReal_mul {s : Set ℝ} (hs : MeasurableSet s) {e : ℝ → ℝ}
    (he : Continuous e) (hb : ∀ x ∈ s, |e x| ≤ 1) {g : ℝ → ℂ} (hg : Integrable g) :
    IntegrableOn (fun x => (e x : ℂ) * g x) s := by
  refine Integrable.bdd_mul (c := 1) hg.integrableOn
    (Complex.continuous_ofReal.comp he).aestronglyMeasurable ?_
  rw [ae_restrict_iff' hs]
  refine Eventually.of_forall fun x hx => ?_
  simpa [Complex.norm_real] using hb x hx

/-- FTC on `(y, ∞)` for `e^{-L(x-y)} φ(x)`. -/
theorem integral_Ioi_exp_mul_deriv {L : ℝ} (hL : 0 < L) {φ φ' : ℝ → ℂ} (hφ : TestLike φ φ')
    (y : ℝ) :
    ∫ x in Ioi y, (Real.exp (-L * (x - y)) : ℂ) * φ' x =
      -φ y + L * ∫ x in Ioi y, (Real.exp (-L * (x - y)) : ℂ) * φ x := by
  obtain ⟨M, hM⟩ := hφ.bdd
  set e : ℝ → ℝ := fun x => Real.exp (-L * (x - y)) with he_def
  have he_cont : Continuous e := by rw [he_def]; fun_prop
  have he_le : ∀ x ∈ Ioi y, |e x| ≤ 1 := fun x hx => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by have : y < x := hx; nlinarith)
  have he_d : ∀ x, HasDerivAt (fun x => (e x : ℂ)) ((e x * (-L) : ℝ) : ℂ) x := by
    intro x
    have h0 : HasDerivAt e (e x * (-L)) x := by
      have := (((hasDerivAt_id x).sub_const y).const_mul (-L)).exp
      simpa [he_def] using this
    exact h0.ofReal_comp
  have hint1 : IntegrableOn (fun x => (e x : ℂ) * φ' x) (Ioi y) :=
    integrableOn_ofReal_mul measurableSet_Ioi he_cont he_le hφ.int'
  have hint2 : IntegrableOn (fun x => (e x : ℂ) * φ x) (Ioi y) :=
    integrableOn_ofReal_mul measurableSet_Ioi he_cont he_le hφ.int
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun x => (e x : ℂ) * φ x)
    (f' := fun x => (e x : ℂ) * φ' x - L * ((e x : ℂ) * φ x)) (m := 0)
    (((he_d y).fun_mul (hφ.deriv y)).continuousAt.continuousWithinAt)
    (fun x _ => ((he_d x).fun_mul (hφ.deriv x)).congr_deriv (by push_cast; ring))
    (hint1.sub (hint2.const_mul _))
    (by
      refine squeeze_zero_norm (a := fun x => e x * M) (fun x => ?_) ?_
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hM x) (Real.exp_pos _).le
      · have := (tendsto_exp_neg_mul_sub_atTop hL y).mul_const M
        rw [zero_mul] at this
        exact this)
  rw [integral_sub hint1 (hint2.const_mul _), integral_const_mul] at hFTC
  have hy : (e y : ℂ) = 1 := by simp [he_def]
  rw [hy, one_mul, zero_sub] at hFTC
  linear_combination hFTC

/-- FTC on `(-∞, y]` for `e^{L(x-y)} φ(x)`. -/
theorem integral_Iic_exp_mul_deriv {L : ℝ} (hL : 0 < L) {φ φ' : ℝ → ℂ} (hφ : TestLike φ φ')
    (y : ℝ) :
    ∫ x in Iic y, (Real.exp (L * (x - y)) : ℂ) * φ' x =
      φ y - L * ∫ x in Iic y, (Real.exp (L * (x - y)) : ℂ) * φ x := by
  obtain ⟨M, hM⟩ := hφ.bdd
  set e : ℝ → ℝ := fun x => Real.exp (L * (x - y)) with he_def
  have he_cont : Continuous e := by rw [he_def]; fun_prop
  have he_le : ∀ x ∈ Iic y, |e x| ≤ 1 := fun x hx => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by have : x ≤ y := hx; nlinarith)
  have he_d : ∀ x, HasDerivAt (fun x => (e x : ℂ)) ((e x * L : ℝ) : ℂ) x := by
    intro x
    have h0 : HasDerivAt e (e x * L) x := by
      have := (((hasDerivAt_id x).sub_const y).const_mul L).exp
      simpa [he_def] using this
    exact h0.ofReal_comp
  have hint1 : IntegrableOn (fun x => (e x : ℂ) * φ' x) (Iic y) :=
    integrableOn_ofReal_mul measurableSet_Iic he_cont he_le hφ.int'
  have hint2 : IntegrableOn (fun x => (e x : ℂ) * φ x) (Iic y) :=
    integrableOn_ofReal_mul measurableSet_Iic he_cont he_le hφ.int
  have hFTC := integral_Iic_of_hasDerivAt_of_tendsto (f := fun x => (e x : ℂ) * φ x)
    (f' := fun x => (e x : ℂ) * φ' x + L * ((e x : ℂ) * φ x)) (m := 0)
    (((he_d y).fun_mul (hφ.deriv y)).continuousAt.continuousWithinAt)
    (fun x _ => ((he_d x).fun_mul (hφ.deriv x)).congr_deriv (by push_cast; ring))
    (hint1.add (hint2.const_mul _))
    (by
      refine squeeze_zero_norm (a := fun x => e x * M) (fun x => ?_) ?_
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hM x) (Real.exp_pos _).le
      · have := (tendsto_exp_mul_sub_atBot hL y).mul_const M
        rw [zero_mul] at this
        exact this)
  rw [integral_add hint1 (hint2.const_mul _), integral_const_mul] at hFTC
  have hy : (e y : ℂ) = 1 := by simp [he_def]
  rw [hy, one_mul, sub_zero] at hFTC
  linear_combination hFTC

/-! ### The distributional derivatives of the kernels -/

theorem integrable_ofReal_mul {e : ℝ → ℝ} (he : Measurable e) (hb : ∀ x, |e x| ≤ 1)
    {g : ℝ → ℂ} (hg : Integrable g) : Integrable (fun x => (e x : ℂ) * g x) := by
  refine Integrable.bdd_mul (c := 1) hg
    (Complex.measurable_ofReal.comp he).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  simpa [Complex.norm_real] using hb x

theorem integrable_k0_sub_mul {L : ℝ} (hL : 0 ≤ L) (y : ℝ) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun x => (k0 L (x - y) : ℂ) * g x) :=
  integrable_ofReal_mul (e := fun x => k0 L (x - y))
    ((continuous_k0 L).measurable.comp (measurable_id.sub_const y))
    (fun x => by rw [abs_of_pos (k0_pos _ _)]; exact k0_le_one hL _) hg

theorem integrable_k1_sub_mul {L : ℝ} (hL : 0 ≤ L) (y : ℝ) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun x => (k1 L (x - y) : ℂ) * g x) :=
  integrable_ofReal_mul (e := fun x => k1 L (x - y))
    ((measurable_k1 L).comp (measurable_id.sub_const y))
    (fun _ => abs_k1_le_one hL _) hg

theorem setIntegral_Ioi_k0 (L y : ℝ) (g : ℝ → ℂ) :
    ∫ x in Ioi y, (k0 L (x - y) : ℂ) * g x =
      ∫ x in Ioi y, (Real.exp (-L * (x - y)) : ℂ) * g x :=
  setIntegral_congr_fun measurableSet_Ioi fun x hx => by
    rw [k0_of_pos (sub_pos.2 hx)]

theorem setIntegral_Ioi_k1 (L y : ℝ) (g : ℝ → ℂ) :
    ∫ x in Ioi y, (k1 L (x - y) : ℂ) * g x =
      ∫ x in Ioi y, (Real.exp (-L * (x - y)) : ℂ) * g x :=
  setIntegral_congr_fun measurableSet_Ioi fun x hx => by
    rw [k1_of_pos (sub_pos.2 hx)]

theorem setIntegral_Iic_k0 (L y : ℝ) (g : ℝ → ℂ) :
    ∫ x in Iic y, (k0 L (x - y) : ℂ) * g x =
      ∫ x in Iic y, (Real.exp (L * (x - y)) : ℂ) * g x :=
  setIntegral_congr_fun measurableSet_Iic fun x hx => by
    rw [k0_of_nonpos (sub_nonpos.2 hx)]

theorem setIntegral_Iic_k1 (L y : ℝ) (g : ℝ → ℂ) :
    ∫ x in Iic y, (k1 L (x - y) : ℂ) * g x =
      -∫ x in Iic y, (Real.exp (L * (x - y)) : ℂ) * g x := by
  rw [← integral_neg]
  refine setIntegral_congr_fun measurableSet_Iic fun x hx => ?_
  rw [k1_of_nonpos (sub_nonpos.2 hx)]
  push_cast
  ring

/-- `∫ k0(x-y) φ'(x) dx = L ∫ k1(x-y) φ(x) dx` (`k0' = -L k1`). -/
theorem integral_k0_mul_deriv {L : ℝ} (hL : 0 < L) {φ φ' : ℝ → ℂ} (hφ : TestLike φ φ')
    (y : ℝ) :
    ∫ x, (k0 L (x - y) : ℂ) * φ' x = L * ∫ x, (k1 L (x - y) : ℂ) * φ x := by
  rw [← integral_add_compl measurableSet_Ioi (integrable_k0_sub_mul hL.le y hφ.int'),
    ← integral_add_compl measurableSet_Ioi (integrable_k1_sub_mul hL.le y hφ.int), compl_Ioi,
    setIntegral_Ioi_k0, setIntegral_Ioi_k1, setIntegral_Iic_k0, setIntegral_Iic_k1,
    integral_Ioi_exp_mul_deriv hL hφ y, integral_Iic_exp_mul_deriv hL hφ y]
  ring

/-- `∫ k1(x-y) φ'(x) dx = -2 φ(y) + L ∫ k0(x-y) φ(x) dx` (`k1' = -L k0 + 2δ`). -/
theorem integral_k1_mul_deriv {L : ℝ} (hL : 0 < L) {φ φ' : ℝ → ℂ} (hφ : TestLike φ φ')
    (y : ℝ) :
    ∫ x, (k1 L (x - y) : ℂ) * φ' x = -2 * φ y + L * ∫ x, (k0 L (x - y) : ℂ) * φ x := by
  rw [← integral_add_compl measurableSet_Ioi (integrable_k1_sub_mul hL.le y hφ.int'),
    ← integral_add_compl measurableSet_Ioi (integrable_k0_sub_mul hL.le y hφ.int), compl_Ioi,
    setIntegral_Ioi_k0, setIntegral_Ioi_k1, setIntegral_Iic_k0, setIntegral_Iic_k1,
    integral_Ioi_exp_mul_deriv hL hφ y, integral_Iic_exp_mul_deriv hL hφ y]
  ring

end NonUniqueEuler.Sob.EnergyAux
