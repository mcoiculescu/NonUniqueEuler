import NonUniqueEuler.H.Sec3.Transport.Basic
import NonUniqueEuler.I.Sec3.Dbr
import NonUniqueEuler.I.Sec3.CutoffGrad
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Helper for `P/Sec3/Transport`: conservation (`lem:transport`(ii))

`03_compactness.tex:526-543`. Let `β ∈ Lip₀` with `|β(s)| ≤ L|s|`, and assume `β(u)` satisfies
`(te)` on `[t₀,T)` with datum `β(u₀)`. For `α ∈ C_c^∞((-∞,T))` test with
`φ_n(t,x) = α(t) ς_{R_n}(x)`, `R_n = n + 1` (`isTestFunction_mul`):
`∂_tφ_n = α' ς_{R_n}`, `w·∇φ_n = α ∇ς_{R_n}·w`, so `(te)` reads
`∫_S β(u) α' ς_{R_n} + ∫_S β(u) α ∇ς_{R_n}·w + ∫ β(u₀) α(t₀) ς_{R_n} = 0`, `S = (t₀,T)×ℝ²`.
* `∫_S β(u) α' ς_{R_n} → ∫_S β(u) α'` (dominated by `L ‖α'‖_∞ |u|`, `u ∈ L¹(S)`);
* `|β(u) α ∇ς_{R_n}·w| ≤ L ‖α‖_∞ ‖∇ς‖_∞ R_n⁻¹ |uw|`, so the flux term tends to `0`
  (`uw ∈ L¹(S)`);
* the datum term tends to `α(t₀) ∫ β(u₀)`.
Hence `∫_{t₀}^T α' B + α(t₀) b₀ = 0` with `B(t) = ∫ β(u(t))`, `b₀ = ∫ β(u₀)`
(`identity_timeTest`). `B` is measurable and bounded by `L M₁`, and `lem:dbr` gives `B = b₀`
a.e. on `(t₀,T)` (`conservation_of_solvesTE`).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Weak.TransportH

/-! ### Derivatives of `α(t) ψ(x)` -/

theorem timeDeriv_mul_test {α : ℝ → ℝ} (hα : Differentiable ℝ α) (ψ : ℂ → ℝ) (t : ℝ) (x : ℂ) :
    timeDeriv (fun p : ℝ × ℂ => α p.1 * ψ p.2) t x = deriv α t * ψ x := by
  simp only [timeDeriv]
  exact deriv_mul_const (hα t) _

theorem spaceDeriv_mul_test (α : ℝ → ℝ) {ψ : ℂ → ℝ} (hψ : Differentiable ℝ ψ) (t : ℝ)
    (x v : ℂ) :
    spaceDeriv (fun p : ℝ × ℂ => α p.1 * ψ p.2) t x v = α t * fderiv ℝ ψ x v := by
  simp only [spaceDeriv]
  rw [fderiv_const_mul (hψ x)]
  rfl

theorem exists_bound_of_isTimeTestFn {T : ℝ} {α : ℝ → ℝ} (hα : IsTimeTestFn T α) :
    (∃ A : ℝ, 0 ≤ A ∧ ∀ t, |α t| ≤ A) ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ t, |deriv α t| ≤ A := by
  constructor
  · obtain ⟨A, hA⟩ := hα.contDiff.continuous.bounded_above_of_compact_support
      hα.hasCompactSupport
    exact ⟨A, (norm_nonneg _).trans (hA 0), fun t => by rw [← Real.norm_eq_abs]; exact hA t⟩
  · obtain ⟨A, hA⟩ := (hα.contDiff.continuous_deriv (by simp)).bounded_above_of_compact_support
      hα.hasCompactSupport.deriv
    exact ⟨A, (norm_nonneg _).trans (hA 0), fun t => by rw [← Real.norm_eq_abs]; exact hA t⟩

/-- Dominated convergence for `|c_n| ≤ K/(n+1)`, `K` integrable: `∫ c_n → 0`. -/
theorem tendsto_integral_of_le_div {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {c : ℕ → X → ℝ} {K : X → ℝ} (hK : Integrable K μ)
    (hm : ∀ n, AEStronglyMeasurable (c n) μ)
    (hb : ∀ n p, ‖c n p‖ ≤ K p * (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => ∫ p, c n p ∂μ) atTop (𝓝 0) := by
  have hK0 : ∀ p, 0 ≤ K p := fun p => by
    have := (norm_nonneg _).trans (hb 0 p)
    simpa using this
  have hb' : ∀ n p, ‖c n p‖ ≤ K p := fun n p => by
    refine (hb n p).trans ?_
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    calc K p * (1 / ((n : ℝ) + 1)) ≤ K p * 1 := mul_le_mul_of_nonneg_left h1 (hK0 p)
      _ = K p := mul_one _
  have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ)) K hm hK
    (fun n => Eventually.of_forall (hb' n)) (Eventually.of_forall fun p => by
      refine squeeze_zero_norm (fun n => hb n p) ?_
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (K p)
      rw [mul_zero] at h
      exact h)
  simpa using h

/-! ### The identity for time test functions -/

section Identity

variable {T t₀ : ℝ} {w : ℝ → ℂ → ℂ} {u : ℝ → ℂ → ℝ} {u₀ : ℂ → ℝ}

/-- `ς_{R_n}(x) = 1` for all large `n`. -/
theorem eventually_sigmaCutR_eq_one (x : ℂ) :
    ∀ᶠ n : ℕ in atTop, sigmaCutR ((n : ℝ) + 1) x = 1 := by
  refine eventually_atTop.2 ⟨⌈‖x‖⌉₊, fun n hn => sigmaCutR_eq_one (by positivity) ?_⟩
  have h1 : ‖x‖ ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  linarith

/-- `(te)` for `β(u)` tested with `α(t) ς_R(x)`, `R → ∞`, gives
`∫_{t₀}^T α' ∫β(u(t)) + α(t₀) ∫β(u₀) = 0` (`03_compactness.tex:528-540`). -/
theorem identity_timeTest (ht₀ : t₀ ∈ Ico 0 T) (hw : IsBddH1DivFreeField (Ioo 0 T) w)
    (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    (hu₀1 : MemLp u₀ 1 volume) {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β)
    (hren : SolvesTE t₀ T (fun t x => β (u t x)) w (fun x => β (u₀ x)))
    {α : ℝ → ℝ} (hα : IsTimeTestFn T α) :
    (∫ t in Ioo t₀ T, deriv α t * ∫ x, β (u t x)) + α t₀ * ∫ x, β (u₀ x) = 0 := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_le_of_isLipO hβ
  have hβc := continuous_of_isLipO hβ
  have hαd : Differentiable ℝ α := hα.contDiff.differentiable (by simp)
  have hαc : Continuous α := hα.contDiff.continuous
  have hα'c : Continuous (deriv α) := hα.contDiff.continuous_deriv (by simp)
  obtain ⟨⟨A₀, hA₀0, hA₀⟩, ⟨A₁, hA₁0, hA₁⟩⟩ := exists_bound_of_isTimeTestFn hα
  obtain ⟨-, hG0⟩ := bddAbove_norm_fderiv_sigmaCut
  set G : ℝ := Smooth.gradSup sigmaCut with hGdef
  have hRpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hς : ∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sigmaCutR ((n : ℝ) + 1)) :=
    fun n => contDiff_sigmaCutR _
  have hςd : ∀ n : ℕ, Differentiable ℝ (sigmaCutR ((n : ℝ) + 1)) :=
    fun n => (hς n).differentiable (by simp)
  have hφ : ∀ n : ℕ, IsTestFunction T (fun p : ℝ × ℂ => α p.1 * sigmaCutR ((n : ℝ) + 1) p.2) :=
    fun n => isTestFunction_mul hα (hς n) (hasCompactSupport_sigmaCutR (hRpos n))
  -- measurability and integrability on the slab
  have hum : AEStronglyMeasurable (Function.uncurry u) (volume.restrict (slabFrom t₀ T)) :=
    hu1.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono (slabFrom_subset_prod ht₀.1) le_rfl)
  have hbu : AEStronglyMeasurable (fun p : ℝ × ℂ => β (u p.1 p.2))
      (volume.restrict (slabFrom t₀ T)) := hβc.comp_aestronglyMeasurable hum
  have hwm := aestronglyMeasurable_w_slabFrom ht₀.1 hw
  have huI : IntegrableOn (Function.uncurry u) (slabFrom t₀ T) :=
    integrableOn_slabFrom_of_memLinfLp_one ht₀.1 hu1
  have huwI : IntegrableOn (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (slabFrom t₀ T) :=
    IntegrableOn.mono_set (t := slab T) huw (slabFrom_subset_slab ht₀.1)
  -- the three families
  set a : ℕ → ℝ × ℂ → ℝ := fun n p =>
    β (u p.1 p.2) * deriv α p.1 * sigmaCutR ((n : ℝ) + 1) p.2 with ha_def
  set c : ℕ → ℝ × ℂ → ℝ := fun n p =>
    β (u p.1 p.2) * α p.1 * fderiv ℝ (sigmaCutR ((n : ℝ) + 1)) p.2 (w p.1 p.2) with hc_def
  set a' : ℝ × ℂ → ℝ := fun p => β (u p.1 p.2) * deriv α p.1 with ha'_def
  have hTI : ∀ n : ℕ, transportIntegrand (fun t x => β (u t x)) w
      (fun p : ℝ × ℂ => α p.1 * sigmaCutR ((n : ℝ) + 1) p.2) = fun p => a n p + c n p := by
    intro n
    funext p
    simp only [transportIntegrand, timeDeriv_mul_test hαd, spaceDeriv_mul_test _ (hςd n), ha_def,
      hc_def]
    ring
  -- bounds
  have ha_bd : ∀ n : ℕ, ∀ p : ℝ × ℂ, ‖a n p‖ ≤ L * A₁ * ‖Function.uncurry u p‖ := by
    intro n p
    simp only [ha_def, Real.norm_eq_abs, abs_mul]
    have h1 := hL (u p.1 p.2)
    have h2 := hA₁ p.1
    have h3 : |sigmaCutR ((n : ℝ) + 1) p.2| ≤ 1 := by
      rw [abs_of_nonneg (sigmaCutR_nonneg _ _)]; exact sigmaCutR_le_one _ _
    calc |β (u p.1 p.2)| * |deriv α p.1| * |sigmaCutR ((n : ℝ) + 1) p.2|
        ≤ (L * |u p.1 p.2|) * A₁ * 1 := by gcongr
      _ = L * A₁ * |u p.1 p.2| := by ring
  have hc_bd : ∀ n : ℕ, ∀ p : ℝ × ℂ,
      ‖c n p‖ ≤ L * A₀ * G * ‖u p.1 p.2 • w p.1 p.2‖ * (1 / ((n : ℝ) + 1)) := by
    intro n p
    simp only [hc_def, Real.norm_eq_abs, abs_mul, norm_smul]
    have h1 := hL (u p.1 p.2)
    have h2 := hA₀ p.1
    have h3 : |fderiv ℝ (sigmaCutR ((n : ℝ) + 1)) p.2 (w p.1 p.2)| ≤
        G / ((n : ℝ) + 1) * ‖w p.1 p.2‖ := by
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ _ p.2).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_sigmaCutR_le (hRpos n) p.2) (norm_nonneg _))
    calc |β (u p.1 p.2)| * |α p.1| * |fderiv ℝ (sigmaCutR ((n : ℝ) + 1)) p.2 (w p.1 p.2)|
        ≤ (L * |u p.1 p.2|) * A₀ * (G / ((n : ℝ) + 1) * ‖w p.1 p.2‖) := by gcongr
      _ = L * A₀ * G * (|u p.1 p.2| * ‖w p.1 p.2‖) * (1 / ((n : ℝ) + 1)) := by ring
  have hc_bd' : ∀ n : ℕ, ∀ p : ℝ × ℂ, ‖c n p‖ ≤ L * A₀ * G * ‖u p.1 p.2 • w p.1 p.2‖ := by
    intro n p
    refine (hc_bd n p).trans ?_
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (hRpos n)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have h0 : 0 ≤ L * A₀ * G * ‖u p.1 p.2 • w p.1 p.2‖ := by positivity
    calc L * A₀ * G * ‖u p.1 p.2 • w p.1 p.2‖ * (1 / ((n : ℝ) + 1))
        ≤ L * A₀ * G * ‖u p.1 p.2 • w p.1 p.2‖ * 1 := mul_le_mul_of_nonneg_left h1 h0
      _ = _ := mul_one _
  -- measurability
  have ha_m : ∀ n : ℕ, AEStronglyMeasurable (a n) (volume.restrict (slabFrom t₀ T)) := by
    intro n
    exact (hbu.mul (hα'c.comp continuous_fst).aestronglyMeasurable).mul
      ((hς n).continuous.comp continuous_snd).aestronglyMeasurable
  have hc_m : ∀ n : ℕ, AEStronglyMeasurable (c n) (volume.restrict (slabFrom t₀ T)) := by
    intro n
    have hfd : Continuous fun p : ℝ × ℂ => fderiv ℝ (sigmaCutR ((n : ℝ) + 1)) p.2 :=
      ((hς n).continuous_fderiv (by simp)).comp continuous_snd
    have hsd : AEStronglyMeasurable
        (fun p : ℝ × ℂ => fderiv ℝ (sigmaCutR ((n : ℝ) + 1)) p.2 (w p.1 p.2))
        (volume.restrict (slabFrom t₀ T)) :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
        hfd.aestronglyMeasurable hwm
    exact (hbu.mul (hαc.comp continuous_fst).aestronglyMeasurable).mul hsd
  have ha_int : ∀ n : ℕ, IntegrableOn (a n) (slabFrom t₀ T) := fun n =>
    (huI.norm.const_mul (L * A₁)).mono' (ha_m n) (Eventually.of_forall (ha_bd n))
  have hc_int : ∀ n : ℕ, IntegrableOn (c n) (slabFrom t₀ T) := fun n =>
    (huwI.norm.const_mul (L * A₀ * G)).mono' (hc_m n) (Eventually.of_forall (hc_bd' n))
  have ha'_int : IntegrableOn a' (slabFrom t₀ T) := by
    refine (huI.norm.const_mul (L * A₁)).mono'
      (hbu.mul (hα'c.comp continuous_fst).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    simp only [ha'_def, Real.norm_eq_abs, abs_mul]
    calc |β (u p.1 p.2)| * |deriv α p.1| ≤ (L * |u p.1 p.2|) * A₁ :=
          mul_le_mul (hL _) (hA₁ _) (abs_nonneg _) (by positivity)
      _ = L * A₁ * |u p.1 p.2| := by ring
  -- the limits
  have hlim_a : Tendsto (fun n : ℕ => ∫ p in slabFrom t₀ T, a n p) atTop
      (𝓝 (∫ p in slabFrom t₀ T, a' p)) := by
    refine tendsto_integral_of_dominated_convergence (fun p => L * A₁ * ‖Function.uncurry u p‖)
      ha_m (huI.norm.const_mul _) (fun n => Eventually.of_forall (ha_bd n))
      (Eventually.of_forall fun p => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_sigmaCutR_eq_one p.2] with n hn
    simp only [ha_def, ha'_def, hn, mul_one]
  have hlim_c : Tendsto (fun n : ℕ => ∫ p in slabFrom t₀ T, c n p) atTop (𝓝 0) :=
    tendsto_integral_of_le_div (huwI.norm.const_mul (L * A₀ * G)) hc_m hc_bd
  have hlim_d : Tendsto (fun n : ℕ => ∫ x, β (u₀ x) * (α t₀ * sigmaCutR ((n : ℝ) + 1) x)) atTop
      (𝓝 (∫ x, β (u₀ x) * α t₀)) := by
    have hu₀I : Integrable u₀ := memLp_one_iff_integrable.1 hu₀1
    have hbu₀ : AEStronglyMeasurable (fun x => β (u₀ x)) volume :=
      hβc.comp_aestronglyMeasurable hu₀1.aestronglyMeasurable
    refine tendsto_integral_of_dominated_convergence (fun x => L * A₀ * ‖u₀ x‖)
      (fun n => hbu₀.mul (aestronglyMeasurable_const.mul
        ((hς n).continuous.aestronglyMeasurable))) (hu₀I.norm.const_mul _)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · simp only [Real.norm_eq_abs, abs_mul]
      have h3 : |sigmaCutR ((n : ℝ) + 1) x| ≤ 1 := by
        rw [abs_of_nonneg (sigmaCutR_nonneg _ _)]; exact sigmaCutR_le_one _ _
      calc |β (u₀ x)| * (|α t₀| * |sigmaCutR ((n : ℝ) + 1) x|)
          ≤ (L * |u₀ x|) * (A₀ * 1) := by gcongr; exact hL _; exact hA₀ _
        _ = L * A₀ * |u₀ x| := by ring
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_sigmaCutR_eq_one x] with n hn
      simp only [hn, mul_one]
  -- the identity for each `n`
  have hid : ∀ n : ℕ, (∫ p in slabFrom t₀ T, a n p) + (∫ p in slabFrom t₀ T, c n p) +
      ∫ x, β (u₀ x) * (α t₀ * sigmaCutR ((n : ℝ) + 1) x) = 0 := by
    intro n
    have h := hren.identity _ (hφ n)
    rw [integral_Ioo_integral_eq (hren.integrableOn _ (hφ n)), hTI n,
      integral_add (ha_int n) (hc_int n)] at h
    exact h
  have hlim := (hlim_a.add hlim_c).add hlim_d
  have heq : (∫ p in slabFrom t₀ T, a' p) + 0 + ∫ x, β (u₀ x) * α t₀ = 0 :=
    tendsto_nhds_unique hlim (by simp_rw [hid]; exact tendsto_const_nhds)
  rw [← integral_Ioo_integral_eq ha'_int] at heq
  have e1 : ∀ t : ℝ, ∫ x : ℂ, a' (t, x) = deriv α t * ∫ x, β (u t x) := by
    intro t
    simp only [ha'_def]
    rw [integral_mul_const, mul_comm]
  have e2 : ∫ x, β (u₀ x) * α t₀ = α t₀ * ∫ x, β (u₀ x) := by
    rw [integral_mul_const, mul_comm]
  simp_rw [e1] at heq
  rw [e2] at heq
  linarith

end Identity

/-- `lem:transport`(ii) from `lem:transport`(i) (`03_compactness.tex:526-543`): if `β ∈ Lip₀`
and `β(u)` satisfies `(te)` on `[t₀,T)` with datum `β(u₀)`, then `β(u(t))` is integrable and
`∫ β(u(t)) = ∫ β(u₀)` for a.e. `t ∈ (t₀,T)`. -/
theorem conservation_of_solvesTE {T t₀ : ℝ} (ht₀ : t₀ ∈ Ico 0 T) {w : ℝ → ℂ → ℂ}
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) {u : ℝ → ℂ → ℝ} {u₀ : ℂ → ℝ}
    (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    (hu₀1 : MemLp u₀ 1 volume) {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β)
    (hren : SolvesTE t₀ T (fun t x => β (u t x)) w (fun x => β (u₀ x))) :
    ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)),
      Integrable (fun x => β (u t x)) volume ∧ ∫ x, β (u t x) = ∫ x, β (u₀ x) := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_le_of_isLipO hβ
  have hβc := continuous_of_isLipO hβ
  obtain ⟨M₁, hM₁⟩ := hu1.essBounded
  have hgood : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)),
      MemLp (u t) 1 volume ∧ (eLpNorm (u t) 1 volume).toReal ≤ M₁ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left ht₀.1) hM₁]
      with t ht
    rw [Measure.restrict_univ] at ht
    exact ht
  have hint : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), Integrable (fun x => β (u t x)) volume := by
    filter_upwards [hgood] with t ht
    refine ((memLp_one_iff_integrable.1 ht.1).norm.const_mul L).mono'
      (hβc.comp_aestronglyMeasurable ht.1.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact hL _
  -- `B(t) = ∫ β(u(t))` is measurable and bounded
  have hum : AEStronglyMeasurable (Function.uncurry u) (volume.restrict (slabFrom t₀ T)) :=
    hu1.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono (slabFrom_subset_prod ht₀.1) le_rfl)
  have hbu : AEStronglyMeasurable (fun p : ℝ × ℂ => β (u p.1 p.2))
      ((volume.restrict (Ioo t₀ T)).prod (volume : Measure ℂ)) := by
    rw [← restrict_slabFrom_eq_prod]; exact hβc.comp_aestronglyMeasurable hum
  have hBm : AEStronglyMeasurable (fun t => ∫ x, β (u t x)) (volume.restrict (Ioo t₀ T)) :=
    hbu.integral_prod_right'
  have hBb : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ‖∫ x, β (u t x)‖ ≤ L * M₁ := by
    filter_upwards [hgood] with t ht
    have hI : Integrable (fun x => L * ‖u t x‖) :=
      (memLp_one_iff_integrable.1 ht.1).norm.const_mul L
    refine (norm_integral_le_of_norm_le hI (Eventually.of_forall fun x => ?_)).trans ?_
    · rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact hL _
    · rw [integral_const_mul, integral_norm_eq_lintegral_enorm ht.1.aestronglyMeasurable,
        ← eLpNorm_one_eq_lintegral_enorm]
      exact mul_le_mul_of_nonneg_left ht.2 hL0
  have hB : MemLp (fun t => ∫ x, β (u t x)) ⊤ (volume.restrict (Ioo t₀ T)) :=
    memLp_top_of_bound hBm (L * M₁) hBb
  have hdbr := duBoisReymond ht₀.2 hB fun α hα =>
    identity_timeTest ht₀ hw hu1 huw hu₀1 hβ hren hα
  filter_upwards [hdbr, hint] with t ht hti
  exact ⟨hti, ht⟩

end NonUniqueEuler.Weak.TransportH
