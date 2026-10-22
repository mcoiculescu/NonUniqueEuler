import NonUniqueEuler.H.Sec4.Sector.GreenKernel
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Helper for `lem:sector`(1): `𝒢_ℓ g` solves the radial Poisson equation

Helper file of `P/Sec4/Sector.lean` (fully proved). Manuscript `04_ring.tex:224-243`.

For a profile `g ∈ L¹([a,b])` vanishing a.e. on `(0,∞) \ [a,b]` (`Prof a b g`), with `0 < a`:
* `Psi a b n g t = ∫_{[a,b]} ker(t,ρ) g(ρ) dρ`, so `𝒢_ℓ g = -(2|ℓ|)⁻¹ Psi` (`green_eq_Psi`);
* `Phi`, `Eps`: the same with `dker`, `eker`.
* Fubini and the kernel FTCs (`H/Sec4/Sector/GreenKernel.lean`) give
  `∫_{a'}^{b'} Phi = Psi(b') - Psi(a')` and `Phi(b') - Phi(a') = ∫_{a'}^{b'} Eps - 2n∫_{a'}^{b'} g`,
  with `Eps = -Phi/t + n² Psi/t²`; `Phi` is continuous on `(0,∞)` (dominated convergence, the
  kernel `dker` is discontinuous only on the diagonal), hence `Psi' = Phi`.
* `isRadialPoissonSol_green`: `𝒢_ℓ g` solves `ψ'' + ψ'/r - ℓ²ψ/r² = g` (integrated form).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.SectorH

open SectorSetting

/-- The hypotheses on a profile: `g ∈ L¹([a,b])` with `0 < a ≤ b`, and `g = 0` a.e. on
`(0, ∞) \ [a,b]`. -/
structure Prof (a b : ℝ) (g : ℝ → ℂ) : Prop where
  pos : 0 < a
  le : a ≤ b
  int : IntegrableOn g (Icc a b)
  supp : ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))), ρ ∉ Icc a b → g ρ = 0

/-- `∫_{[a,b]} ker(t,ρ) g(ρ) dρ`. -/
def Psi (a b : ℝ) (n : ℕ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ ρ in Icc a b, (ker n t ρ : ℂ) * g ρ

/-- `∫_{[a,b]} dker(t,ρ) g(ρ) dρ`. -/
def Phi (a b : ℝ) (n : ℕ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ ρ in Icc a b, (dker n t ρ : ℂ) * g ρ

/-- `∫_{[a,b]} eker(t,ρ) g(ρ) dρ`. -/
def Eps (a b : ℝ) (n : ℕ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ ρ in Icc a b, (eker n t ρ : ℂ) * g ρ

variable {a b : ℝ} {g : ℝ → ℂ}

theorem Prof.pos_of_mem (h : Prof a b g) {ρ : ℝ} (hρ : ρ ∈ Icc a b) : 0 < ρ :=
  h.pos.trans_le hρ.1

theorem Prof.ae_supp (h : Prof a b g) : ∀ᵐ ρ ∂volume, ρ ∈ Ioi (0 : ℝ) → ρ ∉ Icc a b → g ρ = 0 :=
  (ae_restrict_iff' measurableSet_Ioi).1 h.supp

/-- `g` is integrable on every measurable subset of `(0, ∞)`. -/
theorem Prof.integrableOn (h : Prof a b g) {A : Set ℝ} (hA : MeasurableSet A)
    (hA0 : A ⊆ Ioi 0) : IntegrableOn g A := by
  refine (h.int.mono_set (inter_subset_right : A ∩ Icc a b ⊆ Icc a b)).of_ae_sdiff_eq_zero
    hA.nullMeasurableSet ?_
  filter_upwards [h.ae_supp] with x hx hxA
  exact hx (hA0 hxA.1) fun hI => hxA.2 ⟨hxA.1, hI⟩

theorem Prof.intervalIntegrable (h : Prof a b g) {a' b' : ℝ} (ha' : 0 < a') (hb' : 0 < b') :
    IntervalIntegrable g volume a' b' := by
  rw [intervalIntegrable_iff]
  exact h.integrableOn measurableSet_uIoc fun t ht =>
    lt_of_lt_of_le (lt_min ha' hb') (uIoc_subset_uIcc ht).1

/-- A bounded measurable real factor times `g` is integrable on `[a, b]`. -/
theorem Prof.integrable_mul (h : Prof a b g) {F : ℝ → ℝ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ ρ ∈ Icc a b, |F ρ| ≤ M) :
    Integrable (fun ρ => (F ρ : ℂ) * g ρ) (volume.restrict (Icc a b)) := by
  refine h.int.bdd_mul (c := M) (Complex.measurable_ofReal.comp hF).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc fun ρ hρ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hM ρ hρ

theorem Prof.integrable_ker (h : Prof a b g) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ρ => (ker n t ρ : ℂ) * g ρ) (volume.restrict (Icc a b)) :=
  h.integrable_mul (M := b) ((measurable_ker n).comp (measurable_const.prodMk measurable_id))
    fun _ hρ => (abs_ker_le ht (h.pos_of_mem hρ)).trans hρ.2

theorem Prof.integrable_dker (h : Prof a b g) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun ρ => (dker n t ρ : ℂ) * g ρ) (volume.restrict (Icc a b)) :=
  h.integrable_mul (M := n) ((measurable_dker n).comp (measurable_const.prodMk measurable_id))
    fun _ hρ => abs_dker_le ht (h.pos_of_mem hρ)

theorem Prof.integrable_indicator (h : Prof a b g) (s : Set ℝ) (hs : MeasurableSet s) :
    Integrable (fun ρ => ((s.indicator (fun _ => (1 : ℝ)) ρ : ℝ) : ℂ) * g ρ)
      (volume.restrict (Icc a b)) :=
  h.integrable_mul (M := 1) (measurable_const.indicator hs) fun ρ _ => by
    by_cases hρ : ρ ∈ s <;> simp [hρ]

/-! ### Fubini -/

/-- Fubini for a bounded measurable kernel on `[a', b'] × [a, b]`. -/
theorem Prof.fubini (h : Prof a b g) {K : ℝ → ℝ → ℝ}
    (hK : Measurable fun p : ℝ × ℝ => K p.1 p.2) {a' b' M : ℝ}
    (hM : ∀ t ∈ uIoc a' b', ∀ ρ ∈ Icc a b, |K t ρ| ≤ M) :
    ∫ t in a'..b', ∫ ρ in Icc a b, (K t ρ : ℂ) * g ρ =
      ∫ ρ in Icc a b, ((∫ t in a'..b', K t ρ : ℝ) : ℂ) * g ρ := by
  have : IsFiniteMeasure (volume.restrict (uIoc a' b')) :=
    isFiniteMeasure_restrict.2 ((measure_mono uIoc_subset_uIcc).trans_lt measure_Icc_lt_top).ne
  have hbound : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * (M * ‖g z.2‖))
      ((volume.restrict (uIoc a' b')).prod (volume.restrict (Icc a b))) :=
    (integrable_const (1 : ℝ)).mul_prod (h.int.norm.const_mul M)
  have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => (K z.1 z.2 : ℂ) * g z.2)
      ((volume.restrict (uIoc a' b')).prod (volume.restrict (Icc a b))) :=
    (Complex.measurable_ofReal.comp hK).aestronglyMeasurable.mul h.int.aestronglyMeasurable.comp_snd
  have hae : ∀ᵐ z ∂((volume.restrict (uIoc a' b')).prod (volume.restrict (Icc a b))),
      ‖(K z.1 z.2 : ℂ) * g z.2‖ ≤ (1 : ℝ) * (M * ‖g z.2‖) := by
    rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (measurableSet_uIoc.prod measurableSet_Icc) fun z hz => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact mul_le_mul_of_nonneg_right (hM z.1 hz.1 z.2 hz.2) (norm_nonneg _)
  have hint : Integrable (Function.uncurry fun t ρ => (K t ρ : ℂ) * g ρ)
      ((volume.restrict (uIoc a' b')).prod (volume.restrict (Icc a b))) :=
    hbound.mono' hmeas hae
  rw [intervalIntegral_integral_swap hint]
  congr 1
  funext ρ
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]

/-! ### `Psi' = Phi` -/

theorem Prof.integral_Phi (h : Prof a b g) (n : ℕ) {a' b' : ℝ} (ha' : 0 < a') (hab : a' ≤ b') :
    ∫ t in a'..b', Phi a b n g t = Psi a b n g b' - Psi a b n g a' := by
  have hb' : 0 < b' := ha'.trans_le hab
  simp only [Phi]
  rw [h.fubini (measurable_dker n) (M := n) fun t ht ρ hρ =>
    abs_dker_le (lt_of_lt_of_le (lt_min ha' hb') (uIoc_subset_uIcc ht).1) (h.pos_of_mem hρ)]
  have hcongr : ∫ ρ in Icc a b, ((∫ t in a'..b', dker n t ρ : ℝ) : ℂ) * g ρ =
      ∫ ρ in Icc a b, ((ker n b' ρ : ℂ) * g ρ - (ker n a' ρ : ℂ) * g ρ) := by
    refine setIntegral_congr_fun measurableSet_Icc fun ρ hρ => ?_
    rw [integral_dker n (h.pos_of_mem hρ) ha' hab]
    push_cast
    ring
  rw [hcongr, integral_sub (h.integrable_ker n hb'.le) (h.integrable_ker n ha'.le)]
  rfl

theorem Prof.continuousOn_Phi (h : Prof a b g) (n : ℕ) : ContinuousOn (Phi a b n g) (Ioi 0) := by
  intro t₀ ht₀
  refine ContinuousAt.continuousWithinAt ?_
  refine continuousAt_of_dominated (bound := fun ρ => n * ‖g ρ‖) ?_ ?_
    (h.int.norm.const_mul _) ?_
  · exact Eventually.of_forall fun t => (Complex.measurable_ofReal.comp ((measurable_dker n).comp
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable.mul h.int.aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds ht₀] with t ht
    refine ae_restrict_of_forall_mem measurableSet_Icc fun ρ hρ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_dker_le ht (h.pos_of_mem hρ)) (norm_nonneg _)
  · have hne : ∀ᵐ ρ ∂(volume.restrict (Icc a b)), ρ ≠ t₀ := ae_restrict_of_ae (ae_ne_point t₀)
    filter_upwards [hne] with ρ hρ
    exact (Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_dker n ht₀ (Ne.symm hρ))).mul continuousAt_const

theorem Prof.continuousOn_Psi (h : Prof a b g) (n : ℕ) : ContinuousOn (Psi a b n g) (Ici 0) := by
  refine continuousOn_of_dominated (bound := fun ρ => b * ‖g ρ‖) (fun t _ =>
    ((Complex.measurable_ofReal.comp ((measurable_ker n).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable.mul
        h.int.aestronglyMeasurable)) ?_ (h.int.norm.const_mul _) ?_
  · intro t ht
    refine ae_restrict_of_forall_mem measurableSet_Icc fun ρ hρ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((abs_ker_le ht (h.pos_of_mem hρ)).trans hρ.2)
      (norm_nonneg _)
  · refine ae_restrict_of_forall_mem measurableSet_Icc fun ρ hρ => ?_
    exact ((Complex.continuous_ofReal.comp (continuous_ker n (h.pos_of_mem hρ))).mul
      continuous_const).continuousOn

theorem Prof.hasDerivAt_Psi (h : Prof a b g) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (Psi a b n g) (Phi a b n g t) t := by
  have hcont := h.continuousOn_Phi n
  have hF : HasDerivAt (fun s => Psi a b n g t + ∫ u in t..s, Phi a b n g u)
      (Phi a b n g t) t :=
    (intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      (hcont.stronglyMeasurableAtFilter isOpen_Ioi t ht)
      (hcont.continuousAt (Ioi_mem_nhds ht))).const_add _
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  rcases le_total t s with hts | hst
  · rw [h.integral_Phi n ht hts]
    ring
  · rw [intervalIntegral.integral_symm, h.integral_Phi n hs hst]
    ring

/-! ### `Phi' = Eps - 2n g` in integrated form -/

theorem Prof.integral_indicator (h : Prof a b g) {a' b' : ℝ} (ha' : 0 < a') (hab : a' ≤ b') :
    ∫ ρ in Icc a b, (((Ioc a' b').indicator (fun _ => (1 : ℝ)) ρ : ℝ) : ℂ) * g ρ =
      ∫ t in a'..b', g t := by
  have h1 : ∀ ρ, (((Ioc a' b').indicator (fun _ => (1 : ℝ)) ρ : ℝ) : ℂ) * g ρ =
      (Ioc a' b').indicator g ρ := by
    intro ρ
    by_cases hρ : ρ ∈ Ioc a' b' <;> simp [hρ]
  simp_rw [h1]
  rw [setIntegral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hab]
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioc.nullMeasurableSet
    (inter_subset_left : Ioc a' b' ∩ Icc a b ⊆ Ioc a' b'), inter_comm]
  filter_upwards [h.ae_supp] with x hx hxA
  exact hx (ha'.trans hxA.1.1) fun hI => hxA.2 ⟨hxA.1, hI⟩

theorem Prof.Eps_eq (h : Prof a b g) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Eps a b n g t = -(Phi a b n g t / t) + (n : ℂ) ^ 2 * Psi a b n g t / (t : ℂ) ^ 2 := by
  have hpt : ∀ ρ, (eker n t ρ : ℂ) * g ρ =
      -(1 / (t : ℂ)) * ((dker n t ρ : ℂ) * g ρ) + (n : ℂ) ^ 2 / (t : ℂ) ^ 2 * ((ker n t ρ : ℂ) * g ρ) := by
    intro ρ
    simp only [eker]
    push_cast
    ring
  simp only [Eps, hpt]
  rw [integral_add ((h.integrable_dker n ht).const_mul _) ((h.integrable_ker n ht.le).const_mul _),
    integral_const_mul, integral_const_mul]
  simp only [Phi, Psi]
  ring

theorem Prof.Phi_sub (h : Prof a b g) (n : ℕ) {a' b' : ℝ} (ha' : 0 < a') (hab : a' ≤ b') :
    Phi a b n g b' - Phi a b n g a' =
      (∫ t in a'..b', Eps a b n g t) - 2 * n * ∫ t in a'..b', g t := by
  have hb' : 0 < b' := ha'.trans_le hab
  have hE : ∫ t in a'..b', Eps a b n g t =
      ∫ ρ in Icc a b, ((∫ t in a'..b', eker n t ρ : ℝ) : ℂ) * g ρ := by
    simp only [Eps]
    exact h.fubini (measurable_eker n) (M := n / a' + (n : ℝ) ^ 2 * b / a' ^ 2)
      fun t ht ρ hρ => (abs_eker_le ha' (by rw [uIoc_of_le hab] at ht; exact ht.1.le)
        (h.pos_of_mem hρ)).trans (by gcongr; exact hρ.2)
  have hcongr : ∫ ρ in Icc a b, ((∫ t in a'..b', eker n t ρ : ℝ) : ℂ) * g ρ =
      ∫ ρ in Icc a b, (((dker n b' ρ : ℂ) * g ρ - (dker n a' ρ : ℂ) * g ρ) +
        2 * n * ((((Ioc a' b').indicator (fun _ => (1 : ℝ)) ρ : ℝ) : ℂ) * g ρ)) := by
    refine setIntegral_congr_fun measurableSet_Icc fun ρ hρ => ?_
    have := dker_sub_dker n (h.pos_of_mem hρ) ha' hab
    have e : (∫ t in a'..b', eker n t ρ) = dker n b' ρ - dker n a' ρ +
        2 * n * (Ioc a' b').indicator (fun _ => (1 : ℝ)) ρ := by linarith
    rw [e]
    push_cast
    ring
  have i1 : Integrable (fun ρ => (dker n b' ρ : ℂ) * g ρ - (dker n a' ρ : ℂ) * g ρ)
      (volume.restrict (Icc a b)) := (h.integrable_dker n hb').sub (h.integrable_dker n ha')
  have i2 : Integrable (fun ρ => 2 * (n : ℂ) *
      ((((Ioc a' b').indicator (fun _ => (1 : ℝ)) ρ : ℝ) : ℂ) * g ρ))
      (volume.restrict (Icc a b)) := (h.integrable_indicator _ measurableSet_Ioc).const_mul _
  rw [hE, hcongr, integral_add i1 i2,
    integral_sub (h.integrable_dker n hb') (h.integrable_dker n ha'), integral_const_mul,
    h.integral_indicator ha' hab]
  simp only [Phi]
  ring

/-! ### The Green operator -/

theorem natAbs_cast (ℓ : ℤ) : ((ℓ.natAbs : ℕ) : ℝ) = |(ℓ : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem green_eq_Psi (h : Prof a b g) (ℓ : ℤ) (t : ℝ) :
    green ℓ g t = -(((2 * |(ℓ : ℝ)|)⁻¹ : ℝ) : ℂ) * Psi a b ℓ.natAbs g t := by
  simp only [green, Psi]
  congr 1
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
    (fun ρ hρ => h.pos.trans_le hρ.1 : Icc a b ⊆ Ioi 0)]
  · refine setIntegral_congr_fun measurableSet_Icc fun ρ _ => ?_
    simp only [ker]
    push_cast
    ring
  · filter_upwards [h.ae_supp] with x hx hxA
    rw [hx hxA.1 hxA.2, mul_zero, zero_mul]

/-- `𝒢_ℓ g` solves the radial Poisson equation (integrated form). -/
theorem isRadialPoissonSol_green (h : Prof a b g) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    IsRadialPoissonSol ℓ g (green ℓ g) := by
  set n := ℓ.natAbs with hn
  set c : ℂ := (((2 * |(ℓ : ℝ)|)⁻¹ : ℝ) : ℂ) with hc
  have hn0 : (n : ℝ) ≠ 0 := by rw [hn]; exact_mod_cast Int.natAbs_ne_zero.2 hℓ
  have hn0' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have h2nc : 2 * (n : ℂ) * c = 1 := by
    rw [hc, ← natAbs_cast ℓ, ← hn]
    push_cast
    field_simp
  have hℓsq : (ℓ : ℂ) ^ 2 = (n : ℂ) ^ 2 := by
    have h2 := congrArg (fun z : ℤ => (z : ℂ)) (Int.natAbs_sq ℓ)
    simp only [Int.cast_pow, Int.cast_natCast] at h2
    rw [hn]
    exact h2.symm
  have hG : green ℓ g = fun t => -c * Psi a b n g t := funext (green_eq_Psi h ℓ)
  refine ⟨fun t => -c * Phi a b n g t, fun t ht => ?_, ?_, ?_⟩
  · rw [hG]
    exact (h.hasDerivAt_Psi n ht).const_mul (-c)
  · exact continuousOn_const.mul (h.continuousOn_Phi n)
  · -- the identity for `a' ≤ b'`, then by symmetry
    have key : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' →
        -c * Phi a b n g b' - -c * Phi a b n g a' =
          ∫ r in a'..b', (g r - -c * Phi a b n g r / (r : ℂ) +
            (ℓ : ℂ) ^ 2 * green ℓ g r / (r : ℂ) ^ 2) := by
      intro a' b' ha' hab
      have hb' : 0 < b' := ha'.trans_le hab
      have hcont : ContinuousOn (fun r : ℝ => -(-c * Phi a b n g r / (r : ℂ)) +
          (ℓ : ℂ) ^ 2 * green ℓ g r / (r : ℂ) ^ 2) (uIcc a' b') := by
        have hsub : uIcc a' b' ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le (lt_min ha' hb') hr.1
        have hP : ContinuousOn (Phi a b n g) (uIcc a' b') := (h.continuousOn_Phi n).mono hsub
        have hQ : ContinuousOn (Psi a b n g) (uIcc a' b') :=
          (h.continuousOn_Psi n).mono fun r hr => mem_Ici.2 (le_of_lt (hsub hr))
        have hr0 : ∀ r ∈ uIcc a' b', (r : ℂ) ≠ 0 := fun r hr => by
          exact_mod_cast (ne_of_gt (hsub hr))
        rw [hG]
        refine ContinuousOn.add (ContinuousOn.neg (ContinuousOn.div (continuousOn_const.mul hP)
          (Complex.continuous_ofReal.continuousOn) hr0)) (ContinuousOn.div
          (continuousOn_const.mul (continuousOn_const.mul hQ))
          (Complex.continuous_ofReal.continuousOn.pow 2) fun r hr => pow_ne_zero 2 (hr0 r hr))
      have hsplit : ∫ r in a'..b', (g r - -c * Phi a b n g r / (r : ℂ) +
            (ℓ : ℂ) ^ 2 * green ℓ g r / (r : ℂ) ^ 2) =
          (∫ r in a'..b', g r) + ∫ r in a'..b', (-(-c * Phi a b n g r / (r : ℂ)) +
            (ℓ : ℂ) ^ 2 * green ℓ g r / (r : ℂ) ^ 2) := by
        rw [← intervalIntegral.integral_add (h.intervalIntegrable ha' hb')
          (hcont.intervalIntegrable)]
        congr 1
        funext r
        ring
      have hcongr : ∫ r in a'..b', (-(-c * Phi a b n g r / (r : ℂ)) +
            (ℓ : ℂ) ^ 2 * green ℓ g r / (r : ℂ) ^ 2) =
          ∫ r in a'..b', -c * Eps a b n g r := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        have hr0 : 0 < r := lt_of_lt_of_le (lt_min ha' hb') hr.1
        rw [h.Eps_eq n hr0, hG, hℓsq]
        ring
      rw [hsplit, hcongr, intervalIntegral.integral_const_mul]
      have hPhi := h.Phi_sub n ha' hab
      linear_combination (-c) * hPhi + (∫ r in a'..b', g r) * h2nc
    intro a' b' ha' hb'
    rcases le_total a' b' with hab | hba
    · exact key a' b' ha' hab
    · rw [intervalIntegral.integral_symm, ← key b' a' hb' hba]
      ring

end NonUniqueEuler.SectorH
