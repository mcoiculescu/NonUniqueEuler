import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec6.Adm
import NonUniqueEuler.I.Sec6.InnerCirc
import NonUniqueEuler.I.SmoothB.SmoothCovariance
import NonUniqueEuler.I.SmoothB.SmoothFlow
import NonUniqueEuler.I.SmoothB.Flow
import NonUniqueEuler.I.Sec2.BSBasic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Helpers for `P/Sec9/ActiveRing`: ring `k` with time origin `t♯`, in ring-`k` units

Helper file of `P/Sec9/ActiveRing.lean` (`09_relay.tex:759-767`). For a valid
approximation `P` and a time `t₀ ≥ 0` (applied with `t₀ = t♯_k`), the configuration
`P.activeConfig k` (the three parts of `ω^{(n)}(t₀)` in ring-`k` units) has datum
`A_k⁻¹ω^{(n)}(t₀, r_k ·)`; by the time-translation and scaling covariance of `thm:smooth`
(`Smooth.sol_timeShift`, `Smooth.sol_scale`) its flow is `r_k⁻¹Φ_v(t₀ + u/A_k, t₀, r_k ·)` and its
inverse flow `r_k⁻¹Φ_{t₀}Φ_{t₀+u/A_k}⁻¹(r_k ·)`; with `eq:omega-ge` (`regions_basic_three`) the
transported parts are the rescaled `ω(t)1_{S_k(t)}`, `ν^in_k(t)`, `ν^out_k(t)` at
`t = t₀ + u/A_k`. Everything here is proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace ActiveRingAux

open RingData Datum Approx

variable {P : Approx}

/-! ### The flow of `v^{(n)}` -/

/-- `f^{(n)}` is an admissible datum of `thm:smooth` (`lem:adm`). -/
theorem isSmoothDatum (hP : P.Valid) (hN : NumericalHypothesis P.χ) :
    ∃ R₀ : ℝ, Smooth.IsSmoothDatum P.f R₀ := by
  obtain ⟨hcd, hcs, -⟩ :=
    (adm P.χ hP.admissible hN hP.datumParams ⟨hP.kseed_pos, hP.kseed_le⟩).1 P.n hP.two_le_n
  obtain ⟨R₀, hR₀⟩ := hcs.isCompact.isBounded.subset_ball 0
  exact ⟨R₀, hcd, hR₀⟩

theorem velocityField_om (hP : P.Valid) : velocityField P.om = Smooth.vel P.f := by
  rw [Smooth.vel, hP.om_eq]

/-- `v^{(n)}` satisfies the hypotheses of `lem:flow`. -/
theorem vel_smooth (hP : P.Valid) (hN : NumericalHypothesis P.χ) :
    Smooth.IsSmoothBoundedField (velocityField P.om) := by
  obtain ⟨R₀, hD⟩ := isSmoothDatum hP hN
  rw [velocityField_om hP]
  exact Smooth.vel_isSmoothBoundedField hD

/-- `Φ_t ∘ Φ_t⁻¹ = id`. -/
theorem flow_flowInv (hP : P.Valid) (hN : NumericalHypothesis P.χ) (t : ℝ) (x : ℂ) :
    P.flow t (P.flowInv t x) = x :=
  (Smooth.flowOf_diffeo (vel_smooth hP hN) t 0).2.1 x

/-- `Φ_t⁻¹ ∘ Φ_t = id`. -/
theorem flowInv_flow (hP : P.Valid) (hN : NumericalHypothesis P.χ) (t : ℝ) (y : ℂ) :
    P.flowInv t (P.flow t y) = y :=
  (Smooth.flowOf_diffeo (vel_smooth hP hN) t 0).1 y

theorem continuous_flow (hP : P.Valid) (hN : NumericalHypothesis P.χ) (t : ℝ) :
    Continuous (P.flow t) :=
  (Smooth.flowOf_diffeo (vel_smooth hP hN) t 0).2.2.1.continuous

theorem continuous_flowInv (hP : P.Valid) (hN : NumericalHypothesis P.χ) (t : ℝ) :
    Continuous (P.flowInv t) :=
  (Smooth.flowOf_diffeo (vel_smooth hP hN) t 0).2.2.2.continuous

/-- The cocycle identity `Φ_v(t, s, x) = Φ_t(Φ_s⁻¹(x))` (`lem:flow`(b)). -/
theorem flowOf_eq (hP : P.Valid) (hN : NumericalHypothesis P.χ) (t s : ℝ) (x : ℂ) :
    Smooth.flowOf (velocityField P.om) t s x = P.flow t (P.flowInv s x) :=
  (Smooth.flowOf_cocycle (vel_smooth hP hN) t 0 s x).symm

/-- `supp (φ ∘ g) = h(supp φ)` for mutually inverse continuous maps `g`, `h`. -/
theorem tsupport_comp_inverse {g h : ℂ → ℂ} (hg : Continuous g) (hh : Continuous h)
    (hgh : ∀ x, g (h x) = x) (hhg : ∀ x, h (g x) = x) (φ : ℂ → ℝ) :
    tsupport (fun x => φ (g x)) = h '' tsupport φ := by
  let H : ℂ ≃ₜ ℂ :=
    { toFun := g, invFun := h, left_inv := hhg, right_inv := hgh,
      continuous_toFun := hg, continuous_invFun := hh }
  have h1 : tsupport (φ ∘ H) = H ⁻¹' tsupport φ := tsupport_comp_eq_preimage φ H
  have h2 : (fun x => φ (g x)) = φ ∘ H := rfl
  rw [h2, h1]
  ext x
  constructor
  · intro hx
    exact ⟨g x, hx, hhg x⟩
  · rintro ⟨y, hy, rfl⟩
    show g (h y) ∈ tsupport φ
    rw [hgh]
    exact hy

/-! ### The parts of `ω^{(n)}(t)` -/

/-- `ω_{≥k+1}(t) = (Σ_{i>k} f^{(n)}_i) ∘ Φ_t⁻¹` for `1 ≤ k ≤ n` (`eq:omega-ge`; both sides vanish for
`k = n`). -/
theorem omegaGe_succ (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) {t : ℝ} (ht : 0 ≤ t) :
    P.omegaGe (k + 1) t = fun x => ∑ i ∈ Finset.Ioc k P.n, P.term i (P.flowInv t x) := by
  rcases Nat.lt_or_ge k P.n with hlt | hge
  · have hk1 : k + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [(regions_basic_three P hP hN hk1 ht).2.1, Finset.Icc_add_one_left_eq_Ioc]
  · have hkn' : k = P.n := le_antisymm hkn hge
    rw [hkn', omegaGe_succ_n, Finset.Ioc_self]
    funext x
    simp

/-- `ω^{(n)}(t) = ω(t)1_{S_k(t)} + ω_{≥k+1}(t) + ω(t)1_{S_1(t)∪…∪S_{k-1}(t)}` for `t ≥ 0`
(`lem:regions-basic`(3), `thm:smooth`(4)). -/
theorem om_split (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) {t : ℝ} (ht : 0 ≤ t) (x : ℂ) :
    P.om t x = P.omegaRing k t x + P.omegaGe (k + 1) t x + P.omegaOut k t x := by
  have hkI : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨hk, hkn⟩
  obtain ⟨R₀, hD⟩ := isSmoothDatum hP hN
  have h3 := regions_basic_three P hP hN hkI ht
  rw [h3.1, omegaGe_succ hP hN hk hkn ht, h3.2.2.2.1]
  simp only
  rw [hP.om_eq, Smooth.sol_eq_comp_flowInv hD, ← hP.flowInv_eq, f_def,
    approxDatum_split P.χ P.A₁ P.μ P.sbar P.κs hk hkn]
  simp only [term]
  ring

/-- The datum of `P.activeConfig k` is `A_k⁻¹ω^{(n)}(t♯_k, r_k ·)` when `t♯_k ≥ 0`. -/
theorem activeConfig_datum (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) (ht : 0 ≤ P.tsh k) :
    (P.activeConfig k).datum = fun y => (P.A k)⁻¹ * P.om (P.tsh k) (((P.r k : ℝ) : ℂ) * y) := by
  funext y
  simp only [OneRing.RingConfig.datum, activeConfig, unitsVort, scaleVort]
  rw [om_split hP hN hk hkn ht]
  ring

/-! ### Covariance: the flow of `P.activeConfig k` -/

/-- Time-translation and scaling covariance of `thm:smooth` for `P.activeConfig k`: its flow is
`r_k⁻¹Φ_{t♯+u/A_k}Φ_{t♯}⁻¹(r_k ·)`, its inverse flow `r_k⁻¹Φ_{t♯}Φ_{t♯+u/A_k}⁻¹(r_k ·)`, and its datum
is `C_c^∞`. -/
theorem active_scale (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) (ht : 0 ≤ P.tsh k) :
    (∀ (u : ℝ) (y : ℂ), (P.activeConfig k).flow u y =
      ((P.r k : ℝ) : ℂ)⁻¹ *
        P.flow (P.tsh k + u / P.A k) (P.flowInv (P.tsh k) (((P.r k : ℝ) : ℂ) * y))) ∧
    (∀ (u : ℝ) (x : ℂ), (P.activeConfig k).flowInv u x =
      ((P.r k : ℝ) : ℂ)⁻¹ *
        P.flow (P.tsh k) (P.flowInv (P.tsh k + u / P.A k) (((P.r k : ℝ) : ℂ) * x))) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.activeConfig k).datum ∧
    HasCompactSupport (P.activeConfig k).datum := by
  obtain ⟨R₀, hD⟩ := isSmoothDatum hP hN
  set t₀ := P.tsh k with ht₀
  obtain ⟨hD₁, -, -, hf1⟩ := Smooth.sol_timeShift hD t₀
  obtain ⟨hD₂, -, -, hf2, hfi2⟩ := Smooth.sol_scale hD₁ (hP.A_pos k) (hP.r_pos k)
  have hdat : (P.activeConfig k).datum =
      fun y => (P.A k)⁻¹ * Smooth.sol P.f t₀ (((P.r k : ℝ) : ℂ) * y) := by
    rw [activeConfig_datum hP hN hk hkn ht, hP.om_eq]
  -- the inverse flow of the restarted datum `ω(t₀)`
  have hfi1 : ∀ (τ : ℝ) (x : ℂ), Smooth.flowInv (Smooth.sol P.f t₀) τ x =
      Smooth.flow P.f t₀ (Smooth.flowInv P.f (t₀ + τ) x) := by
    intro τ x
    obtain ⟨hl, -⟩ := Smooth.flow_diffeo hD₁ τ
    obtain ⟨hl0, hr0, -⟩ := Smooth.flow_diffeo hD t₀
    obtain ⟨-, hrτ, -⟩ := Smooth.flow_diffeo hD (t₀ + τ)
    have hx : Smooth.flow (Smooth.sol P.f t₀) τ
        (Smooth.flow P.f t₀ (Smooth.flowInv P.f (t₀ + τ) x)) = x := by
      rw [hf1, hl0, hrτ]
    calc Smooth.flowInv (Smooth.sol P.f t₀) τ x
        = Smooth.flowInv (Smooth.sol P.f t₀) τ (Smooth.flow (Smooth.sol P.f t₀) τ
            (Smooth.flow P.f t₀ (Smooth.flowInv P.f (t₀ + τ) x))) := by rw [hx]
      _ = _ := hl _
  refine ⟨fun u y => ?_, fun u x => ?_, ?_, ?_⟩
  · rw [OneRing.RingConfig.flow, hdat, hf2, hf1, hP.flow_eq, hP.flowInv_eq, Complex.ofReal_inv]
  · rw [OneRing.RingConfig.flowInv, hdat, hfi2, hfi1, hP.flow_eq, hP.flowInv_eq,
      Complex.ofReal_inv]
  · rw [hdat]; exact hD₂.contDiff
  · rw [hdat]; exact hD₂.hasCompactSupport

/-- A part `A_k⁻¹ g(r_k ·)` transported by the flow of `P.activeConfig k`. -/
theorem unitsVort_flowInv (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) (ht : 0 ≤ P.tsh k) (g : ℂ → ℝ) (u : ℝ) (x : ℂ) :
    P.unitsVort k g ((P.activeConfig k).flowInv u x) =
      (P.A k)⁻¹ * g (P.flow (P.tsh k) (P.flowInv (P.tsh k + u / P.A k)
        (((P.r k : ℝ) : ℂ) * x))) := by
  rw [(active_scale hP hN hk hkn ht).2.1 u x]
  have hr : ((P.r k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hP.r_pos k).ne'
  simp only [unitsVort, scaleVort]
  rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul]

/-- The transported parts of `P.activeConfig k` at active time `u ≥ 0` are the rescaled
`ω(t)1_{S_k(t)}`, `ν^in_k(t)`, `ν^out_k(t)`, `t = t♯_k + u/A_k`. -/
theorem active_parts (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) (ht : 0 ≤ P.tsh k) {u : ℝ} (hu : 0 ≤ u) :
    (P.activeConfig k).ringPart u = P.unitsVort k (P.omegaRing k (P.tsh k + u / P.A k)) ∧
    (P.activeConfig k).innerPart u = P.nuIn k (P.tsh k + u / P.A k) ∧
    (P.activeConfig k).outerPart u = P.nuOut k (P.tsh k + u / P.A k) := by
  have hkI : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨hk, hkn⟩
  have ht' : 0 ≤ P.tsh k + u / P.A k := add_nonneg ht (div_nonneg hu (hP.A_pos k).le)
  have h3 := regions_basic_three P hP hN hkI ht
  have h3' := regions_basic_three P hP hN hkI ht'
  have hinv := flowInv_flow hP hN (P.tsh k)
  refine ⟨?_, ?_, ?_⟩
  · funext x
    show P.unitsVort k (P.omegaRing k (P.tsh k)) ((P.activeConfig k).flowInv u x) = _
    rw [unitsVort_flowInv hP hN hk hkn ht, h3.1, h3'.1]
    simp only [unitsVort, scaleVort]
    rw [hinv]
  · funext x
    show P.unitsVort k (P.omegaGe (k + 1) (P.tsh k)) ((P.activeConfig k).flowInv u x) = _
    rw [unitsVort_flowInv hP hN hk hkn ht, nuIn, omegaGe_succ hP hN hk hkn ht,
      omegaGe_succ hP hN hk hkn ht']
    simp only [unitsVort, scaleVort]
    rw [hinv]
  · funext x
    show P.unitsVort k (P.omegaOut k (P.tsh k)) ((P.activeConfig k).flowInv u x) = _
    rw [unitsVort_flowInv hP hN hk hkn ht, nuOut, h3.2.2.2.1, h3'.2.2.2.1]
    simp only [unitsVort, scaleVort]
    rw [hinv]

/-! ### The inner circulation -/

/-- `G = G_k` for `P.activeConfig k` (`lem:inner-circ`: `∫ω_{≥k+1}(t♯_k) = ∫ω_{≥k+1}(0)`, and the
change of variables `x = r_k y`). -/
theorem active_G (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) (ht : 0 ≤ P.tsh k) :
    (P.activeConfig k).G = P.G k := by
  have hkI : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨hk, hkn⟩
  have hr := hP.r_pos k
  have hconst := (inner_circ P hP hN).1 k hkI (P.tsh k) ht
  simp only [OneRing.RingConfig.G, Approx.G]
  set g : ℂ → ℝ := P.omegaGe (k + 1) (P.tsh k) with hg
  have hcv : ∫ x, (P.activeConfig k).inner0 x = (P.A k)⁻¹ * (((P.r k) ^ 2)⁻¹ * ∫ x, g x) := by
    show ∫ x, (P.A k)⁻¹ * g (((P.r k : ℝ) : ℂ) * x) = _
    rw [integral_const_mul]
    congr 1
    have hs : (fun x : ℂ => g (((P.r k : ℝ) : ℂ) * x)) = fun x : ℂ => g (P.r k • x) := by
      funext x
      rw [Complex.real_smul]
    rw [hs, Measure.integral_comp_smul, Complex.finrank_real_complex, smul_eq_mul,
      abs_of_pos (inv_pos.mpr (pow_pos hr 2))]
  rw [hcv, hg, hconst]
  ring

/-! ### The field `h` -/

/-- Linearity of `K_BS *` on `L¹ ∩ L^∞` (absolute convergence, `lem:BS-basic`(b)). -/
theorem velocity_add {f g : ℂ → ℝ} (hf : MemLp f 1 volume) (hf' : MemLp f ⊤ volume)
    (hg : MemLp g 1 volume) (hg' : MemLp g ⊤ volume) (x : ℂ) :
    velocity (fun y => f y + g y) x = velocity f x + velocity g x := by
  have h1 := (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf hf hf' x).1
  have h2 := (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf hg hg' x).1
  simp only [velocity]
  rw [← integral_add h1 h2]
  congr 1
  funext y
  push_cast
  ring

/-- Ring-`k` units preserve continuity and compact support. -/
theorem unitsVort_cont (hP : P.Valid) (k : ℕ) {g : ℂ → ℝ} (hg : Continuous g)
    (hg' : HasCompactSupport g) :
    Continuous (P.unitsVort k g) ∧ HasCompactSupport (P.unitsVort k g) := by
  have hr : P.r k ≠ 0 := (hP.r_pos k).ne'
  have heq : P.unitsVort k g = fun y => (P.A k)⁻¹ * (fun x : ℂ => g (P.r k • x)) y := by
    funext y
    simp only [unitsVort, scaleVort, Complex.real_smul]
  rw [heq]
  refine ⟨continuous_const.mul (hg.comp (continuous_const_smul _)), ?_⟩
  exact (hg'.comp_smul hr).mul_left

/-- `ν^in_k(t)` and `ν^out_k(t)` are continuous with compact support (`t ≥ 0`). -/
theorem nu_reg (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) {t : ℝ} (ht : 0 ≤ t) :
    (Continuous (P.nuIn k t) ∧ HasCompactSupport (P.nuIn k t)) ∧
      (Continuous (P.nuOut k t) ∧ HasCompactSupport (P.nuOut k t)) := by
  have hkI : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨hk, hkn⟩
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_or_ge k P.n with hlt | hge
    · have hk1 : k + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      obtain ⟨-, -, -, -, -, -, -, ⟨hcd, hcs, -⟩⟩ := regions_basic_three P hP hN hk1 ht
      exact unitsVort_cont hP k hcd.continuous hcs
    · have hkn' : k = P.n := le_antisymm hkn hge
      have h0 : P.nuIn k t = fun _ => 0 := by
        funext y
        simp only [nuIn, unitsVort, scaleVort]
        rw [hkn', omegaGe_succ_n]
        simp
      rw [h0]
      exact ⟨continuous_const, HasCompactSupport.zero⟩
  · have hO := (regions_basic_three P hP hN hkI ht).2.2.2.2.1
    have hsub : ∀ i ∈ Finset.Ico 1 k, i ∈ Finset.Icc 1 P.n := fun i hi => by
      rw [Finset.mem_Ico] at hi
      exact Finset.mem_Icc.mpr ⟨hi.1, by omega⟩
    have hreg : ∀ i ∈ Finset.Ico 1 k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.omegaRing i t) ∧
        HasCompactSupport (P.omegaRing i t) := fun i hi => by
      obtain ⟨-, -, -, -, -, -, ⟨hcd, hcs, -⟩, -⟩ := regions_basic_three P hP hN (hsub i hi) ht
      exact ⟨hcd, hcs⟩
    have hc : Continuous (P.omegaOut k t) := by
      rw [hO]
      exact continuous_finsetSum _ fun i hi => (hreg i hi).1.continuous
    have hcs : HasCompactSupport (P.omegaOut k t) := by
      rw [hO]
      have h := HasCompactSupport.finset_sum (s := Finset.Ico 1 k)
        (f := fun i => P.omegaRing i t) fun i hi => (hreg i hi).2
      simpa only [Finset.sum_fn] using h
    exact unitsVort_cont hP k hc hcs

/-- The field of `P.activeConfig k` at active time `u ≥ 0` is `h_k(t̄♯_k + u)` everywhere. -/
theorem active_h (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) (ht : 0 ≤ P.tsh k) {u : ℝ} (hu : 0 ≤ u) (y : ℂ) :
    (P.activeConfig k).h u y = P.hField k (P.tash k + u) y := by
  have hA := hP.A_pos k
  have ht' : 0 ≤ P.tsh k + u / P.A k := add_nonneg ht (div_nonneg hu hA.le)
  obtain ⟨-, hinner, houter⟩ := active_parts hP hN hk hkn ht hu
  obtain ⟨hin_reg, hout_reg⟩ := nu_reg hP hN hk hkn ht'
  have hadd := velocity_add (hin_reg.1.memLp_of_hasCompactSupport hin_reg.2)
    (hin_reg.1.memLp_of_hasCompactSupport hin_reg.2)
    (hout_reg.1.memLp_of_hasCompactSupport hout_reg.2)
    (hout_reg.1.memLp_of_hasCompactSupport hout_reg.2) y
  have htime : (P.tash k + u) / P.A k = P.tsh k + u / P.A k := by
    rw [tash_def]
    field_simp
  rw [OneRing.RingConfig.h, hinner, houter, active_G hP hN hk hkn ht, hadd, hField, hIn, hOut,
    htime]
  ring

/-- The running coefficient of `P.activeConfig k` is `c_k` (`eq:running-k`) at every `u ≥ 0`. -/
theorem active_runCoef (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) (ht : 0 ≤ P.tsh k) {u : ℝ} (hu : 0 ≤ u) :
    OneRing.runCoef P.χ (P.activeConfig k).G ((P.activeConfig k).pert0 P.χ)
      (P.activeConfig k).h u = P.runCoefK k u := by
  rw [active_G hP hN hk hkn ht, runCoefK, OneRing.runCoef, OneRing.runCoef]
  have hp : (P.activeConfig k).pert0 P.χ = P.w k (P.tsh k) := rfl
  rw [hp]
  congr 1
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [uIcc_of_le hu] at hv
  have hfun : (P.activeConfig k).h v = fun y => P.hField k (P.tash k + v) y :=
    funext fun y => active_h hP hN hk hkn ht hv.1 y
  have hF : OneRing.forcing P.χ (P.activeConfig k).h v =
      OneRing.forcing P.χ (fun v => P.hField k (P.tash k + v)) v := by
    funext x
    simp only [OneRing.forcing, hfun]
  simp only [hF]

end ActiveRingAux

end Relay

end NonUniqueEuler
