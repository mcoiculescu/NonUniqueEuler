import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec5.Active.RunCoefShift
import NonUniqueEuler.I.Sec6.FieldContinuity
import NonUniqueEuler.I.Sec6.DefClock
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec8.Coupling
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec9.Detuning
import NonUniqueEuler.I.Infra.Ip.Ip
import NonUniqueEuler.H.Sec9.Drift.EllLinear

/-!
# Proof: `lem:drift`, `eq:drift-interval`, `eq:drift` (the drift of the running coefficient)

Proof of `I/Sec9/Drift.lean` (`09_relay.tex:769-861`).

Structure (following `09_relay.tex:803-861`):
* `DriftProof.drift_interval` (`eq:drift-interval`):
  1. `c_k(u') - c_k(u) = ∫_u^{u'} e^{-λ_k v} ℓ_*(G_k)(F_k(v)) dv` from `OneRing.runCoef_shift`
     (`I/Sec5/Active/RunCoefShift.lean`), the field `v ↦ h_k(t̄♯_k + v)` being continuous into
     `C^0(N')` by `hField_continuous`;
  2. pointwise, `ℓ_*(G_k)(F_k(v)) = ℓ_*(-h^in_k·∇Φ) + ℓ_*(-h^out_k·∇Φ)`
     (`OneRing.DriftAux.ellFn_neg_hGradPhi_add`, helper `H/Sec9/Drift/EllLinear.lean`); the outer
     term is bounded by `C_ls η â_k(v)` (`lem:uniform`, (iii)); the inner one vanishes for `k = n`
     (`h^in_n = 0`), and for `k < n` equals `μβ_k q_{k+1}` (`coupling_one`), with
     `q_{k+1}(t(v)) = qKick k (T_pin + μv)` (`kickTime_eq`) bounded by (i);
  3. the substitution `τ_K = T_pin + μv` and `intervalIntegral_le_mul_Ip`
     (`DriftProof.integral_inner_le`), `x_k ≥ σ/4` (`detuning`), `I_3` decreasing, and (ii)
     (`DriftProof.inner_const_le`) give the inner bound `2κ r_T(T_pin + μu)`.
* `drift_from_zero` (`eq:drift`): the pair `(0, u)`.
* `drift`: the interval bound, `2/64 + 1/32 = 1/16`, `|c_k(0)| = κ♯_k`, (Coef) since
  `|c_k| ≤ 17κ/16 ≤ 2κ`, and `κ♯_k e^{σ_k T̂_k} = δ₀`.

The integral bound of step 2 is a pointwise bound of the integrand (the manuscript bounds the inner
and outer integrals separately; we bound `|e^{-λv}ℓ_*(F_k(v))|` by the sum of the two integrands and
integrate once, which needs no integrability of the two pieces separately).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace DriftProof

/-! ### Generic helpers -/

/-- A path continuous into `C^M(U)` on `[a, a+b]`, shifted to `[0, b]`. -/
theorem ckPathOn_shift {M : ℕ} {U : Set ℂ} {a b : ℝ} {f : ℝ → ℂ → ℂ}
    (hf : OneRing.CkPathOn M U (Icc a (a + b)) f) :
    OneRing.CkPathOn M U (Icc 0 b) (fun v => f (a + v)) := by
  have hmaps : MapsTo (fun v : ℝ => a + v) (Icc 0 b) (Icc a (a + b)) :=
    fun v hv => ⟨by linarith [hv.1], by linarith [hv.2]⟩
  refine ⟨fun t ht => hf.1 _ (hmaps ht), fun t ht => ?_⟩
  have hc : Tendsto (fun v : ℝ => a + v) (𝓝[Icc 0 b] t) (𝓝[Icc a (a + b)] (a + t)) :=
    ((continuous_const.add continuous_id).continuousWithinAt).tendsto_nhdsWithin hmaps
  exact (hf.2 (a + t) (hmaps ht)).comp hc

/-- `h^in_n = 0`: `D_{n+1} = ∅` and `G_n = 0` (`09_relay.tex:819-820`). -/
theorem hIn_n (P : Approx) (τ : ℝ) : P.hIn P.n τ = 0 := by
  funext y
  simp [Approx.hIn, Approx.nuIn, Approx.unitsVort, scaleVort, Approx.omegaGe_succ_n,
    Approx.G_n, velocity]

/-- `C_ls ≥ 0`. -/
theorem Cls_nonneg (χ : ℝ → ℝ) : 0 ≤ Eig.Cls χ := by
  unfold Eig.Cls
  refine mul_nonneg ?_ ENNReal.toReal_nonneg
  refine Real.sSup_nonneg fun x hx => ?_
  obtain ⟨G, -, rfl⟩ := hx
  exact norm_nonneg (Eig.ell χ 0 G)

/-- Integrating a pointwise bound `‖g‖ ≤ B + C` over `[u, u']`. -/
theorem norm_integral_le_add {g : ℝ → ℂ} {B : ℝ → ℝ} {C u u' : ℝ} (huu' : u ≤ u')
    (hB : ContinuousOn B (Icc u u')) (hg : ∀ w ∈ Icc u u', ‖g w‖ ≤ B w + C) :
    ‖∫ w in u..u', g w‖ ≤ (∫ w in u..u', B w) + C * (u' - u) := by
  have hBi : IntervalIntegrable B volume u u' := hB.intervalIntegrable_of_Icc huu'
  have hCi : IntervalIntegrable (fun _ : ℝ => C) volume u u' := intervalIntegrable_const
  calc ‖∫ w in u..u', g w‖ ≤ ∫ w in u..u', (B w + C) :=
        intervalIntegral.norm_integral_le_of_norm_le huu'
          (Eventually.of_forall fun w hw => hg w ⟨hw.1.le, hw.2⟩) (hBi.add hCi)
    _ = (∫ w in u..u', B w) + C * (u' - u) := by
        rw [intervalIntegral.integral_add hBi hCi, intervalIntegral.integral_const, smul_eq_mul]
        ring

/-- **The inner integral** (`09_relay.tex:824-834`): with `x = σ/μ`, the substitution
`τ = T + μw` and `eq:Ip` (`intervalIntegral_le_mul_Ip`) give
`∫_u^{u'} e^{-σw} μ(1 + T + μw)³ dw ≤ e^{xT}(1 + τ_a)³e^{-xτ_a} I_3(x)`, `τ_a = T + μu`. -/
theorem integral_inner_le {σ μ T u u' : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) (hT : 0 ≤ T) (hu : 0 ≤ u)
    (huu' : u ≤ u') :
    ∫ w in u..u', Real.exp (-(σ * w)) * (μ * (1 + (T + μ * w)) ^ 3) ≤
      Real.exp (σ / μ * T) *
        ((1 + (T + μ * u)) ^ 3 * Real.exp (-(σ / μ) * (T + μ * u)) * Ip 3 (σ / μ)) := by
  have hx0 : 0 < σ / μ := div_pos hσ hμ
  have hpt : ∀ w : ℝ, Real.exp (-(σ * w)) * (μ * (1 + (T + μ * w)) ^ 3) =
      Real.exp (σ / μ * T) *
        (μ * (Real.exp (-(σ / μ) * (μ * w + T)) * (1 + (μ * w + T)) ^ 3)) := by
    intro w
    have h1 : -(σ * w) = σ / μ * T + -(σ / μ) * (μ * w + T) := by
      field_simp
      ring
    rw [h1, Real.exp_add]
    ring
  have h2 : ∫ w in u..u', μ * (Real.exp (-(σ / μ) * (μ * w + T)) * (1 + (μ * w + T)) ^ 3) =
      ∫ s in (μ * u + T)..(μ * u' + T), Real.exp (-(σ / μ) * s) * (1 + s) ^ 3 := by
    rw [intervalIntegral.integral_const_mul]
    exact intervalIntegral.smul_integral_comp_mul_add
      (f := fun s => Real.exp (-(σ / μ) * s) * (1 + s) ^ 3) μ T
  have h3 := intervalIntegral_le_mul_Ip 3 hx0 (τ := μ * u + T) (τ' := μ * u' + T)
    (by positivity) (by nlinarith)
  rw [intervalIntegral.integral_congr (fun w _ => hpt w), intervalIntegral.integral_const_mul,
    h2]
  rw [show T + μ * u = μ * u + T by ring]
  exact mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le

/-- **The constants of (ii)** (`09_relay.tex:840-845`): from
`|β||q'|/(10|z|(μ-1)) ≤ |A^in|` and `μ - 1 ≤ |q'|/(10|z|C_mom I)`, `|β| C_mom I ≤ |A^in|`. -/
theorem inner_const_le {β Cm I A z μ q : ℝ} (hβ : 0 ≤ β) (hCm : 0 ≤ Cm) (hI : 0 ≤ I)
    (hz : 0 ≤ z) (hμ : 1 < μ) (h1 : β * q / (10 * z * (μ - 1)) ≤ A)
    (h2 : μ - 1 ≤ q / (10 * z * Cm * I)) : β * Cm * I ≤ A := by
  have hD0 : 0 ≤ 10 * z * Cm * I := by positivity
  have hD : 0 < 10 * z * Cm * I := by
    rcases hD0.lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq, div_zero] at h2
      linarith
  have hzpos : 0 < z := by
    rcases hz.lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq] at hD
      simp at hD
  have h3 : (μ - 1) * (10 * z * Cm * I) ≤ q := (le_div_iff₀ hD).1 h2
  have h4 : Cm * I ≤ q / (10 * z * (μ - 1)) := by
    rw [le_div_iff₀ (by have : 0 < μ - 1 := by linarith
                        positivity)]
    linarith [show Cm * I * (10 * z * (μ - 1)) = (μ - 1) * (10 * z * Cm * I) by ring]
  calc β * Cm * I = β * (Cm * I) := by ring
    _ ≤ β * (q / (10 * z * (μ - 1))) := mul_le_mul_of_nonneg_left h4 hβ
    _ = β * q / (10 * z * (μ - 1)) := by ring
    _ ≤ A := h1

/-! ### `eq:drift-interval` -/

/-- **`eq:drift-interval`** (`09_relay.tex:786-790`, proof `:803-848`). -/
theorem drift_interval (S : Standing) (hS : S.Holds) (hDet : S.Det) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ S.P.n) (hc : S.P.ClockUpTo k) {ubar η : ℝ} (_hu : ubar ∈ Icc 0 (S.P.That k))
    (_hη : 0 ≤ η) (h : S.DriftHyp k ubar η) :
    ∀ u ∈ Icc (0 : ℝ) ubar, ∀ u' ∈ Icc u ubar,
      ‖S.P.runCoefK k u' - S.P.runCoefK k u‖ ≤
        (if k < S.P.n then 2 * S.rT (S.P.Tpin + S.P.μ * u) * S.P.ksh k else 0) +
          Eig.Cls S.P.χ * η * (u' - u) * S.P.ksh k := by
  intro u hu0 u' hu'
  have hP : S.P.Valid := hS.valid
  have hN : NumericalHypothesis S.P.χ := hS.hN
  have hχ : IsAdmissibleCutoff S.P.χ := hP.admissible
  have hkI : k ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hk, hkn⟩
  obtain ⟨hsigb, -, hGs, hlev⟩ := standing_levels S hS
  obtain ⟨-, hGk, hsigk⟩ := hlev k hkI
  have hσk : 0 < S.P.sigma k := lt_of_lt_of_le hsigb hsigk
  have hA : 0 < S.P.A k := hP.A_pos k
  have hμ1 : 1 < S.P.μ := hS.one_lt_μ
  have hμ0 : 0 < S.P.μ := by linarith
  have hTpin : 0 < S.P.Tpin := hS.Tpin_pos
  have htsh : 0 ≤ S.P.tsh k := (Approx.clock_order S.P hP hN hGs hk hc).2.2.2 k
    (Finset.mem_Icc.2 ⟨le_rfl, hkn⟩)
  have hκ0 : 0 ≤ S.P.ksh k := S.P.ksh_nonneg k
  have hCls : 0 ≤ Eig.Cls S.P.χ := Cls_nonneg _
  have hu'0 : 0 ≤ u' := le_trans hu0.1 hu'.1
  -- the time map `v ↦ t♯_k + v/A_k`
  have hAt : ∀ w : ℝ, S.P.A k * (S.P.tsh k + w / S.P.A k) = S.P.tash k + w := by
    intro w
    rw [Approx.tash_def, mul_add, mul_div_cancel₀ _ hA.ne']
  have hgeom : ∀ t ∈ Icc (S.P.tsh k) (S.P.tsh k + ubar / S.P.A k), S.P.HDefined k t := h.geom
  have hFpath := Approx.hField_continuous S.P hP hN hk hkn htsh hgeom 0
  have hInPath := Approx.hIn_continuous S.P hP hN hk hkn htsh (fun t ht => (hgeom t ht).1) 0
  have hOutPath := Approx.hOut_continuous S.P hP hN hk hkn htsh (fun t ht => (hgeom t ht).2) 0
  rw [hAt, show S.P.A k * S.P.tsh k = S.P.tash k from rfl] at hFpath hInPath hOutPath
  have hfpath : OneRing.CkPathOn 0 annN' (Icc 0 ubar)
      (fun v => S.P.hField k (S.P.tash k + v)) := ckPathOn_shift hFpath
  have hτmem : ∀ w ∈ Icc (0 : ℝ) ubar, S.P.tash k + w ∈ Icc (S.P.tash k) (S.P.tash k + ubar) :=
    fun w hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hwmem : ∀ w ∈ Icc u u', w ∈ Icc (0 : ℝ) ubar :=
    fun w hw => ⟨le_trans hu0.1 hw.1, le_trans hw.2 hu'.2⟩
  -- Step 1: the integral representation
  have hrep : S.P.runCoefK k u' - S.P.runCoefK k u =
      ∫ w in u..u', Complex.exp (-(Eig.lam S.P.χ (S.P.G k) * w)) *
        Eig.ellFn S.P.χ (S.P.G k)
          (OneRing.forcing S.P.χ (fun v => S.P.hField k (S.P.tash k + v)) w) := by
    have hshift := OneRing.runCoef_shift S.P.χ hχ hN hGk hfpath hu0.1 (sub_nonneg.2 hu'.1)
      (by linarith [hu'.2]) (S.P.w k (S.P.tsh k)) 0
    rw [show u + (u' - u) = u' by ring] at hshift
    have hJ : (∫ v in (0 : ℝ)..(u' - u), Complex.exp (-(Eig.lam S.P.χ (S.P.G k) * v)) *
        Eig.ellFn S.P.χ (S.P.G k) (OneRing.forcing S.P.χ
          (fun τ => (fun v => S.P.hField k (S.P.tash k + v)) (u + τ)) v)) =
        Complex.exp (Eig.lam S.P.χ (S.P.G k) * u) *
          ∫ w in u..u', Complex.exp (-(Eig.lam S.P.χ (S.P.G k) * w)) *
            Eig.ellFn S.P.χ (S.P.G k)
              (OneRing.forcing S.P.χ (fun v => S.P.hField k (S.P.tash k + v)) w) := by
      have hpt : ∀ v : ℝ, Complex.exp (-(Eig.lam S.P.χ (S.P.G k) * v)) *
          Eig.ellFn S.P.χ (S.P.G k) (OneRing.forcing S.P.χ
            (fun τ => (fun v => S.P.hField k (S.P.tash k + v)) (u + τ)) v) =
          Complex.exp (Eig.lam S.P.χ (S.P.G k) * u) *
            (Complex.exp (-(Eig.lam S.P.χ (S.P.G k) * ((u + v : ℝ) : ℂ))) *
              Eig.ellFn S.P.χ (S.P.G k)
                (OneRing.forcing S.P.χ (fun v => S.P.hField k (S.P.tash k + v)) (u + v))) := by
        intro v
        rw [← mul_assoc, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      rw [intervalIntegral.integral_congr (fun v _ => hpt v), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_add_left (fun w : ℝ =>
          Complex.exp (-(Eig.lam S.P.χ (S.P.G k) * w)) * Eig.ellFn S.P.χ (S.P.G k)
            (OneRing.forcing S.P.χ (fun v => S.P.hField k (S.P.tash k + v)) w)) u]
      rw [add_zero, show u + (u' - u) = u' by ring]
    have hdef : OneRing.runCoef S.P.χ (S.P.G k) 0
        (fun τ => (fun v => S.P.hField k (S.P.tash k + v)) (u + τ)) (u' - u) =
        Eig.ellFn S.P.χ (S.P.G k) 0 +
          ∫ v in (0 : ℝ)..(u' - u), Complex.exp (-(Eig.lam S.P.χ (S.P.G k) * v)) *
            Eig.ellFn S.P.χ (S.P.G k) (OneRing.forcing S.P.χ
              (fun τ => (fun v => S.P.hField k (S.P.tash k + v)) (u + τ)) v) := rfl
    rw [hdef, hJ] at hshift
    have hshift' : Complex.exp (Eig.lam S.P.χ (S.P.G k) * u) *
        (∫ w in u..u', Complex.exp (-(Eig.lam S.P.χ (S.P.G k) * w)) *
          Eig.ellFn S.P.χ (S.P.G k)
            (OneRing.forcing S.P.χ (fun v => S.P.hField k (S.P.tash k + v)) w)) =
        Complex.exp (Eig.lam S.P.χ (S.P.G k) * u) *
          (S.P.runCoefK k u' - S.P.runCoefK k u) := by
      have e : S.P.runCoefK k u' - S.P.runCoefK k u =
          OneRing.runCoef S.P.χ (S.P.G k) (S.P.w k (S.P.tsh k))
            (fun v => S.P.hField k (S.P.tash k + v)) u' -
          OneRing.runCoef S.P.χ (S.P.G k) (S.P.w k (S.P.tsh k))
            (fun v => S.P.hField k (S.P.tash k + v)) u := rfl
      rw [e]
      linear_combination hshift
    exact (mul_left_cancel₀ (Complex.exp_ne_zero _) hshift').symm
  -- Step 2: the pointwise bounds
  have hnormexp : ∀ w : ℝ, ‖Complex.exp (-(Eig.lam S.P.χ (S.P.G k) * w))‖ =
      Real.exp (-(S.P.sigma k * w)) := by
    intro w
    rw [Complex.norm_exp]
    congr 1
    simp [Approx.sigma, Eig.sigma]
  have hsplit : ∀ w ∈ Icc (0 : ℝ) ubar,
      Eig.ellFn S.P.χ (S.P.G k)
          (OneRing.forcing S.P.χ (fun v => S.P.hField k (S.P.tash k + v)) w) =
        Eig.ellFn S.P.χ (S.P.G k) (fun x => -Eig.hGradPhi S.P.χ (S.P.hIn k (S.P.tash k + w)) x) +
        Eig.ellFn S.P.χ (S.P.G k)
          (fun x => -Eig.hGradPhi S.P.χ (S.P.hOut k (S.P.tash k + w)) x) := by
    intro w hw
    exact OneRing.DriftAux.ellFn_neg_hGradPhi_add S.P.χ hχ hN hGk
      (hInPath.1 _ (hτmem w hw)) (hOutPath.1 _ (hτmem w hw))
  have hOutB : ∀ w ∈ Icc (0 : ℝ) ubar, Real.exp (-(S.P.sigma k * w)) *
      ‖Eig.ellFn S.P.χ (S.P.G k)
        (fun x => -Eig.hGradPhi S.P.χ (S.P.hOut k (S.P.tash k + w)) x)‖ ≤
      Eig.Cls S.P.χ * η * S.P.ksh k := by
    intro w hw
    have h1 := (Eig.uniform_inequalities S.P.χ hχ hN).1 (S.P.G k) hGk _
      (hOutPath.1 _ (hτmem w hw))
    have h2 := h.outer w hw
    rw [Standing.ahatK_def] at h2
    have h3 : ‖Eig.ellFn S.P.χ (S.P.G k)
        (fun x => -Eig.hGradPhi S.P.χ (S.P.hOut k (S.P.tash k + w)) x)‖ ≤
        Eig.Cls S.P.χ * (η * (S.P.ksh k * Real.exp (S.P.sigma k * w))) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 hCls)
    calc Real.exp (-(S.P.sigma k * w)) *
          ‖Eig.ellFn S.P.χ (S.P.G k)
            (fun x => -Eig.hGradPhi S.P.χ (S.P.hOut k (S.P.tash k + w)) x)‖
        ≤ Real.exp (-(S.P.sigma k * w)) *
          (Eig.Cls S.P.χ * (η * (S.P.ksh k * Real.exp (S.P.sigma k * w)))) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      _ = Eig.Cls S.P.χ * η * S.P.ksh k *
          (Real.exp (-(S.P.sigma k * w)) * Real.exp (S.P.sigma k * w)) := by ring
      _ = Eig.Cls S.P.χ * η * S.P.ksh k := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  rw [hrep]
  by_cases hkn' : k < S.P.n
  · -- `k < n`: the inner rings contribute
    simp only [hkn', ↓reduceIte]
    have hB : ContinuousOn (fun w : ℝ => ‖S.P.betaK k‖ * Rings.Cmom *
        (Real.exp (-(S.P.sigma k * w)) * (S.P.μ * (1 + (S.P.Tpin + S.P.μ * w)) ^ 3)))
        (Icc u u') := Continuous.continuousOn (by fun_prop)
    refine (norm_integral_le_add (C := Eig.Cls S.P.χ * η * S.P.ksh k) hu'.1 hB
      (fun w hw => ?_)).trans ?_
    · have hw0 := hwmem w hw
      -- the inner term: `ℓ_*(-h^in_k·∇Φ) = μβ_k q_{k+1}(t)`, `t = t♯_k + w/A_k`
      have ht0 : 0 ≤ S.P.tsh k + w / S.P.A k := add_nonneg htsh (div_nonneg hw0.1 hA.le)
      have htmem : S.P.tsh k + w / S.P.A k ∈ Icc (S.P.tsh k) (S.P.tsh k + ubar / S.P.A k) :=
        ⟨le_add_of_nonneg_right (div_nonneg hw0.1 hA.le),
          by linarith [div_le_div_of_nonneg_right hw0.2 hA.le]⟩
      have hcoup := (Kick.coupling_one S.P hP hN hk hkn' ht0 (hgeom _ htmem).1).2.1
      rw [hAt w] at hcoup
      have hact : S.P.activeTime k (S.P.tsh k + w / S.P.A k) = w := by
        rw [Approx.activeTime, add_sub_cancel_left, mul_div_cancel₀ _ hA.ne']
      have hkt := (Approx.kickTime_eq S.P hP hk hkn').1 (S.P.tsh k + w / S.P.A k)
      rw [hact] at hkt
      have hA1 : 0 < S.P.A (k + 1) := hP.A_pos (k + 1)
      have hq : S.P.q (k + 1) (S.P.tsh k + w / S.P.A k) = S.P.qKick k (S.P.Tpin + S.P.μ * w) := by
        rw [← hkt, Approx.qKick, Approx.kickTime, mul_div_cancel_left₀ _ hA1.ne']
        ring_nf
      have hmom := h.moment hkn' (S.P.Tpin + S.P.μ * w)
        ⟨le_add_of_nonneg_right (mul_nonneg hμ0.le hw0.1),
          by linarith [mul_le_mul_of_nonneg_left hw0.2 hμ0.le]⟩
      have hinB : ‖Eig.ellFn S.P.χ (S.P.G k)
          (fun x => -Eig.hGradPhi S.P.χ (S.P.hIn k (S.P.tash k + w)) x)‖ ≤
          S.P.μ * ‖S.P.betaK k‖ * (Rings.Cmom * (1 + (S.P.Tpin + S.P.μ * w)) ^ 3) := by
        have e : Eig.ellFn S.P.χ (S.P.G k)
            (fun x => -Eig.hGradPhi S.P.χ (S.P.hIn k (S.P.tash k + w)) x) =
            (S.P.μ : ℂ) * S.P.betaK k * S.P.qKick k (S.P.Tpin + S.P.μ * w) := by
          rw [← hq]
          exact hcoup
        rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ0.le]
        exact mul_le_mul_of_nonneg_left hmom (by positivity)
      rw [Complex.norm_mul, hnormexp, hsplit w hw0]
      have htri := norm_add_le
        (Eig.ellFn S.P.χ (S.P.G k)
          (fun x => -Eig.hGradPhi S.P.χ (S.P.hIn k (S.P.tash k + w)) x))
        (Eig.ellFn S.P.χ (S.P.G k)
          (fun x => -Eig.hGradPhi S.P.χ (S.P.hOut k (S.P.tash k + w)) x))
      have hE : 0 < Real.exp (-(S.P.sigma k * w)) := Real.exp_pos _
      have hO := hOutB w hw0
      calc Real.exp (-(S.P.sigma k * w)) *
            ‖Eig.ellFn S.P.χ (S.P.G k)
                (fun x => -Eig.hGradPhi S.P.χ (S.P.hIn k (S.P.tash k + w)) x) +
              Eig.ellFn S.P.χ (S.P.G k)
                (fun x => -Eig.hGradPhi S.P.χ (S.P.hOut k (S.P.tash k + w)) x)‖
          ≤ Real.exp (-(S.P.sigma k * w)) *
              ‖Eig.ellFn S.P.χ (S.P.G k)
                (fun x => -Eig.hGradPhi S.P.χ (S.P.hIn k (S.P.tash k + w)) x)‖ +
            Real.exp (-(S.P.sigma k * w)) *
              ‖Eig.ellFn S.P.χ (S.P.G k)
                (fun x => -Eig.hGradPhi S.P.χ (S.P.hOut k (S.P.tash k + w)) x)‖ := by
            rw [← mul_add]
            exact mul_le_mul_of_nonneg_left htri hE.le
        _ ≤ Real.exp (-(S.P.sigma k * w)) *
              (S.P.μ * ‖S.P.betaK k‖ * (Rings.Cmom * (1 + (S.P.Tpin + S.P.μ * w)) ^ 3)) +
            Eig.Cls S.P.χ * η * S.P.ksh k := by
            gcongr
        _ = ‖S.P.betaK k‖ * Rings.Cmom *
              (Real.exp (-(S.P.sigma k * w)) * (S.P.μ * (1 + (S.P.Tpin + S.P.μ * w)) ^ 3)) +
            Eig.Cls S.P.χ * η * S.P.ksh k := by ring
    · -- Step 3: the inner integral
      have hint := integral_inner_le (σ := S.P.sigma k) (T := S.P.Tpin) hμ0 hσk hTpin.le hu0.1
        hu'.1
      rw [intervalIntegral.integral_const_mul]
      obtain ⟨-, -, hdet⟩ := detuning S hS hDet
      obtain ⟨-, -, -, hxk, -, -⟩ := hdet k hkI
      have hσ0 : 0 < S.sigma0 := by
        obtain ⟨hsb, hsb0, -⟩ := standing_levels S hS
        exact lt_of_lt_of_le hsb hsb0
      have hx : S.P.xk k = S.P.sigma k / S.P.μ := rfl
      rw [← hx] at hint
      have hx0 : 0 < S.P.xk k := lt_of_lt_of_le (by positivity) hxk
      obtain ⟨-, hAin, q', -, hq1, hq2⟩ := h.kick hkn'
      have hIpos : 0 < Ip 3 (S.sigma0 / 4) := Ip_pos 3 (by positivity)
      have hIle : Ip 3 (S.P.xk k) ≤ Ip 3 (S.sigma0 / 4) :=
        Ip_antitoneOn 3 (show S.sigma0 / 4 ∈ Ioi (0 : ℝ) from by simp; positivity)
          (show S.P.xk k ∈ Ioi (0 : ℝ) from hx0) hxk
      have hIx : 0 ≤ Ip 3 (S.P.xk k) := (Ip_pos 3 hx0).le
      have hconst := inner_const_le (norm_nonneg _) Rings.Cmom_pos.le hIpos.le (norm_nonneg _)
        hμ1 hq1 hq2
      set τa := S.P.Tpin + S.P.μ * u with hτa
      have hτa0 : 0 ≤ τa := add_nonneg hTpin.le (mul_nonneg hμ0.le hu0.1)
      have hR : (1 + τa) ^ 3 * Real.exp (-S.P.xk k * τa) ≤ S.rT τa := by
        rw [Standing.rT_def]
        gcongr
        nlinarith
      have hE : 0 < Real.exp (S.P.xk k * S.P.Tpin) := Real.exp_pos _
      have hAinE : ‖S.P.Ain k S.P.Tpin‖ * Real.exp (S.P.xk k * S.P.Tpin) ≤ 2 * S.P.ksh k := by
        linarith
      have hβC : 0 ≤ ‖S.P.betaK k‖ * Rings.Cmom := mul_nonneg (norm_nonneg _) Rings.Cmom_pos.le
      have hrT : 0 ≤ S.rT τa := by rw [Standing.rT_def]; positivity
      have hstep : (1 + τa) ^ 3 * Real.exp (-S.P.xk k * τa) * Ip 3 (S.P.xk k) ≤
          S.rT τa * Ip 3 (S.sigma0 / 4) := mul_le_mul hR hIle hIx hrT
      have s1 := mul_le_mul_of_nonneg_left hint hβC
      have s2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep hE.le) hβC
      have s3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst hE.le) hrT
      have s4 := mul_le_mul_of_nonneg_right hAinE hrT
      calc ‖S.P.betaK k‖ * Rings.Cmom *
            (∫ w in u..u', Real.exp (-(S.P.sigma k * w)) *
              (S.P.μ * (1 + (S.P.Tpin + S.P.μ * w)) ^ 3)) +
            Eig.Cls S.P.χ * η * S.P.ksh k * (u' - u)
          ≤ ‖S.P.betaK k‖ * Rings.Cmom *
              (Real.exp (S.P.xk k * S.P.Tpin) * (S.rT τa * Ip 3 (S.sigma0 / 4))) +
            Eig.Cls S.P.χ * η * S.P.ksh k * (u' - u) := by linarith
        _ = (‖S.P.betaK k‖ * Rings.Cmom * Ip 3 (S.sigma0 / 4)) *
              Real.exp (S.P.xk k * S.P.Tpin) * S.rT τa +
            Eig.Cls S.P.χ * η * S.P.ksh k * (u' - u) := by ring
        _ ≤ 2 * S.P.ksh k * S.rT τa + Eig.Cls S.P.χ * η * S.P.ksh k * (u' - u) := by linarith
        _ = 2 * S.rT τa * S.P.ksh k + Eig.Cls S.P.χ * η * (u' - u) * S.P.ksh k := by ring
  · -- `k = n`: `h^in_n = 0`
    simp only [hkn', ↓reduceIte]
    have hkeq : k = S.P.n := le_antisymm hkn (not_lt.1 hkn')
    refine (norm_integral_le_add (B := fun _ => (0 : ℝ)) (C := Eig.Cls S.P.χ * η * S.P.ksh k)
      hu'.1 continuousOn_const
      (fun w hw => ?_)).trans ?_
    · have hw0 := hwmem w hw
      have hz : S.P.hIn k (S.P.tash k + w) = 0 := by
        rw [hkeq]
        exact hIn_n S.P _
      have e : Eig.ellFn S.P.χ (S.P.G k)
          (OneRing.forcing S.P.χ (fun v => S.P.hField k (S.P.tash k + v)) w) =
          Eig.ellFn S.P.χ (S.P.G k)
            (fun x => -Eig.hGradPhi S.P.χ (S.P.hOut k (S.P.tash k + w)) x) := by
        have e1 : Eig.ellFn S.P.χ (S.P.G k)
            (OneRing.forcing S.P.χ (fun v => S.P.hField k (S.P.tash k + v)) w) =
            Eig.ellFn S.P.χ (S.P.G k) (fun x => -Eig.hGradPhi S.P.χ
              (S.P.hIn k (S.P.tash k + w) + S.P.hOut k (S.P.tash k + w)) x) := rfl
        rw [e1, hz, zero_add]
      rw [Complex.norm_mul, hnormexp, e, zero_add]
      exact hOutB w hw0
    · simp only [intervalIntegral.integral_zero, zero_add]
      linarith [show Eig.Cls S.P.χ * η * S.P.ksh k * (u' - u) =
        Eig.Cls S.P.χ * η * (u' - u) * S.P.ksh k by ring]

end DriftProof

/-- **`lem:drift`** (`09_relay.tex:769-801`). Assume (SA), (Det), `1 ≤ k ≤ n`, the clock defined up
to level `k`, `0 ≤ ū ≤ T̂_k`, `η ≥ 0` and the hypotheses (i)–(iv) (`S.DriftHyp k ū η`). Then
`eq:drift-interval` holds for `0 ≤ u ≤ u' ≤ ū` (without the inner term if `k = n`); and if
`r_T(T_pin) ≤ 1/64` and `C_ls η T̂_k ≤ 1/32`, then `|c_k(u) - c_k(0)| ≤ κ♯_k/16` on `[0,ū]`, (Coef)
holds on `[0,ū]` (for every `C₀ ≥ 0`), and if `ū = T̂_k`,
`|c_k(T̂_k)| e^{σ_k T̂_k} ∈ [15δ₀/16, 17δ₀/16]`. -/
theorem drift (S : Standing) (hS : S.Holds) (hDet : S.Det) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ S.P.n) (hc : S.P.ClockUpTo k) {ubar η : ℝ} (hu : ubar ∈ Icc 0 (S.P.That k))
    (hη : 0 ≤ η) (h : S.DriftHyp k ubar η) :
    (∀ u ∈ Icc (0 : ℝ) ubar, ∀ u' ∈ Icc u ubar,
      ‖S.P.runCoefK k u' - S.P.runCoefK k u‖ ≤
        (if k < S.P.n then 2 * S.rT (S.P.Tpin + S.P.μ * u) * S.P.ksh k else 0) +
          Eig.Cls S.P.χ * η * (u' - u) * S.P.ksh k) ∧
    (S.rT S.P.Tpin ≤ 1 / 64 → Eig.Cls S.P.χ * η * S.P.That k ≤ 1 / 32 →
      (∀ u ∈ Icc (0 : ℝ) ubar, ‖S.P.runCoefK k u - S.P.runCoefK k 0‖ ≤ 1 / 16 * S.P.ksh k) ∧
      (∀ C₀ : ℝ, 0 ≤ C₀ → S.CoefK C₀ k ubar) ∧
      (ubar = S.P.That k →
        ‖S.P.runCoefK k (S.P.That k)‖ * Real.exp (S.P.sigma k * S.P.That k) ∈
          Icc (15 / 16 * S.P.δ₀) (17 / 16 * S.P.δ₀))) := by
  have hint := DriftProof.drift_interval S hS hDet hk hkn hc hu hη h
  refine ⟨hint, fun hrT hCη => ?_⟩
  have hκ0 : 0 ≤ S.P.ksh k := S.P.ksh_nonneg k
  have hCls : 0 ≤ Eig.Cls S.P.χ := DriftProof.Cls_nonneg _
  -- `|c_k(u) - c_k(0)| ≤ κ/16`
  have h16 : ∀ u ∈ Icc (0 : ℝ) ubar,
      ‖S.P.runCoefK k u - S.P.runCoefK k 0‖ ≤ 1 / 16 * S.P.ksh k := by
    intro u hu'
    have h1 := hint 0 ⟨le_rfl, hu.1⟩ u ⟨hu'.1, hu'.2⟩
    rw [mul_zero, add_zero, sub_zero] at h1
    have hif : (if k < S.P.n then 2 * S.rT S.P.Tpin * S.P.ksh k else 0) ≤
        1 / 32 * S.P.ksh k := by
      split_ifs
      · nlinarith
      · positivity
    have hCu : Eig.Cls S.P.χ * η * u * S.P.ksh k ≤ 1 / 32 * S.P.ksh k := by
      have : Eig.Cls S.P.χ * η * u ≤ Eig.Cls S.P.χ * η * S.P.That k :=
        mul_le_mul_of_nonneg_left (hu'.2.trans hu.2) (mul_nonneg hCls hη)
      exact mul_le_mul_of_nonneg_right (this.trans hCη) hκ0
    linarith
  have hc0 : ‖S.P.runCoefK k 0‖ = S.P.ksh k := by
    rw [Approx.runCoefK_zero]
    rfl
  have hup : ∀ u ∈ Icc (0 : ℝ) ubar, ‖S.P.runCoefK k u‖ ≤ 17 / 16 * S.P.ksh k := by
    intro u hu'
    have h1 := h16 u hu'
    have h2 := norm_le_norm_add_norm_sub' (S.P.runCoefK k u) (S.P.runCoefK k 0)
    linarith
  refine ⟨h16, fun C₀ hC₀ u hu' => ?_, fun hT => ?_⟩
  · have h1 := hup u hu'
    have h2 : 0 ≤ C₀ * Prelim.jap u ^ OneRing.pW * Real.exp (-(S.P.sigma k * u)) := by
      have := Prelim.jap_nonneg u
      positivity
    nlinarith
  · have hmem : S.P.That k ∈ Icc (0 : ℝ) ubar := ⟨hT ▸ hu.1, hT.ge⟩
    have hκ := hc.ksh_mem (le_refl k) hkn
    have hkI : k ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hk, hkn⟩
    obtain ⟨hsigb, -, -, hlev⟩ := standing_levels S hS
    have hσk : 0 < S.P.sigma k := lt_of_lt_of_le hsigb (hlev k hkI).2.2
    have hexp : Real.exp (S.P.sigma k * S.P.That k) = S.P.δ₀ / S.P.ksh k := by
      rw [Approx.That, ← mul_assoc, mul_inv_cancel₀ hσk.ne', one_mul,
        Real.exp_log (div_pos (hκ.1.trans hκ.2) hκ.1)]
    have hlo : 15 / 16 * S.P.ksh k ≤ ‖S.P.runCoefK k (S.P.That k)‖ := by
      have h1 := h16 _ hmem
      have h2 := norm_sub_norm_le (S.P.runCoefK k 0) (S.P.runCoefK k (S.P.That k))
      rw [norm_sub_rev] at h1
      linarith
    have hhi := hup _ hmem
    rw [hexp]
    have hκpos : 0 < S.P.ksh k := hκ.1
    constructor
    · rw [mul_div_assoc', le_div_iff₀ hκpos]
      nlinarith [hS.δ₀_pos]
    · rw [mul_div_assoc', div_le_iff₀ hκpos]
      nlinarith [hS.δ₀_pos]

/-- **`eq:drift`** (`09_relay.tex:791-795`, the "in particular" of `lem:drift`): under the
hypotheses of `lem:drift`, for `u ∈ [0, ū]`,
`|c_k(u) - c_k(0)| ≤ (2 r_T(T_pin) + C_ls η T̂_k) κ♯_k`, without the first term if `k = n`. -/
theorem drift_from_zero (S : Standing) (hS : S.Holds) (hDet : S.Det) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ S.P.n) (hc : S.P.ClockUpTo k) {ubar η : ℝ} (hu : ubar ∈ Icc 0 (S.P.That k))
    (hη : 0 ≤ η) (h : S.DriftHyp k ubar η) :
    ∀ u ∈ Icc (0 : ℝ) ubar, ‖S.P.runCoefK k u - S.P.runCoefK k 0‖ ≤
      ((if k < S.P.n then 2 * S.rT S.P.Tpin else 0) + Eig.Cls S.P.χ * η * S.P.That k) *
        S.P.ksh k := by
  intro u hu'
  have h1 := DriftProof.drift_interval S hS hDet hk hkn hc hu hη h 0 ⟨le_rfl, hu.1⟩ u
    ⟨hu'.1, hu'.2⟩
  rw [mul_zero, add_zero, sub_zero] at h1
  have hκ0 : 0 ≤ S.P.ksh k := S.P.ksh_nonneg k
  have hCls : 0 ≤ Eig.Cls S.P.χ := DriftProof.Cls_nonneg _
  have hCu : Eig.Cls S.P.χ * η * u * S.P.ksh k ≤ Eig.Cls S.P.χ * η * S.P.That k * S.P.ksh k :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hu'.2.trans hu.2) (mul_nonneg hCls hη)) hκ0
  have hif : (if k < S.P.n then 2 * S.rT S.P.Tpin * S.P.ksh k else 0) =
      (if k < S.P.n then 2 * S.rT S.P.Tpin else 0) * S.P.ksh k := by
    split_ifs <;> ring
  rw [hif] at h1
  linarith [show ((if k < S.P.n then 2 * S.rT S.P.Tpin else 0) + Eig.Cls S.P.χ * η * S.P.That k) *
      S.P.ksh k = (if k < S.P.n then 2 * S.rT S.P.Tpin else 0) * S.P.ksh k +
        Eig.Cls S.P.χ * η * S.P.That k * S.P.ksh k by ring]

end Relay

end NonUniqueEuler
