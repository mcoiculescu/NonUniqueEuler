import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec9.QuietRing
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec6.FieldContinuity
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec5.Majorant
import NonUniqueEuler.I.Sec5.Quiet
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.H.Sec9.Prehistory.Moment
import NonUniqueEuler.H.Sec9.Prehistory.Inner

/-!
# Proof: `lem:prehistory` (the moment `q_j` before ring `j` becomes active)

Proof of `I/Sec9/Prehistory.lean` (same declaration, statement copied verbatim). Manuscript
`09_relay.tex:1042-1101`.

1. Pointwise bound (`PrehistoryAux.pointwise`), `t ∈ [0,t♯_j]`, `τ = A_jt ∈ [0,t̄♯_j]`:
   `thm:quiet`(a) for ring `j` (`quiet_ring`) gives `S_j(t) ⊂ 𝒩₋_j ⊂ N_j`; the hypotheses give
   `D_{j+1}(t) ⊂ B_{ar_j/8}`. Then `q_j(t) = 2π pout_3[w_j(t)] + 2π pout_3[ν^in_j(t)]`
   (`PrehistoryAux.q_eq`, `H/Sec9/Prehistory/Moment.lean`), `|2π pout_3[w_j(t)]| ≤ 2³‖w_j(t)‖_{L¹}`
   (`norm_two_pi_pout_w_le`) and `|2π pout_3[ν^in_j(t)]| ≤ 4πη^in_j(A_jt)`
   (`norm_two_pi_pout_nuIn_le`, `H/Sec9/Prehistory/Inner.lean`, from `lem:coupling`(1) at `r = 1`).
2. Integral bound (`PrehistoryAux.integral_bound`): `‖w_j(τ/A_j)‖_{L¹} ≤ C_{L1}‖w_j‖_{H^{s_h}}
   ≤ C_{L1}C_Q maj_j(τ) ≤ C_{L1}C_Q e^{-σ_j(t̄♯_j-τ)}maj_j(t̄♯_j)` (`lem:regions-basic`(4),
   `MemH.l2_le`, `thm:quiet`(c), (M1) of `lem:majorant`), `∫₀^{t̄♯} e^{-(σ_j-σ_o)(t̄♯-τ)} ≤ (σ_j-σ_o)⁻¹`
   (`integral_exp_neg_le`), and `e^{σ_o(t̄♯-τ)}η^in_j(τ) ≤ e^{σ_j(t̄♯-τ)}η_j(τ)`, whose integral is
   `maj_j(t̄♯_j)`. The integrand is continuous on `[0,t̄♯_j]` (`q_continuous`, `j ≥ 2`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace PrehistoryAux

/-- `t♯_k > 0` for `k < n` when the clock is defined up to level `k+1` (`lem:clock`(1); copied
from `P/Sec9/Handoff.lean`, `HandoffAux.tsh_pos`). -/
theorem tsh_pos (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall)
    {k : ℕ} (hkn : k < P.n) (hc : P.ClockUpTo (k + 1)) : 0 < P.tsh k := by
  have hmem : k + 1 ∈ Finset.Icc (k + 1) P.n := Finset.mem_Icc.mpr ⟨le_rfl, hkn⟩
  have hord := Approx.clock_order P hP hN hG (Nat.le_add_left 1 k) hc
  have hT : 0 < P.T (k + 1) := lt_of_le_of_lt (hord.2.2.2 (k + 1) hmem) (hord.1 (k + 1) hmem)
  rw [P.tsh_eq_T_add hkn]
  have := hP.Tpin_pos
  have := hP.A_pos (k + 1)
  positivity

/-- `𝒩₋_k ⊂ N_k` (copied from `P/Sec9/Handoff.lean`, `HandoffAux.Nmk_subset_Nk`). -/
theorem Nmk_subset_Nk (P : Approx) (k : ℕ) : P.Nmk k ⊆ P.Nk k := by
  intro x hx
  have ha := zero_lt_a
  have hx' : (P.r k : ℂ)⁻¹ * x ∈ annNm := hx
  show (P.r k : ℂ)⁻¹ * x ∈ annN
  obtain ⟨h1, h2⟩ := hx'
  exact ⟨by linarith, by linarith⟩

/-- `‖w_j(t)‖_{L¹} ≤ C_{L1}‖w_j(t)‖_{H^s}` when `S_j(t) ⊂ N_j` (`lem:regions-basic`(4):
`‖w‖_{L¹} ≤ C_{L1}‖w‖_{L²}`, and `‖w‖_{L²} ≤ ‖w‖_{H^s}`). -/
theorem l1_le_CL1_normH (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 P.n) {t : ℝ} (ht : 0 ≤ t) (hS : P.PertDefined j t) (s : ℕ) :
    (eLpNorm (P.wR j t) 1 volume).toReal ≤ Rings.CL1 * Sob.normH s (P.w j t) := by
  obtain ⟨-, -, -, -, hX, -, -, hL1⟩ := P.regions_basic_four hP hN hj ht hS
  have hH : Sob.MemH s (P.w j t) := (hX s).1
  have hl2 := hH.l2_le
  have heq : eLpNorm (P.w j t) 2 volume = eLpNorm (P.wR j t) 2 volume :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun y => by simp [Approx.w])
  have hfin : eLpNorm (P.wR j t) 2 volume ≠ ⊤ := by
    rw [← heq]
    exact (Sob.memH_iff.1 hH).1.eLpNorm_ne_top
  have hCL1 : 0 ≤ Rings.CL1 := Real.sqrt_nonneg _
  calc (eLpNorm (P.wR j t) 1 volume).toReal
      ≤ (ENNReal.ofReal Rings.CL1 * eLpNorm (P.wR j t) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hL1
    _ = Rings.CL1 * Sob.l2 (P.w j t) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCL1, Sob.l2, heq]
    _ ≤ Rings.CL1 * Sob.normH s (P.w j t) := mul_le_mul_of_nonneg_left hl2 hCL1

/-- `∫₀^T e^{-c(T-τ)} dτ = (1 - e^{-cT})/c ≤ 1/c` for `c > 0`. -/
theorem integral_exp_neg_le {c T : ℝ} (hc : 0 < c) :
    ∫ τ in (0 : ℝ)..T, Real.exp (-(c * (T - τ))) ≤ 1 / c := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) T, HasDerivAt (fun τ => Real.exp (-(c * (T - τ))) / c)
      (Real.exp (-(c * (T - x)))) x := by
    intro x _
    have h1 : HasDerivAt (fun τ => -(c * (T - τ))) c x := by
      have h := ((hasDerivAt_id x).const_mul c).sub_const (c * T)
      have e : (fun τ => -(c * (T - τ))) = fun x => c * id x - c * T := by
        funext τ
        simp only [id]
        ring
      rw [e]
      simpa using h
    have h2 := h1.exp.div_const c
    have e2 : Real.exp (-(c * (T - x))) * c / c = Real.exp (-(c * (T - x))) := by
      rw [mul_div_assoc, div_self hc.ne', mul_one]
    rw [e2] at h2
    exact h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have e1 : Real.exp (-(c * (T - T))) = 1 := by simp
  have hpos : 0 < Real.exp (-(c * (T - 0))) / c := div_pos (Real.exp_pos _) hc
  rw [e1]
  linarith

/-- **The pointwise bound of `lem:prehistory`** (`09_relay.tex:1059-1085`): for `t ∈ [0,t♯_j]`,
`S_j(t) ⊂ N_j` and `|q_j(t)| ≤ C_qr(‖w_j(t)‖_{L¹} + η^in_j(A_jt))`. -/
theorem pointwise (S : Standing) (hS : S.Holds) {j : ℕ} (h : S.PrehistoryHyp j) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (S.P.tsh j)) :
    S.P.PertDefined j t ∧
      ‖S.P.q j t‖ ≤ Cqr * ((eLpNorm (S.P.wR j t) 1 volume).toReal + S.etaIn j (S.P.A j * t)) := by
  have hP := hS.valid
  have hN := hS.hN
  have hj1 : 1 ≤ j := le_trans (by norm_num) h.two_le
  have hjn := h.lt_n
  have hjI : j ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hj1, hjn.le⟩
  have hA : 0 < S.P.A j := hP.A_pos j
  have hτ : S.P.A j * t ∈ Icc (0 : ℝ) (S.P.tash j) :=
    ⟨mul_nonneg hA.le ht.1, by rw [Approx.tash_def]; exact mul_le_mul_of_nonneg_left ht.2 hA.le⟩
  have hτA : S.P.A j * t / S.P.A j = t := mul_div_cancel_left₀ t hA.ne'
  have hsupp := (quiet_ring S hS h.quiet).supp _ hτ
  rw [hτA] at hsupp
  have hpert : S.P.PertDefined j t := hsupp.trans (Nmk_subset_Nk S.P j)
  have htA : t ∈ Icc (0 : ℝ) (S.P.tash j / S.P.A j) := by
    rw [Approx.tash_def, mul_div_cancel_left₀ _ hA.ne']
    exact ht
  have hdef := h.quiet.hdef t htA
  refine ⟨hpert, ?_⟩
  rw [q_eq S.P hP hN hj1 hjn.le ht.1]
  have hw := norm_two_pi_pout_w_le S.P hP hN hjI ht.1 hpert
  have hin := norm_two_pi_pout_nuIn_le S.P hP hN hj1 hjn ht.1 hdef.1 S.Mh
  have h8 : (2 : ℝ) ^ 3 ≤ Cqr := le_max_left _ _
  have h4 : 4 * Real.pi ≤ Cqr := le_max_right _ _
  have hL : 0 ≤ (eLpNorm (S.P.wR j t) 1 volume).toReal := ENNReal.toReal_nonneg
  have hE : 0 ≤ S.etaIn j (S.P.A j * t) := S.etaIn_nonneg _ _
  calc ‖2 * Real.pi * BS.pout 3 (S.P.w j t) +
        2 * Real.pi * BS.pout 3 (fun y => ((S.P.nuIn j t y : ℝ) : ℂ))‖
      ≤ ‖2 * Real.pi * BS.pout 3 (S.P.w j t)‖ +
          ‖2 * Real.pi * BS.pout 3 (fun y => ((S.P.nuIn j t y : ℝ) : ℂ))‖ := norm_add_le _ _
    _ ≤ 2 ^ 3 * (eLpNorm (S.P.wR j t) 1 volume).toReal +
          4 * Real.pi * S.etaIn j (S.P.A j * t) := add_le_add hw hin
    _ ≤ Cqr * (eLpNorm (S.P.wR j t) 1 volume).toReal + Cqr * S.etaIn j (S.P.A j * t) :=
        add_le_add (mul_le_mul_of_nonneg_right h8 hL) (mul_le_mul_of_nonneg_right h4 hE)
    _ = Cqr * ((eLpNorm (S.P.wR j t) 1 volume).toReal + S.etaIn j (S.P.A j * t)) := by ring

/-- **The integral bound of `lem:prehistory`** (`09_relay.tex:1086-1101`). -/
theorem integral_bound (S : Standing) (hS : S.Holds) {j : ℕ} (h : S.PrehistoryHyp j) {σo : ℝ}
    (hσo : σo < S.P.sigma j) :
    IntegrableOn (fun τ => Real.exp (σo * (S.P.tash j - τ)) * ‖S.P.q j (τ / S.P.A j)‖)
        (Icc 0 (S.P.tash j)) ∧
      ∫ τ in (0 : ℝ)..S.P.tash j, Real.exp (σo * (S.P.tash j - τ)) * ‖S.P.q j (τ / S.P.A j)‖ ≤
        Cqr * (Rings.CL1 * S.CQ / (S.P.sigma j - σo) + 1) * S.maj j (S.P.tash j) := by
  have hP := hS.valid
  have hN := hS.hN
  have hχ := hS.admissible
  have hj1 : 1 ≤ j := le_trans (by norm_num) h.two_le
  have hj2 := h.two_le
  have hjn := h.lt_n
  have hjI : j ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hj1, hjn.le⟩
  obtain ⟨hsigb, -, hGs, hlev⟩ := standing_levels S hS
  have hσ : 0 < S.P.sigma j := lt_of_lt_of_le hsigb (hlev j hjI).2.2
  have hA : 0 < S.P.A j := hP.A_pos j
  have htsh : 0 < S.P.tsh j := tsh_pos S.P hP hN hGs hjn h.clock
  have hTA : S.P.tash j / S.P.A j = S.P.tsh j := by
    rw [Approx.tash_def]
    exact mul_div_cancel_left₀ _ hA.ne'
  have hdef : ∀ t ∈ Icc (0 : ℝ) (S.P.tsh j), S.P.HDefined j t := fun t ht =>
    h.quiet.hdef t (by rwa [hTA])
  have hQC := quiet_ring S hS h.quiet
  set T := S.P.tash j with hTdef
  have hT : 0 ≤ T := (mul_pos hA htsh).le
  -- continuity of `η_j` on `[0, T]`
  obtain ⟨-, -, hcEta⟩ := Approx.eta_continuous S.P hP hN hj1 hjn.le (t₁ := 0)
    (t₂ := S.P.tsh j) le_rfl S.Mh
  have hIcc : Icc (S.P.A j * 0) (S.P.A j * S.P.tsh j) = Icc 0 T := by
    rw [mul_zero, hTdef, Approx.tash_def]
  have hηc : ContinuousOn (S.P.eta S.Mh j) (Icc 0 T) := by
    have := hcEta hdef
    rwa [hIcc] at this
  -- the constants and the majorant
  have hCQ : 0 ≤ S.CQ :=
    (OneRing.quietConsts_spec (OneRing.quiet S.P.χ hχ hN hS.three_le_sh S.two_le_NQ
      (S.Lam_le_NQ_mul hsigb))).2.1
  have hCL1 : 0 ≤ Rings.CL1 := Real.sqrt_nonneg _
  have hmaj := (OneRing.majorant_of_pos hσ hηc.integrableOn_Icc
    (fun τ _ => S.P.eta_nonneg S.Mh j τ)).1
  -- continuity of the integrand
  have hqc : ContinuousOn (S.P.q j) (Ici 0) := by
    have := Approx.q_continuous S.P hP hN (k := j - 1) (by omega) (by omega)
    rwa [Nat.sub_add_cancel hj1] at this
  have hqc' : ContinuousOn (fun τ => S.P.q j (τ / S.P.A j)) (Icc 0 T) :=
    hqc.comp (continuousOn_id.div_const _) (fun τ hτ => div_nonneg hτ.1 hA.le)
  have hLc : ContinuousOn (fun τ => Real.exp (σo * (T - τ)) * ‖S.P.q j (τ / S.P.A j)‖)
      (Icc 0 T) :=
    (Continuous.continuousOn (by fun_prop)).mul hqc'.norm
  have hint : IntegrableOn (fun τ => Real.exp (σo * (T - τ)) * ‖S.P.q j (τ / S.P.A j)‖)
      (Icc 0 T) := hLc.integrableOn_Icc
  refine ⟨hint, ?_⟩
  set c := S.P.sigma j - σo with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  set m := S.maj j T with hm
  have hm0 : 0 ≤ m := by
    show 0 ≤ OneRing.maj (S.P.sigma j) (S.P.eta S.Mh j) T
    unfold OneRing.maj
    exact intervalIntegral.integral_nonneg hT fun v _ =>
      mul_nonneg (Real.exp_pos _).le (S.P.eta_nonneg _ _ _)
  -- the pointwise majorant `F`
  have hpt : ∀ τ ∈ Icc 0 T, Real.exp (σo * (T - τ)) * ‖S.P.q j (τ / S.P.A j)‖ ≤
      Cqr * (Rings.CL1 * S.CQ * m * Real.exp (-(c * (T - τ))) +
        Real.exp (S.P.sigma j * (T - τ)) * S.P.eta S.Mh j τ) := by
    intro τ hτ
    have htτ : τ / S.P.A j ∈ Icc (0 : ℝ) (S.P.tsh j) :=
      ⟨div_nonneg hτ.1 hA.le, by rw [← hTA]; exact div_le_div_of_nonneg_right hτ.2 hA.le⟩
    obtain ⟨hpert, hq⟩ := pointwise S hS h htτ
    have hAτ : S.P.A j * (τ / S.P.A j) = τ := mul_div_cancel₀ τ hA.ne'
    rw [hAτ] at hq
    have hL1 := l1_le_CL1_normH S.P hP hN hjI htτ.1 hpert S.sh
    have hbd := hQC.bound τ hτ
    have hmτ : Real.exp (S.P.sigma j * (T - τ)) * S.maj j τ ≤ m :=
      (hmaj τ T hτ.1 hτ.2 le_rfl).1
    have hw : (eLpNorm (S.P.wR j (τ / S.P.A j)) 1 volume).toReal ≤
        Rings.CL1 * (S.CQ * S.maj j τ) :=
      hL1.trans (mul_le_mul_of_nonneg_left hbd hCL1)
    have hexp : Real.exp (σo * (T - τ)) =
        Real.exp (-(c * (T - τ))) * Real.exp (S.P.sigma j * (T - τ)) := by
      rw [← Real.exp_add]
      congr 1
      rw [hc]
      ring
    have hE1 : Real.exp (σo * (T - τ)) * S.maj j τ ≤ Real.exp (-(c * (T - τ))) * m := by
      rw [hexp, mul_assoc]
      exact mul_le_mul_of_nonneg_left hmτ (Real.exp_pos _).le
    have hE2 : Real.exp (σo * (T - τ)) * S.etaIn j τ ≤
        Real.exp (S.P.sigma j * (T - τ)) * S.P.eta S.Mh j τ := by
      have hle : S.etaIn j τ ≤ S.P.eta S.Mh j τ := by
        have := S.etaOut_nonneg j τ
        have e := S.eta_eq_add j τ
        rw [S.eta_def] at e
        linarith
      exact mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hσo.le
        (sub_nonneg.2 hτ.2))) hle (S.etaIn_nonneg j τ) (Real.exp_pos _).le
    have hCqr := Cqr_pos.le
    have hex := (Real.exp_pos (σo * (T - τ))).le
    calc Real.exp (σo * (T - τ)) * ‖S.P.q j (τ / S.P.A j)‖
        ≤ Real.exp (σo * (T - τ)) *
            (Cqr * ((eLpNorm (S.P.wR j (τ / S.P.A j)) 1 volume).toReal + S.etaIn j τ)) :=
          mul_le_mul_of_nonneg_left hq hex
      _ ≤ Real.exp (σo * (T - τ)) *
            (Cqr * (Rings.CL1 * (S.CQ * S.maj j τ) + S.etaIn j τ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hw le_rfl) hCqr) hex
      _ = Cqr * (Rings.CL1 * S.CQ * (Real.exp (σo * (T - τ)) * S.maj j τ) +
            Real.exp (σo * (T - τ)) * S.etaIn j τ) := by ring
      _ ≤ Cqr * (Rings.CL1 * S.CQ * (Real.exp (-(c * (T - τ))) * m) +
            Real.exp (S.P.sigma j * (T - τ)) * S.P.eta S.Mh j τ) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left hE1 (mul_nonneg hCL1 hCQ)) hE2) hCqr
      _ = Cqr * (Rings.CL1 * S.CQ * m * Real.exp (-(c * (T - τ))) +
            Real.exp (S.P.sigma j * (T - τ)) * S.P.eta S.Mh j τ) := by ring
  -- integrate
  have hi1 : IntervalIntegrable (fun τ => Real.exp (-(c * (T - τ)))) volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi2 : IntervalIntegrable (fun τ => Real.exp (S.P.sigma j * (T - τ)) * S.P.eta S.Mh j τ)
      volume 0 T := by
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 ?_
    exact ((Continuous.continuousOn (by fun_prop)).mul hηc).integrableOn_Icc
  have hi1' : IntervalIntegrable (fun τ => Rings.CL1 * S.CQ * m * Real.exp (-(c * (T - τ))))
      volume 0 T := hi1.const_mul _
  have hFint : IntervalIntegrable (fun τ => Cqr * (Rings.CL1 * S.CQ * m *
      Real.exp (-(c * (T - τ))) + Real.exp (S.P.sigma j * (T - τ)) * S.P.eta S.Mh j τ))
      volume 0 T := (hi1'.add hi2).const_mul _
  have hmajT : ∫ τ in (0 : ℝ)..T, Real.exp (S.P.sigma j * (T - τ)) * S.P.eta S.Mh j τ = m :=
    rfl
  have hI := integral_exp_neg_le (T := T) hc0
  calc ∫ τ in (0 : ℝ)..T, Real.exp (σo * (T - τ)) * ‖S.P.q j (τ / S.P.A j)‖
      ≤ ∫ τ in (0 : ℝ)..T, Cqr * (Rings.CL1 * S.CQ * m * Real.exp (-(c * (T - τ))) +
          Real.exp (S.P.sigma j * (T - τ)) * S.P.eta S.Mh j τ) :=
        intervalIntegral.integral_mono_on hT
          ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 hint) hFint hpt
    _ = Cqr * (Rings.CL1 * S.CQ * m * (∫ τ in (0 : ℝ)..T, Real.exp (-(c * (T - τ)))) + m) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi1' hi2,
          intervalIntegral.integral_const_mul, hmajT]
    _ ≤ Cqr * (Rings.CL1 * S.CQ * m * (1 / c) + m) := by
        have h0 : 0 ≤ Rings.CL1 * S.CQ * m := mul_nonneg (mul_nonneg hCL1 hCQ) hm0
        exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hI h0) le_rfl)
          Cqr_pos.le
    _ = Cqr * (Rings.CL1 * S.CQ / c + 1) * m := by ring

end PrehistoryAux

/-- **`lem:prehistory`** (`09_relay.tex:1042-1057`). Assume (SA) and the hypotheses
`S.PrehistoryHyp j` (`2 ≤ j < n`, clock up to level `j+1`, `thm:quiet` hypotheses for ring `j` on
`[0, t̄♯_j]`). Then `|q_j(t)| ≤ C_qr(‖w_j(t)‖_{L¹} + η^in_j(A_jt))` on `[0, t♯_j]`, and for every
`σ_o < σ_j` the weighted integral of `|q_j(τ/A_j)|` over `[0, t̄♯_j]` (integrable) is at most
`C_qr(C_{L1}C_Q/(σ_j-σ_o) + 1) maj_j(t̄♯_j)`. -/
theorem prehistory (S : Standing) (hS : S.Holds) {j : ℕ} (h : S.PrehistoryHyp j) :
    (∀ t ∈ Icc (0 : ℝ) (S.P.tsh j),
      ‖S.P.q j t‖ ≤ Cqr * ((eLpNorm (S.P.wR j t) 1 volume).toReal + S.etaIn j (S.P.A j * t))) ∧
    ∀ σo : ℝ, σo < S.P.sigma j →
      IntegrableOn (fun τ => Real.exp (σo * (S.P.tash j - τ)) * ‖S.P.q j (τ / S.P.A j)‖)
        (Icc 0 (S.P.tash j)) ∧
      ∫ τ in (0 : ℝ)..S.P.tash j, Real.exp (σo * (S.P.tash j - τ)) * ‖S.P.q j (τ / S.P.A j)‖ ≤
        Cqr * (Rings.CL1 * S.CQ / (S.P.sigma j - σo) + 1) * S.maj j (S.P.tash j) :=
  ⟨fun _ ht => (PrehistoryAux.pointwise S hS h ht).2,
    fun _ hσo => PrehistoryAux.integral_bound S hS h hσo⟩

end Relay

end NonUniqueEuler
