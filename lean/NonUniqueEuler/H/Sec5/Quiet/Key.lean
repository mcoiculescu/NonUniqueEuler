import NonUniqueEuler.H.Sec5.Quiet.Basic
import NonUniqueEuler.H.Sec5.Quiet.Estimates
import NonUniqueEuler.I.Sec5.Energy
import NonUniqueEuler.I.Sec5.Bilinear
import NonUniqueEuler.I.Sec5.Majorant
import NonUniqueEuler.I.Sec5.ReductionEq
import NonUniqueEuler.I.Sec5.ReductionField
import NonUniqueEuler.I.Sec5.ReductionVelocity
import NonUniqueEuler.I.Sec4.PropU

/-!
# Helpers for `thm:quiet`: the comparison step on `[0,t']`

Helper of `P/Sec5/Quiet.lean` (fully proved). The heart of the continuity argument of
`thm:quiet` (`05_single_ring.tex:514-549`): if on `[0,t']` the trajectories of the ring move
radially by at most `a/8` and `‖w‖_{H^{s_h}} ≤ 1`, then on `[0,t']` the improved bounds `eq:Q-b`
and the radial displacement bound `δ_r ≤ C_Δ maj` hold (`key`).

* `sigb_facts`: `0 < σ_b ≤ σ(G)` on `[0,G₁]` (`prop:U`(a));
* `eta_integrableOn`: a measurable `η` with `0 ≤ η ≤ 1` on `[0,T]` is integrable there;
* `key`: the comparison step.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.QuietH

open RingData Sect Sob

/-- `0 < σ_b ≤ σ(G)` for `G ∈ [0,G₁]` (`prop:U`(a)). -/
theorem sigb_facts (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) : 0 < Eig.sigb χ ∧ Eig.sigb χ ≤ Eig.sigma χ G := by
  obtain ⟨-, -, ⟨G₀, -, hb, hmin⟩, hpos, -⟩ := Eig.propU_a χ hχ hN
  refine ⟨by linarith, ?_⟩
  rw [hb]
  exact hmin G hG

/-- A measurable `η` with `0 ≤ η ≤ 1` on `[0,T]` is integrable on `[0,T]`. -/
theorem eta_integrableOn {η : ℝ → ℝ} {T : ℝ} (hη : Measurable η)
    (hb : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ η t ∧ η t ≤ 1) : IntegrableOn η (Icc 0 T) := by
  refine IntegrableOn.of_bound measure_Icc_lt_top hη.aestronglyMeasurable 1 ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall fun t ht => by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hb t ht]

/-- `N ⊆ N'`. -/
theorem annN_subset_annN' (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) : annN ⊆ annN' := by
  have ha0 : 0 < a := (ringFacts_of_admissible hχ).2.2.2.2.2.2.1
  intro x hx
  rw [mem_annN] at hx
  rw [mem_annN']
  constructor <;> linarith [hx.1, hx.2]

/-- **The comparison step of `thm:quiet`** (`05_single_ring.tex:514-549`). Let `w_app` be the
approximate solution (`I/Sec5/Quiet/Approx.lean`, constant `C_app`) and `C_Q ≥ C_app(2 + σ_b⁻¹)`.
If `0 < t' ≤ T`, every trajectory of `ω_r` moves radially by at most `a/8` on `[0,t']` and
`‖w‖_{H^{s_h}} ≤ 1` on `[0,t']`, then for `τ ∈ [0,t']`: every trajectory moves radially by at most
`C_Δ maj(τ)` on `[0,τ]`, `C_Δ = 1 + C_BS C_Q/σ_b`, `‖w(τ)‖_{H^{s_h}} ≤ C_Q maj(τ)` and
`‖w(τ) - wlin(τ)‖_{H^{s_h}} ≤ C_Q maj(τ)²`. -/
theorem key (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {sh NQ : ℕ} (hs : 3 ≤ sh) (hQ : 2 ≤ NQ) (hΛ : Lam χ sh ≤ NQ * Eig.sigb χ)
    {c : RingConfig} {T : ℝ} (hc : c.Hyp T) (hr : c.ring0 = ringPhi χ)
    (hG : c.G ∈ Icc (0 : ℝ) Gbar) {η : ℝ → ℝ} (hηm : Measurable η)
    (hh : ∀ t ∈ Icc (0 : ℝ) T, normCk (Mh sh NQ) annN' (c.h t) ≤ η t ∧ η t ≤ 1)
    (hmaj1 : ∀ t ∈ Icc (0 : ℝ) T, maj (Eig.sigma χ c.G) η t ≤ 1)
    {Capp CQ : ℝ} (hCapp : 0 ≤ Capp) (hCQ : Capp * (2 + (Eig.sigb χ)⁻¹) ≤ CQ)
    {wapp wapp' : ℝ → ℂ → ℂ} (happ : PathC (sh + 1) T wapp) (happ' : PathC1 sh T wapp wapp')
    (hreal : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure ℂ), (wapp t x).im = 0)
    (hzero : wapp 0 =ᵐ[volume] (0 : ℂ → ℂ))
    (hbd : ∀ t ∈ Icc (0 : ℝ) T,
      Sob.normH (sh + 1) (wapp t) ≤ Capp * maj (Eig.sigma χ c.G) η t ∧
      Sob.normH sh (wapp t - (wlin χ sh c.G c.h t).fn) ≤
        Capp * maj (Eig.sigma χ c.G) η t ^ 2 ∧
      Sob.normH sh (Rapp χ c.G c.h wapp wapp' t) ≤
        Capp * (maj (Eig.sigma χ c.G) η t ^ (NQ + 1) + η t * maj (Eig.sigma χ c.G) η t ^ NQ))
    (hwapp1 : ∀ t ∈ Icc (0 : ℝ) T, Sob.normH (sh + 1) (wapp t) ≤ 1)
    {t' : ℝ} (ht' : 0 < t') (ht'T : t' ≤ T) (hmove : c.MovesRadially t' (a / 8))
    (hw1 : ∀ τ ∈ Icc (0 : ℝ) t', Sob.normH sh (c.w χ τ) ≤ 1) :
    ∀ τ ∈ Icc (0 : ℝ) t',
      c.MovesRadially τ ((1 + CBS * CQ / Eig.sigb χ) * maj (Eig.sigma χ c.G) η τ) ∧
      Sob.normH sh (c.w χ τ) ≤ CQ * maj (Eig.sigma χ c.G) η τ ∧
      Sob.normH sh (c.w χ τ - (wlin χ sh c.G c.h τ).fn) ≤
        CQ * maj (Eig.sigma χ c.G) η τ ^ 2 := by
  obtain ⟨hσb, hσbσ⟩ := sigb_facts χ hχ hN hG
  set σ := Eig.sigma χ c.G with hσdef
  set σb := Eig.sigb χ with hσbdef
  have hσ : 0 < σ := lt_of_lt_of_le hσb hσbσ
  have hη0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ η t := fun t ht =>
    (normCk_nonneg _ _ _).trans (hh t ht).1
  have hηint : IntegrableOn η (Icc 0 T) :=
    eta_integrableOn hηm (fun t ht => ⟨hη0 t ht, (hh t ht).2⟩)
  obtain ⟨hM, hmono⟩ := majorant_of_pos hσ hηint hη0
  set m := maj σ η with hmdef
  have hm0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ m t := by
    intro t ht
    have h := hmono ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
    rwa [hmdef, maj_zero] at h
  have hmint : ∀ τ ∈ Icc (0 : ℝ) T, IntervalIntegrable m volume 0 τ := by
    intro τ hτ
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hτ.1]
    exact hmono.mono (Icc_subset_Icc le_rfl hτ.2)
  have hηint' : ∀ τ ∈ Icc (0 : ℝ) T, IntervalIntegrable η volume 0 τ := by
    intro τ hτ
    refine IntegrableOn.intervalIntegrable (hηint.mono_set ?_)
    rw [uIcc_of_le hτ.1]
    exact Icc_subset_Icc le_rfl hτ.2
  -- the support stays in `N` on `[0,t']`, so `eq:ring` holds there
  have hsupp : c.RingSupportedIn t' annN := (supp_of_movesRadially hχ hc hr hmove).2 le_rfl
  have hct : c.Hyp t' := hc.mono ht' ht'T
  have hpe := (reduction_eq χ hχ hct hsupp).2
  have hX : ∀ k : ℕ, ∀ τ ∈ Icc (0 : ℝ) t', Lin.MemXFn k (c.w χ τ) :=
    fun k τ hτ => (hpe k).1.1 τ hτ
  -- the field
  have hfield := reduction_field hc
  have hCk : ∀ τ ∈ Icc (0 : ℝ) T, MemCk (Mh sh NQ) annN' (c.h τ) :=
    fun τ hτ => (hfield.2 (Mh sh NQ)).1 τ hτ
  have hTt : ∀ τ ∈ Icc (0 : ℝ) t', τ ∈ Icc (0 : ℝ) T := fun τ hτ => ⟨hτ.1, hτ.2.trans ht'T⟩
  have hh1 : ∀ τ ∈ Icc (0 : ℝ) t', normCk (sh + 1) annN' (c.h τ) ≤ 1 := by
    intro τ hτ
    have hτT := hTt τ hτ
    calc normCk (sh + 1) annN' (c.h τ) ≤ normCk (Mh sh NQ) annN' (c.h τ) :=
          normCk_mono_order (hCk τ hτT) (by rw [Mh_eq]; omega)
      _ ≤ η τ := (hh τ hτT).1
      _ ≤ 1 := (hh τ hτT).2
  -- `lem:energy` on `[0,t']`
  have hE := energy χ hχ hN hs hct hG hsupp (PathC.mono happ ht'T) (PathC1.mono happ' ht'T)
    (fun τ hτ => hreal τ (hTt τ hτ)) hw1 (fun τ hτ => hwapp1 τ (hTt τ hτ)) hh1
  have hw0 : c.w χ 0 = 0 := by
    rw [(RingConfig.setting_sol_eq_parts hc).2.2.2.2.2 χ]
    funext x
    simp [RingConfig.pert0, hr]
  have hv0 : Sob.normH sh (c.w χ 0 - wapp 0) = 0 := by
    apply normH_eq_zero_of_ae
    filter_upwards [hzero] with x hx
    simp [hw0, hx]
  -- `eq:Q-v`
  have hv : ∀ τ ∈ Icc (0 : ℝ) t',
      Sob.normH sh (c.w χ τ - wapp τ) ≤ Capp * (1 + σb⁻¹) * m τ ^ (NQ + 1) := by
    intro τ hτ
    have hτT := hTt τ hτ
    have h1 := hE τ hτ
    rw [hv0, mul_zero, zero_add] at h1
    refine h1.trans ?_
    have hsub : ∀ t ∈ Icc (0 : ℝ) τ, t ∈ Icc (0 : ℝ) T := fun t ht => ⟨ht.1, ht.2.trans hτT.2⟩
    have hΛσ : Lam χ sh ≤ (NQ : ℝ) * σ :=
      hΛ.trans (mul_le_mul_of_nonneg_left hσbσ (Nat.cast_nonneg _))
    exact energy_integral_le (R := fun t => Sob.normH sh (Rapp χ c.G c.h wapp wapp' t))
      hσb hσbσ hΛσ hCapp hτ.1 (fun t ht => hm0 t (hsub t ht)) (fun t ht => hη0 t (hsub t ht))
      (fun t ht => (hM t τ ht.1 ht.2 hτT.2).1) (hM 0 τ le_rfl hτ.1 hτT.2).2.1
      (hM 0 τ le_rfl hτ.1 hτT.2).2.2 (hmint τ hτT) (hηint' τ hτT)
      (fun t ht => (hbd t (hsub t ht)).2.2)
  -- `eq:Q-b`
  have hσbinv : 0 ≤ σb⁻¹ := inv_nonneg.2 hσb.le
  have hb : ∀ τ ∈ Icc (0 : ℝ) t', Sob.normH sh (c.w χ τ) ≤ CQ * m τ ∧
      Sob.normH sh (c.w χ τ - (wlin χ sh c.G c.h τ).fn) ≤ CQ * m τ ^ 2 := by
    intro τ hτ
    have hτT := hTt τ hτ
    have hvτ := hv τ hτ
    obtain ⟨hb1, hb2, -⟩ := hbd τ hτT
    have hm0τ := hm0 τ hτT
    have hm1τ := hmaj1 τ hτT
    have hmemw : MemH sh (c.w χ τ) := (hX sh τ hτ).1
    have hmemapp1 : MemH (sh + 1) (wapp τ) := (happ.1 τ hτT).1
    have hmemapp : MemH sh (wapp τ) := hmemapp1.mono_order (Nat.le_succ sh)
    have hmemlin : MemH sh (wlin χ sh c.G c.h τ).fn := (memH_Yfn _).1
    have hd1 := hmemw.sub hmemapp
    have hd2 := hmemapp.sub hmemlin
    have hCa : 0 ≤ Capp * (1 + σb⁻¹) := mul_nonneg hCapp (by linarith)
    have hp1 : m τ ^ (NQ + 1) ≤ m τ := by
      simpa using pow_le_pow_of_le_one hm0τ hm1τ (show 1 ≤ NQ + 1 by omega)
    have hp2 : m τ ^ (NQ + 1) ≤ m τ ^ 2 := pow_le_pow_of_le_one hm0τ hm1τ (by omega)
    constructor
    · have htri := (hd1.1.add hmemapp).2
      have heq : (c.w χ τ - wapp τ) + wapp τ = c.w χ τ := sub_add_cancel _ _
      rw [heq] at htri
      have hmono' : Sob.normH sh (wapp τ) ≤ Sob.normH (sh + 1) (wapp τ) :=
        hmemapp1.normH_mono (Nat.le_succ sh)
      calc Sob.normH sh (c.w χ τ)
          ≤ Sob.normH sh (c.w χ τ - wapp τ) + Sob.normH sh (wapp τ) := htri
        _ ≤ Capp * (1 + σb⁻¹) * m τ ^ (NQ + 1) + Capp * m τ := add_le_add hvτ (hmono'.trans hb1)
        _ ≤ Capp * (1 + σb⁻¹) * m τ + Capp * m τ := by
            have := mul_le_mul_of_nonneg_left hp1 hCa
            linarith
        _ = Capp * (2 + σb⁻¹) * m τ := by ring
        _ ≤ CQ * m τ := mul_le_mul_of_nonneg_right hCQ hm0τ
    · have htri := (hd1.1.add hd2.1).2
      have heq : (c.w χ τ - wapp τ) + (wapp τ - (wlin χ sh c.G c.h τ).fn) =
          c.w χ τ - (wlin χ sh c.G c.h τ).fn := sub_add_sub_cancel _ _ _
      rw [heq] at htri
      calc Sob.normH sh (c.w χ τ - (wlin χ sh c.G c.h τ).fn)
          ≤ Sob.normH sh (c.w χ τ - wapp τ) +
              Sob.normH sh (wapp τ - (wlin χ sh c.G c.h τ).fn) := htri
        _ ≤ Capp * (1 + σb⁻¹) * m τ ^ (NQ + 1) + Capp * m τ ^ 2 := add_le_add hvτ hb2
        _ ≤ Capp * (1 + σb⁻¹) * m τ ^ 2 + Capp * m τ ^ 2 := by
            have := mul_le_mul_of_nonneg_left hp2 hCa
            linarith
        _ = Capp * (2 + σb⁻¹) * m τ ^ 2 := by ring
        _ ≤ CQ * m τ ^ 2 := mul_le_mul_of_nonneg_right hCQ (sq_nonneg _)
  -- the radial displacement
  have hCQ0 : 0 ≤ CQ := le_trans (mul_nonneg hCapp (by linarith)) hCQ
  have hCBS := CBS_pos
  have hNN' := annN_subset_annN' χ hχ
  have hrad : ∀ τ ∈ Icc (0 : ℝ) t', ∀ y ∈ tsupport c.ring0,
      |‖c.flow τ y‖ - ‖y‖| ≤ (1 + CBS * CQ / σb) * m τ := by
    intro τ hτ y hy
    have hτT := hTt τ hτ
    have hin : ∀ τ'' ∈ Icc (0 : ℝ) τ, c.flow τ'' y ∈ annN' := by
      intro τ'' hτ''
      have hτ''t : τ'' ∈ Icc (0 : ℝ) t' := ⟨hτ''.1, hτ''.2.trans hτ.2⟩
      have hmem : c.flow τ'' y ∈ tsupport (c.ringPart τ'') := by
        rw [(RingConfig.setting_tsupport_parts hc τ'').1]
        exact mem_image_of_mem _ hy
      exact hNN' (hsupp τ'' hτ''t hmem)
    have hformula := (reduction_velocity χ hχ hc).2.2 τ hτT y hin
    rw [hformula]
    refine radial_integral_le (A := CBS * CQ) hσb hσbσ (mul_nonneg hCBS.le hCQ0) hτ.1
      (hm0 τ hτT) (hM 0 τ le_rfl hτ.1 hτT.2).2.1 (hM 0 τ le_rfl hτ.1 hτT.2).2.2
      (hmint τ hτT) (hηint' τ hτT) ?_
    intro τ'' hτ''
    have hτ''t : τ'' ∈ Icc (0 : ℝ) t' := ⟨hτ''.1.le, hτ''.2.trans hτ.2⟩
    have hτ''T := hTt τ'' hτ''t
    have hx : c.flow τ'' y ∈ annN' := hin τ'' ⟨hτ''.1.le, hτ''.2⟩
    refine (abs_radComp_le _ _).trans ((norm_add_le _ _).trans ?_)
    have h1 : ‖c.h τ'' (c.flow τ'' y)‖ ≤ η τ'' :=
      (norm_le_normCk (hCk τ'' hτ''T) hx).trans (hh τ'' hτ''T).1
    have h2 : ‖velocity (fun z => c.ringPart τ'' z - ringPhi χ z) (c.flow τ'' y)‖ ≤
        CBS * (CQ * m τ'') := by
      rw [← bsNorm_w]
      have hBS := bilinear_BS (k := 2) le_rfl (hX (2 + 1) τ'' hτ''t) (c.flow τ'' y) hx.2
      have hmono1 : Sob.normH 1 (c.w χ τ'') ≤ Sob.normH sh (c.w χ τ'') :=
        (hX sh τ'' hτ''t).1.normH_mono (by omega)
      calc bsNorm (c.w χ τ'') (c.flow τ'' y) ≤ CBS * Sob.normH 1 (c.w χ τ'') := hBS
        _ ≤ CBS * (CQ * m τ'') :=
            mul_le_mul_of_nonneg_left (hmono1.trans (hb τ'' hτ''t).1) hCBS.le
    nlinarith
  -- conclusion
  intro τ hτ
  have hτT := hTt τ hτ
  refine ⟨?_, (hb τ hτ).1, (hb τ hτ).2⟩
  intro y hy τ'' hτ''
  have hτ''t : τ'' ∈ Icc (0 : ℝ) t' := ⟨hτ''.1, hτ''.2.trans hτ.2⟩
  refine (hrad τ'' hτ''t y hy).trans ?_
  have hCΔ : 0 ≤ 1 + CBS * CQ / σb :=
    add_nonneg zero_le_one (div_nonneg (mul_nonneg hCBS.le hCQ0) hσb.le)
  exact mul_le_mul_of_nonneg_left (hmono ⟨hτ''.1, hτ''.2.trans hτT.2⟩ hτT hτ''.2) hCΔ

end NonUniqueEuler.OneRing.QuietH
