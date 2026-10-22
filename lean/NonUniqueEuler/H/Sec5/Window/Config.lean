import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.Setting
import NonUniqueEuler.I.Sec5.ReductionVelocity
import NonUniqueEuler.I.Sec5.ReductionField
import NonUniqueEuler.I.Sec5.ReductionEq
import NonUniqueEuler.I.Sec5.Bilinear
import NonUniqueEuler.I.SmoothB.SmoothFlow
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.Sobolev.Paths
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import Mathlib.Topology.Order.Compact

/-!
# Helpers for `lem:window`: facts about the configuration

Helper file of `P/Sec5/Window.lean`. Fully proved from
interface files (`I/Sec5/Setting`, `I/Sec5/ReductionVelocity`, `I/Sec5/ReductionField`,
`I/Sec5/ReductionEq`, `I/Sec5/Bilinear`, `I/SmoothB/SmoothFlow`, `I/Sec4/RingFacts`,
`I/Infra/Sobolev/*`):
* `w(t) = ω_r(t) - Φ` is smooth with compact support, in every `H^k`, and
  `t ↦ ‖w(t)‖_{H^k}` is continuous (`thm:smooth`; `05_single_ring.tex:858-860`);
* the largest radial displacement `δ_r(t)` at time `t` (`dispFn`) is continuous, and its relation
  to `RingConfig.MovesRadially` (`05_single_ring.tex:800-802`);
* `w(0) = ω_r(0) - Φ ∈ X^k` when `supp ω_r(0) ⊂ N`;
* the support bookkeeping of `lem:window` (`05_single_ring.tex:803-806`: a radial displacement
  `≤ a/16` keeps `supp ω_r(u)` in `{51a/64 ≤ |y| ≤ 5/4 + 5a/64} ⊂ N`);
* the displacement bound (`05_single_ring.tex:846-855`, `lem:reduction`(2) and
  `lem:bilinear`(4)): `|Φ_τ(y)| - |y|` is bounded by `∫₀^τ (‖h‖_{C^0(N')} + C_BS‖w‖_{H^1})`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler

namespace OneRing

open RingData

namespace WindowH

variable {c : RingConfig} {T : ℝ}

/-! ### Smoothness and the flow -/

theorem isSmoothDatum (hc : c.Hyp T) : ∃ R₀ : ℝ, Smooth.IsSmoothDatum c.datum R₀ := by
  obtain ⟨R₀, hR₀⟩ := hc.datum_hasCompactSupport.isCompact.isBounded.subset_ball 0
  exact ⟨R₀, ⟨hc.datum_contDiff, hR₀⟩⟩

theorem continuous_flow_uncurry (hc : c.Hyp T) :
    Continuous (fun p : ℝ × ℂ => c.flow p.1 p.2) := by
  obtain ⟨R₀, hD⟩ := isSmoothDatum hc
  exact (Smooth.flow_contDiff hD).1.continuous

theorem continuous_flow (hc : c.Hyp T) (t : ℝ) : Continuous (c.flow t) :=
  (continuous_flow_uncurry hc).comp (continuous_const.prodMk continuous_id)

theorem isCompact_tsupport_ring0 (hc : c.Hyp T) : IsCompact (tsupport c.ring0) :=
  (RingConfig.setting_parts_smooth hc).1.2.isCompact

theorem hasCompactSupport_ringPart (hc : c.Hyp T) (t : ℝ) :
    HasCompactSupport (c.ringPart t) := by
  rw [HasCompactSupport, (RingConfig.setting_tsupport_parts hc t).1]
  exact (isCompact_tsupport_ring0 hc).image (continuous_flow hc t)

theorem flow_zero (hc : c.Hyp T) (y : ℂ) : c.flow 0 y = y :=
  (RingConfig.setting_sol_eq_parts hc).2.2.2.1 y

theorem w_zero (hc : c.Hyp T) (χ : ℝ → ℝ) : c.w χ 0 = c.pert0 χ :=
  (RingConfig.setting_sol_eq_parts hc).2.2.2.2.2 χ

/-- `(t, x) ↦ w(t, x)` is smooth. -/
theorem contDiff_w {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hc : c.Hyp T) :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => c.w χ p.1 p.2) := by
  have h1 := (RingConfig.setting_parts_smooth hc).2.2.2.1
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ringPhi χ p.2) :=
    (ringFacts_of_admissible hχ).1.comp contDiff_snd
  exact Complex.ofRealCLM.contDiff.comp (h1.sub h2)

theorem contDiff_w_at {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hc : c.Hyp T) (t : ℝ) :
    ContDiff ℝ ∞ (c.w χ t) :=
  (contDiff_w hχ hc).comp (contDiff_const.prodMk contDiff_id)

theorem hasCompactSupport_w {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hc : c.Hyp T) (t : ℝ) :
    HasCompactSupport (c.w χ t) := by
  have hr := hasCompactSupport_ringPart hc t
  have hΦ : HasCompactSupport (ringPhi χ) := (ringFacts_of_admissible hχ).2.1
  exact (hr.sub hΦ).comp_left (g := Complex.ofReal) Complex.ofReal_zero

theorem memH_w {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hc : c.Hyp T) (t : ℝ) (k : ℕ) :
    Sob.MemH k (c.w χ t) :=
  (Sob.memH_of_contDiff_hasCompactSupport (contDiff_w_at hχ hc t) (hasCompactSupport_w hχ hc t)
    k).1

/-- `t ↦ ‖w(t)‖_{H^k}` is continuous on `[0,T]` (`thm:smooth`). -/
theorem continuousOn_normH_w {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hc : c.Hyp T) (k : ℕ) :
    ContinuousOn (fun t => Sob.normH k (c.w χ t)) (Icc 0 T) := by
  set K := (fun p : ℝ × ℂ => c.flow p.1 p.2) '' (Icc (-1 : ℝ) (T + 1) ×ˢ tsupport c.ring0) ∪
    tsupport (ringPhi χ) with hKdef
  have hK : IsCompact K :=
    ((isCompact_Icc.prod (isCompact_tsupport_ring0 hc)).image
      (continuous_flow_uncurry hc)).union (ringFacts_of_admissible hχ).2.1
  have hsupp : ∀ t ∈ Ioo (-1 : ℝ) (T + 1), ∀ x ∉ K, c.w χ t x = 0 := by
    intro t ht x hx
    have h1 : c.ringPart t x = 0 := by
      by_contra hne
      apply hx
      left
      refine ⟨(t, c.flowInv t x), ⟨⟨ht.1.le, ht.2.le⟩, subset_tsupport _ hne⟩, ?_⟩
      exact (RingConfig.setting_sol_eq_parts hc).2.1 t x
    have h2 : ringPhi χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))
    simp [RingConfig.w, h1, h2]
  have hcont := Sob.continuousOn_toHk_of_contDiff (k := k) (contDiff_w hχ hc) hK isOpen_Ioo hsupp
  have hn : ContinuousOn (fun t => ‖Sob.toHk k (c.w χ t)‖) (Ioo (-1 : ℝ) (T + 1)) := hcont.norm
  refine (hn.mono ?_).congr ?_
  · intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro t _
    exact (Sob.norm_toHk (memH_w hχ hc t k)).symm

/-! ### The radial displacement -/

/-- `δ_r(t) = sup_{y ∈ supp ω_r(0)} ||Φ_t(y)| - |y||`, the largest radial displacement of a
trajectory of `ω_r` at time `t` (`05_single_ring.tex:800-801`; `0` if `ω_r(0) = 0`). -/
def dispFn (c : RingConfig) (t : ℝ) : ℝ :=
  sSup ((fun y => |‖c.flow t y‖ - ‖y‖|) '' tsupport c.ring0)

theorem continuous_dispFn (hc : c.Hyp T) : Continuous (dispFn c) := by
  have hf : Continuous (fun p : ℝ × ℂ => |‖c.flow p.1 p.2‖ - ‖p.2‖|) :=
    (((continuous_flow_uncurry hc).norm).sub continuous_snd.norm).abs
  exact (isCompact_tsupport_ring0 hc).continuous_sSup
    (f := fun t y => |‖c.flow t y‖ - ‖y‖|) hf

theorem dispFn_le_of_movesRadially {t δ : ℝ} (hδ : 0 ≤ δ) (h : c.MovesRadially t δ) :
    ∀ τ ∈ Icc (0 : ℝ) t, dispFn c τ ≤ δ := by
  intro τ hτ
  apply Real.sSup_le _ hδ
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy τ hτ

theorem movesRadially_of_dispFn_le (hc : c.Hyp T) {t δ : ℝ}
    (h : ∀ τ ∈ Icc (0 : ℝ) t, dispFn c τ ≤ δ) : c.MovesRadially t δ := by
  intro y hy τ hτ
  refine le_trans ?_ (h τ hτ)
  have hcont : Continuous (fun y => |‖c.flow τ y‖ - ‖y‖|) :=
    (((continuous_flow hc τ).norm).sub continuous_norm).abs
  exact le_csSup ((isCompact_tsupport_ring0 hc).image hcont).bddAbove (mem_image_of_mem _ hy)

theorem dispFn_zero_le (hc : c.Hyp T) {δ : ℝ} (hδ : 0 ≤ δ) : dispFn c 0 ≤ δ := by
  apply Real.sSup_le _ hδ
  rintro _ ⟨y, _, rfl⟩
  simp [flow_zero hc y, hδ]

/-! ### Support bookkeeping -/

theorem win_a_pos : 0 < a := ringData_order.2.2.2.2.2.2.2.1

theorem win_a_lt_one : a < 1 := ringData_order.2.2.2.2.2.2.2.2

theorem window_annulus_subset_annN :
    Sect.closedAnnulus ((7 / 8 - 1 / 64) * a) (5 / 4 + a / 64) ⊆ annN := by
  have ha := win_a_pos
  have ha1 := win_a_lt_one
  intro x hx
  simp only [annN, Sect.closedAnnulus, mem_ofPred_eq] at hx ⊢
  constructor <;> nlinarith [hx.1, hx.2]

/-- A radial displacement `≤ a/16` keeps `supp ω_r(τ)` inside `N` (`05_single_ring.tex:803-806`:
`(7/8 - 1/64 - 1/16)a = 51a/64 ≥ a/2` and `5/4 + 5a/64 ≤ 2`). -/
theorem ringSupportedIn_of_moves (hc : c.Hyp T) {t : ℝ}
    (hr : tsupport c.ring0 ⊆ Sect.closedAnnulus ((7 / 8 - 1 / 64) * a) (5 / 4 + a / 64))
    (hm : c.MovesRadially t (a / 16)) : c.RingSupportedIn t annN := by
  have ha := win_a_pos
  have ha1 := win_a_lt_one
  intro τ hτ x hx
  obtain ⟨y, hy, -, hxy⟩ := RingConfig.setting_movesRadially_tsupport hc hm τ hτ x hx
  have hy' := hr hy
  simp only [Sect.closedAnnulus, mem_ofPred_eq] at hy'
  simp only [annN, Sect.closedAnnulus, mem_ofPred_eq]
  have h1 := (abs_le.1 hxy).1
  have h2 := (abs_le.1 hxy).2
  constructor <;> nlinarith

theorem win_annN_subset_annN' : annN ⊆ annN' := by
  have ha := win_a_pos
  intro x hx
  simp only [annN, annN', Sect.closedAnnulus, mem_ofPred_eq] at hx ⊢
  constructor <;> linarith [hx.1, hx.2]

/-! ### `w(0) ∈ X^k` -/

theorem tsupport_ringPhi_subset_annN {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    tsupport (ringPhi χ) ⊆ annN := by
  have ha := win_a_pos
  intro x hx
  have h := (ringFacts_of_admissible hχ).2.2.2.2.2.1 hx
  simp only [mem_ofPred_eq] at h
  simp only [annN, Sect.closedAnnulus, mem_ofPred_eq]
  constructor <;> linarith [h.1, h.2]

/-- `w(0) = ω_r(0) - Φ ∈ X^k` when `supp ω_r(0) ⊂ N`. -/
theorem memXFn_pert0 {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hc : c.Hyp T)
    (hr : tsupport c.ring0 ⊆ annN) (k : ℕ) : Lin.MemXFn k (c.pert0 χ) := by
  refine ⟨w_zero hc χ ▸ memH_w hχ hc 0 k, ?_, ?_⟩
  · refine Filter.Eventually.of_forall (fun x hx => ?_)
    have h1 : c.ring0 x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hr h))
    have h2 : ringPhi χ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_ringPhi_subset_annN hχ h))
    simp [RingConfig.pert0, h1, h2]
  · have hs := hc.sym_ring
    have hrad : IsRadialPointwise (ringPhi χ) := (ringFacts_of_admissible hχ).2.2.1
    unfold Ang.IsMFoldSymmetricC
    filter_upwards [hs] with x hx
    simp only [RingConfig.pert0]
    rw [hrad]
    rw [hx]

theorem pert0_im (χ : ℝ → ℝ) (x : ℂ) : (c.pert0 χ x).im = 0 := by
  simp [RingConfig.pert0]

/-! ### The displacement bound -/

theorem win_abs_radComp_le (F : ℂ → ℂ) (x : ℂ) : |radComp F x| ≤ ‖F x‖ := by
  unfold radComp
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_conj, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_norm]
  have h : ‖x‖⁻¹ * ‖x‖ ≤ 1 := by
    rcases eq_or_ne ‖x‖ 0 with h0 | h0
    · simp [h0]
    · rw [inv_mul_cancel₀ h0]
  calc ‖F x‖ * (‖x‖⁻¹ * ‖x‖) ≤ ‖F x‖ * 1 := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = ‖F x‖ := mul_one _

theorem win_bsNorm_w (χ : ℝ → ℝ) (t : ℝ) (x : ℂ) :
    bsNorm (c.w χ t) x = ‖velocity (fun z => c.ringPart t z - ringPhi χ z) x‖ := by
  have h1 : BS.velocityRe (c.w χ t) = velocity (fun z => c.ringPart t z - ringPhi χ z) := by
    unfold BS.velocityRe
    congr 1
  have h2 : BS.velocityIm (c.w χ t) x = 0 := by
    unfold BS.velocityIm velocity
    simp [RingConfig.w]
  rw [bsNorm, h1, h2]
  simp [Real.sqrt_sq (norm_nonneg _)]

/-- **The displacement bound** (`05_single_ring.tex:846-855`): if `supp ω_r(τ) ⊂ N` on `[0,t]`,
`‖h(τ)‖_{C^0(N')} ≤ A(τ)` and `‖w(τ)‖_{H^1} ≤ B(τ)` with `A, B` continuous, then every trajectory
of `ω_r` satisfies `||Φ_τ(y)| - |y|| ≤ ∫₀^τ (A + C_BS B)` for `τ ∈ [0,t]`. -/
theorem displacement_le {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hc : c.Hyp T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (hsupp : c.RingSupportedIn t annN) {A B : ℝ → ℝ}
    (hA : ContinuousOn A (Icc 0 t)) (hB : ContinuousOn B (Icc 0 t))
    (hhA : ∀ τ ∈ Icc (0 : ℝ) t, normCk 0 annN' (c.h τ) ≤ A τ)
    (hwB : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH 1 (c.w χ τ) ≤ B τ) :
    ∀ y ∈ tsupport c.ring0, ∀ τ ∈ Icc (0 : ℝ) t,
      |‖c.flow τ y‖ - ‖y‖| ≤ ∫ τ' in (0 : ℝ)..τ, (A τ' + CBS * B τ') := by
  intro y hy τ hτ
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · -- `t = 0`
    have hτ0 : τ = 0 := le_antisymm (ht0 ▸ hτ.2) hτ.1
    subst hτ0
    simp [flow_zero hc y]
  have hct : c.Hyp t := hc.mono ht0 ht.2
  have hPE := (reduction_eq χ hχ hct hsupp).2
  -- the trajectory stays in `N ⊆ N'`
  have htrajN : ∀ τ' ∈ Icc (0 : ℝ) τ, c.flow τ' y ∈ annN := by
    intro τ' hτ'
    have hτ't : τ' ∈ Icc (0 : ℝ) t := ⟨hτ'.1, hτ'.2.trans hτ.2⟩
    apply hsupp τ' hτ't
    rw [(RingConfig.setting_tsupport_parts hc τ').1]
    exact mem_image_of_mem _ hy
  have hτT : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans ht.2⟩
  have hform := (reduction_velocity χ hχ hc).2.2 τ hτT y
    (fun τ' hτ' => win_annN_subset_annN' (htrajN τ' hτ'))
  rw [hform, ← Real.norm_eq_abs]
  have hgc : ContinuousOn (fun τ' => A τ' + CBS * B τ') (Icc 0 t) :=
    hA.add (continuousOn_const.mul hB)
  have hint : IntervalIntegrable (fun τ' => A τ' + CBS * B τ') volume 0 τ := by
    apply (hgc.mono _).intervalIntegrable
    rw [uIcc_of_le hτ.1]
    exact Icc_subset_Icc le_rfl hτ.2
  refine intervalIntegral.norm_integral_le_of_norm_le hτ.1 ?_ hint
  refine Filter.Eventually.of_forall (fun τ' hτ' => ?_)
  have hτ'1 : τ' ∈ Icc (0 : ℝ) τ := ⟨hτ'.1.le, hτ'.2⟩
  have hτ't : τ' ∈ Icc (0 : ℝ) t := ⟨hτ'1.1, hτ'1.2.trans hτ.2⟩
  have hτ'T : τ' ∈ Icc (0 : ℝ) T := ⟨hτ't.1, hτ't.2.trans ht.2⟩
  set x := c.flow τ' y with hx
  have hxN : x ∈ annN := htrajN τ' hτ'1
  have hx3 : ‖x‖ ≤ 3 := by
    have := hxN.2
    linarith
  rw [Real.norm_eq_abs]
  refine (win_abs_radComp_le _ _).trans ?_
  refine (norm_add_le _ _).trans ?_
  have hmemCk : MemCk 0 annN' (c.h τ') := ((reduction_field hc).2 0).1 τ' hτ'T
  have hh1 : ‖c.h τ' x‖ ≤ normCk 0 annN' (c.h τ') :=
    norm_le_normCk hmemCk (win_annN_subset_annN' hxN)
  have hX : Lin.MemXFn (2 + 1) (c.w χ τ') := ((hPE 3).1.1 τ' hτ't)
  have hv : ‖velocity (fun z => c.ringPart τ' z - ringPhi χ z) x‖ ≤
      CBS * Sob.normH 1 (c.w χ τ') := by
    rw [← win_bsNorm_w χ τ' x]
    exact bilinear_BS (le_refl 2) hX x hx3
  have hCBS := CBS_pos
  have := hhA τ' hτ't
  have := hwB τ' hτ't
  nlinarith

end WindowH

end OneRing

end NonUniqueEuler
