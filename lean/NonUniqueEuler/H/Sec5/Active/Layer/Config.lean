import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.Setting
import NonUniqueEuler.I.Sec5.ReductionVelocity
import NonUniqueEuler.I.Sec5.ReductionField
import NonUniqueEuler.I.Sec5.ReductionEq
import NonUniqueEuler.I.Sec5.Bilinear
import NonUniqueEuler.I.Sec5.Lambda
import NonUniqueEuler.I.SmoothB.SmoothFlow
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec4.Annuli
import NonUniqueEuler.I.Sec4.PropU
import NonUniqueEuler.I.Infra.Sobolev.Paths
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Infra.CkNorm.Basic
import Mathlib.Topology.Order.Compact

/-!
# Helpers for the initial layer of `thm:active`: facts about the configuration

Helper of `P/Sec5/Active/Layer.lean` (fully proved modulo the interface files it imports).
Namespace `NonUniqueEuler.OneRing.LayerH`. Copies (renamed) of proved helpers of the proofs
`Sec5/Window` (`H/Sec5/Window/Config.lean`) and `Sec5/Active` (`H/Sec5/Active/Tools.lean`), which
a proof file may not import (import rules, `README.md`).

* smoothness of `w(t) = ω_r(t) - Φ`, `w(t) ∈ H^k`, continuity of `t ↦ ‖w(t)‖_{H^k}`;
* the largest radial displacement `dispFn c t` (continuous) and its relation to `MovesRadially`;
* support bookkeeping: a radial displacement `≤ a/16` from `supp ω_r(0) ⊂ 𝒩₋` keeps
  `supp ω_r` in `𝒩 ⊂ N` (`lem:annuli`);
* the displacement bound (`lem:reduction`(2), `lem:bilinear`(4));
* `normCk_congr_of_eqOn`, `field_bound` ((Field) gives the bound of `‖h‖_{C^M(N')}`),
  `sigma_facts` (`0 < σ_b ≤ σ(G) ≤ σ_max`), `norm_exp_lam`, `normH_mono_order'`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler

namespace OneRing

open RingData

namespace LayerH

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

/-- `w(t)` is real. -/
theorem w_im (χ : ℝ → ℝ) (t : ℝ) (x : ℂ) : (c.w χ t x).im = 0 := by
  simp [RingConfig.w]

theorem pert0_im (χ : ℝ → ℝ) (x : ℂ) : (c.pert0 χ x).im = 0 := by
  simp [RingConfig.pert0]

/-! ### The radial displacement -/

/-- `δ_r(t) = sup_{y ∈ supp ω_r(0)} ||Φ_t(y)| - |y||`. -/
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

/-! ### Supports -/

/-- `0 < a < 1`. -/
theorem a_facts {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) : 0 < a ∧ a < 1 :=
  ⟨(ringFacts_of_admissible hχ).2.2.2.2.2.2.1, (ringFacts_of_admissible hχ).2.2.2.2.2.2.2⟩

theorem lay_annN_subset_annN' : annN ⊆ annN' := annuli_chain.2.2.2.2

/-- A radial displacement `≤ a/16` on `[0,t]` from `supp ω_r(0) ⊂ 𝒩₋` keeps `supp ω_r(τ)` in
`𝒩` (`lem:annuli`). -/
theorem tsupport_ringPart_of_moves (hc : c.Hyp T) {t δ : ℝ}
    (h0 : tsupport c.ring0 ⊆ annNm) (hmove : c.MovesRadially t δ) (hδ : δ ≤ a / 16) :
    ∀ τ ∈ Icc (0 : ℝ) t, tsupport (c.ringPart τ) ⊆ annNn := by
  intro τ hτ
  have hT' : ∀ y' ∈ tsupport (c.ringPart τ), ∃ y ∈ tsupport c.ring0, |‖y'‖ - ‖y‖| ≤ a / 16 := by
    intro y' hy'
    obtain ⟨y, hy, -, hyy⟩ := RingConfig.setting_movesRadially_tsupport hc hmove τ hτ y' hy'
    exact ⟨y, hy, hyy.trans hδ⟩
  exact (annuli_slack hT').2 h0

/-- The same, in `N`: `c.RingSupportedIn t annN`. -/
theorem ringSupported_of_moves (hc : c.Hyp T) {t δ : ℝ}
    (h0 : tsupport c.ring0 ⊆ annNm) (hmove : c.MovesRadially t δ) (hδ : δ ≤ a / 16) :
    c.RingSupportedIn t annN := by
  intro τ hτ
  obtain ⟨-, -, h3, h4, -⟩ := annuli_chain
  exact (tsupport_ringPart_of_moves hc h0 hmove hδ τ hτ).trans
    ((h3.trans interior_subset).trans h4)

theorem tsupport_ringPhi_subset_annN {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    tsupport (ringPhi χ) ⊆ annN := by
  have ha := (a_facts hχ).1
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

/-! ### The displacement bound -/

theorem lay_abs_radComp_le (F : ℂ → ℂ) (x : ℂ) : |radComp F x| ≤ ‖F x‖ := by
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

theorem lay_bsNorm_w (χ : ℝ → ℝ) (t : ℝ) (x : ℂ) :
    bsNorm (c.w χ t) x = ‖velocity (fun z => c.ringPart t z - ringPhi χ z) x‖ := by
  have h1 : BS.velocityRe (c.w χ t) = velocity (fun z => c.ringPart t z - ringPhi χ z) := by
    unfold BS.velocityRe
    congr 1
  have h2 : BS.velocityIm (c.w χ t) x = 0 := by
    unfold BS.velocityIm velocity
    simp [RingConfig.w]
  rw [bsNorm, h1, h2]
  simp [Real.sqrt_sq (norm_nonneg _)]

/-- **The displacement bound** (`05_single_ring.tex:968-971`): if `supp ω_r(τ) ⊂ N` on `[0,t]`,
`‖h(τ)‖_{C^0(N')} ≤ A` and `‖w(τ)‖_{H^1} ≤ B` (constants), then every trajectory of `ω_r`
satisfies `||Φ_τ(y)| - |y|| ≤ τ(A + C_BS B)` for `τ ∈ [0,t]`. -/
theorem displacement_le {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hc : c.Hyp T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (hsupp : c.RingSupportedIn t annN) {A B : ℝ}
    (hhA : ∀ τ ∈ Icc (0 : ℝ) t, normCk 0 annN' (c.h τ) ≤ A)
    (hwB : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH 1 (c.w χ τ) ≤ B) :
    ∀ y ∈ tsupport c.ring0, ∀ τ ∈ Icc (0 : ℝ) t,
      |‖c.flow τ y‖ - ‖y‖| ≤ τ * (A + CBS * B) := by
  intro y hy τ hτ
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · have hτ0 : τ = 0 := le_antisymm (ht0 ▸ hτ.2) hτ.1
    subst hτ0
    simp [flow_zero hc y]
  have hct : c.Hyp t := hc.mono ht0 ht.2
  have hPE := (reduction_eq χ hχ hct hsupp).2
  have htrajN : ∀ τ' ∈ Icc (0 : ℝ) τ, c.flow τ' y ∈ annN := by
    intro τ' hτ'
    have hτ't : τ' ∈ Icc (0 : ℝ) t := ⟨hτ'.1, hτ'.2.trans hτ.2⟩
    apply hsupp τ' hτ't
    rw [(RingConfig.setting_tsupport_parts hc τ').1]
    exact mem_image_of_mem _ hy
  have hτT : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans ht.2⟩
  have hform := (reduction_velocity χ hχ hc).2.2 τ hτT y
    (fun τ' hτ' => lay_annN_subset_annN' (htrajN τ' hτ'))
  rw [hform, ← Real.norm_eq_abs]
  have hconst : (∫ _ in (0 : ℝ)..τ, (A + CBS * B)) = τ * (A + CBS * B) := by
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [← hconst]
  refine intervalIntegral.norm_integral_le_of_norm_le hτ.1 ?_ intervalIntegrable_const
  refine Filter.Eventually.of_forall (fun τ' hτ' => ?_)
  have hτ'1 : τ' ∈ Icc (0 : ℝ) τ := ⟨hτ'.1.le, hτ'.2⟩
  have hτ't : τ' ∈ Icc (0 : ℝ) t := ⟨hτ'1.1, hτ'1.2.trans hτ.2⟩
  have hτ'T : τ' ∈ Icc (0 : ℝ) T := ⟨hτ't.1, hτ't.2.trans ht.2⟩
  set x := c.flow τ' y with hx
  have hxN : x ∈ annN := htrajN τ' hτ'1
  have hx3 : ‖x‖ ≤ 3 := by
    have := hxN.2
    have := (a_facts hχ).2
    simp only [annN, Sect.closedAnnulus] at *
    linarith
  rw [Real.norm_eq_abs]
  refine (lay_abs_radComp_le _ _).trans ?_
  refine (norm_add_le _ _).trans ?_
  have hmemCk : MemCk 0 annN' (c.h τ') := ((reduction_field hc).2 0).1 τ' hτ'T
  have hh1 : ‖c.h τ' x‖ ≤ normCk 0 annN' (c.h τ') :=
    norm_le_normCk hmemCk (lay_annN_subset_annN' hxN)
  have hX : Lin.MemXFn (2 + 1) (c.w χ τ') := ((hPE 3).1.1 τ' hτ't)
  have hv : ‖velocity (fun z => c.ringPart τ' z - ringPhi χ z) x‖ ≤
      CBS * Sob.normH 1 (c.w χ τ') := by
    rw [← lay_bsNorm_w χ τ' x]
    exact bilinear_BS (le_refl 2) hX x hx3
  have hCBS := CBS_pos
  have h1 := hhA τ' hτ't
  have h2 := hwB τ' hτ't
  have h3 : CBS * Sob.normH 1 (c.w χ τ') ≤ CBS * B := mul_le_mul_of_nonneg_left h2 hCBS.le
  linarith

/-! ### `C^k` norms, `σ`, `λ`, `H^k` norms -/

/-- `‖f‖_{H^k} ≤ ‖f‖_{H^{k'}}` for `k ≤ k'`, with no membership hypothesis. -/
theorem normH_mono_order' {k k' : ℕ} (hk : k ≤ k') (f : ℂ → ℂ) :
    Sob.normH k f ≤ Sob.normH k' f := by
  unfold Sob.normH Sob.normHOn
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum_of_subset_of_nonneg (Sob.multiIdx_mono hk)
    (fun _ _ _ => sq_nonneg _)

/-- `C^k(K)` norms only see the values on an open set containing `K`. -/
theorem normCk_congr_of_eqOn {k : ℕ} {K U : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U)
    {f g : ℂ → ℂ} (hfg : ∀ x ∈ U, f x = g x) : normCk k K f = normCk k K g := by
  unfold normCk normCkE supIterDerivE
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  refine iSup_congr fun x => iSup_congr fun hx => ?_
  have h : f =ᶠ[𝓝 x] g := Filter.eventuallyEq_of_mem (hU.mem_nhds (hKU hx)) hfg
  rw [(h.iteratedFDeriv ℝ q).eq_of_nhds]

/-- (Field) gives `‖h(u)‖_{C^M(N')} ≤ C₀κ⟨u⟩^p + η_b â(u)` on `[0,ū]`. -/
theorem field_bound {χ : ℝ → ℝ} {s : ℕ} {ubar C₀ κ ηb : ℝ}
    (hF : c.ActiveField χ s ubar C₀ κ ηb) :
    ∀ u ∈ Icc (0 : ℝ) ubar, normCk (Mact χ s) annN' (c.h u) ≤
      C₀ * κ * Prelim.jap u ^ pW + ηb * ahat κ (Eig.sigma χ c.G) u := by
  intro u hu
  obtain ⟨h₁, h₂, hh⟩ := hF
  obtain ⟨⟨U, hU, hNU, heq⟩, hm₁, hn₁, hm₂, hn₂⟩ := hh u hu
  rw [normCk_congr_of_eqOn hU hNU (g := h₁ u + h₂ u) (fun x hx => by
    rw [heq x hx]; rfl)]
  exact ((hm₁.add hm₂).2).trans (add_le_add hn₁ hn₂)

/-- `0 < σ_b ≤ σ(G) ≤ σ_max` for `G ∈ [0,G₁]` (`prop:U`(a), `eq:Lambda`). -/
theorem sigma_facts (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) :
    0 < Eig.sigb χ ∧ Eig.sigb χ ≤ Eig.sigma χ G ∧ Eig.sigma χ G ≤ sigmaMax χ := by
  obtain ⟨-, -, ⟨G₀, -, hb, hmin⟩, hpos, -⟩ := Eig.propU_a χ hχ hN
  have hmax := (lambda_consts χ hχ hN (le_refl 3)).2.2.2.2
  refine ⟨by linarith, hb ▸ hmin G hG, hmax.2 ⟨G, hG, rfl⟩⟩

/-- `|e^{λu}| = e^{σu}`. -/
theorem norm_exp_lam (χ : ℝ → ℝ) (G u : ℝ) :
    ‖Complex.exp (Eig.lam χ G * u)‖ = Real.exp (Eig.sigma χ G * u) := by
  rw [Complex.norm_exp]
  simp [Eig.sigma, Complex.mul_re]

end LayerH

end OneRing

end NonUniqueEuler
