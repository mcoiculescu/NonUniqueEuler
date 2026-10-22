import NonUniqueEuler.H.Sec5.ReductionField.Basic
import NonUniqueEuler.I.Sec5.Setting
import NonUniqueEuler.I.SmoothB.SmoothFlow
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Infra.CkNorm.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Helper for `lem:reduction`(1): joint smoothness of `h` and continuity into `C^k(N')`

Helper of `P/Sec5/ReductionField.lean` (`05_single_ring.tex:146-163`).

The manuscript differentiates `K * (ω_i + ω_o)(t)` under the integral sign on a neighbourhood of
`N'` that stays away from the supports, using `|∂^β K(z)| ≤ C_β |z|^{-1-|β|}`. We use instead that
`(t, x) ↦ ω_i(t, x) + ω_o(t, x)` is `C^∞` on `ℝ × ℝ²` (`setting_parts_smooth`) with supports in a
fixed compact set for `t` in a bounded interval (the supports are `Φ_t(K_i ∪ K_o)` and the flow is
continuous), so that Mathlib's parametric convolution theorem
(`contDiffOn_convolution_left_with_param`) gives `K * (ω_i + ω_o) ∈ C^∞(ℝ × ℝ²)` jointly; the point
vortex `G x^⊥/|x|²` is smooth off `0`. Hence `(t, x) ↦ h(t, x)` is `C^∞` on
`(-1, T+1) × (ℝ² ∖ {0})`, an open set containing `[0,T] × N'`, and `t ↦ h(t) ∈ C^k(N')` is
continuous on `[0,T]` (`tendsto_normCk_sub_of_contDiffOn`). (Deviation of proof only: the
derivatives fall on `ω_i + ω_o` instead of on the kernel.)

Main results: `contDiffOn_h_joint`, `ckPathOn_h`, `parts_contDiff`, `parts_hasCompactSupport`,
`parts_eq_zero_of_mem`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff

namespace NonUniqueEuler

namespace OneRing

open RingData

namespace RedFieldH

/-- The Biot–Savart kernel is locally integrable (`lem:BS-basic`(a)). -/
theorem locallyIntegrable_biotSavartKernel : LocallyIntegrable biotSavartKernel volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨r, hr, hkr⟩ := hk.isBounded.subset_ball_lt 0 0
  exact (BS.integral_norm_biotSavartKernel_ball hr).1.mono_set hkr

/-- Velocity of a smooth family of vorticities with supports in a fixed compact set: jointly
`C^∞` in `(t, x)` (Mathlib's parametric convolution theorem). -/
theorem contDiffOn_velocity_param {g : ℝ → ℂ → ℝ} {s : Set ℝ} (hs : IsOpen s) {k : Set ℂ}
    (hk : IsCompact k) (hgs : ∀ p x, p ∈ s → x ∉ k → g p x = 0)
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℂ => g q.1 q.2) (s ×ˢ univ)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℂ => velocity (g q.1) q.2)
      (s ×ˢ univ) := by
  have hg' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (↿(fun (p : ℝ) (x : ℂ) => ((g p x : ℝ) : ℂ))) (s ×ˢ univ) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hg
  have h := contDiffOn_convolution_left_with_param (μ := volume)
    (ContinuousLinearMap.mul ℝ ℂ) (f := biotSavartKernel)
    (g := fun (p : ℝ) (x : ℂ) => ((g p x : ℝ) : ℂ)) (n := ⊤) hs hk
    (fun p x hp hx => by simp [hgs p x hp hx]) locallyIntegrable_biotSavartKernel hg'
  refine h.congr fun q _ => ?_
  simp only [Conv.velocity_eq_convolution]

variable {c : RingConfig} {T : ℝ}

/-- The datum of a configuration satisfying `c.Hyp T` is a smooth datum of `thm:smooth`. -/
theorem exists_isSmoothDatum (hc : c.Hyp T) : ∃ R₀, Smooth.IsSmoothDatum c.datum R₀ := by
  obtain ⟨R, hR⟩ := hc.datum_hasCompactSupport.isCompact.isBounded.subset_ball 0
  exact ⟨R, ⟨hc.datum_contDiff, hR⟩⟩

/-- The flow `(t, y) ↦ Φ_t(y)` is continuous. -/
theorem continuous_flow (hc : c.Hyp T) : Continuous (fun p : ℝ × ℂ => c.flow p.1 p.2) := by
  obtain ⟨R, hR⟩ := exists_isSmoothDatum hc
  exact (Smooth.flow_contDiff hR).1.continuous

/-- For `t` in a compact set `J`, the supports of `ω_i(t)` and `ω_o(t)` lie in a fixed compact
set (`supp ω_•(t) = Φ_t(K_•)`, `05_single_ring.tex:139`). -/
theorem exists_compact_support_parts (hc : c.Hyp T) {J : Set ℝ} (hJ : IsCompact J) :
    ∃ k : Set ℂ, IsCompact k ∧
      ∀ p ∈ J, ∀ x ∉ k, c.innerPart p x = 0 ∧ c.outerPart p x = 0 := by
  obtain ⟨-, ⟨-, hi⟩, ⟨-, ho⟩, -⟩ := RingConfig.setting_parts_smooth hc
  have hK : IsCompact (tsupport c.inner0 ∪ tsupport c.outer0) := hi.isCompact.union ho.isCompact
  refine ⟨(fun p : ℝ × ℂ => c.flow p.1 p.2) '' (J ×ˢ (tsupport c.inner0 ∪ tsupport c.outer0)),
    (hJ.prod hK).image (continuous_flow hc), ?_⟩
  intro p hp x hx
  have hinv := (RingConfig.setting_sol_eq_parts hc).2.1 p x
  constructor
  · by_contra hne
    exact hx ⟨(p, c.flowInv p x), ⟨hp, Or.inl (subset_tsupport _ hne)⟩, hinv⟩
  · by_contra hne
    exact hx ⟨(p, c.flowInv p x), ⟨hp, Or.inr (subset_tsupport _ hne)⟩, hinv⟩

/-- `(t, x) ↦ ω_i(t, x) + ω_o(t, x)` is `C^∞` on `ℝ × ℝ²`. -/
theorem parts_contDiff_joint (hc : c.Hyp T) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℂ => c.innerPart q.1 q.2 + c.outerPart q.1 q.2) := by
  obtain ⟨-, -, -, -, hi, ho⟩ := RingConfig.setting_parts_smooth hc
  exact hi.add ho

/-- `ω_i(t) + ω_o(t) ∈ C^∞`. -/
theorem parts_contDiff (hc : c.Hyp T) (t : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => c.innerPart t y + c.outerPart t y) :=
  (parts_contDiff_joint hc).comp (contDiff_const.prodMk contDiff_id)

/-- `ω_i(t) + ω_o(t)` has compact support. -/
theorem parts_hasCompactSupport (hc : c.Hyp T) (t : ℝ) :
    HasCompactSupport (fun y => c.innerPart t y + c.outerPart t y) := by
  obtain ⟨k, hk, hks⟩ := exists_compact_support_parts hc (isCompact_singleton (x := t))
  refine HasCompactSupport.intro hk fun x hx => ?_
  obtain ⟨h1, h2⟩ := hks t rfl x hx
  simp [h1, h2]

/-- On `{a/8 < |x| < 6}` both `ω_i(t)` and `ω_o(t)` vanish, for `t ∈ [0,T]`. -/
theorem parts_eq_zero_of_mem (hc : c.Hyp T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {x : ℂ}
    (hx1 : a / 8 < ‖x‖) (hx2 : ‖x‖ < 6) : c.innerPart t x = 0 ∧ c.outerPart t x = 0 := by
  constructor
  · apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hc.inner_tsupport t ht hmem
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  · apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hx : x ∈ tsupport (c.outerPart t) ∩ ball 0 6 :=
      ⟨hmem, by rw [mem_ball, dist_zero_right]; exact hx2⟩
    rw [hc.outer_tsupport t ht] at hx
    exact hx

/-- **Joint smoothness of `h`** on `(-1, T+1) × (ℝ² ∖ {0})`. -/
theorem contDiffOn_h_joint (hc : c.Hyp T) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℂ => c.h q.1 q.2)
      (Ioo (-1) (T + 1) ×ˢ ({0}ᶜ : Set ℂ)) := by
  obtain ⟨k, hk, hks⟩ := exists_compact_support_parts hc (isCompact_Icc (a := -1) (b := T + 1))
  have hvel := contDiffOn_velocity_param (g := fun p y => c.innerPart p y + c.outerPart p y)
    isOpen_Ioo hk (fun p x hp hx => by
      obtain ⟨h1, h2⟩ := hks p (Ioo_subset_Icc_self hp) x hx
      simp [h1, h2]) (parts_contDiff_joint hc).contDiffOn
  have hvel' := hvel.mono (prod_mono subset_rfl (subset_univ ({0}ᶜ : Set ℂ)))
  have hvor : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℂ => vortex c.G q.2)
      (Ioo (-1) (T + 1) ×ˢ ({0}ᶜ : Set ℂ)) :=
    (contDiffOn_vortex c.G).comp contDiffOn_snd (fun q hq => hq.2)
  exact hvel'.sub hvor

/-- **`t ↦ h(t) ∈ C^k(N')` is continuous on `[0,T]`**, for every `k`
(`lem:reduction`(1), `05_single_ring.tex:108-109`, `:157-163`). -/
theorem ckPathOn_h (hc : c.Hyp T) (k : ℕ) : CkPathOn k annN' (Icc 0 T) c.h := by
  have ha : 0 < a := Real.exp_pos _
  have hW : IsOpen (Ioo (-1 : ℝ) (T + 1) ×ˢ ({0}ᶜ : Set ℂ)) :=
    isOpen_Ioo.prod isOpen_compl_singleton
  have hsub : Icc (0 : ℝ) T ×ˢ annN' ⊆ Ioo (-1 : ℝ) (T + 1) ×ˢ ({0}ᶜ : Set ℂ) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    intro h0
    have h0' : x = 0 := h0
    have := (mem_annN'.1 hx).1
    rw [h0', norm_zero] at this
    linarith
  have hh : ContDiffOn ℝ k (fun q : ℝ × ℂ => c.h q.1 q.2)
      (Ioo (-1 : ℝ) (T + 1) ×ˢ ({0}ᶜ : Set ℂ)) :=
    (contDiffOn_h_joint hc).of_le (by exact_mod_cast le_top)
  exact ⟨fun t ht => memCk_slice_of_contDiffOn isCompact_annN' hW hsub hh ht,
    fun t ht => tendsto_normCk_sub_of_contDiffOn isCompact_annN' hW hsub hh ht⟩

end RedFieldH

end OneRing

end NonUniqueEuler
