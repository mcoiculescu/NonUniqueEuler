import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.Setting
import NonUniqueEuler.I.SmoothB.SmoothFlow
import NonUniqueEuler.I.SmoothB.FlowFacts
import NonUniqueEuler.I.Sec4.RingFacts

/-!
# Helpers for `lem:reduction`(3): facts about the perturbation `w = ω_r - Φ`

Helper of `P/Sec5/ReductionEq.lean` (`05_single_ring.tex:129-145`, `:204-210`):
* `RedEqH.exists_isSmoothDatum`: the datum is a datum of `thm:smooth`;
* `RedEqH.hasDerivAt_ringPart`: the transport equation `∂_t ω_r = -v·∇ω_r` on `ℝ × ℝ²`
  (`ω_r(t) = ω_r(0) ∘ Φ_t⁻¹`, `I/SmoothB/FlowFacts.lean`);
* `RedEqH.deriv_w`: hence `∂_t w = -v·∇ω_r`;
* `RedEqH.w_contDiff`: `w ∈ C^∞(ℝ × ℝ²)`;
* `RedEqH.exists_compact_supp`: the supports of `w(t)`, `t ∈ (-1, T+1)`, lie in a fixed compact;
* `RedEqH.w_eq_zero_of_not_mem`, `RedEqH.fderiv_ringPart_eq_zero`,
  `RedEqH.fderiv_ringPhi_eq_zero`: for `t ∈ [0,T]`, `w(t)`, `∇ω_r(t)`, `∇Φ` vanish outside `N`;
* `RedEqH.w_rot`: `w(t)` is `3`-fold symmetric.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.OneRing.RedEqH

open RingData

variable {c : RingConfig} {T : ℝ}

/-- The datum of a configuration satisfying `c.Hyp T` is a datum of `thm:smooth`. -/
theorem exists_isSmoothDatum (hc : c.Hyp T) : ∃ R₀ : ℝ, Smooth.IsSmoothDatum c.datum R₀ := by
  obtain ⟨R, hR⟩ := hc.datum_hasCompactSupport.isCompact.isBounded.subset_ball (0 : ℂ)
  exact ⟨R, hc.datum_contDiff, hR⟩

/-- **Transport equation for `ω_r`**: `∂_t ω_r(t,x) = -Dω_r(t)(x) v(t,x)` (differentiate
`ω_r(t) = ω_r(0) ∘ Φ_t⁻¹`, `05_single_ring.tex:207-208`). -/
theorem hasDerivAt_ringPart (hc : c.Hyp T) (t : ℝ) (x : ℂ) :
    HasDerivAt (fun s => c.ringPart s x)
      (-(fderiv ℝ (c.ringPart t) x (velocity (c.sol t) x))) t := by
  obtain ⟨R₀, hR⟩ := exists_isSmoothDatum hc
  have hu := Smooth.vel_isSmoothBoundedField hR
  have hg : ContDiff ℝ 1 c.ring0 :=
    (RingConfig.setting_parts_smooth hc).1.1.of_le (by exact_mod_cast le_top)
  exact Smooth.hasDerivAt_comp_flowOf hu hg 0 t x

/-- `∂_t w(t,x) = -Dω_r(t)(x) v(t,x)`. -/
theorem deriv_w (χ : ℝ → ℝ) (hc : c.Hyp T) (t : ℝ) (x : ℂ) :
    deriv (fun s => c.w χ s x) t =
      (((-(fderiv ℝ (c.ringPart t) x (velocity (c.sol t) x))) : ℝ) : ℂ) := by
  have h := ((hasDerivAt_ringPart hc t x).sub_const (ringPhi χ x)).ofReal_comp
  exact h.deriv

/-- `Φ` is supported in `N`. -/
theorem tsupport_ringPhi_subset_annN {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    tsupport (ringPhi χ) ⊆ annN := by
  obtain ⟨-, -, -, -, -, hsupp, ha, -⟩ := ringFacts_of_admissible hχ
  intro y hy
  obtain ⟨h1, h2⟩ := hsupp hy
  exact ⟨by linarith, by linarith⟩

/-- `w ∈ C^∞(ℝ × ℝ²)`. -/
theorem w_contDiff {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hc : c.Hyp T) :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => c.w χ p.1 p.2) := by
  have hR := (RingConfig.setting_parts_smooth hc).2.2.2.1
  have hP : ContDiff ℝ ∞ (ringPhi χ) := (ringFacts_of_admissible hχ).1
  have h : ContDiff ℝ ∞ (fun p : ℝ × ℂ => c.ringPart p.1 p.2 - ringPhi χ p.2) :=
    hR.sub (hP.comp contDiff_snd)
  exact Complex.ofRealCLM.contDiff.comp h

/-- The ring part is supported in the compact set `Φ_s(supp ω_r(0))`, `s ∈ [-1, T+1]`, and `Φ`
in `supp Φ`: the supports of `w(s)`, `s ∈ (-1, T+1)`, lie in a fixed compact set. -/
theorem exists_compact_supp {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hc : c.Hyp T) :
    ∃ K' : Set ℂ, IsCompact K' ∧ ∀ s ∈ Ioo (-1 : ℝ) (T + 1), ∀ x ∉ K', c.w χ s x = 0 := by
  obtain ⟨R₀, hR⟩ := exists_isSmoothDatum hc
  have hflow : Continuous (fun p : ℝ × ℂ => c.flow p.1 p.2) :=
    (Smooth.flow_contDiff hR).1.continuous
  have hK0 : IsCompact (tsupport c.ring0) := (RingConfig.setting_parts_smooth hc).1.2
  have hPc : IsCompact (tsupport (ringPhi χ)) := (ringFacts_of_admissible hχ).2.1
  refine ⟨(fun p : ℝ × ℂ => c.flow p.1 p.2) '' (Icc (-1 : ℝ) (T + 1) ×ˢ tsupport c.ring0) ∪
      tsupport (ringPhi χ),
    ((isCompact_Icc.prod hK0).image hflow).union hPc, ?_⟩
  intro s hs x hx
  have hinv := (RingConfig.setting_sol_eq_parts hc).2.1 s x
  have h1 : c.ringPart s x = 0 := by
    show c.ring0 (c.flowInv s x) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact hx (Or.inl ⟨(s, c.flowInv s x), ⟨Ioo_subset_Icc_self hs, hmem⟩, hinv⟩)
  have h2 : ringPhi χ x = 0 := image_eq_zero_of_notMem_tsupport fun hmem => hx (Or.inr hmem)
  simp [RingConfig.w, h1, h2]

/-- For `t ∈ [0,T]` and `x ∉ N`, `ω_r(t,x) = 0`. -/
theorem ringPart_eq_zero_of_not_mem (hsupp : c.RingSupportedIn T annN) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) {x : ℂ} (hx : x ∉ annN) : c.ringPart t x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem => hx (hsupp t ht hmem)

/-- For `t ∈ [0,T]` and `x ∉ N`, `w(t,x) = 0`. -/
theorem w_eq_zero_of_not_mem {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ)
    (hsupp : c.RingSupportedIn T annN) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {x : ℂ}
    (hx : x ∉ annN) : c.w χ t x = 0 := by
  have h1 := ringPart_eq_zero_of_not_mem hsupp ht hx
  have h2 : ringPhi χ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun hmem => hx (tsupport_ringPhi_subset_annN hχ hmem)
  simp [RingConfig.w, h1, h2]

/-- For `t ∈ [0,T]` and `x ∉ N`, `Dω_r(t)(x) = 0`. -/
theorem fderiv_ringPart_eq_zero (hsupp : c.RingSupportedIn T annN) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) {x : ℂ} (hx : x ∉ annN) : fderiv ℝ (c.ringPart t) x = 0 :=
  fderiv_of_notMem_tsupport ℝ fun hmem => hx (hsupp t ht hmem)

/-- For `x ∉ N`, `DΦ(x) = 0`. -/
theorem fderiv_ringPhi_eq_zero {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {x : ℂ}
    (hx : x ∉ annN) : fderiv ℝ (ringPhi χ) x = 0 :=
  fderiv_of_notMem_tsupport ℝ fun hmem => hx (tsupport_ringPhi_subset_annN hχ hmem)

/-- `w(s)` is `3`-fold symmetric (pointwise), for every `s`. -/
theorem w_rot {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hc : c.Hyp T) (s : ℝ) (x : ℂ) :
    c.w χ s (rot (2 * Real.pi / 3) x) = c.w χ s x := by
  have h1 := (RingConfig.setting_symmetric hc).2.2.1 s x
  have h2 := (ringFacts_of_admissible hχ).2.2.1 (2 * Real.pi / 3) x
  simp only [RingConfig.w, h1, h2]

end NonUniqueEuler.OneRing.RedEqH
