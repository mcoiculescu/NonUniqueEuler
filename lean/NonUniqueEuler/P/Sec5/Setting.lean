import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.SmoothB.SmoothFlow
import NonUniqueEuler.I.SmoothB.SmoothCovariance
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Algebra.Support

/-!
# Proof of the setting of Section 5 and the configuration of `lem:reduction`

Proof of `I/Sec5/Setting.lean` (`05_single_ring.tex:28-40`, `:129-145`).

Structure (following the first paragraph of the proof of `lem:reduction`):
1. the datum `ω(0)` is an admissible datum of `thm:smooth` (`exists_isSmoothDatum`);
2. a part whose `tsupport` is disjoint from the other two agrees with `ω(0)` near its own
   `tsupport` and vanishes near every other point, so it is `C_c^∞` (`part_smooth`);
3. `Φ_t` is a homeomorphism with inverse `Φ_t⁻¹` (`flow_diffeo`), hence
   `supp(g ∘ Φ_t⁻¹) = Φ_t(supp g)` (`tsupport_comp_flowInv`) and, by area preservation
   (`flow_measurePreserving`), `∫ g ∘ Φ_t⁻¹ = ∫ g` (`integral_comp_flowInv`);
4. the parts are continuous and a.e. `3`-fold symmetric, hence pointwise symmetric
   (`sym_pointwise`); so is the datum, and `vel_flow_rot_of_symm` gives
   `Φ_t ∘ O = O ∘ Φ_t`, `Φ_t⁻¹ ∘ O = O ∘ Φ_t⁻¹`.

Helpers are `private`, so integration adds no new public names.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

namespace RingConfig

/-! ### Helpers -/

/-- The datum of a configuration satisfying `Hyp` is an admissible datum of `thm:smooth`. -/
private theorem exists_isSmoothDatum {c : RingConfig} {T : ℝ} (hc : c.Hyp T) :
    ∃ R₀ : ℝ, Smooth.IsSmoothDatum c.datum R₀ := by
  obtain ⟨R, hR⟩ := hc.datum_hasCompactSupport.isCompact.isBounded.subset_ball (0 : ℂ)
  exact ⟨R, hc.datum_contDiff, hR⟩

/-- A part `f` of a smooth compactly supported `D = f + g + k`, whose `tsupport` is disjoint from
those of `g` and `k`, is smooth with compact support (`05_single_ring.tex:130-133`). -/
private theorem part_smooth {D f g k : ℂ → ℝ} (hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hDc : HasCompactSupport D) (hsum : ∀ x, D x = f x + g x + k x)
    (hfg : Disjoint (tsupport f) (tsupport g)) (hfk : Disjoint (tsupport f) (tsupport k)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f := by
  constructor
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport f
    · have hg : g =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (Set.disjoint_left.mp hfg hx)
      have hk : k =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (Set.disjoint_left.mp hfk hx)
      refine hD.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [hg, hk] with y hy1 hy2
      rw [hsum y, hy1, hy2]
      simp
    · have hf : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hf
  · refine hDc.mono' ?_
    intro x hx
    have hxt : x ∈ tsupport f := subset_tsupport f hx
    have hg : g x = 0 := image_eq_zero_of_notMem_tsupport (Set.disjoint_left.mp hfg hxt)
    have hk : k x = 0 := image_eq_zero_of_notMem_tsupport (Set.disjoint_left.mp hfk hxt)
    apply subset_tsupport D
    show D x ≠ 0
    rw [hsum x, hg, hk, add_zero, add_zero]
    exact hx

/-- `Φ_t` as a homeomorphism of the plane, with inverse `Φ_t⁻¹`. -/
private theorem exists_flowHomeomorph {c : RingConfig} {R₀ : ℝ}
    (hsd : Smooth.IsSmoothDatum c.datum R₀) (t : ℝ) :
    ∃ e : ℂ ≃ₜ ℂ, (⇑e = c.flow t) ∧ ⇑e.symm = c.flowInv t := by
  obtain ⟨hL, hR, hf, hfi, -⟩ := Smooth.flow_diffeo hsd t
  exact ⟨{ toFun := c.flow t
           invFun := c.flowInv t
           left_inv := hL
           right_inv := hR
           continuous_toFun := hf.continuous
           continuous_invFun := hfi.continuous }, rfl, rfl⟩

/-- `supp (g ∘ Φ_t⁻¹) = Φ_t(supp g)`. -/
private theorem tsupport_comp_flowInv {c : RingConfig} {R₀ : ℝ}
    (hsd : Smooth.IsSmoothDatum c.datum R₀) (t : ℝ) (g : ℂ → ℝ) :
    tsupport (fun x => g (c.flowInv t x)) = c.flow t '' tsupport g := by
  obtain ⟨e, he, hes⟩ := exists_flowHomeomorph hsd t
  have h1 : (fun x => g (c.flowInv t x)) = g ∘ e.symm := by
    rw [hes]; rfl
  rw [h1, tsupport_comp_eq_preimage, ← Homeomorph.image_eq_preimage_symm, he]

/-- `∫ g ∘ Φ_t⁻¹ = ∫ g` (area preservation). -/
private theorem integral_comp_flowInv {c : RingConfig} {R₀ : ℝ}
    (hsd : Smooth.IsSmoothDatum c.datum R₀) (t : ℝ) (g : ℂ → ℝ) :
    ∫ x, g (c.flowInv t x) = ∫ x, g x := by
  obtain ⟨e, -, hes⟩ := exists_flowHomeomorph hsd t
  have hemb : MeasurableEmbedding (c.flowInv t) := hes ▸ e.symm.measurableEmbedding
  exact (Smooth.flow_measurePreserving hsd t).2.integral_comp hemb g

/-- A continuous a.e. `3`-fold symmetric function is pointwise `3`-fold symmetric. -/
private theorem sym_pointwise {f : ℂ → ℝ} (hf : Continuous f) (hs : IsMFoldSymmetric 3 f) :
    ∀ x : ℂ, f (rot (2 * Real.pi / 3) x) = f x := by
  have hrot : Continuous (rot (2 * Real.pi / ((3 : ℕ) : ℝ))) := by
    unfold rot
    exact continuous_const.mul continuous_id
  have hcont : Continuous fun x => f (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x) := hf.comp hrot
  have heq := (hcont.ae_eq_iff_eq volume hf).mp hs
  intro x
  have hx := congrFun heq x
  simpa using hx

/-- The three parts of the datum are `C_c^∞`. -/
private theorem parts0_smooth {c : RingConfig} {T : ℝ} (hc : c.Hyp T) :
    (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c.ring0 ∧ HasCompactSupport c.ring0) ∧
      (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c.inner0 ∧ HasCompactSupport c.inner0) ∧
      (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c.outer0 ∧ HasCompactSupport c.outer0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact part_smooth hc.datum_contDiff hc.datum_hasCompactSupport (fun x => c.datum_apply x)
      hc.disjoint_ring_inner hc.disjoint_ring_outer
  · refine part_smooth (g := c.ring0) (k := c.outer0) hc.datum_contDiff
      hc.datum_hasCompactSupport (fun x => ?_) hc.disjoint_ring_inner.symm
      hc.disjoint_inner_outer
    rw [c.datum_apply]; ring
  · refine part_smooth (g := c.ring0) (k := c.inner0) hc.datum_contDiff
      hc.datum_hasCompactSupport (fun x => ?_) hc.disjoint_ring_outer.symm
      hc.disjoint_inner_outer.symm
    rw [c.datum_apply]; ring

/-- The datum is pointwise `3`-fold symmetric. -/
private theorem datum_sym {c : RingConfig} {T : ℝ} (hc : c.Hyp T) :
    ∀ x : ℂ, c.datum (rot (2 * Real.pi / 3) x) = c.datum x := by
  obtain ⟨⟨hr, -⟩, ⟨hi, -⟩, ⟨ho, -⟩⟩ := parts0_smooth hc
  intro x
  rw [c.datum_apply, c.datum_apply, sym_pointwise hr.continuous hc.sym_ring x,
    sym_pointwise hi.continuous hc.sym_inner x, sym_pointwise ho.continuous hc.sym_outer x]

/-! ### The interface statements -/

/-- **The parts of the configuration are smooth** (`05_single_ring.tex:130-139`): under the
hypotheses of `lem:reduction`, each part `ω_•(0)` of the datum is `C_c^∞`, and each transported
part `ω_•(t,x) = ω_•(0)(Φ_t⁻¹(x))` is `C^∞` on `ℝ × ℝ²`. -/
theorem setting_parts_smooth {c : RingConfig} {T : ℝ} (hc : c.Hyp T) :
    (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c.ring0 ∧ HasCompactSupport c.ring0) ∧
      (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c.inner0 ∧ HasCompactSupport c.inner0) ∧
      (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c.outer0 ∧ HasCompactSupport c.outer0) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => c.ringPart p.1 p.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => c.innerPart p.1 p.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => c.outerPart p.1 p.2) := by
  obtain ⟨R₀, hsd⟩ := exists_isSmoothDatum hc
  obtain ⟨⟨hr, hrc⟩, ⟨hi, hic⟩, ⟨ho, hoc⟩⟩ := parts0_smooth hc
  have hfi := (Smooth.flow_contDiff hsd).2
  exact ⟨⟨hr, hrc⟩, ⟨hi, hic⟩, ⟨ho, hoc⟩, hr.comp hfi, hi.comp hfi, ho.comp hfi⟩

/-- **The solution is the sum of the transported parts; the flow at time `0`**
(`05_single_ring.tex:88-93`, `:133-139`): `ω(t) = ω_r(t) + ω_i(t) + ω_o(t)`, `Φ_t⁻¹` is the
two-sided inverse of `Φ_t`, `Φ_0 = Φ_0⁻¹ = id`, and therefore `w(0) = ω_r(0) - Φ`. -/
theorem setting_sol_eq_parts {c : RingConfig} {T : ℝ} (hc : c.Hyp T) :
    (∀ (t : ℝ) (x : ℂ), c.sol t x = c.ringPart t x + c.innerPart t x + c.outerPart t x) ∧
      (∀ (t : ℝ) (x : ℂ), c.flow t (c.flowInv t x) = x) ∧
      (∀ (t : ℝ) (y : ℂ), c.flowInv t (c.flow t y) = y) ∧
      (∀ x : ℂ, c.flow 0 x = x) ∧ (∀ x : ℂ, c.flowInv 0 x = x) ∧
      ∀ χ : ℝ → ℝ, c.w χ 0 = c.pert0 χ := by
  obtain ⟨R₀, hsd⟩ := exists_isSmoothDatum hc
  have hflow0 : ∀ x : ℂ, c.flow 0 x = x := fun x => (Smooth.flow_global hsd x).2.init
  have hflowInv0 : ∀ x : ℂ, c.flowInv 0 x = x := hflow0
  refine ⟨fun t x => ?_, fun t x => (Smooth.flow_diffeo hsd t).2.1 x,
    fun t y => (Smooth.flow_diffeo hsd t).1 y, hflow0, hflowInv0,
    fun χ => c.w_zero_of_flowInv_zero χ hflowInv0⟩
  rw [c.sol_eq, Smooth.sol_eq_comp_flowInv hsd t x]
  rfl

/-- **Supports of the transported parts** (`05_single_ring.tex:36-37`, `:139`):
`supp ω_•(t) = Φ_t(supp ω_•(0))` for every `t`. -/
theorem setting_tsupport_parts {c : RingConfig} {T : ℝ} (hc : c.Hyp T) (t : ℝ) :
    tsupport (c.ringPart t) = c.flow t '' tsupport c.ring0 ∧
      tsupport (c.innerPart t) = c.flow t '' tsupport c.inner0 ∧
      tsupport (c.outerPart t) = c.flow t '' tsupport c.outer0 := by
  obtain ⟨R₀, hsd⟩ := exists_isSmoothDatum hc
  exact ⟨tsupport_comp_flowInv hsd t c.ring0, tsupport_comp_flowInv hsd t c.inner0,
    tsupport_comp_flowInv hsd t c.outer0⟩

/-- **The inner circulation is conserved** (`05_single_ring.tex:139-140`): `Φ_t` preserves area,
so `∫ ω_i(t) = ∫ ω_i(0) = 2πG` for every `t`. -/
theorem setting_integral_innerPart {c : RingConfig} {T : ℝ} (hc : c.Hyp T) (t : ℝ) :
    ∫ x, c.innerPart t x = 2 * Real.pi * c.G := by
  obtain ⟨R₀, hsd⟩ := exists_isSmoothDatum hc
  have h1 : ∫ x, c.innerPart t x = ∫ x, c.inner0 x := integral_comp_flowInv hsd t c.inner0
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [h1, G, mul_inv_cancel_left₀ hpi]

/-- **Symmetry of the configuration** (`05_single_ring.tex:140-145`): `ω(t)` is `3`-fold
symmetric, the flow commutes with `O = O_{2π/3}`, and each `ω_•(t)` is `3`-fold symmetric (stated
pointwise; the parts are continuous). -/
theorem setting_symmetric {c : RingConfig} {T : ℝ} (hc : c.Hyp T) :
    (∀ (t : ℝ) (y : ℂ),
        c.flow t (rot (2 * Real.pi / 3) y) = rot (2 * Real.pi / 3) (c.flow t y)) ∧
      (∀ (t : ℝ) (x : ℂ), c.sol t (rot (2 * Real.pi / 3) x) = c.sol t x) ∧
      (∀ (t : ℝ) (x : ℂ), c.ringPart t (rot (2 * Real.pi / 3) x) = c.ringPart t x) ∧
      (∀ (t : ℝ) (x : ℂ), c.innerPart t (rot (2 * Real.pi / 3) x) = c.innerPart t x) ∧
      ∀ (t : ℝ) (x : ℂ), c.outerPart t (rot (2 * Real.pi / 3) x) = c.outerPart t x := by
  obtain ⟨R₀, hsd⟩ := exists_isSmoothDatum hc
  obtain ⟨⟨hr, -⟩, ⟨hi, -⟩, ⟨ho, -⟩⟩ := parts0_smooth hc
  have hθ := datum_sym hc
  have hinv : ∀ (t : ℝ) (x : ℂ),
      c.flowInv t (rot (2 * Real.pi / 3) x) = rot (2 * Real.pi / 3) (c.flowInv t x) :=
    fun t x => (Smooth.vel_flow_rot_of_symm hsd hθ t).2.2 x
  refine ⟨fun t y => (Smooth.vel_flow_rot_of_symm hsd hθ t).2.1 y, fun t x => ?_,
    fun t x => ?_, fun t x => ?_, fun t x => ?_⟩
  · rw [c.sol_eq, Smooth.sol_eq_comp_flowInv hsd t, Smooth.sol_eq_comp_flowInv hsd t]
    exact (congrArg c.datum (hinv t x)).trans (hθ _)
  · exact (congrArg c.ring0 (hinv t x)).trans (sym_pointwise hr.continuous hc.sym_ring _)
  · exact (congrArg c.inner0 (hinv t x)).trans (sym_pointwise hi.continuous hc.sym_inner _)
  · exact (congrArg c.outer0 (hinv t x)).trans (sym_pointwise ho.continuous hc.sym_outer _)

/-- **Radial motion controls the support** (`05_single_ring.tex:33-40`): if every trajectory of
`ω_r` moves radially by at most `δ` on `[0,t]`, then for `τ ∈ [0,t]` every point `x` of
`supp ω_r(τ) = Φ_τ(supp ω_r(0))` is `x = Φ_τ(y)` for some `y ∈ supp ω_r(0)` with
`||x| - |y|| ≤ δ`: the support of `ω_r(τ)` lies within radial distance `δ` of
`supp ω_r(0)` (the form taken by `RingData.annuli_slack`, `I/Sec4/Annuli.lean`). -/
theorem setting_movesRadially_tsupport {c : RingConfig} {T : ℝ} (hc : c.Hyp T) {t δ : ℝ}
    (hmove : c.MovesRadially t δ) :
    ∀ τ ∈ Icc (0 : ℝ) t, ∀ x ∈ tsupport (c.ringPart τ),
      ∃ y ∈ tsupport c.ring0, c.flow τ y = x ∧ |‖x‖ - ‖y‖| ≤ δ := by
  intro τ hτ x hx
  rw [(setting_tsupport_parts hc τ).1] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, rfl, hmove y hy τ hτ⟩

end RingConfig

end OneRing

end NonUniqueEuler
