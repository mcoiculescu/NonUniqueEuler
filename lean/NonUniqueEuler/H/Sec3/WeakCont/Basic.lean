import NonUniqueEuler.Defs.Sec3.Transport
import NonUniqueEuler.Defs.Sec3.Paths
import NonUniqueEuler.I.Sec3.WeakCont.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Helpers for the proof of `lem:weak-cont` (`P/Sec3/WeakCont.lean`)

Small, fully proved lemmas: density of an a.e. set of times, continuity and the Lipschitz bound
of primitives `t ↦ ∫_0^t c`, integrability of the flux `c_ψ(t) = ∫ u(t) w(t)·∇ψ` on `(0,T)`,
conversions between `Lp` norms and `eLpNorm`, invariance of `(te)` under a.e. change of the datum,
and "orthogonal to a dense sequence implies zero".
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology InnerProductSpace

namespace NonUniqueEuler.Weak.WeakCont

/-- A vector orthogonal to every member of a sequence with dense range is zero. -/
theorem eq_zero_of_inner_denseRange {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e : ℕ → E} (he : DenseRange e) {x : E} (h : ∀ k, ⟪x, e k⟫_ℝ = 0) : x = 0 := by
  have hcl : IsClosed {y : E | ⟪x, y⟫_ℝ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hsub : range e ⊆ {y : E | ⟪x, y⟫_ℝ = 0} := by
    rintro _ ⟨k, rfl⟩
    exact h k
  have hx : x ∈ {y : E | ⟪x, y⟫_ℝ = 0} := by
    have h1 := hcl.closure_subset_iff.2 hsub
    rw [he.closure_range] at h1
    exact h1 (mem_univ x)
  exact inner_self_eq_zero.1 hx

/-- `(te)` only sees the datum up to a.e. equality. -/
theorem solvesTE_congr_datum {t₀ T : ℝ} {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {u₀ u₀' : ℂ → ℝ}
    (h : SolvesTE t₀ T u w u₀) (he : u₀' =ᵐ[volume] u₀) : SolvesTE t₀ T u w u₀' where
  integrableOn := h.integrableOn
  datum_integrable φ hφ :=
    (h.datum_integrable φ hφ).congr (he.mono fun x hx => by simp only [hx])
  identity φ hφ := by
    have : (fun x => u₀' x * φ (t₀, x)) =ᵐ[volume] fun x => u₀ x * φ (t₀, x) :=
      he.mono fun x hx => by simp only [hx]
    rw [integral_congr_ae this]
    exact h.identity φ hφ

/-- Every `t ∈ [0,T]` is in the closure of a set of full measure in `(0,T)`. -/
theorem mem_closure_of_ae {T : ℝ} (hT : 0 < T) {p : ℝ → Prop}
    (hp : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), p t) {t : ℝ} (ht : t ∈ Icc 0 T) :
    t ∈ closure (Ioo 0 T ∩ {s | p s}) := by
  have hp' : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioo 0 T → p s :=
    (ae_restrict_iff' measurableSet_Ioo).1 hp
  have hD := Measure.dense_of_ae hp'
  rw [_root_.mem_closure_iff]
  intro o ho hto
  have h1 : (o ∩ Ioo 0 T).Nonempty := by
    have : t ∈ closure (Ioo (0 : ℝ) T) := by rw [closure_Ioo hT.ne]; exact ht
    exact _root_.mem_closure_iff.1 this o ho hto
  obtain ⟨s, ⟨hso, hsI⟩, hsp⟩ :=
    dense_iff_inter_open.1 hD (o ∩ Ioo 0 T) (ho.inter isOpen_Ioo) h1
  exact ⟨s, hso, hsI, hsp hsI⟩

/-- The primitive `t ↦ ∫_{(0,t)} c` of `c ∈ L¹(0,T)` is continuous on `[0,T]`. -/
theorem continuousOn_primitive_Ioo {T : ℝ} {c : ℝ → ℝ} (hc : IntegrableOn c (Ioo 0 T)) :
    ContinuousOn (fun t => ∫ s in Ioo 0 t, c s) (Icc 0 T) := by
  have hc' : IntegrableOn c (Icc 0 T) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact hc
  refine (intervalIntegral.continuousOn_primitive hc').congr fun t _ => ?_
  exact (integral_Ioc_eq_integral_Ioo).symm

/-- Lipschitz bound for the primitive of an a.e. bounded `c ∈ L¹(0,T)`. -/
theorem abs_setIntegral_Ioo_sub_le {T C : ℝ} {c : ℝ → ℝ} (hc : IntegrableOn c (Ioo 0 T))
    (hb : ∀ᵐ r ∂(volume.restrict (Ioo 0 T)), |c r| ≤ C) {s t : ℝ} (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) :
    |(∫ r in Ioo 0 t, c r) - ∫ r in Ioo 0 s, c r| ≤ C * |t - s| := by
  have hIoo : ∀ x ∈ Icc 0 T, ∫ r in Ioo 0 x, c r = ∫ r in (0 : ℝ)..x, c r := fun x hx => by
    rw [intervalIntegral.integral_of_le hx.1, integral_Ioc_eq_integral_Ioo]
  have hii : ∀ x ∈ Icc 0 T, IntervalIntegrable c volume 0 x := fun x hx =>
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.1).2
      (hc.mono_set (Ioo_subset_Ioo_right hx.2))
  rw [hIoo t ht, hIoo s hs, intervalIntegral.integral_interval_sub_left (hii t ht) (hii s hs)]
  have h1 : ∀ᵐ r ∂(volume.restrict (Ioc 0 T)), |c r| ≤ C := by
    rwa [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := T))]
  have hb' : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Set.uIoc s t → ‖c r‖ ≤ C := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 h1] with r hr hrI
    rw [Real.norm_eq_abs]
    rw [uIoc, mem_Ioc] at hrI
    exact hr ⟨lt_of_le_of_lt (le_min hs.1 ht.1) hrI.1, hrI.2.trans (max_le hs.2 ht.2)⟩
  exact intervalIntegral.norm_integral_le_of_norm_le_const_ae hb'

/-- Fubini: the slice integrals of an integrable function on the slab are integrable in time. -/
theorem integrableOn_integral_slab {T : ℝ} {F : ℝ × ℂ → ℝ} (hF : IntegrableOn F (slab T)) :
    IntegrableOn (fun t => ∫ x, F (t, x)) (Ioo 0 T) := by
  have h : Integrable F ((volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure ℂ)) := by
    rw [← JointRep.volume_restrict_slab]
    exact hF
  exact h.integral_prod_left

/-- `C^∞ ⇒ C¹`. -/
theorem contDiff_one_of_smooth {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) :
    ContDiff ℝ 1 ψ := by
  simpa using contDiff_infty.1 hψ 1

/-- The flux `c_ψ(t) = ∫ u(t) w(t)·∇ψ` is integrable on `(0,T)`. -/
theorem integrableOn_flux {T : ℝ} {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ}
    (hw : ∀ R : ℝ, 0 < R → Prelim.MemLinfLp (Ioo 0 T) (ball (0 : ℂ) R) 2 w)
    (hu : Prelim.MemLinfLp (Ioo 0 T) univ 2 u) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    IntegrableOn (fun s => ∫ x, u s x * fderiv ℝ ψ x (w s x)) (Ioo 0 T) :=
  integrableOn_integral_slab (F := fun p : ℝ × ℂ => u p.1 p.2 * fderiv ℝ ψ p.2 (w p.1 p.2))
    (integrableOn_slab_mul_fderiv hw hu (contDiff_one_of_smooth hψ) hψc)

/-- The right side `A_ψ(t) = ∫ u₀ ψ + ∫_0^t c_ψ` of the identity (b) is continuous on `[0,T]`. -/
theorem continuousOn_rhs {T : ℝ} {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} (u₀ : ℂ → ℝ)
    (hw : ∀ R : ℝ, 0 < R → Prelim.MemLinfLp (Ioo 0 T) (ball (0 : ℂ) R) 2 w)
    (hu : Prelim.MemLinfLp (Ioo 0 T) univ 2 u) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ContinuousOn (fun t => (∫ x, u₀ x * ψ x) + ∫ s in Ioo 0 t, ∫ x, u s x * fderiv ℝ ψ x (w s x))
      (Icc 0 T) :=
  continuousOn_const.add (continuousOn_primitive_Ioo (integrableOn_flux hw hu hψ hψc))

/-- An `eLpNorm` bound gives a bound on the norm of an `Lp` element. -/
theorem norm_le_of_eLpNorm_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {f : Lp ℝ p μ} {N : ℝ} (hN : 0 ≤ N) (h : eLpNorm f p μ ≤ ENNReal.ofReal N) :
    ‖f‖ ≤ N := by
  rw [Lp.norm_def]
  exact ENNReal.toReal_le_of_le_ofReal hN h

/-- A bound on the norm of an `Lp` element gives an `eLpNorm` bound. -/
theorem eLpNorm_le_of_norm_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {f : Lp ℝ p μ} {N : ℝ} (h : ‖f‖ ≤ N) : eLpNorm f p μ ≤ ENNReal.ofReal N := by
  rw [← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal h

/-- Integrals against the `L²` class of a slice in `L²` are integrals against the slice. -/
theorem integral_toPath_mul {ω : ℝ → ℂ → ℝ} {t : ℝ} (h : MemLp (ω t) 2 volume) (g : ℂ → ℝ) :
    ∫ z, (JointRep.toPath (μ := (volume : Measure ℂ)) ω t : ℂ → ℝ) z * g z = ∫ z, ω t z * g z :=
  integral_congr_ae ((JointRep.coeFn_toPath h).mono fun z hz => by simp only [hz])

end NonUniqueEuler.Weak.WeakCont
