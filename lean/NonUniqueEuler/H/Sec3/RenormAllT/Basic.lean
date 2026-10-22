import NonUniqueEuler.Defs.Sec3.Paths
import NonUniqueEuler.Defs.Sec3.Solutions
import NonUniqueEuler.Defs.Sec3.Transport
import NonUniqueEuler.Defs.Sec3.Auxiliary

/-!
# Helpers for `lem:renorm-all-t`: elementary facts

Helper file of `P/Sec3/RenormAllT.lean` (fully proved).

* `memLinfLp_of_isWeakSolution`: a weak solution in `X₂(T)` lies in `L^∞(0,T;L¹) ∩ L^∞(0,T;L²)`;
  `datum_memLp_two`: its datum is in `L²`.
* `exists_ae_eLpNorm_le`: a nonnegative essential bound in `ℝ≥0∞` form.
* `abs_le_of_isLipO`, `memLp_comp_of_isLipO`, `integrable_comp_of_isLipO`: `|β(s)| ≤ K|s|` for
  `β ∈ Lip₀`, so `β ∘ g ∈ L^p` for `g ∈ L^p`.
* `SolvesTE.congr_datum`: `(te)` only sees the datum up to a.e. equality.
* `memLinfLp_abs`: `|u| ∈ L^∞(I;L^p(Ω))` for `u ∈ L^∞(I;L^p(Ω))`.
* `abs_integral_mul_le`: Cauchy–Schwarz `|∫ f g| ≤ ‖f‖₂ ‖g‖₂`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology InnerProductSpace

namespace NonUniqueEuler.Weak.RenormAllTH

theorem ofReal_two : ENNReal.ofReal (2 : ℝ) = 2 := ENNReal.ofReal_ofNat 2

/-- A weak solution in `X₂(T)` lies in `L^∞(0,T;L¹) ∩ L^∞(0,T;L²)`. -/
theorem memLinfLp_of_isWeakSolution {T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsWeakSolution 2 T ωin ω) :
    Prelim.MemLinfLp (Ioo 0 T) univ 1 ω ∧ Prelim.MemLinfLp (Ioo 0 T) univ 2 ω := by
  have := Prelim.memX_iff.1 h.memX
  rwa [ofReal_two] at this

theorem datum_memLp_two {T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsWeakSolution 2 T ωin ω) : MemLp ωin 2 volume := by
  have := h.datum_memLp_q
  rwa [ofReal_two] at this

/-- A nonnegative essential bound of `‖u(t)‖_{L^p}` in `ℝ≥0∞` form. -/
theorem exists_ae_eLpNorm_le {I : Set ℝ} {p : ℝ≥0∞} {u : ℝ → ℂ → ℝ}
    (h : Prelim.MemLinfLp I univ p u) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ᵐ t ∂(volume.restrict I), eLpNorm (u t) p volume ≤ ENNReal.ofReal N := by
  obtain ⟨M, hM⟩ := h.essBounded
  refine ⟨max M 0, le_max_right _ _, hM.mono fun t ht => ?_⟩
  rw [Measure.restrict_univ] at ht
  rw [← ENNReal.ofReal_toReal ht.1.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal (ht.2.trans (le_max_left _ _))

/-- `|β(s)| ≤ K |s|` for `β ∈ Lip₀`. -/
theorem abs_le_of_isLipO {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s, |β s| ≤ K * |s| := by
  obtain ⟨⟨K, hK⟩, h0⟩ := hβ
  refine ⟨K, K.2, fun s => ?_⟩
  have := hK.dist_le_mul s 0
  simpa [Real.dist_eq, h0] using this

theorem continuous_of_isLipO {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β) : Continuous β := by
  obtain ⟨⟨K, hK⟩, _⟩ := hβ
  exact hK.continuous

theorem memLp_comp_of_isLipO {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β) {g : ℂ → ℝ} {p : ℝ≥0∞}
    (hg : MemLp g p volume) : MemLp (fun x => β (g x)) p volume := by
  obtain ⟨K, -, hK⟩ := abs_le_of_isLipO hβ
  refine hg.of_le_mul (c := K) ((continuous_of_isLipO hβ).comp_aestronglyMeasurable hg.1)
    (Eventually.of_forall fun x => ?_)
  simpa [Real.norm_eq_abs] using hK (g x)

theorem integrable_comp_of_isLipO {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β) {g : ℂ → ℝ}
    (hg : MemLp g 1 volume) : Integrable (fun x => β (g x)) volume :=
  memLp_one_iff_integrable.1 (memLp_comp_of_isLipO hβ hg)

/-- `(te)` sees the datum only up to a.e. equality. -/
theorem SolvesTE.congr_datum {t₀ T : ℝ} {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {u₀ u₀' : ℂ → ℝ}
    (h : SolvesTE t₀ T u w u₀) (he : u₀ =ᵐ[volume] u₀') : SolvesTE t₀ T u w u₀' where
  integrableOn := h.integrableOn
  datum_integrable φ hφ :=
    (h.datum_integrable φ hφ).congr (he.mono fun x hx => by simp only [hx])
  identity φ hφ := by
    have := h.identity φ hφ
    have he' : (fun x => u₀ x * φ (t₀, x)) =ᵐ[volume] fun x => u₀' x * φ (t₀, x) :=
      he.mono fun x hx => by simp only [hx]
    rwa [integral_congr_ae he'] at this

/-- `|u| ∈ L^∞(I;L^p(Ω))` for `u ∈ L^∞(I;L^p(Ω))`. -/
theorem memLinfLp_abs {I : Set ℝ} {Ω : Set ℂ} {p : ℝ≥0∞} {u : ℝ → ℂ → ℝ}
    (h : Prelim.MemLinfLp I Ω p u) : Prelim.MemLinfLp I Ω p (fun t x => |u t x|) := by
  refine ⟨continuous_abs.comp_aestronglyMeasurable h.aestronglyMeasurable, ?_⟩
  obtain ⟨M, hM⟩ := h.essBounded
  refine ⟨M, hM.mono fun t ht => ⟨?_, ?_⟩⟩
  · exact ht.1.of_le_mul (c := 1) (continuous_abs.comp_aestronglyMeasurable ht.1.1)
      (Eventually.of_forall fun x => by simp)
  · have : eLpNorm (fun x => |u t x|) p (volume.restrict Ω) = eLpNorm (u t) p (volume.restrict Ω) :=
      eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by simp)
    rw [this]
    exact ht.2

/-- Cauchy–Schwarz in `L²`: `|∫ f g| ≤ ‖f‖₂ ‖g‖₂`. -/
theorem abs_integral_mul_le {f g : ℂ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    |∫ x, f x * g x| ≤ (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  rw [← WeakL2.inner_toLp_toLp hf hg, ← Lp.norm_toLp f hf, ← Lp.norm_toLp g hg]
  exact abs_real_inner_le_norm _ _

end NonUniqueEuler.Weak.RenormAllTH
