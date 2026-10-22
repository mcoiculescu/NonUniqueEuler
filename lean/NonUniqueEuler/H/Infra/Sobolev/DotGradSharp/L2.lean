import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.L2Space
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `P/Infra/Sobolev/DotGradSharp`: `L²` bounds

* `memLp_l2_le_of_ae_bound`: a function bounded a.e. by `∑ cᵢ |Hᵢ|` with `Hᵢ ∈ L²` lies in `L²`,
  with `‖G‖₂ ≤ ∑ cᵢ ‖Hᵢ‖₂` (Minkowski; same argument as the helper of the same name in
  `H/Infra/Sobolev/Leibniz/L2.lean`);
* `l2_sq_eq_integral`: `‖f‖₂² = ∫ |f|²`;
* `pairNorm A B = (|A|² + |B|²)^{1/2}` and `memLp_pairNorm`: it lies in `L²` with
  `‖pairNorm A B‖₂² = ‖A‖₂² + ‖B‖₂²` (`04_ring.tex:1564`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace NonUniqueEuler.Sob.DotGradSharpAux

theorem memLp_l2_le_of_ae_bound {ι : Type*} (s : Finset ι) {G : ℂ → ℂ} {H : ι → ℂ → ℂ}
    (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) (hH : ∀ i ∈ s, MemLp (H i) 2 volume)
    (hG : AEStronglyMeasurable G volume) (hb : ∀ᵐ x, ‖G x‖ ≤ ∑ i ∈ s, c i * ‖H i x‖) :
    MemLp G 2 volume ∧ l2 G ≤ ∑ i ∈ s, c i * l2 (H i) := by
  set S : ℂ → ℝ := fun x => ∑ i ∈ s, c i * ‖H i x‖ with hSdef
  have hT : ∀ i ∈ s, MemLp (fun x => c i * ‖H i x‖) 2 volume := fun i hi =>
    (hH i hi).norm.const_mul (c i)
  have hS : MemLp S 2 volume := memLp_finsetSum s hT
  have hSnn : ∀ x, 0 ≤ S x := fun x =>
    Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi) (norm_nonneg _)
  have hGm : MemLp G 2 volume :=
    hS.of_le hG (hb.mono fun x hx => by rw [Real.norm_of_nonneg (hSnn x)]; exact hx)
  refine ⟨hGm, ?_⟩
  have h1 : eLpNorm G 2 volume ≤ eLpNorm S 2 volume := eLpNorm_mono_ae_real hb
  have h2 : eLpNorm S 2 volume ≤ ∑ i ∈ s, eLpNorm (fun x => c i * ‖H i x‖) 2 volume := by
    have := eLpNorm_sum_le (f := fun i x => c i * ‖H i x‖) (s := s) (μ := volume)
      (fun i hi => (hT i hi).aestronglyMeasurable) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    convert this using 2
    ext x
    simp [hSdef, Finset.sum_apply]
  have h3 : ∀ i ∈ s, eLpNorm (fun x => c i * ‖H i x‖) 2 volume =
      ENNReal.ofReal (c i) * eLpNorm (H i) 2 volume := by
    intro i hi
    have : (fun x => c i * ‖H i x‖) = c i • (fun x => ‖H i x‖) := rfl
    rw [this, eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal (hc i hi)]
  have hfin : ∀ i ∈ s, ENNReal.ofReal (c i) * eLpNorm (H i) 2 volume ≠ ⊤ := fun i hi =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hH i hi).eLpNorm_ne_top
  have h4 : eLpNorm G 2 volume ≤ ∑ i ∈ s, ENNReal.ofReal (c i) * eLpNorm (H i) 2 volume :=
    h1.trans (h2.trans_eq (Finset.sum_congr rfl h3))
  unfold l2
  calc (eLpNorm G 2 volume).toReal
      ≤ (∑ i ∈ s, ENNReal.ofReal (c i) * eLpNorm (H i) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin) h4
    _ = ∑ i ∈ s, c i * (eLpNorm (H i) 2 volume).toReal := by
        rw [ENNReal.toReal_sum hfin]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hc i hi)]

/-- `‖f‖₂² = ∫ |f|²` for `f ∈ L²`. -/
theorem l2_sq_eq_integral {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    l2 f ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h := hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2] at h
  have hI : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) := integral_nonneg fun x => by positivity
  unfold l2
  rw [h, ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hI]
  norm_num

/-- The pointwise norm `(|A|² + |B|²)^{1/2}` of the pair `(A, B)`, as a complex function. -/
def pairNorm (A B : ℂ → ℂ) (x : ℂ) : ℂ :=
  (Real.sqrt (‖A x‖ ^ 2 + ‖B x‖ ^ 2) : ℂ)

theorem norm_pairNorm (A B : ℂ → ℂ) (x : ℂ) :
    ‖pairNorm A B x‖ = Real.sqrt (‖A x‖ ^ 2 + ‖B x‖ ^ 2) := by
  rw [pairNorm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

theorem memLp_pairNorm {A B : ℂ → ℂ} (hA : MemLp A 2 volume) (hB : MemLp B 2 volume) :
    MemLp (pairNorm A B) 2 volume ∧ l2 (pairNorm A B) ^ 2 = l2 A ^ 2 + l2 B ^ 2 := by
  have hAi : Integrable (fun x => ‖A x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hA.1).1 hA
  have hBi : Integrable (fun x => ‖B x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hB.1).1 hB
  have hsq : ∀ x, ‖pairNorm A B x‖ ^ 2 = ‖A x‖ ^ 2 + ‖B x‖ ^ 2 := fun x => by
    rw [norm_pairNorm, Real.sq_sqrt (by positivity)]
  have hmeas : AEStronglyMeasurable (pairNorm A B) volume := by
    have h1 : AEStronglyMeasurable (fun x => Real.sqrt (‖A x‖ ^ 2 + ‖B x‖ ^ 2)) volume :=
      Real.continuous_sqrt.comp_aestronglyMeasurable
        ((hA.1.norm.pow 2).add (hB.1.norm.pow 2))
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable h1
  have hmem : MemLp (pairNorm A B) 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm hmeas]
    simp_rw [hsq]
    exact hAi.add hBi
  refine ⟨hmem, ?_⟩
  rw [l2_sq_eq_integral hmem, l2_sq_eq_integral hA, l2_sq_eq_integral hB]
  simp_rw [hsq]
  exact integral_add hAi hBi

end NonUniqueEuler.Sob.DotGradSharpAux
