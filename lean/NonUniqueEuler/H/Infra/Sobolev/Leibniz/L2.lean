import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Data.Nat.Choose.Sum
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `P/Infra/Sobolev/Leibniz`: `L²` and counting bounds

* `memLp_l2_le_of_ae_bound`: a function bounded a.e. by `∑ cᵢ |Hᵢ|` with `Hᵢ ∈ L²` lies in `L²`,
  with `‖G‖₂ ≤ ∑ cᵢ ‖Hᵢ‖₂`;
* `card_multiIdx_le`: `#multiIdx k ≤ (k+1)²`;
* `sum_choose_leIdx`: `∑_{β ≤ γ} C(γ₁,β₁) C(γ₂,β₂) = 2^{|γ|}`;
* `sqrt_sum_sq_le`: `(∑_{γ ∈ multiIdx k} aᵧ²)^{1/2} ≤ (k+1) B` when `0 ≤ aᵧ ≤ B`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace NonUniqueEuler.Sob.LeibnizAux

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

theorem card_multiIdx_le (k : ℕ) : ((multiIdx k).card : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
  have : (multiIdx k).card ≤ (k + 1) ^ 2 := by
    unfold multiIdx
    refine (Finset.card_filter_le _ _).trans ?_
    simp [Finset.card_product, sq]
  exact_mod_cast this

theorem sum_choose_leIdx (γ : ℕ × ℕ) :
    ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℝ) = 2 ^ (γ.1 + γ.2) := by
  have : ∑ β ∈ leIdx γ, (γ.1.choose β.1 * γ.2.choose β.2 : ℕ) = 2 ^ (γ.1 + γ.2) := by
    rw [leIdx, Finset.sum_product, pow_add, ← Nat.sum_range_choose γ.1,
      ← Nat.sum_range_choose γ.2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  exact_mod_cast this

theorem sqrt_sum_sq_le {k : ℕ} {a : ℕ × ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (ha0 : ∀ γ ∈ multiIdx k, 0 ≤ a γ) (ha : ∀ γ ∈ multiIdx k, a γ ≤ B) :
    Real.sqrt (∑ γ ∈ multiIdx k, a γ ^ 2) ≤ (k + 1) * B := by
  rw [Real.sqrt_le_left (by positivity)]
  calc ∑ γ ∈ multiIdx k, a γ ^ 2 ≤ ∑ _γ ∈ multiIdx k, B ^ 2 :=
        Finset.sum_le_sum fun γ hγ => pow_le_pow_left₀ (ha0 γ hγ) (ha γ hγ) 2
    _ = (multiIdx k).card * B ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((k : ℝ) + 1) ^ 2 * B ^ 2 := by gcongr; exact card_multiIdx_le k
    _ = ((k + 1) * B) ^ 2 := by ring

end NonUniqueEuler.Sob.LeibnizAux
