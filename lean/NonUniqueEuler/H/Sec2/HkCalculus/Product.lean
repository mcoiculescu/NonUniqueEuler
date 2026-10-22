import NonUniqueEuler.H.Sec2.HkCalculus.Terms
import NonUniqueEuler.I.Sec2.HkCalculus.ProductLeibniz

/-!
# Helper for `P/Sec2/HkCalculus`: `lem:Hk-calculus`(2), the product bound

`02_prelim.tex:672-688`. For `2 ≤ j ≤ k` and `g, h ∈ H^j`, the weak Leibniz rule
(`hasWeakDerivOn_mul_of_memH`, `I/Sec2/HkCalculus/ProductLeibniz.lean`) and the term bounds
(`prodTerm_bound`) give `‖∂^γ(gh)‖_{L²} ≤ 2^{|γ|} ‖g‖_{H^j} ‖h‖_{H^j}`, hence
`‖gh‖_{H^j} ≤ (k+1) 2^k ‖g‖_{H^j} ‖h‖_{H^j}` (`exists_isHkProdConst`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Sob.HkCalcAux

/-- The Leibniz sum `Σ_{β ≤ γ} C(γ,β) ∂^β g ∂^{γ-β} h`. -/
def leibSum (γ : ℕ × ℕ) (g h : ℂ → ℂ) (x : ℂ) : ℂ :=
  ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ) * weakPartial β g x *
    weakPartial (γ.1 - β.1, γ.2 - β.2) h x

theorem leibSum_bound {j : ℕ} (hj : 2 ≤ j) {g h : ℂ → ℂ} (hg : MemH j g) (hh : MemH j h)
    {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx j) :
    MemLp (leibSum γ g h) 2 volume ∧
      l2 (leibSum γ g h) ≤ 2 ^ (γ.1 + γ.2) * (normH j g * normH j h) := by
  set F : ℕ × ℕ → ℂ → ℂ := fun β x =>
    ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ) *
      (weakPartial β g x * weakPartial (γ.1 - β.1, γ.2 - β.2) h x) with hF
  have hS : leibSum γ g h = fun x => ∑ β ∈ leIdx γ, F β x := by
    funext x
    simp only [leibSum, hF, mul_assoc]
  have hFb : ∀ β ∈ leIdx γ, MemLp (F β) 2 volume ∧
      l2 (F β) ≤ ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℝ) * (normH j g * normH j h) := by
    intro β hβ
    obtain ⟨h1, h2⟩ := prodTerm_bound hj hg hh hγ hβ
    refine ⟨h1.const_mul _, ?_⟩
    rw [hF, l2_const_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  obtain ⟨h1, h2⟩ := l2_finset_sum (leIdx γ) F fun β hβ => (hFb β hβ).1
  rw [hS]
  refine ⟨h1, h2.trans ?_⟩
  calc ∑ β ∈ leIdx γ, l2 (F β) ≤
        ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℝ) * (normH j g * normH j h) :=
        Finset.sum_le_sum fun β hβ => (hFb β hβ).2
    _ = 2 ^ (γ.1 + γ.2) * (normH j g * normH j h) := by
        rw [← Finset.sum_mul, sum_leIdx_choose]

/-- `lem:Hk-calculus`(2) with the constant `(k+1) 2^k`. -/
theorem isHkProdConst_explicit (k : ℕ) : IsHkProdConst k ((k + 1) * 2 ^ k) := by
  intro j hj hjk g h hg hh
  have hD : ∀ γ ∈ multiIdx j, HasWeakDerivOn univ (pdList γ) (g * h) (leibSum γ g h) :=
    fun γ hγ => hasWeakDerivOn_mul_of_memH hj hg hh hγ
  have hmem : MemH j (g * h) := by
    rw [memH_iff]
    refine ⟨(l2_mul_le_of_H2_left (hg.mono_order hj) (memLp_of_memH hh)).1,
      fun γ hγ => ⟨leibSum γ g h, (leibSum_bound hj hg hh hγ).1, hD γ hγ⟩⟩
  refine ⟨hmem, ?_⟩
  have hgn := normH_nonneg j g
  have hhn := normH_nonneg j h
  have hB : ∀ γ ∈ multiIdx j, 0 ≤ l2 (weakPartial γ (g * h)) ∧
      l2 (weakPartial γ (g * h)) ≤ 2 ^ j * (normH j g * normH j h) := by
    intro γ hγ
    obtain ⟨h1, h2⟩ := leibSum_bound hj hg hh hγ
    have h3 := hmem.weakPartial_ae_eq hγ h1 (hD γ hγ)
    refine ⟨l2_nonneg _, ?_⟩
    rw [l2_congr_ae h3]
    refine h2.trans (mul_le_mul_of_nonneg_right ?_ (mul_nonneg hgn hhn))
    exact pow_le_pow_right₀ (by norm_num) (mem_multiIdx.1 hγ)
  rw [normH_eq]
  refine (sqrt_sum_sq_le (card_multiIdx_le j) (by positivity) hB).trans ?_
  have hjk' : ((j : ℝ) + 1) ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hjk
  have h2 : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hjk
  calc ((j + 1 : ℕ) : ℝ) * (2 ^ j * (normH j g * normH j h)) =
        ((j : ℝ) + 1) * 2 ^ j * (normH j g * normH j h) := by push_cast; ring
    _ ≤ ((k : ℝ) + 1) * 2 ^ k * (normH j g * normH j h) := by gcongr
    _ = ((k : ℝ) + 1) * 2 ^ k * normH j g * normH j h := by ring

theorem exists_isHkProdConst (k : ℕ) : ∃ C : ℝ, 0 < C ∧ IsHkProdConst k C :=
  ⟨(k + 1) * 2 ^ k, by positivity, isHkProdConst_explicit k⟩

end NonUniqueEuler.Sob.HkCalcAux
