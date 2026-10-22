import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Normed.Group.Bounded
import NonUniqueEuler.I.Infra.Sobolev.Leibniz
import NonUniqueEuler.I.Infra.Sobolev.Density
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Proof of `I/Sec2/HkCalculus/ProductLeibniz.lean`: the weak Leibniz rule in `H^j × H^j`

Manuscript: `lem:Hk-calculus`, `02_prelim.tex:672-688` (proof of (2)) and `02_prelim.tex:697-707`
(`eq:Leibniz-comm`).

Statement. For `g, h ∈ H^j(ℝ²)` and `|γ| ≤ j`,
`∂^γ(gh) = Σ_{β ≤ γ} C(γ₁,β₁) C(γ₂,β₂) ∂^β g ∂^{γ-β} h` weakly on the plane.

Proof (density in the second factor, as in the manuscript, but with the limit passage done
against the test function). Fix a test function `φ`, put `ψ = ∂^γ φ`, and let
`L(u) = ∫ g u ψ`, `R(u) = ∫ (Σ_β C(γ,β) ∂^β g ∂^{γ-β} u) φ`.
1. For a test function `h'`, `MemH.weakPartial_mul_ae_eq` (multiplier `χ = h'`, `f = g`) and the
   reflection `β ↦ γ - β` of `leIdx γ` give `L(h') = (-1)^{|γ|} R'(h')`, where `R'` uses the
   classical derivatives of `h'` (`hasWeakDerivOn_mul_testFn`).
2. `|L(h) - L(h')| ≤ ‖g ψ‖₂ ‖h - h'‖₂` and
   `|R(h) - R'(h')| ≤ Σ_β C(γ,β) ‖∂^β g φ‖₂ ‖∂^{γ-β}(h - h')‖₂` by Cauchy–Schwarz
   (`norm_integral_mul_le_l2`), using `∂^δ (h - h') = ∂^δ h - ∂^δ h'` a.e.
   (`weakPartial_sub_ae`). Both are `≤ M ‖h - h'‖_{H^j}` with `M` independent of `h'`.
3. Density (`MemH.exists_testFn_approx`) makes `‖h - h'‖_{H^j}` arbitrarily small, so
   `L(h) = (-1)^{|γ|} R(h)`.

**Deviation (simplification).** Since the test function `φ` is bounded with compact support,
`∂^β g φ ∈ L²` for every `β`, so the limit passage needs only Cauchy–Schwarz in `L²`; the
embeddings (E1), (E2) of `lem:embed` used in the manuscript's term bounds are not needed, and the
hypothesis `2 ≤ j` is not used (the product rule holds weakly for all `j`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Sob

namespace ProductLeibnizAux

/-- Cauchy–Schwarz for complex functions: `‖∫ A D‖ ≤ ‖A‖₂ ‖D‖₂`. -/
theorem norm_integral_mul_le_l2 {A D : ℂ → ℂ} (hA : MemLp A 2 volume) (hD : MemLp D 2 volume) :
    ‖∫ x, A x * D x‖ ≤ l2 A * l2 D := by
  have h1 : ‖∫ x, A x * D x‖ ≤ ∫ x, ‖A x‖ * ‖D x‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp only [norm_mul]
  have h2 := integral_mul_norm_le_Lp_mul_Lq (μ := volume) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (by simpa using hA) (by simpa using hD)
  have e : ∀ F : ℂ → ℂ, MemLp F 2 volume →
      l2 F = (∫ x, ‖F x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    intro F hF
    rw [l2, hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
      ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => by positivity) _)]
    norm_num
  rw [e A hA, e D hD]
  exact h1.trans h2

/-- `L² × L² × L^∞ ⊆ L¹`. -/
theorem integrable_mul_mul {A B C : ℂ → ℂ} (hA : MemLp A 2 volume) (hB : MemLp B 2 volume)
    (hC : MemLp C ⊤ volume) : Integrable (fun x => A x * B x * C x) volume :=
  (hA.integrable_mul hB).mul_of_top_left hC

/-- `L² × L^∞ ⊆ L²`. -/
theorem memLp_mul_top {A C : ℂ → ℂ} (hA : MemLp A 2 volume) (hC : MemLp C ⊤ volume) :
    MemLp (fun x => A x * C x) 2 volume :=
  MemLp.mul' (r := 2) hC hA

/-- A test function lies in `C^k(ℝ²)` (all derivatives are continuous with compact support). -/
theorem memCk_of_isTestFn {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) (k : ℕ) : MemCk k univ φ := by
  refine ⟨⟨univ, isOpen_univ, subset_rfl, (contDiff_infty.1 hφ.smooth k).contDiffOn⟩, ?_⟩
  have hb : ∀ q : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ q φ x‖ ≤ C := fun q =>
    ((contDiff_infty.1 hφ.smooth q).continuous_iteratedFDeriv le_rfl).bounded_above_of_compact_support
      (hφ.compact.iteratedFDeriv q)
  choose M hM using hb
  exact normCkE_ne_top_of_bound M fun q _ x _ => hM q x

theorem mem_leIdx {γ β : ℕ × ℕ} : β ∈ leIdx γ ↔ β.1 ≤ γ.1 ∧ β.2 ≤ γ.2 := by
  simp only [leIdx, Finset.mem_product, Finset.mem_range]
  omega

/-- Multi-indices `β ≤ γ` and `γ - β` have order `≤ j` when `|γ| ≤ j`. -/
theorem mem_multiIdx_of_mem_leIdx {j : ℕ} {γ β : ℕ × ℕ} (hγ : γ ∈ multiIdx j)
    (hβ : β ∈ leIdx γ) : β ∈ multiIdx j ∧ (γ.1 - β.1, γ.2 - β.2) ∈ multiIdx j := by
  rw [mem_multiIdx] at hγ
  rw [mem_leIdx] at hβ
  refine ⟨mem_multiIdx.2 (by omega), mem_multiIdx.2 (by simp only; omega)⟩

/-- The reflection `β ↦ γ - β` of `leIdx γ` in a Leibniz sum
(`C(γ, γ - β) = C(γ, β)`). -/
theorem sum_leIdx_swap (γ : ℕ × ℕ) (a b : ℕ × ℕ → ℂ) :
    ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ) * a β *
        b (γ.1 - β.1, γ.2 - β.2) =
      ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ) * b β *
        a (γ.1 - β.1, γ.2 - β.2) := by
  refine Finset.sum_nbij' (fun β => (γ.1 - β.1, γ.2 - β.2)) (fun β => (γ.1 - β.1, γ.2 - β.2))
    ?_ ?_ ?_ ?_ ?_
  · intro β hβ
    rw [mem_leIdx] at hβ ⊢
    simp only
    omega
  · intro β hβ
    rw [mem_leIdx] at hβ ⊢
    simp only
    omega
  · intro β hβ
    rw [mem_leIdx] at hβ
    ext <;> simp only <;> omega
  · intro β hβ
    rw [mem_leIdx] at hβ
    ext <;> simp only <;> omega
  · intro β hβ
    rw [mem_leIdx] at hβ
    have e1 : γ.1 - (γ.1 - β.1) = β.1 := by omega
    have e2 : γ.2 - (γ.2 - β.2) = β.2 := by omega
    simp only [e1, e2, Nat.choose_symm hβ.1, Nat.choose_symm hβ.2]
    have e4 : (β.1, β.2) = β := rfl
    rw [e4]
    ring

/-- The weak Leibniz rule when the second factor is a test function. -/
theorem hasWeakDerivOn_mul_testFn {j : ℕ} {g h' : ℂ → ℂ} (hg : MemH j g)
    (hh' : IsTestFn univ h') {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx j) :
    HasWeakDerivOn univ (pdList γ) (fun x => g x * h' x) (fun x =>
      ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ) * weakPartial β g x *
        partialD (γ.1 - β.1, γ.2 - β.2) h' x) := by
  have hCk := memCk_of_isTestFn hh' j
  have hmem : MemH j (fun x => h' x * g x) :=
    (MemH.mul_of_memCk isClosed_univ hg
      (Filter.Eventually.of_forall fun x hx => absurd (mem_univ x) hx) hCk).1
  have hw := (hmem.memLp_weakPartial hγ).2
  have hae := hg.weakPartial_mul_ae_eq hCk hγ
  refine hw.congr_ae (Filter.Eventually.of_forall fun x _ => mul_comm _ _) ?_
  filter_upwards [hae] with x hx _
  rw [hx]
  exact sum_leIdx_swap γ (fun β => partialD β h' x) (fun β => weakPartial β g x)

/-- `∂^δ (h - h') = ∂^δ h - ∂^δ h'` a.e. for a test function `h'`. -/
theorem weakPartial_sub_ae {j : ℕ} {h h' : ℂ → ℂ} (hh : MemH j h) (hh' : IsTestFn univ h')
    (hd : MemH j (h - h')) {δ : ℕ × ℕ} (hδ : δ ∈ multiIdx j) :
    weakPartial δ (h - h') =ᵐ[volume] fun x => weakPartial δ h x - partialD δ h' x := by
  obtain ⟨h1, h2⟩ := hh.memLp_weakPartial hδ
  have hc : HasWeakDerivOn univ (pdList δ) h' (partialD δ h') :=
    hasWeakDerivOn_of_contDiffOn isOpen_univ (n := δ.1 + δ.2) (by simp)
      (contDiff_infty.1 hh'.smooth _).contDiffOn
  have hpL2 : MemLp (partialD δ h') 2 volume := (hh'.partialD δ).memLp 2 volume
  have hhL2 : MemLp h 2 volume := (memH_iff.1 hh).1
  have hadd : HasWeakDerivOn univ (pdList δ) (h + fun x => -1 * h' x)
      (weakPartial δ h + fun x => -1 * partialD δ h' x) := HasWeakDerivOn.add isOpen_univ
    ((hhL2.locallyIntegrable (by norm_num)).locallyIntegrableOn univ)
    (((continuous_const.mul hh'.continuous).locallyIntegrable (μ := volume)).locallyIntegrableOn
      univ)
    ((h1.locallyIntegrable (by norm_num)).locallyIntegrableOn univ)
    (((continuous_const.mul (hh'.partialD δ).continuous).locallyIntegrable
      (μ := volume)).locallyIntegrableOn univ)
    h2 (hc.const_mul (-1))
  have e1 : (h + fun x => -1 * h' x) = h - h' := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have e2 : (weakPartial δ h + fun x => -1 * partialD δ h' x) =
      fun x => weakPartial δ h x - partialD δ h' x := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [e1, e2] at hadd
  exact hd.weakPartial_ae_eq hδ (h1.sub hpL2) hadd

/-- Step 2, first factor: `|∫ g u ψ - ∫ g u' ψ| ≤ ‖g ψ‖₂ ‖u - u'‖₂`. -/
theorem norm_integral_sub_le {g u u' ψ : ℂ → ℂ} (hg : MemLp g 2 volume) (hu : MemLp u 2 volume)
    (hu' : MemLp u' 2 volume) (hψ : MemLp ψ ⊤ volume) :
    ‖(∫ x, g x * u x * ψ x) - ∫ x, g x * u' x * ψ x‖ ≤
      l2 (fun x => g x * ψ x) * l2 (fun x => u x - u' x) := by
  rw [← integral_sub (integrable_mul_mul hg hu hψ) (integrable_mul_mul hg hu' hψ)]
  have e : (fun x => g x * u x * ψ x - g x * u' x * ψ x) =
      fun x => (g x * ψ x) * (u x - u' x) := by
    funext x
    ring
  rw [e]
  exact norm_integral_mul_le_l2 (memLp_mul_top hg hψ) (hu.sub hu')

/-- Integrability of `(Σ_β c_β A_β B_β) φ` for `A_β, B_β ∈ L²`, `φ ∈ L^∞`. -/
theorem integrable_sum_mul {s : Finset (ℕ × ℕ)} {c : ℕ × ℕ → ℂ} {A B : ℕ × ℕ → ℂ → ℂ}
    {φ : ℂ → ℂ} (hA : ∀ β ∈ s, MemLp (A β) 2 volume) (hB : ∀ β ∈ s, MemLp (B β) 2 volume)
    (hφ : MemLp φ ⊤ volume) :
    Integrable (fun x => (∑ β ∈ s, c β * A β x * B β x) * φ x) volume := by
  have : Integrable (fun x => ∑ β ∈ s, c β * (A β x * B β x * φ x)) volume :=
    integrable_finsetSum _ fun β hβ => (integrable_mul_mul (hA β hβ) (hB β hβ) hφ).const_mul _
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Finset.sum_mul]
  exact Finset.sum_congr rfl fun β _ => by ring

/-- Step 2, second factor:
`|∫ (Σ c_β A_β B_β) φ - ∫ (Σ c_β A_β B'_β) φ| ≤ (Σ |c_β| ‖A_β φ‖₂) ε` when
`‖B_β - B'_β‖₂ ≤ ε`. -/
theorem norm_integral_sum_sub_le {s : Finset (ℕ × ℕ)} {c : ℕ × ℕ → ℂ}
    {A B B' : ℕ × ℕ → ℂ → ℂ} {φ : ℂ → ℂ} {ε : ℝ} (hA : ∀ β ∈ s, MemLp (A β) 2 volume)
    (hB : ∀ β ∈ s, MemLp (B β) 2 volume) (hB' : ∀ β ∈ s, MemLp (B' β) 2 volume)
    (hφ : MemLp φ ⊤ volume) (hε : ∀ β ∈ s, l2 (fun x => B β x - B' β x) ≤ ε) :
    ‖(∫ x, (∑ β ∈ s, c β * A β x * B β x) * φ x) -
        ∫ x, (∑ β ∈ s, c β * A β x * B' β x) * φ x‖ ≤
      (∑ β ∈ s, ‖c β‖ * l2 (fun x => A β x * φ x)) * ε := by
  rw [← integral_sub (integrable_sum_mul hA hB hφ) (integrable_sum_mul hA hB' hφ)]
  have e : (fun x => (∑ β ∈ s, c β * A β x * B β x) * φ x -
      (∑ β ∈ s, c β * A β x * B' β x) * φ x) =
      fun x => ∑ β ∈ s, c β * ((A β x * φ x) * (B β x - B' β x)) := by
    funext x
    rw [← sub_mul, ← Finset.sum_sub_distrib, Finset.sum_mul]
    exact Finset.sum_congr rfl fun β _ => by ring
  have hAφ : ∀ β ∈ s, MemLp (fun x => A β x * φ x) 2 volume := fun β hβ =>
    memLp_mul_top (hA β hβ) hφ
  have hD : ∀ β ∈ s, MemLp (fun x => B β x - B' β x) 2 volume := fun β hβ =>
    (hB β hβ).sub (hB' β hβ)
  rw [e, integral_finsetSum s (f := fun β x => c β * ((A β x * φ x) * (B β x - B' β x)))
    fun β hβ => ((hAφ β hβ).integrable_mul (hD β hβ)).const_mul (c β)]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun β hβ => ?_
  rw [integral_const_mul, norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (norm_integral_mul_le_l2 (hAφ β hβ) (hD β hβ)).trans
    (mul_le_mul_of_nonneg_left (hε β hβ) (l2_nonneg _))

/-- Algebra of step 3. -/
theorem norm_sub_mul_le {a a' r t s : ℂ} (hL : a' = s * t) (hs : ‖s‖ = 1) :
    ‖a - s * r‖ ≤ ‖a - a'‖ + ‖r - t‖ := by
  have : a - s * r = (a - a') - s * (r - t) := by
    rw [hL]
    ring
  rw [this]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, hs, one_mul]

/-- If `‖a - b‖ ≤ M ε` for every `ε > 0`, then `a = b`. -/
theorem eq_of_forall_norm_sub_le {a b : ℂ} {M : ℝ} (h : ∀ ε : ℝ, 0 < ε → ‖a - b‖ ≤ M * ε) :
    a = b := by
  have h1 : ∀ ε : ℝ, 0 < ε → ‖a - b‖ ≤ ε := by
    intro ε hε
    have hM1 : 0 < |M| + 1 := by positivity
    have := h (ε / (|M| + 1)) (div_pos hε hM1)
    calc ‖a - b‖ ≤ M * (ε / (|M| + 1)) := this
      _ ≤ (|M| + 1) * (ε / (|M| + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self M]) (div_pos hε hM1).le
      _ = ε := mul_div_cancel₀ ε hM1.ne'
  by_contra hne
  have hpos : 0 < ‖a - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have := h1 (‖a - b‖ / 2) (by positivity)
  linarith

end ProductLeibnizAux

open ProductLeibnizAux

/-- The weak Leibniz rule for products of two `H^j` functions, `j ≥ 2`:
`∂^γ(gh) = Σ_{β ≤ γ} C(γ,β) ∂^β g ∂^{γ-β} h` weakly on the plane, for `|γ| ≤ j`. -/
theorem hasWeakDerivOn_mul_of_memH {j : ℕ} (hj : 2 ≤ j) {g h : ℂ → ℂ} (hg : MemH j g)
    (hh : MemH j h) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx j) :
    HasWeakDerivOn univ (pdList γ) (fun x => g x * h x) (fun x =>
      ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ) * weakPartial β g x *
        weakPartial (γ.1 - β.1, γ.2 - β.2) h x) := by
  have _h2j : 2 ≤ j := hj -- the hypothesis `2 ≤ j` is not needed (see the module docstring)
  intro φ hφ
  beta_reduce
  have hψ := hφ.iterDirDeriv (pdList γ)
  have hgL2 : MemLp g 2 volume := (memH_iff.1 hg).1
  have hhL2 : MemLp h 2 volume := (memH_iff.1 hh).1
  have hA : ∀ β ∈ leIdx γ, MemLp (weakPartial β g) 2 volume := fun β hβ =>
    (hg.memLp_weakPartial (mem_multiIdx_of_mem_leIdx hγ hβ).1).1
  have hB : ∀ β ∈ leIdx γ, MemLp (weakPartial (γ.1 - β.1, γ.2 - β.2) h) 2 volume := fun β hβ =>
    (hh.memLp_weakPartial (mem_multiIdx_of_mem_leIdx hγ hβ).2).1
  refine eq_of_forall_norm_sub_le (M := l2 (fun x => g x * iterDirDeriv (pdList γ) φ x) +
    ∑ β ∈ leIdx γ, ‖((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ)‖ *
      l2 (fun x => weakPartial β g x * φ x)) fun ε hε => ?_
  have hM : 0 ≤ l2 (fun x => g x * iterDirDeriv (pdList γ) φ x) +
      ∑ β ∈ leIdx γ, ‖((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ)‖ *
        l2 (fun x => weakPartial β g x * φ x) :=
    add_nonneg (l2_nonneg _)
      (Finset.sum_nonneg fun β _ => mul_nonneg (norm_nonneg _) (l2_nonneg _))
  obtain ⟨h', hh', hd, hdε⟩ := hh.exists_testFn_approx hε
  have hL := hasWeakDerivOn_mul_testFn hg hh' hγ φ hφ
  beta_reduce at hL
  refine (norm_sub_mul_le hL (by simp)).trans ?_
  have hb := norm_integral_sub_le hgL2 hhL2 (hh'.memLp 2 volume) (hψ.memLp ⊤ volume)
  have hb' : l2 (fun x => h x - h' x) ≤ normH j (h - h') := hd.l2_le
  have hε' : ∀ β ∈ leIdx γ, l2 (fun x => weakPartial (γ.1 - β.1, γ.2 - β.2) h x -
      partialD (γ.1 - β.1, γ.2 - β.2) h' x) ≤ normH j (h - h') := by
    intro β hβ
    have hδ := (mem_multiIdx_of_mem_leIdx hγ hβ).2
    have hae := weakPartial_sub_ae hh hh' hd hδ
    rw [l2, ← eLpNorm_congr_ae hae]
    exact hd.l2_weakPartial_le hδ
  have hc := norm_integral_sum_sub_le (s := leIdx γ)
    (c := fun β => ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ))
    (A := fun β => weakPartial β g) (B := fun β => weakPartial (γ.1 - β.1, γ.2 - β.2) h)
    (B' := fun β => partialD (γ.1 - β.1, γ.2 - β.2) h') (φ := φ) hA hB
    (fun β _ => (hh'.partialD _).memLp 2 volume) (hφ.memLp ⊤ volume) hε'
  calc _ ≤ l2 (fun x => g x * iterDirDeriv (pdList γ) φ x) * normH j (h - h') +
        (∑ β ∈ leIdx γ, ‖((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ)‖ *
          l2 (fun x => weakPartial β g x * φ x)) * normH j (h - h') :=
        add_le_add (hb.trans (mul_le_mul_of_nonneg_left hb' (l2_nonneg _))) hc
    _ = (l2 (fun x => g x * iterDirDeriv (pdList γ) φ x) +
        ∑ β ∈ leIdx γ, ‖((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ)‖ *
          l2 (fun x => weakPartial β g x * φ x)) * normH j (h - h') := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdε.le hM

end NonUniqueEuler.Sob
