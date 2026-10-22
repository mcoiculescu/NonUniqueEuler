import Mathlib.Tactic.LinearCombination
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.Density
import NonUniqueEuler.H.Infra.Sobolev.Interp.Basic

/-!
# Proof: `lem:embed` (E3), the interpolation inequality (library I-HK)

Manuscript: `02_prelim.tex:607-608, 632-643`. For an integer `k ≥ 0` and `g ∈ H^{2k}`,
`‖g‖²_{H^k} ≤ 3^k ‖g‖_{L²} ‖g‖_{H^{2k}}`.

Restructuring R3 (integration by parts instead of Plancherel):
1. for a test function `φ`, testing the weak derivatives `∂^γ g` and `∂^{2γ} g` against
   `∂^γ conj φ` and `conj φ` gives `∫ ∂^γ g · conj(∂^γ φ) = (-1)^{|γ|} ∫ ∂^{2γ} g · conj φ`
   (`key_testFn`);
2. density of test functions in `H^{2k}` and continuity of the `L²` inner product give
   `‖∂^γ g‖² = (-1)^{|γ|} ⟨g, ∂^{2γ} g⟩` (`l2_weakPartial_sq_eq`);
3. Cauchy–Schwarz and `‖∂^{2γ} g‖ ≤ ‖g‖_{H^{2k}}` give `‖∂^γ g‖² ≤ ‖g‖ ‖g‖_{H^{2k}}`; summing over
   `|γ| ≤ k` and `#multiIdx k ≤ 3^k` give (E3).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology InnerProductSpace

namespace NonUniqueEuler.Sob

/-- `pdList (2γ)` is a permutation of `pdList γ ++ pdList γ`. -/
private theorem pdList_double_perm (γ : ℕ × ℕ) :
    (pdList (2 * γ.1, 2 * γ.2)).Perm (pdList γ ++ pdList γ) := by
  rw [List.perm_iff_count]
  intro x
  simp only [pdList, List.count_append, List.count_replicate]
  split_ifs <;> omega

private theorem mem_multiIdx_double {k : ℕ} {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    γ ∈ multiIdx (2 * k) ∧ (2 * γ.1, 2 * γ.2) ∈ multiIdx (2 * k) := by
  rw [mem_multiIdx] at hγ
  exact ⟨mem_multiIdx.2 (by omega), mem_multiIdx.2 (by simp only; omega)⟩

/-- Step 1: the integration-by-parts identity against a test function. -/
private theorem key_testFn {k : ℕ} {g : ℂ → ℂ} (hg : MemH (2 * k) g) {γ : ℕ × ℕ}
    (hγ : γ ∈ multiIdx k) {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) :
    ∫ x, weakPartial γ g x * starRingEnd ℂ (partialD γ φ x) =
      (-1 : ℂ) ^ (γ.1 + γ.2) *
        ∫ x, weakPartial (2 * γ.1, 2 * γ.2) g x * starRingEnd ℂ (φ x) := by
  obtain ⟨hγ1, hγ2⟩ := mem_multiIdx_double hγ
  have h1 := (hg.memLp_weakPartial hγ1).2
  have h2 := ((hg.memLp_weakPartial hγ2).2).perm (pdList_double_perm γ)
  have hψ : IsTestFn univ (fun x => starRingEnd ℂ (φ x)) := InterpH.isTestFn_conj hφ
  have e1 := h1 _ (hψ.partialD γ)
  have e2 := h2 _ hψ
  rw [iterDirDeriv_append] at e2
  have hpsi : partialD γ (fun x => starRingEnd ℂ (φ x)) =
      fun x => starRingEnd ℂ (partialD γ φ x) := InterpH.iterDirDeriv_conj _ _
  have e : (-1 : ℂ) ^ (γ.1 + γ.2) *
        ∫ x, weakPartial γ g x * starRingEnd ℂ (partialD γ φ x) =
      (-1 : ℂ) ^ (γ.1 + γ.2) * (-1 : ℂ) ^ (γ.1 + γ.2) *
        ∫ x, weakPartial (2 * γ.1, 2 * γ.2) g x * starRingEnd ℂ (φ x) := by
    have e12 := e1.symm.trans e2
    simp only [hpsi, pdList_length, List.length_append] at e12
    rw [← pow_add]
    exact e12
  have hs : (-1 : ℂ) ^ (γ.1 + γ.2) * (-1 : ℂ) ^ (γ.1 + γ.2) = 1 := by
    rw [← mul_pow]; norm_num
  linear_combination (-1 : ℂ) ^ (γ.1 + γ.2) * e -
    ((∫ x, weakPartial γ g x * starRingEnd ℂ (partialD γ φ x)) -
      (-1 : ℂ) ^ (γ.1 + γ.2) *
        ∫ x, weakPartial (2 * γ.1, 2 * γ.2) g x * starRingEnd ℂ (φ x)) * hs

/-- For `g ∈ L²` with `L²` weak derivative `h = ∂^γ g` and a test function `φ`,
`h - ∂^γ φ` is the weak derivative of `g - φ`. -/
private theorem hasWeakDerivOn_sub_testFn {γ : ℕ × ℕ} {g h φ : ℂ → ℂ}
    (hgL : MemLp g 2 volume) (hhL : MemLp h 2 volume)
    (hgh : HasWeakDerivOn univ (pdList γ) g h) (hφ : IsTestFn univ φ) :
    HasWeakDerivOn univ (pdList γ) (g - φ) (h - partialD γ φ) := by
  have hφW : HasWeakDerivOn univ (pdList γ) φ (partialD γ φ) :=
    hasWeakDerivOn_of_contDiffOn isOpen_univ (n := γ.1 + γ.2) (by simp)
      (hφ.smooth.of_le (by exact_mod_cast le_top)).contDiffOn
  have hli : ∀ {u : ℂ → ℂ}, MemLp u 2 volume → LocallyIntegrableOn u univ := fun hu =>
    (hu.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have := HasWeakDerivOn.add isOpen_univ (hli hgL) (hli ((hφ.memLp 2 volume).const_mul (-1)))
    (hli hhL) (hli (((hφ.partialD γ).memLp 2 volume).const_mul (-1))) hgh (hφW.const_mul (-1))
  convert this using 1 <;> funext x <;> simp [sub_eq_add_neg]

/-- The integration-by-parts identity behind (E3): `‖∂^γ g‖² = (-1)^{|γ|} ⟨g, ∂^{2γ} g⟩`. -/
theorem l2_weakPartial_sq_eq {k : ℕ} {g : ℂ → ℂ} (hg : MemH (2 * k) g) {γ : ℕ × ℕ}
    (hγ : γ ∈ multiIdx k) :
    ((l2 (weakPartial γ g) ^ 2 : ℝ) : ℂ) =
      (-1 : ℂ) ^ (γ.1 + γ.2) *
        ∫ x, (starRingEnd ℂ) (g x) * weakPartial (2 * γ.1, 2 * γ.2) g x := by
  obtain ⟨hγ1, hγ2⟩ := mem_multiIdx_double hγ
  obtain ⟨hhL, hhW⟩ := hg.memLp_weakPartial hγ1
  have hfL := (hg.memLp_weakPartial hγ2).1
  have hgL : MemLp g 2 volume := (memH_iff.1 hg).1
  -- an approximating sequence of test functions
  have hex : ∀ n : ℕ, ∃ φ : ℂ → ℂ, IsTestFn univ φ ∧ MemH (2 * k) (g - φ) ∧
      normH (2 * k) (g - φ) < 1 / ((n : ℝ) + 1) :=
    fun n => hg.exists_testFn_approx (by positivity)
  choose φ hφ hφH hφn using hex
  have hA : ∀ n, MemLp (partialD γ (φ n)) 2 volume := fun n =>
    ((hφ n).partialD γ).memLp 2 volume
  have hB : ∀ n, MemLp (φ n) 2 volume := fun n => (hφ n).memLp 2 volume
  -- distances in `L²`
  have hdA : ∀ n, l2 (weakPartial γ g - partialD γ (φ n)) < 1 / ((n : ℝ) + 1) := by
    intro n
    have hW := hasWeakDerivOn_sub_testFn hgL hhL hhW (hφ n)
    have hae := (hφH n).weakPartial_ae_eq hγ1 (hhL.sub (hA n)) hW
    have : l2 (weakPartial γ g - partialD γ (φ n)) = l2 (weakPartial γ (g - φ n)) := by
      unfold l2; rw [eLpNorm_congr_ae hae]
    rw [this]
    exact ((hφH n).l2_weakPartial_le hγ1).trans_lt (hφn n)
  have hdB : ∀ n, l2 (g - φ n) < 1 / ((n : ℝ) + 1) := fun n =>
    ((hφH n).l2_le).trans_lt (hφn n)
  have tA : Tendsto (fun n => (hA n).toLp (partialD γ (φ n))) atTop (𝓝 (hhL.toLp _)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [← MemLp.toLp_sub, Lp.norm_toLp, eLpNorm_sub_comm]
    exact (hdA n).le
  have tB : Tendsto (fun n => (hB n).toLp (φ n)) atTop (𝓝 (hgL.toLp g)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [← MemLp.toLp_sub, Lp.norm_toLp, eLpNorm_sub_comm]
    exact (hdB n).le
  have lim1 := Filter.Tendsto.inner (𝕜 := ℂ) tA
    (tendsto_const_nhds (x := hhL.toLp (weakPartial γ g)))
  have lim2 := (Filter.Tendsto.inner (𝕜 := ℂ) tB
    (tendsto_const_nhds (x := hfL.toLp _))).const_mul
    ((-1 : ℂ) ^ (γ.1 + γ.2))
  have heq : ∀ n, ⟪(hA n).toLp (partialD γ (φ n)), hhL.toLp (weakPartial γ g)⟫_ℂ =
      (-1 : ℂ) ^ (γ.1 + γ.2) * ⟪(hB n).toLp (φ n), hfL.toLp _⟫_ℂ := by
    intro n
    rw [← InterpH.integral_conj_mul_eq_inner, ← InterpH.integral_conj_mul_eq_inner]
    simp_rw [mul_comm (starRingEnd ℂ _)]
    exact key_testFn hg hγ (hφ n)
  simp_rw [heq] at lim1
  have hlim := tendsto_nhds_unique lim1 lim2
  rw [inner_self_eq_norm_sq_to_K, Lp.norm_toLp] at hlim
  rw [InterpH.integral_conj_mul_eq_inner hgL hfL, ← hlim]
  push_cast
  rfl

/-- (E3) `‖g‖²_{H^k} ≤ 3^k ‖g‖_{L²} ‖g‖_{H^{2k}}` for `g ∈ H^{2k}`. -/
theorem interp {k : ℕ} {g : ℂ → ℂ} (hg : MemH (2 * k) g) :
    normH k g ^ 2 ≤ 3 ^ k * l2 g * normH (2 * k) g := by
  have hgL : MemLp g 2 volume := (memH_iff.1 hg).1
  have hterm : ∀ γ ∈ multiIdx k, l2 (weakPartial γ g) ^ 2 ≤ l2 g * normH (2 * k) g := by
    intro γ hγ
    obtain ⟨-, hγ2⟩ := mem_multiIdx_double hγ
    have hfL := (hg.memLp_weakPartial hγ2).1
    have e := l2_weakPartial_sq_eq hg hγ
    have hn : l2 (weakPartial γ g) ^ 2 = ‖((l2 (weakPartial γ g) ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    rw [hn, e, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc _ ≤ l2 g * l2 (weakPartial (2 * γ.1, 2 * γ.2) g) :=
          InterpH.norm_integral_conj_mul_le hgL hfL
      _ ≤ l2 g * normH (2 * k) g :=
          mul_le_mul_of_nonneg_left (hg.l2_weakPartial_le hγ2) (l2_nonneg _)
  rw [normH_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  calc ∑ γ ∈ multiIdx k, l2 (weakPartial γ g) ^ 2
      ≤ ∑ γ ∈ multiIdx k, l2 g * normH (2 * k) g := Finset.sum_le_sum hterm
    _ = ((multiIdx k).card : ℝ) * (l2 g * normH (2 * k) g) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 ^ k * (l2 g * normH (2 * k) g) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast InterpH.card_multiIdx_le k)
          (mul_nonneg (l2_nonneg _) (normH_nonneg _ _))
    _ = 3 ^ k * l2 g * normH (2 * k) g := by ring

end NonUniqueEuler.Sob
