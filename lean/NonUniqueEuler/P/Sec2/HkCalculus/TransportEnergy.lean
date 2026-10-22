import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import NonUniqueEuler.Defs.Sec2.HkCalculus
import NonUniqueEuler.I.Infra.Sobolev.Density
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.H.Sec2.HkCalculus.TransportEnergy.Bounds
import NonUniqueEuler.H.Sec2.HkCalculus.TransportEnergy.Smooth

/-!
# Proof of `I/Sec2/HkCalculus/TransportEnergy`: the transport term has no real energy

Manuscript: `lem:Hk-calculus`(1), second claim, `02_prelim.tex:735-745`:
`Re ⟨Ũ·∇g, g⟩_{L²} = ½ ∫ Ũ·∇|g|² dx = -½ ∫ (div Ũ)|g|² dx = 0`.

Proof (as in the interface docstring).
1. Smooth case (`H/.../Smooth.lean`): for a test function `φ`,
   `Re ⟨U·∇φ, φ⟩ = -½ ∫ (div U) |φ|²` (weak derivatives of `U` tested against `|φ|²`).
2. Density: take a test function `φ` with `‖g - φ‖_{H^1} < ε` (`MemH.exists_testFn_approx`),
   `e = g - φ`. Then `∂_l g = ∂_l φ + ∂_l e` a.e. and
   `(U·∇g) ḡ = (U·∇φ) φ̄ + (U·∇g) ē + (U·∇e) ḡ - (U·∇e) ē` a.e.; the last three terms are
   `O(ε)` by `L^∞ × L² × L²` bounds (`H/.../Bounds.lean`).
3. `(div U) |φ|² = (div U) |e|²` a.e. (`div U = 0` a.e. on `N`, `g = 0` a.e. outside `N`), so
   `|∫ (div U) |φ|²| ≤ ‖div U‖_∞ ε²`. Hence `|Re ⟨U·∇g, g⟩| ≤ K ε` for every `ε ∈ (0, 1]`.

Deviation from the manuscript: the manuscript integrates by parts directly with `|g|² ∈ W^{1,1}`;
here the integration by parts is done for test functions and passed to the limit, as in the
interface proof sketch. Step 3 uses `div U · g = 0` a.e. directly for the approximants instead of
passing `∫ (div U)|φ_n|²` to the limit.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

namespace NonUniqueEuler.Sob

namespace TransportEnergyAux

/-- A real number bounded by `K ε` for every `ε ∈ (0, 1]` vanishes. -/
theorem eq_zero_of_forall_abs_le {a K : ℝ} (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → |a| ≤ K * ε) :
    a = 0 := by
  have hK : 0 < |K| + 1 := by positivity
  have : |a| ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hδpos : 0 < min 1 (ε / (|K| + 1)) := lt_min one_pos (by positivity)
    have hδ1 : min 1 (ε / (|K| + 1)) ≤ 1 := min_le_left _ _
    have hδ2 : min 1 (ε / (|K| + 1)) ≤ ε / (|K| + 1) := min_le_right _ _
    have h1 := h _ hδpos hδ1
    have h2 : K * min 1 (ε / (|K| + 1)) ≤ |K| * min 1 (ε / (|K| + 1)) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) hδpos.le
    have h4 : (|K| + 1) * min 1 (ε / (|K| + 1)) ≤ ε := by
      rw [le_div_iff₀ hK] at hδ2
      linarith
    nlinarith
  exact abs_nonpos_iff.1 this

/-- `∂^γ f = ∂^γ φ + ∂^γ (f - φ)` a.e. for `f, φ, f - φ ∈ H^k`. -/
theorem weakPartial_ae_eq_add_sub {k : ℕ} {f φ : ℂ → ℂ} (hf : MemH k f) (hφ : MemH k φ)
    (he : MemH k (f - φ)) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    weakPartial γ f =ᵐ[volume] weakPartial γ φ + weakPartial γ (f - φ) := by
  obtain ⟨hφL, hφd⟩ := hφ.memLp_weakPartial hγ
  obtain ⟨heL, hed⟩ := he.memLp_weakPartial hγ
  have li : ∀ {u : ℂ → ℂ}, MemLp u 2 volume → LocallyIntegrableOn u univ volume :=
    fun hu => (hu.locallyIntegrable (by norm_num)).locallyIntegrableOn univ
  have hadd := HasWeakDerivOn.add isOpen_univ (li (memH_iff.1 hφ).1) (li (memH_iff.1 he).1)
    (li hφL) (li heL) hφd hed
  have hfe : φ + (f - φ) = f := add_sub_cancel φ f
  rw [hfe] at hadd
  exact hf.weakPartial_ae_eq hγ (hφL.add heL) hadd

end TransportEnergyAux

open TransportEnergyAux in
/-- `Re ⟨U·∇g, g⟩_{L²} = 0` for `g ∈ H^1` vanishing outside a compact `N` and a real vector
field `U ∈ W^{1,∞}(ℝ²)` with `div U = 0` a.e. on `N`. -/
theorem re_innerL2_dotGrad_self_eq_zero {N : Set ℂ} (hN : IsCompact N) {g U : ℂ → ℂ}
    (hg : MemH 1 g) (hgN : ∀ᵐ x, x ∉ N → g x = 0) (hU : MemW1infOn univ U)
    (hdiv : ∀ᵐ x, x ∈ N → weakDivOn univ U x = 0) :
    (Prelim.innerL2 (dotGrad U g) g).re = 0 := by
  -- the weak derivatives of `U`
  obtain ⟨G₁, hG₁, hG₁li, hd₁⟩ := hU.deriv (1, 0) (by simp)
  obtain ⟨G₂, hG₂, hG₂li, hd₂⟩ := hU.deriv (0, 1) (by simp)
  rw [Measure.restrict_univ] at hG₁ hG₂
  have hUL : MemLp U ⊤ volume := by simpa using hU.memLp
  have hdivG : ∀ᵐ x, x ∈ N → (G₁ x).re + (G₂ x).im = 0 := by
    filter_upwards [hdiv, weakDerivOn_ae_eq isOpen_univ hG₁li hd₁,
      weakDerivOn_ae_eq isOpen_univ hG₂li hd₂] with x hx e1 e2 hxN
    have := hx hxN
    simp only [weakDivOn, weakPartialOn] at this
    rw [e1 (mem_univ x), e2 (mem_univ x)] at this
    exact this
  -- the constants
  obtain ⟨M, hM, hUb⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x, ‖U x‖ ≤ M :=
    ⟨_, ENNReal.toReal_nonneg, ae_norm_le_toReal_eLpNorm_top hUL⟩
  obtain ⟨D, hD, hDb⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ᵐ x, |(G₁ x).re + (G₂ x).im| ≤ D := by
    refine ⟨(eLpNorm G₁ ⊤ volume).toReal + (eLpNorm G₂ ⊤ volume).toReal,
      add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg, ?_⟩
    filter_upwards [ae_norm_le_toReal_eLpNorm_top hG₁, ae_norm_le_toReal_eLpNorm_top hG₂]
      with x h1 h2
    calc |(G₁ x).re + (G₂ x).im| ≤ |(G₁ x).re| + |(G₂ x).im| := abs_add_le _ _
      _ ≤ ‖G₁ x‖ + ‖G₂ x‖ := add_le_add (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
      _ ≤ _ := add_le_add h1 h2
  have hm1 : ((1 : ℕ), (0 : ℕ)) ∈ multiIdx 1 := by simp [mem_multiIdx]
  have hm2 : ((0 : ℕ), (1 : ℕ)) ∈ multiIdx 1 := by simp [mem_multiIdx]
  have hgL : MemLp g 2 volume := (memH_iff.1 hg).1
  have hg1L := (hg.memLp_weakPartial hm1).1
  have hg2L := (hg.memLp_weakPartial hm2).1
  have hg1n : l2 (weakPartial (1, 0) g) ≤ normH 1 g := hg.l2_weakPartial_le hm1
  have hg2n : l2 (weakPartial (0, 1) g) ≤ normH 1 g := hg.l2_weakPartial_le hm2
  have hgn : l2 g ≤ normH 1 g := hg.l2_le
  have hGn : 0 ≤ normH 1 g := normH_nonneg 1 g
  show (∫ x, dotGrad U g x * conj (g x)).re = 0
  -- the estimate `|Re ⟨U·∇g, g⟩| ≤ K ε`
  apply eq_zero_of_forall_abs_le (K := D / 2 + 4 * M * normH 1 g + 2 * M)
  intro ε hε hε1
  obtain ⟨φ, hφ, he, hen⟩ := hg.exists_testFn_approx hε
  have hφH : MemH 1 φ := hφ.memH 1
  have hφL : MemLp φ 2 volume := hφ.memLp 2 volume
  have hφ1L := (hφH.memLp_weakPartial hm1).1
  have hφ2L := (hφH.memLp_weakPartial hm2).1
  have heL : MemLp (g - φ) 2 volume := (memH_iff.1 he).1
  have he1L := (he.memLp_weakPartial hm1).1
  have he2L := (he.memLp_weakPartial hm2).1
  have hen0 : l2 (g - φ) ≤ ε := (he.l2_le.trans_lt hen).le
  have he1n : l2 (weakPartial (1, 0) (g - φ)) ≤ ε := ((he.l2_weakPartial_le hm1).trans_lt hen).le
  have he2n : l2 (weakPartial (0, 1) (g - φ)) ≤ ε := ((he.l2_weakPartial_le hm2).trans_lt hen).le
  have hs1 := weakPartial_ae_eq_add_sub hg hφH he hm1
  have hs2 := weakPartial_ae_eq_add_sub hg hφH he hm2
  -- the error terms
  obtain ⟨iA, bA⟩ := dotGrad_mul_conj_bound hM hUL.1 hUb hg1L hg2L heL
  obtain ⟨iB, bB⟩ := dotGrad_mul_conj_bound hM hUL.1 hUb he1L he2L hgL
  obtain ⟨iC, bC⟩ := dotGrad_mul_conj_bound hM hUL.1 hUb he1L he2L heL
  obtain ⟨iY, -⟩ := dotGrad_mul_conj_bound hM hUL.1 hUb hφ1L hφ2L hφL
  set A := ∫ x, dotGrad U g x * conj ((g - φ) x) with hA
  set B := ∫ x, dotGrad U (g - φ) x * conj (g x) with hB
  set C := ∫ x, dotGrad U (g - φ) x * conj ((g - φ) x) with hC
  set Y := ∫ x, dotGrad U φ x * conj (φ x) with hY
  have iAB : Integrable (fun x => dotGrad U g x * conj ((g - φ) x) +
      dotGrad U (g - φ) x * conj (g x)) volume := iA.add iB
  have iZ : Integrable (fun x => dotGrad U g x * conj ((g - φ) x) +
      dotGrad U (g - φ) x * conj (g x) - dotGrad U (g - φ) x * conj ((g - φ) x)) volume :=
    iAB.sub iC
  have hXY : ∫ x, dotGrad U g x * conj (g x) = Y + (A + B - C) := by
    rw [hA, hB, hC, hY, ← integral_add iA iB, ← integral_sub iAB iC, ← integral_add iY iZ]
    refine integral_congr_ae ?_
    filter_upwards [hs1, hs2] with x e1 e2
    simp only [Pi.add_apply] at e1 e2
    simp only [dotGrad, Pi.sub_apply]
    rw [e1, e2, map_sub]
    ring
  -- the smooth case and the divergence term
  have hYre := re_integral_dotGrad_testFn hφ hUL hG₁ hG₂ hd₁ hd₂
  have hdeq : ∫ x, ((G₁ x).re + (G₂ x).im) * ‖φ x‖ ^ 2 =
      ∫ x, ((G₁ x).re + (G₂ x).im) * ‖(g - φ) x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hdivG, hgN] with x h1 h2
    by_cases hxN : x ∈ N
    · rw [h1 hxN]
      simp
    · rw [Pi.sub_apply, h2 hxN, zero_sub, norm_neg]
  have hdiv_bound : |∫ x, ((G₁ x).re + (G₂ x).im) * ‖(g - φ) x‖ ^ 2| ≤
      D * (l2 (g - φ) * l2 (g - φ)) := by
    have hmeas : AEStronglyMeasurable
        (fun x => ((((G₁ x).re + (G₂ x).im) * ‖(g - φ) x‖ ^ 2 : ℝ) : ℂ)) volume :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable
        (((Complex.continuous_re.comp_aestronglyMeasurable hG₁.1).add
          (Complex.continuous_im.comp_aestronglyMeasurable hG₂.1)).mul (heL.1.norm.pow 2))
    obtain ⟨-, hb⟩ := norm_integral_le_of_ae_le hD hmeas heL heL (by
      filter_upwards [hDb] with x hx
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖(g - φ) x‖),
        sq]
      exact mul_le_mul_of_nonneg_right hx (by positivity))
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs] at hb
    exact hb
  -- assembling
  have hYb : |Y.re| ≤ 1 / 2 * (D * (ε * ε)) := by
    rw [hYre, hdeq, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left (hdiv_bound.trans ?_) (by norm_num)
    exact mul_le_mul_of_nonneg_left (mul_le_mul hen0 hen0 (l2_nonneg _) hε.le) hD
  have hAb : ‖A‖ ≤ M * (2 * normH 1 g) * ε :=
    bA.trans (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hM) hen0 (l2_nonneg _)
      (mul_nonneg hM (by linarith)))
  have hBb : ‖B‖ ≤ M * (2 * ε) * normH 1 g :=
    bB.trans (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hM) hgn (l2_nonneg _)
      (mul_nonneg hM (by linarith)))
  have hCb : ‖C‖ ≤ M * (2 * ε) * ε :=
    bC.trans (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hM) hen0 (l2_nonneg _)
      (mul_nonneg hM (by linarith)))
  have hZ : |(A + B - C).re| ≤ ‖A‖ + ‖B‖ + ‖C‖ :=
    (Complex.abs_re_le_norm _).trans ((norm_sub_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl))
  have hεε : ε * ε ≤ ε := by nlinarith
  have hDε : D * (ε * ε) ≤ D * ε := mul_le_mul_of_nonneg_left hεε hD
  have hMε : M * (ε * ε) ≤ M * ε := mul_le_mul_of_nonneg_left hεε hM
  rw [hXY, Complex.add_re]
  calc |Y.re + (A + B - C).re| ≤ |Y.re| + |(A + B - C).re| := abs_add_le _ _
    _ ≤ (D / 2 + 4 * M * normH 1 g + 2 * M) * ε := by nlinarith

end NonUniqueEuler.Sob
