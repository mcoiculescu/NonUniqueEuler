import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecificLimits.Basic
import NonUniqueEuler.Defs.Infra.Sobolev
import NonUniqueEuler.I.Infra.Sobolev.Density
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.H.Infra.Sobolev.EmbedLinf.TestFn

/-!
# Proof: `lem:embed` (E2), `H^2(ℝ²) ⊂ C₀ ∩ L^∞` with constant `1` (library I-HK)

Proof of `I/Infra/Sobolev/EmbedLinf.lean`. Manuscript: `02_prelim.tex:604-606, 624-630`.

For test functions the bound `|g(x)| ≤ ‖g‖_{H²}` is
`EmbedLinfAux.norm_le_normH_two_of_testFn` (`H/Infra/Sobolev/EmbedLinf/TestFn.lean`, by the
fundamental theorem of calculus on lines; no Fourier transform). For `g ∈ H²`, take test
functions `φ_n` with `‖g - φ_n‖_{H²} < 1/(n+1)` (`I/Infra/Sobolev/Density.lean`); they are Cauchy
in the sup norm, so they converge in `C₀(ℂ, ℂ)` (complete) to some `g'`, and `g = g'` a.e.
because a subsequence of `φ_n` converges to `g` a.e. (`L²` convergence).

**Deviation from the manuscript.** The manuscript proves (E2) with the Fourier transform; we
use the elementary argument above. The statement (constant `1`) is the manuscript's.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Sob

namespace EmbedLinfAux

theorem IsTestFn.sub' {φ ψ : ℂ → ℂ} (hφ : IsTestFn univ φ) (hψ : IsTestFn univ ψ) :
    IsTestFn univ (φ - ψ) :=
  ⟨hφ.smooth.sub hψ.smooth, hφ.compact.sub hψ.compact, subset_univ _⟩

/-- A test function as an element of `C₀(ℂ, ℂ)`. -/
def toC0 {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) : ZeroAtInftyContinuousMap ℂ ℂ :=
  ⟨⟨φ, hφ.continuous⟩, hφ.compact.is_zero_at_infty⟩

theorem toC0_apply {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) (x : ℂ) : toC0 hφ x = φ x := rfl

/-- `eLpNorm f 2 = ofReal (l2 f)` for `f ∈ L²`. -/
theorem eLpNorm_two_eq_ofReal_l2 {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    eLpNorm f 2 volume = ENNReal.ofReal (l2 f) := by
  rw [l2, ENNReal.ofReal_toReal hf.eLpNorm_ne_top]

end EmbedLinfAux

open EmbedLinfAux in
/-- (E2) An `H^2` function has a continuous representative, vanishing at infinity, bounded by
`‖g‖_{H^2}`. -/
theorem Linf_le_H2 {g : ℂ → ℂ} (hg : MemH 2 g) :
    ∃ g' : ℂ → ℂ, Continuous g' ∧ g =ᵐ[volume] g' ∧ (∀ x, ‖g' x‖ ≤ normH 2 g) ∧
      Tendsto g' (cocompact ℂ) (𝓝 0) := by
  -- an approximating sequence of test functions
  have hex : ∀ n : ℕ, ∃ φ : ℂ → ℂ, IsTestFn univ φ ∧ MemH 2 (g - φ) ∧
      normH 2 (g - φ) < 1 / ((n : ℝ) + 1) :=
    fun n => hg.exists_testFn_approx (by positivity)
  choose φ hφ hφH hφn using hex
  set ψ : ℕ → ZeroAtInftyContinuousMap ℂ ℂ := fun n => toC0 (hφ n) with hψ_def
  -- sup-norm bound on differences
  have hdist : ∀ n m, dist (ψ n) (ψ m) ≤ 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) := by
    intro n m
    rw [← ZeroAtInftyContinuousMap.dist_toBCF_eq_dist]
    refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun x => ?_
    change dist (φ n x) (φ m x) ≤ _
    rw [dist_eq_norm]
    have h1 := norm_le_normH_two_of_testFn (IsTestFn.sub' (hφ n) (hφ m)) x
    have heq : (g - φ m) - (g - φ n) = φ n - φ m := sub_sub_sub_cancel_left _ _ _
    have h2 := ((hφH m).sub (hφH n)).2
    rw [heq] at h2
    have h3 := hφn n
    have h4 := hφn m
    simp only [Pi.sub_apply] at h1
    linarith
  have hcauchy : CauchySeq ψ := by
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 / ((N : ℝ) + 1)) ?_ ?_
    · intro n m N hn hm
      refine (hdist n m).trans ?_
      have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hn' : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hn
      have hm' : (N : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hm
      have e1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := one_div_le_one_div_of_le hN hn'
      have e2 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := one_div_le_one_div_of_le hN hm'
      calc 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) :=
            add_le_add e1 e2
        _ = 2 / ((N : ℝ) + 1) := by ring
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
      simpa [div_eq_mul_inv] using this
  obtain ⟨Ψ, hΨ⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hunif := ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly.1 hΨ
  have hpt : ∀ x, Tendsto (fun n => φ n x) atTop (𝓝 (Ψ x)) := fun x => hunif.tendsto_at x
  refine ⟨Ψ, map_continuous Ψ, ?_, ?_, Ψ.zero_at_infty'⟩
  · -- a.e. equality, via an a.e. convergent subsequence
    have hgm : MemLp g 2 volume := (memH_iff.1 hg).1
    have hle : ∀ n, eLpNorm (φ n - g) 2 volume ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      intro n
      rw [eLpNorm_sub_comm, eLpNorm_two_eq_ofReal_l2 (memH_iff.1 (hφH n)).1]
      exact ENNReal.ofReal_le_ofReal (((hφH n).l2_le).trans (hφn n).le)
    have hlim : Tendsto (fun n => eLpNorm (φ n - g) 2 volume) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
        (fun _ => bot_le) hle
    have hmeas : TendstoInMeasure volume φ atTop g :=
      tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
        (fun n => (hφ n).continuous.aestronglyMeasurable) hgm.aestronglyMeasurable hlim
    obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
    filter_upwards [hae] with x hx
    exact tendsto_nhds_unique hx ((hpt x).comp hns.tendsto_atTop)
  · -- the pointwise bound
    intro x
    have hb : ∀ n, ‖φ n x‖ ≤ normH 2 g + 1 / ((n : ℝ) + 1) := by
      intro n
      have h1 := norm_le_normH_two_of_testFn (hφ n) x
      have h2 := (hg.sub (hφH n)).2
      rw [sub_sub_cancel] at h2
      linarith [hφn n]
    have hr : Tendsto (fun n : ℕ => normH 2 g + 1 / ((n : ℝ) + 1)) atTop (𝓝 (normH 2 g)) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (normH 2 g)
    exact le_of_tendsto_of_tendsto' (hpt x).norm hr hb

/-- (E2) for continuous functions: the bound holds at every point. -/
theorem norm_le_normH_two_of_continuous {g : ℂ → ℂ} (hg : MemH 2 g) (hc : Continuous g)
    (x : ℂ) : ‖g x‖ ≤ normH 2 g := by
  obtain ⟨g', hc', hae, hb, -⟩ := Linf_le_H2 hg
  have heq : g = g' := (Continuous.ae_eq_iff_eq volume hc hc').1 hae
  rw [congrFun heq x]
  exact hb x

/-- (E2), `L^∞` form: `‖g‖_{L^∞} ≤ ‖g‖_{H^2}`. -/
theorem eLpNorm_top_le_normH_two {g : ℂ → ℂ} (hg : MemH 2 g) :
    eLpNorm g ⊤ volume ≤ ENNReal.ofReal (normH 2 g) := by
  obtain ⟨g', -, hae, hb, -⟩ := Linf_le_H2 hg
  rw [eLpNorm_congr_ae hae, eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound (ae_of_all _ hb)

end NonUniqueEuler.Sob
