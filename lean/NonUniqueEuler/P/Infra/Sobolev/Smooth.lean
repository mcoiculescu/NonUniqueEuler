import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import NonUniqueEuler.Defs.Infra.Sobolev
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Proof: classical functions in `H^k` (library I-HK)

Proof of `I/Infra/Sobolev/Smooth.lean` (same declarations, same statements).

* `partialD_eq_iteratedFDeriv` follows from the general identity
  `iterDirDeriv_eq_iteratedFDeriv`: for `f` of class `C^n` at `x` and a list `vs` of `n`
  directions, `∂_{v₁} ⋯ ∂_{vₙ} f (x) = D^n f(x) (v₁, …, vₙ)`. Induction on `vs`: near `x` the
  inner derivative is `y ↦ D^{n-1} f(y)(v₂, …, vₙ)` (induction hypothesis at the points where
  `f` is still `C^{n}`), and `fderiv` commutes with evaluation of a multilinear map at a constant
  vector (`fderiv_continuousMultilinear_apply_const_apply`), then `iteratedFDeriv_succ_apply_left`.
* the norm bounds use `ContinuousMultilinearMap.le_opNorm` and `‖1‖ = ‖I‖ = 1`;
* the `H^k` statements use the black boxes `hasWeakDerivOn_of_contDiffOn` and
  `weakDerivOn_ae_eq` of `I/Infra/Sobolev/WeakDeriv.lean`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace NonUniqueEuler.Sob

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The iterated directional derivative of a `C^n` function along `n` directions is the
`n`-th Fréchet derivative applied to them. -/
theorem iterDirDeriv_eq_iteratedFDeriv (vs : List E) :
    ∀ {n : ℕ} (hn : vs.length = n) {f : E → ℂ} {x : E}, ContDiffAt ℝ n f x →
      iterDirDeriv vs f x = iteratedFDeriv ℝ n f x (fun i => vs.get (Fin.cast hn.symm i)) := by
  induction vs with
  | nil =>
    intro n hn f x _
    subst hn
    simp
  | cons v vs ih =>
    intro n hn f x hf
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨vs.length, by simp at hn; omega⟩
    have hm : vs.length = m := by simp at hn; omega
    -- near `x`, the inner derivative is given by the `m`-th Fréchet derivative
    have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ (m + 1 : ℕ) f y :=
      hf.eventually (by exact_mod_cast WithTop.natCast_ne_top (m + 1))
    have heq : iterDirDeriv vs f =ᶠ[𝓝 x]
        fun y => iteratedFDeriv ℝ m f y (fun i => vs.get (Fin.cast hm.symm i)) := by
      filter_upwards [hev] with y hy
      exact ih hm (hy.of_le (by exact_mod_cast Nat.le_succ m))
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ m f) x :=
      hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self m)
    rw [iterDirDeriv_cons, dirDeriv, heq.fderiv_eq,
      fderiv_continuousMultilinear_apply_const_apply hdiff, iteratedFDeriv_succ_apply_left]
    rfl

end Generic

/-- Every direction of `pdList γ` is `1` or `I`, hence of norm `1`. -/
private theorem norm_mem_pdList {γ : ℕ × ℕ} {v : ℂ} (hv : v ∈ pdList γ) : ‖v‖ = 1 := by
  simp only [pdList, List.mem_append, List.mem_replicate] at hv
  rcases hv with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

/-- The classical `∂^γ f(x)` is the iterated Fréchet derivative applied to the directions of
`pdList γ`. -/
theorem partialD_eq_iteratedFDeriv {γ : ℕ × ℕ} {f : ℂ → ℂ} {x : ℂ}
    (hf : ContDiffAt ℝ (γ.1 + γ.2) f x) :
    partialD γ f x = iteratedFDeriv ℝ (γ.1 + γ.2) f x
      (fun i => (pdList γ).get (Fin.cast (pdList_length γ).symm i)) := by
  exact iterDirDeriv_eq_iteratedFDeriv (pdList γ) (pdList_length γ) (by exact_mod_cast hf)

theorem norm_partialD_le_norm_iteratedFDeriv {γ : ℕ × ℕ} {f : ℂ → ℂ} {x : ℂ}
    (hf : ContDiffAt ℝ (γ.1 + γ.2) f x) :
    ‖partialD γ f x‖ ≤ ‖iteratedFDeriv ℝ (γ.1 + γ.2) f x‖ := by
  rw [partialD_eq_iteratedFDeriv hf]
  refine ((iteratedFDeriv ℝ (γ.1 + γ.2) f x).le_opNorm _).trans (le_of_eq ?_)
  have h1 : ∏ i : Fin (γ.1 + γ.2),
      ‖(pdList γ).get (Fin.cast (pdList_length γ).symm i)‖ = 1 :=
    Finset.prod_eq_one fun i _ => norm_mem_pdList (List.get_mem _ _)
  rw [h1, mul_one]

/-- The manuscript's `|∂^γ h(x)| ≤ ‖h‖_{C^k(U)}` for `x ∈ U` and `|γ| ≤ k`. -/
theorem norm_partialD_le_normCk {k : ℕ} {U : Set ℂ} {h : ℂ → ℂ} (hh : MemCk k U h)
    {γ : ℕ × ℕ} (hγ : γ.1 + γ.2 ≤ k) {x : ℂ} (hx : x ∈ U) :
    ‖partialD γ h x‖ ≤ normCk k U h := by
  obtain ⟨V, hVo, hUV, hcd⟩ := hh.near
  have hat : ContDiffAt ℝ k h x := hcd.contDiffAt (hVo.mem_nhds (hUV hx))
  have hat' : ContDiffAt ℝ (γ.1 + γ.2 : ℕ) h x := hat.of_le (by exact_mod_cast hγ)
  exact (norm_partialD_le_norm_iteratedFDeriv (by exact_mod_cast hat')).trans
    (norm_iteratedFDeriv_le_normCk hh hγ hx)

/-- An `L²(V)` function on an open set is locally integrable on it. -/
private theorem locallyIntegrableOn_of_memLp_restrict {V : Set ℂ} {g : ℂ → ℂ}
    (hg : MemLp g 2 (volume.restrict V)) : LocallyIntegrableOn g V :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hg.locallyIntegrable (by norm_num))

/-- A function that is `C^k` on an open set `V`, with classical derivatives of order `≤ k` in
`L²(V)`, lies in `H^k(V)`; its weak derivatives are the classical ones a.e. on `V`. -/
theorem memHOn_of_contDiffOn {k : ℕ} {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ k f V)
    (hL2 : ∀ γ ∈ multiIdx k, MemLp (partialD γ f) 2 (volume.restrict V)) :
    MemHOn k V f ∧ ∀ γ ∈ multiIdx k, ∀ᵐ x, x ∈ V → weakPartialOn V γ f x = partialD γ f x := by
  have hweak : ∀ γ ∈ multiIdx k, HasWeakDerivOn V (pdList γ) f (partialD γ f) := fun γ hγ =>
    hasWeakDerivOn_of_contDiffOn hV (by simpa using mem_multiIdx.1 hγ) hf
  refine ⟨⟨?_, fun γ hγ => ⟨partialD γ f, hL2 γ hγ, hweak γ hγ⟩⟩, fun γ hγ => ?_⟩
  · simpa [partialD, pdList] using hL2 (0, 0) (zero_mem_multiIdx k)
  · exact weakDerivOn_ae_eq hV (locallyIntegrableOn_of_memLp_restrict (hL2 γ hγ)) (hweak γ hγ)

/-- The `H^k(V)` norm of such a function, computed with classical derivatives. -/
theorem normHOn_eq_of_contDiffOn {k : ℕ} {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ k f V)
    (hL2 : ∀ γ ∈ multiIdx k, MemLp (partialD γ f) 2 (volume.restrict V)) :
    normHOn k V f = Real.sqrt (∑ γ ∈ multiIdx k, l2On V (partialD γ f) ^ 2) := by
  have hae := (memHOn_of_contDiffOn hV hf hL2).2
  unfold normHOn
  congr 1
  refine Finset.sum_congr rfl fun γ hγ => ?_
  have h1 : weakPartialOn V γ f =ᵐ[volume.restrict V] partialD γ f :=
    (ae_restrict_iff' hV.measurableSet).2 (hae γ hγ)
  simp only [l2On, eLpNorm_congr_ae h1]

/-- Smooth compactly supported functions lie in every `H^k`; their weak derivatives are the
classical ones (a.e.) and the norm is computed classically. -/
theorem memH_of_contDiff_hasCompactSupport {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (k : ℕ) :
    MemH k f ∧ (∀ γ ∈ multiIdx k, weakPartial γ f =ᵐ[volume] partialD γ f) ∧
      normH k f = Real.sqrt (∑ γ ∈ multiIdx k, l2 (partialD γ f) ^ 2) := by
  have htest : IsTestFn univ f := ⟨hf, hc, subset_univ _⟩
  have hfk : ContDiffOn ℝ k f univ :=
    (hf.of_le (by exact_mod_cast le_top)).contDiffOn
  have hL2 : ∀ γ ∈ multiIdx k, MemLp (partialD γ f) 2 (volume.restrict univ) := fun γ _ =>
    (htest.partialD γ).memLp 2 _
  obtain ⟨hmem, hae⟩ := memHOn_of_contDiffOn isOpen_univ hfk hL2
  refine ⟨hmem, fun γ hγ => ?_, ?_⟩
  · filter_upwards [hae γ hγ] with x hx using hx (mem_univ x)
  · rw [normH, normHOn_eq_of_contDiffOn isOpen_univ hfk hL2]
    simp only [l2On_univ]

/-- The same for test functions `IsTestFn univ φ`. -/
theorem IsTestFn.memH {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) (k : ℕ) : MemH k φ :=
  (memH_of_contDiff_hasCompactSupport hφ.smooth hφ.compact k).1

end NonUniqueEuler.Sob
