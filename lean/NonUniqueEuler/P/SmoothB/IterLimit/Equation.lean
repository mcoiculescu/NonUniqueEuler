import NonUniqueEuler.Defs.SmoothB.Iteration
import NonUniqueEuler.I.SmoothB.Iterates
import NonUniqueEuler.I.SmoothB.IterLimit.IterEquation
import NonUniqueEuler.I.Sec2.BSSmooth
import NonUniqueEuler.H.SmoothB.IterLimit.Equation.Good
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Proof: `prop:iter-limit`, step 4 — the differentiated transport equation of the limit

Proof of `I/SmoothB/IterLimit/Equation.lean` (`B_global_smooth.tex:432-448`).

**Argument.** Fix `γ`, `t`, `x`, put `T = |t| + 1` and `S = [-T, T] × {x}` (compact).
1. The families `ω^{[n+1]} → ω` and `v^{[n]} → v` are "good" on `S` (`H/.../Equation/Good.lean`):
   `C^∞` iterates (`iterates_smooth_support`, `iterates_velocity`), `C^∞` limit slices (`hsm`;
   `BS.contDiff_velocity_of_smooth`, the support of `ω(s)` being compact by `hsupp`), and uniform
   convergence on `S` of all `x`-derivatives (`hconv`, `hvel`; a list of directions in `{1, i}` is
   a permutation of some `pdList β`, and derivatives of smooth functions commute).
2. `↑(Dw(y) u(y)) = ∂₁w(y) Re u(y) + ∂₂w(y) Im u(y)`, so the transport terms
   `v^{[n]} · ∇ω^{[n+1]}` and `v · ∇ω` form a good family (closure of the class under `∂_1`,
   `∂_2`, real-linear maps, products and sums: the Leibniz step of the manuscript). In particular
   `∂_x^γ(v^{[n]} · ∇ω^{[n+1]})(·, x) → ∂_x^γ(v · ∇ω)(·, x)` uniformly on `(-T, T)`.
3. `∂_t ∂_x^γ ω^{[n+1]} = -∂_x^γ(v^{[n]} · ∇ω^{[n+1]})` (`iter_hasDerivAt_spaceD`) and
   `∂_x^γ ω^{[n+1]}(s, x) → ∂_x^γ ω(s, x)` (`hconv`), so the theorem on uniform limits of
   derivatives (`hasDerivAt_of_tendstoUniformlyOn`) gives the claim.

**Deviation.** The manuscript passes to the limit in the integrated equation and then applies the
fundamental theorem of calculus; here the theorem on uniform limits of derivatives is applied
directly (same content: it is proved by the mean value inequality). The Leibniz formula is not
written out: the class of families with uniformly convergent derivatives is shown to be closed under
products by induction on the number of derivatives.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace NonUniqueEuler.Smooth

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

namespace IterLimitEqAux

open Sob

theorem Good.of_eq {S : Set (ℝ × ℂ)} {F F' : ℕ → ℝ → ℂ → ℂ} {G G' : ℝ → ℂ → ℂ}
    (h : Good S F G) (hF : ∀ n s, F n s = F' n s) (hG : ∀ s, G s = G' s) : Good S F' G' := by
  have e1 : F = F' := funext fun n => funext (hF n)
  have e2 : G = G' := funext hG
  subst e1 e2
  exact h

/-- A family is good as soon as the classical derivatives `∂_x^β` converge for every `β`. -/
theorem good_of_spaceD {S : Set (ℝ × ℂ)} {F : ℕ → ℝ → ℂ → ℂ} {G : ℝ → ℂ → ℂ}
    (hF : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (F n)))
    (hG : ∀ s, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G s))
    (hc : ∀ β : ℕ × ℕ, TendstoUniformlyOn (fun n (p : ℝ × ℂ) => spaceD β (F n) p.1 p.2)
      (fun p => spaceD β G p.1 p.2) atTop S) :
    Good S F G where
  smoothF := hF
  smoothG := hG
  conv ws hws := by
    obtain ⟨β, hβ, -⟩ := exists_perm_pdList hws
    have e1 : (fun n (p : ℝ × ℂ) => iterDirDeriv ws (F n p.1) p.2) =
        fun n p => spaceD β (F n) p.1 p.2 := by
      funext n p
      rw [iterDirDeriv_perm hβ (contDiff_slice (hF n) p.1)]
      rfl
    have e2 : (fun p : ℝ × ℂ => iterDirDeriv ws (G p.1) p.2) =
        fun p => spaceD β G p.1 p.2 := by
      funext p
      rw [iterDirDeriv_perm hβ (hG p.1)]
      rfl
    rw [e1, e2]
    exact hc β

end IterLimitEqAux

open IterLimitEqAux in
/-- `prop:iter-limit`, step 4 (`B_global_smooth.tex:432-448`): the limit satisfies
`∂_t ∂_x^γ ω = -∂_x^γ(v · ∇ω)` on `ℝ × ℝ²` for every multi-index `γ`. -/
theorem limit_hasDerivAt_spaceD (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0)
    {ω : ℝ → ℂ → ℝ} (hsm : ∀ t, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω t))
    (hsupp : ∀ (t : ℝ) (x : ℂ), suppRadius ω₀ R₀ t < ‖x‖ → ω t x = 0)
    (hconv : ∀ T : ℝ, 0 < T → ∀ γ : ℕ × ℕ,
      TendstoUniformlyOn (fun (j : ℕ) (p : ℝ × ℂ) => spaceD γ (ofRealST (iter ω₀ j)) p.1 p.2)
        (fun p : ℝ × ℂ => spaceD γ (ofRealST ω) p.1 p.2) atTop (Icc (-T) T ×ˢ univ))
    (hvel : ∀ T : ℝ, 0 < T → ∀ γ : ℕ × ℕ,
      TendstoUniformlyOn (fun (j : ℕ) (p : ℝ × ℂ) => spaceD γ (iterVel ω₀ j) p.1 p.2)
        (fun p : ℝ × ℂ => spaceD γ (velocityField ω) p.1 p.2) atTop (Icc (-T) T ×ˢ univ))
    (γ : ℕ × ℕ) (t : ℝ) (x : ℂ) :
    HasDerivAt (fun s => spaceD γ (ofRealST ω) s x)
      (-(spaceD γ (fun s y => ((fderiv ℝ (ω s) y (velocityField ω s y) : ℝ) : ℂ)) t x)) t := by
  set T : ℝ := |t| + 1 with hTdef
  have hT : 0 < T := by positivity
  set S : Set (ℝ × ℂ) := Icc (-T) T ×ˢ {x} with hSdef
  have hSc : IsCompact S := isCompact_Icc.prod isCompact_singleton
  have hSsub : S ⊆ Icc (-T) T ×ˢ univ := prod_mono subset_rfl (subset_univ _)
  -- the smooth slices of the limit, with compact support
  have hcs : ∀ s, HasCompactSupport (ω s) := fun s =>
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (suppRadius ω₀ R₀ s))
      (fun y hy => hsupp s y (by simpa [Metric.mem_closedBall, dist_zero_right] using hy))
  have hsmI : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (iter ω₀ (n + 1))) :=
    fun n => (iterates_smooth_support h hne (n + 1)).1
  -- step 1: the base families
  have gi : Good S (fun n => ofRealST (iter ω₀ (n + 1))) (ofRealST ω) :=
    good_of_spaceD (fun n => Complex.ofRealCLM.contDiff.comp (hsmI n))
      (fun s => Complex.ofRealCLM.contDiff.comp (hsm s))
      (fun β => tendstoUniformlyOn_succ ((hconv T hT β).mono hSsub))
  have gv : Good S (iterVel ω₀) (velocityField ω) :=
    good_of_spaceD (fun n => (iterates_velocity h hne n).1)
      (fun s => (BS.contDiff_velocity_of_smooth (hsm s) (hcs s)).1)
      (fun β => (hvel T hT β).mono hSsub)
  -- step 2: the transport terms
  have gt := ((gi.dirDeriv (Or.inl rfl)).mul (gv.clm reL) hSc).add
    ((gi.dirDeriv (Or.inr rfl)).mul (gv.clm imL) hSc)
  have gt' : Good S
      (fun n s y => ((fderiv ℝ (iter ω₀ (n + 1) s) y (iterVel ω₀ n s y) : ℝ) : ℂ))
      (fun s y => ((fderiv ℝ (ω s) y (velocityField ω s y) : ℝ) : ℂ)) :=
    gt.of_eq
      (fun n s => (ofReal_fderiv_apply_eq
        ((contDiff_slice (hsmI n) s).differentiable (by simp)) (iterVel ω₀ n s)).symm)
      (fun s => (ofReal_fderiv_apply_eq ((hsm s).differentiable (by simp))
        (velocityField ω s)).symm)
  have hU := (tendstoUniformlyOn_slice (gt'.conv (Sob.pdList γ) (fun v hv => mem_pdList hv))).neg
  -- step 3: uniform limits of derivatives
  have hx : t ∈ Ioo (-T) T := by
    constructor
    · linarith [neg_abs_le t]
    · linarith [le_abs_self t]
  refine hasDerivAt_of_tendstoUniformlyOn (f := fun n s => spaceD γ (ofRealST (iter ω₀ (n + 1))) s x)
    (f' := fun n s => -(spaceD γ
      (fun s y => ((fderiv ℝ (iter ω₀ (n + 1) s) y (iterVel ω₀ n s y) : ℝ) : ℂ)) s x))
    (g' := fun s => -(spaceD γ (fun s y => ((fderiv ℝ (ω s) y (velocityField ω s y) : ℝ) : ℂ))
      s x))
    isOpen_Ioo hU ?_ ?_ hx
  · exact Eventually.of_forall fun n s _ => iter_hasDerivAt_spaceD h hne n γ s x
  · intro s hs
    have hmem : (s, x) ∈ Icc (-T) T ×ˢ (univ : Set ℂ) :=
      ⟨Ioo_subset_Icc_self hs, mem_univ _⟩
    exact ((hconv T hT γ).tendsto_at hmem).comp (tendsto_add_atTop_nat 1)

end NonUniqueEuler.Smooth
