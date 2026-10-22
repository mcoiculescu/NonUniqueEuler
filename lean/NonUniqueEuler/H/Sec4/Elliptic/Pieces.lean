import NonUniqueEuler.Defs.Infra.SobolevOneD
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Helpers for `P/Sec4/Elliptic`: local pieces of weak derivatives on the half-line

* `weakDerivOn_congr`: the chosen weak derivative depends only on the values on `V`;
* `memLp_of_weakDeriv_piece`: a weak derivative on `V` that agrees on an open `W ⊆ V` with an
  `L²(W)` weak derivative of a function equal to ours on `W` is in `L²(W)` (uniqueness);
* `memLp_two_union`, `memLp_congr_on`: `L²` on unions and under pointwise equality on a set;
* `memLp_Ioo_of_continuous`: continuous functions are in `L²` of a bounded interval;
* the powers `r ↦ B r^m` (`m : ℤ`): smoothness on `(0, ∞)`, their iterated derivatives
  `B (∏_{i<j} (m - i)) r^{m-j}`, and the square integrability on `(c, ∞)` for `m ≤ -1`.

All proofs are complete.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob.EllipticH

/-- The chosen weak derivative on `V` depends only on the values of the function on `V`. -/
theorem weakDerivOn_congr {V : Set ℝ} {vs : List ℝ} {f f' : ℝ → ℂ}
    (h : ∀ x ∈ V, f x = f' x) : weakDerivOn V vs f = weakDerivOn V vs f' := by
  have key : HasWeakDerivOn V vs f = HasWeakDerivOn V vs f' := by
    funext g
    apply propext
    constructor
    · intro hg
      exact hg.congr_ae (ae_of_all _ h) (ae_of_all _ fun _ _ => rfl)
    · intro hg
      exact hg.congr_ae (ae_of_all _ fun x hx => (h x hx).symm) (ae_of_all _ fun _ _ => rfl)
  unfold weakDerivOn
  rw [key]

theorem weakDeriv1On_congr {V : Set ℝ} {j : ℕ} {f f' : ℝ → ℂ}
    (h : ∀ x ∈ V, f x = f' x) : weakDeriv1On V j f = weakDeriv1On V j f' :=
  weakDerivOn_congr h

/-- `secNormSq` on a subset of `(0,∞)` depends only on the values on `(0, ∞)`. -/
theorem secNormSq_congr {k : ℕ} {ℓ : ℤ} {I : Set ℝ} {f f' : ℝ → ℂ}
    (h : ∀ x ∈ Ioi (0 : ℝ), f x = f' x) : secNormSq k ℓ I f = secNormSq k ℓ I f' := by
  unfold secNormSq
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weakDeriv1On_congr h]

/-- Pointwise equality on a measurable set transports `L²`. -/
theorem memLp_congr_on {W : Set ℝ} (hW : MeasurableSet W) {F F' : ℝ → ℂ}
    (h : ∀ x ∈ W, F x = F' x) (hF : MemLp F 2 (volume.restrict W)) :
    MemLp F' 2 (volume.restrict W) :=
  hF.ae_eq ((ae_restrict_iff' hW).2 (ae_of_all _ h))

/-- Uniqueness of weak derivatives on a piece. -/
theorem memLp_of_weakDeriv_piece {V W : Set ℝ} (hW : IsOpen W) (hWV : W ⊆ V) {vs : List ℝ}
    {f F h H : ℝ → ℂ} (hh : HasWeakDerivOn V vs f h) (hhli : LocallyIntegrableOn h V)
    (hfF : ∀ x ∈ W, f x = F x) (hH : HasWeakDerivOn W vs F H) (hHli : LocallyIntegrableOn H W)
    (hHL : MemLp H 2 (volume.restrict W)) : MemLp h 2 (volume.restrict W) := by
  have h1 : HasWeakDerivOn W vs F h :=
    (hh.mono hWV).congr_ae (ae_of_all _ hfF) (ae_of_all _ fun _ _ => rfl)
  have h2 := HasWeakDerivOn.ae_eq hW hHli (hhli.mono_set hWV) hH h1
  exact hHL.ae_eq ((ae_restrict_iff' hW.measurableSet).2 h2)

/-- `L²` on a union. -/
theorem memLp_two_union {f : ℝ → ℂ} {s t : Set ℝ} (hs : MemLp f 2 (volume.restrict s))
    (ht : MemLp f 2 (volume.restrict t)) : MemLp f 2 (volume.restrict (s ∪ t)) := by
  have hm : AEStronglyMeasurable f (volume.restrict (s ∪ t)) :=
    aestronglyMeasurable_union_iff.2 ⟨hs.1, ht.1⟩
  rw [memLp_two_iff_integrable_sq_norm hm]
  exact IntegrableOn.union hs.norm.integrable_sq ht.norm.integrable_sq

/-- An `L²(Ioo a b)` function is locally integrable on `Ioo a b`. -/
theorem locallyIntegrableOn_Ioo_of_memLp {a b : ℝ} {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) : LocallyIntegrableOn f (Ioo a b) :=
  IntegrableOn.locallyIntegrableOn (hf.integrable one_le_two)

/-- Continuous functions on `[a, b]` are in `L²((a, b))`. -/
theorem memLp_Ioo_of_continuousOn {a b : ℝ} {F : ℝ → ℂ} (hF : ContinuousOn F (Icc a b)) :
    MemLp F 2 (volume.restrict (Ioo a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  refine MemLp.of_bound ((hF.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
    C ?_
  exact (ae_restrict_iff' measurableSet_Ioo).2
    (ae_of_all _ fun x hx => hC x (Ioo_subset_Icc_self hx))

/-! ### Powers `r ↦ B r^m` -/

/-- Iterated derivatives of `r ↦ B r^m` away from `0`. -/
theorem iteratedDeriv_const_mul_zpow (B : ℂ) (m : ℤ) (j : ℕ) {r : ℝ} (hr : r ≠ 0) :
    iteratedDeriv j (fun s : ℝ => B * (s : ℂ) ^ m) r =
      B * (∏ i ∈ Finset.range j, ((m : ℂ) - i)) * (r : ℂ) ^ (m - j) := by
  induction j generalizing r with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv j (fun s : ℝ => B * (s : ℂ) ^ m) =ᶠ[𝓝 r]
        fun s : ℝ => B * (∏ i ∈ Finset.range j, ((m : ℂ) - i)) * (s : ℂ) ^ (m - j) := by
      filter_upwards [isOpen_ne.mem_nhds hr] with s hs using ih hs
    rw [heq.deriv_eq]
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    have hd := ((hasDerivAt_zpow (m - j) (r : ℂ) (Or.inl hr')).comp_ofReal).const_mul
      (B * (∏ i ∈ Finset.range j, ((m : ℂ) - i)))
    rw [hd.deriv, Finset.prod_range_succ,
      show m - (j : ℤ) - 1 = m - ((j + 1 : ℕ) : ℤ) by push_cast; ring]
    push_cast
    ring

/-- `r ↦ B r^m` is smooth on `(0, ∞)`. -/
theorem contDiffOn_const_mul_zpow (B : ℂ) (m : ℤ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun s : ℝ => B * (s : ℂ) ^ m) (Ioi 0) := by
  intro s hs
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have hof : ContDiffAt ℝ n (fun s : ℝ => (s : ℂ)) s := Complex.ofRealCLM.contDiff.contDiffAt
  rcases le_or_gt 0 m with hm | hm
  · lift m to ℕ using hm
    have : (fun s : ℝ => B * (s : ℂ) ^ (m : ℤ)) = fun s : ℝ => B * (s : ℂ) ^ m := by
      funext s; simp
    rw [this]
    exact (contDiffAt_const.mul (hof.pow m)).contDiffWithinAt
  · obtain ⟨p, hp⟩ : ∃ p : ℕ, m = -(p : ℤ) := ⟨m.natAbs, by omega⟩
    subst hp
    have : (fun s : ℝ => B * (s : ℂ) ^ (-(p : ℤ))) = fun s : ℝ => B * ((s : ℂ) ^ p)⁻¹ := by
      funext s; simp [zpow_neg]
    rw [this]
    exact (contDiffAt_const.mul ((hof.pow p).inv (pow_ne_zero p hs'))).contDiffWithinAt

/-- `r ↦ c r^e` with `e ≤ -1` is in `L²((c₀, ∞))`, `c₀ > 0`. -/
theorem memLp_const_mul_zpow_Ioi (c : ℂ) {e : ℤ} (he : e ≤ -1) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    MemLp (fun s : ℝ => c * (s : ℂ) ^ e) 2 (volume.restrict (Ioi c₀)) := by
  have hcont : ContinuousOn (fun s : ℝ => c * (s : ℂ) ^ e) (Ioi c₀) := by
    refine continuousOn_const.mul ?_
    refine (Complex.continuous_ofReal.continuousOn).zpow₀ e fun s hs => Or.inl ?_
    exact_mod_cast (ne_of_gt (hc₀.trans hs))
  rw [memLp_two_iff_integrable_sq_norm (hcont.aestronglyMeasurable measurableSet_Ioi)]
  have hlt : ((2 * e : ℤ) : ℝ) < -1 := by
    exact_mod_cast (show (2 * e : ℤ) < -1 by omega)
  have hint : IntegrableOn (fun s : ℝ => ‖c‖ ^ 2 * s ^ ((2 * e : ℤ) : ℝ)) (Ioi c₀) :=
    (integrableOn_Ioi_rpow_of_lt hlt hc₀).const_mul (‖c‖ ^ 2)
  refine hint.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hs0 : 0 < s := hc₀.trans hs
  simp only [norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
    Real.rpow_intCast, mul_pow]
  congr 1
  rw [← zpow_natCast (s ^ e) 2, ← zpow_mul]
  congr 1
  push_cast
  ring

end NonUniqueEuler.Sob.EllipticH
