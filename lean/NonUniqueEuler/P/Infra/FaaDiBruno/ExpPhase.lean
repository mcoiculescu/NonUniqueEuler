import NonUniqueEuler.Defs.Infra.SobolevOneD
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import NonUniqueEuler.I.Infra.SobolevOneD.Multiplier
import NonUniqueEuler.H.Infra.FaaDiBruno.ExpPhase.Dilation

/-!
# Proof: derivatives of `e^{iφ} g` (library I-FAA)

Proof of `NonUniqueEuler/I/Infra/FaaDiBruno/ExpPhase.lean` (`lem:semigroup-construct`(1),
`04_ring.tex:949-962`).

* Phase bound: Mathlib's Faà di Bruno bound `norm_iteratedFDerivWithin_comp_le` with outer
  function `s ↦ e^{is}` (all derivatives of norm `1`) and `D = max 1 M`.
* Pointwise Leibniz bound: `norm_iteratedFDerivWithin_mul_le` and the phase bound.
* Weighted bound (restructured, see below): rescale `x = s r` with `s = (1+ℓ²)^{1/2}`. For
  `f̃ = f(s⁻¹ ·)` one has `s² ‖f‖²_{k,ℓ;[α,β]} = s^{2k} ‖f̃‖²_{k,0;[sα,sβ]}`
  (`secNormSq_rescale`), and the rescaled phase `φ̃ = φ(s⁻¹ ·)` satisfies
  `|φ̃^{(i)}| = s^{-i} |φ^{(i)}(s⁻¹ ·)| ≤ A` for `1 ≤ i ≤ k`. Hence
  `|∂^i e^{iφ̃}| ≤ k! (1+A)^k` on `[sα, sβ]` for `i ≤ k`, and the multiplier lemma
  `Sob.secNormSq_mul_le` (`I/Infra/SobolevOneD/Multiplier.lean`) at `ℓ = 0` gives
  `‖e^{iφ̃} g̃‖²_{k,0} ≤ 4^{k+1} (k!)² (1+A)^{2k} ‖g̃‖²_{k,0}`; scaling back gives the claim with
  `C(k) = 4^{k+1} (k!)²`.

Deviation from the manuscript: instead of expanding `∂_r^j(e^{iφ} g)` with complete Bell
polynomials and redistributing the weights `(1+ℓ²)^{k-j} (1+ℓ²)^{i}` by hand, we use the
dilation `r ↦ s r`, which turns the `ℓ`-dependent weights into the unweighted (`ℓ = 0`) norm and
the bound `|φ^{(i)}| ≤ A s` into `|φ̃^{(i)}| ≤ A`. The two arguments are equivalent; the
dilation version reuses the uniform multiplier lemma.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace NonUniqueEuler.FaaDiBruno

namespace ExpPhaseAux

open NonUniqueEuler.Sob

theorem iteratedDeriv_exp_ofReal_mul_I (n : ℕ) :
    iteratedDeriv n (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I)) =
      fun s : ℝ => Complex.I ^ n * Complex.exp ((s : ℂ) * Complex.I) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    have h0 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) (1 * Complex.I) s := by
      simpa using (hasDerivAt_id s).ofReal_comp.mul_const Complex.I
    have h1 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
        (Complex.exp ((s : ℂ) * Complex.I) * (1 * Complex.I)) s := h0.cexp
    rw [(h1.const_mul (Complex.I ^ n)).deriv]
    ring

theorem contDiff_exp_ofReal_mul_I (m : WithTop ℕ∞) :
    ContDiff ℝ m (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I)) :=
  Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)

theorem contDiffOn_exp_mul_I {n : WithTop ℕ∞} {U : Set ℝ} {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ n φ U) :
    ContDiffOn ℝ n (fun s => Complex.exp ((φ s : ℂ) * Complex.I)) U :=
  (contDiff_exp_ofReal_mul_I n).comp_contDiffOn hφ

theorem norm_iteratedDeriv_exp_ofReal_mul_I (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I)) x‖ = 1 := by
  rw [iteratedDeriv_exp_ofReal_mul_I, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
    Complex.norm_exp_ofReal_mul_I]

/-- Derivatives of a dilation at points of `(0, ∞)`, for a function that is only `C^n` on
`(0, ∞)`. -/
theorem iteratedDeriv_comp_mul_of_contDiffOn {n : ℕ} {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ n φ (Ioi 0)) {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (fun y => φ (c * y)) x = c ^ n * iteratedDeriv n φ (c * x) := by
  have hmaps : MapsTo (c * ·) (Ioi (0 : ℝ)) (Ioi 0) := fun y hy => mul_pos hc hy
  have h := iteratedDerivWithin_comp_const_smul (show x ∈ Ioi (0 : ℝ) from hx)
    (uniqueDiffOn_Ioi 0) hφ c hmaps
  rw [iteratedDerivWithin_of_isOpen isOpen_Ioi (show x ∈ Ioi (0 : ℝ) from hx),
    iteratedDerivWithin_of_isOpen isOpen_Ioi (show c * x ∈ Ioi (0 : ℝ) from mul_pos hc hx)] at h
  simpa using h

end ExpPhaseAux

open ExpPhaseAux

/-- Derivatives of the phase factor `e^{iφ}`. -/
theorem norm_iteratedDeriv_exp_mul_I_le {n : ℕ} {U : Set ℝ} (hU : IsOpen U) {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ n φ U) {r : ℝ} (hr : r ∈ U) {M : ℝ}
    (hM : ∀ i, 1 ≤ i → i ≤ n → |iteratedDeriv i φ r| ≤ M) :
    ‖iteratedDeriv n (fun s => Complex.exp ((φ s : ℂ) * Complex.I)) r‖ ≤ (n.factorial : ℝ) * max 1 M ^ n := by
  set E : ℝ → ℂ := fun s => Complex.exp ((s : ℂ) * Complex.I) with hE_def
  have hcomp : (fun s => Complex.exp ((φ s : ℂ) * Complex.I)) = E ∘ φ := rfl
  rw [hcomp, ← iteratedDerivWithin_of_isOpen hU hr,
    ← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  have hC : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i E univ (φ r)‖ ≤ 1 := by
    intro i _
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      norm_iteratedDeriv_exp_ofReal_mul_I]
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i φ U r‖ ≤ max 1 M ^ i := by
    intro i hi1 hin
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, iteratedDerivWithin_of_isOpen hU hr,
      Real.norm_eq_abs]
    exact (hM i hi1 hin).trans
      ((le_max_right 1 M).trans (le_self_pow₀ (le_max_left 1 M) (by omega)))
  have h := norm_iteratedFDerivWithin_comp_le ((contDiff_exp_ofReal_mul_I n).contDiffOn) hφ le_rfl
    uniqueDiffOn_univ hU.uniqueDiffOn (mapsTo_univ _ _) hr hC hD
  rwa [mul_one] at h

/-- Pointwise Leibniz bound for `e^{iφ} g`. -/
theorem norm_iteratedDeriv_exp_mul_I_mul_le {n : ℕ} {U : Set ℝ} (hU : IsOpen U) {φ : ℝ → ℝ}
    {g : ℝ → ℂ} (hφ : ContDiffOn ℝ n φ U) (hg : ContDiffOn ℝ n g U) {r : ℝ} (hr : r ∈ U) {M : ℝ}
    (hM : ∀ i, 1 ≤ i → i ≤ n → |iteratedDeriv i φ r| ≤ M) :
    ‖iteratedDeriv n (fun s => Complex.exp ((φ s : ℂ) * Complex.I) * g s) r‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((i.factorial : ℝ) * max 1 M ^ i) *
        ‖iteratedDeriv (n - i) g r‖ := by
  have hE : ContDiffOn ℝ n (fun s => Complex.exp ((φ s : ℂ) * Complex.I)) U :=
    contDiffOn_exp_mul_I hφ
  rw [← iteratedDerivWithin_of_isOpen hU hr,
    ← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  refine (norm_iteratedFDerivWithin_mul_le hE hg hU.uniqueDiffOn hr le_rfl).trans ?_
  refine Finset.sum_le_sum fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, iteratedDerivWithin_of_isOpen hU hr,
    iteratedDerivWithin_of_isOpen hU hr]
  gcongr
  exact norm_iteratedDeriv_exp_mul_I_le hU (hφ.of_le (by exact_mod_cast hin)) hr
    (fun i' h1 h2 => hM i' h1 (h2.trans hin))

namespace ExpPhaseAux

open NonUniqueEuler.Sob

/-- The rescaling identity `s² ‖F‖²_{k,ℓ;[α,β]} = s^{2k} ‖F(s⁻¹ ·)‖²_{k,0;[sα,sβ]}` for
`s = (1+ℓ²)^{1/2}`. -/
theorem secNormSq_rescale {k : ℕ} (ℓ : ℤ) {α β : ℝ} (hα : 0 < α) {F : ℝ → ℂ}
    (hF : MemH1On k (Ioi 0) F) :
    Real.sqrt (1 + (ℓ : ℝ) ^ 2) ^ 2 * secNormSq k ℓ (Icc α β) F =
      Real.sqrt (1 + (ℓ : ℝ) ^ 2) ^ (2 * k) *
        secNormSq k 0 (Icc (Real.sqrt (1 + (ℓ : ℝ) ^ 2) * α) (Real.sqrt (1 + (ℓ : ℝ) ^ 2) * β))
          (fun x => F ((Real.sqrt (1 + (ℓ : ℝ) ^ 2))⁻¹ * x)) := by
  set s := Real.sqrt (1 + (ℓ : ℝ) ^ 2) with hs_def
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by nlinarith [sq_nonneg (ℓ : ℝ)])
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs1
  have hsq : s ^ 2 = 1 + (ℓ : ℝ) ^ 2 := Real.sq_sqrt (by positivity)
  rw [secNormSq_comp_mul (inv_pos.2 hs0) hF 0 (mul_pos hs0 hα)]
  simp only [inv_mul_cancel_left₀ hs0.ne']
  unfold secNormSq
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  simp only [secWeight, Nat.add_sub_cancel_left, Int.cast_zero]
  rw [← hsq]
  have hs0' : s ≠ 0 := hs0.ne'
  simp only [inv_pow, inv_inv]
  field_simp
  ring

end ExpPhaseAux

/-- The weighted bound of `lem:semigroup-construct`(1): multiplication by `e^{iφ}` with
`|φ^{(i)}| ≤ A (1+ℓ²)^{1/2}` on `I` is bounded on `‖·‖_{k,ℓ;I}` by `C(k) (1+A)^{2k}`, for
profiles on `(0, ∞)` supported in `I = [α, β] ⊂ (0, ∞)`. -/
theorem exists_secNormSq_exp_mul_I_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℤ) (A : ℝ) (α β : ℝ) (φ : ℝ → ℝ) (g : ℝ → ℂ), 0 < α → 0 ≤ A →
      ContDiffOn ℝ k φ (Ioi 0) →
      (∀ i, 1 ≤ i → i ≤ k → ∀ r ∈ Icc α β,
        |iteratedDeriv i φ r| ≤ A * Real.sqrt (1 + (ℓ : ℝ) ^ 2)) →
      Sob.MemH1On k (Ioi 0) g → (∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc α β → g r = 0) →
      Sob.MemH1On k (Ioi 0) (fun r => Complex.exp ((φ r : ℂ) * Complex.I) * g r) ∧
        Sob.secNormSq k ℓ (Icc α β) (fun r => Complex.exp ((φ r : ℂ) * Complex.I) * g r) ≤
          C * (1 + A) ^ (2 * k) * Sob.secNormSq k ℓ (Icc α β) g := by
  refine ⟨4 ^ (k + 1) * (k.factorial : ℝ) ^ 2, by positivity, ?_⟩
  intro ℓ A α β φ g hα hA hφ hbd hg hgI
  set s := Real.sqrt (1 + (ℓ : ℝ) ^ 2) with hs_def
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by nlinarith [sq_nonneg (ℓ : ℝ)])
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs1
  have hc : 0 < s⁻¹ := inv_pos.2 hs0
  set φt : ℝ → ℝ := fun x => φ (s⁻¹ * x) with hφt_def
  set gt : ℝ → ℂ := fun x => g (s⁻¹ * x) with hgt_def
  set et : ℝ → ℂ := fun x => Complex.exp ((φt x : ℂ) * Complex.I) with het_def
  have hφt : ContDiffOn ℝ k φt (Ioi 0) :=
    hφ.comp (contDiff_const.mul contDiff_id).contDiffOn fun x hx => mul_pos hc hx
  have hmemI : ∀ x ∈ Icc (s * α) (s * β), s⁻¹ * x ∈ Icc α β := by
    intro x hx
    exact ⟨(le_inv_mul_iff₀ hs0).2 hx.1, (inv_mul_le_iff₀ hs0).2 hx.2⟩
  have hpos : ∀ x ∈ Icc (s * α) (s * β), 0 < x := fun x hx =>
    lt_of_lt_of_le (mul_pos hs0 hα) hx.1
  -- the rescaled phase has derivatives bounded by `A`
  have hbdt : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ Icc (s * α) (s * β), |iteratedDeriv i φt x| ≤ A := by
    intro i hi1 hik x hx
    rw [hφt_def, iteratedDeriv_comp_mul_of_contDiffOn (hφ.of_le (by exact_mod_cast hik)) hc
      (hpos x hx), abs_mul, abs_pow, abs_of_pos hc]
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have hm : s⁻¹ ^ m ≤ 1 := pow_le_one₀ (inv_nonneg.2 hs0.le) (inv_le_one_of_one_le₀ hs1)
    calc s⁻¹ ^ (m + 1) * |iteratedDeriv (m + 1) φ (s⁻¹ * x)|
        ≤ s⁻¹ ^ (m + 1) * (A * s) :=
          mul_le_mul_of_nonneg_left (hbd (m + 1) hi1 hik _ (hmemI x hx)) (by positivity)
      _ = A * s⁻¹ ^ m := by
          rw [pow_succ]
          field_simp
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hm hA
      _ = A := mul_one A
  -- hence the rescaled phase factor has derivatives bounded by `k! (1+A)^k`
  have hM : ∀ i ≤ k, ∀ x ∈ Icc (s * α) (s * β),
      ‖iteratedDeriv i et x‖ ≤ (k.factorial : ℝ) * (1 + A) ^ k := by
    intro i hik x hx
    have h1 := norm_iteratedDeriv_exp_mul_I_le isOpen_Ioi (hφt.of_le (by exact_mod_cast hik))
      (show x ∈ Ioi (0 : ℝ) from hpos x hx) (M := A)
      (fun i' h1 h2 => hbdt i' h1 (h2.trans hik) x hx)
    refine h1.trans ?_
    have hmax : max 1 A ≤ 1 + A := max_le (by linarith) (by linarith)
    have hfac : (i.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hik
    have hpow : max 1 A ^ i ≤ (1 + A) ^ k :=
      (pow_le_pow_left₀ (by positivity) hmax i).trans (pow_le_pow_right₀ (by linarith) hik)
    exact mul_le_mul hfac hpow (by positivity) (by positivity)
  have het : ContDiffOn ℝ k et (Ioi 0) := contDiffOn_exp_mul_I hφt
  have hgt : Sob.MemH1On k (Ioi 0) gt := memH1On_comp_mul hc hg
  have hgtI : ∀ᵐ x ∂(volume.restrict (Ioi 0)), x ∉ Icc (s * α) (s * β) → gt x = 0 := by
    filter_upwards [ae_comp_mul hc hgI] with x hx hxI
    refine hx fun hmem => hxI ⟨?_, ?_⟩
    · exact (le_inv_mul_iff₀ hs0).1 hmem.1
    · exact (inv_mul_le_iff₀ hs0).1 hmem.2
  obtain ⟨hmem, hbound⟩ := Sob.secNormSq_mul_le (mul_pos hs0 hα) het hM hgt hgtI 0
  -- back to the original variable
  have hback : (fun r => Complex.exp ((φ r : ℂ) * Complex.I) * g r) =
      fun r => (fun x => et x * gt x) (s * r) := by
    funext r
    simp only [het_def, hφt_def, hgt_def, inv_mul_cancel_left₀ hs0.ne']
  have hmem' : Sob.MemH1On k (Ioi 0) (fun r => Complex.exp ((φ r : ℂ) * Complex.I) * g r) := by
    rw [hback]
    exact memH1On_comp_mul hs0 hmem
  refine ⟨hmem', ?_⟩
  have h1 : s ^ 2 * Sob.secNormSq k ℓ (Icc α β)
      (fun r => Complex.exp ((φ r : ℂ) * Complex.I) * g r) =
      s ^ (2 * k) * Sob.secNormSq k 0 (Icc (s * α) (s * β)) (fun x => et x * gt x) :=
    secNormSq_rescale ℓ hα hmem'
  have h2 : s ^ 2 * Sob.secNormSq k ℓ (Icc α β) g =
      s ^ (2 * k) * Sob.secNormSq k 0 (Icc (s * α) (s * β)) gt :=
    secNormSq_rescale ℓ hα hg
  have hs2 : 0 < s ^ 2 := by positivity
  have e1 : Sob.secNormSq k ℓ (Icc α β) (fun r => Complex.exp ((φ r : ℂ) * Complex.I) * g r) =
      (s ^ 2)⁻¹ * (s ^ (2 * k) * Sob.secNormSq k 0 (Icc (s * α) (s * β))
        (fun x => et x * gt x)) := by
    rw [← h1, ← mul_assoc, inv_mul_cancel₀ hs2.ne', one_mul]
  have e2 : Sob.secNormSq k ℓ (Icc α β) g =
      (s ^ 2)⁻¹ * (s ^ (2 * k) * Sob.secNormSq k 0 (Icc (s * α) (s * β)) gt) := by
    rw [← h2, ← mul_assoc, inv_mul_cancel₀ hs2.ne', one_mul]
  rw [e1, e2]
  calc (s ^ 2)⁻¹ * (s ^ (2 * k) * Sob.secNormSq k 0 (Icc (s * α) (s * β))
        (fun x => et x * gt x))
      ≤ (s ^ 2)⁻¹ * (s ^ (2 * k) * (4 ^ (k + 1) * ((k.factorial : ℝ) * (1 + A) ^ k) ^ 2 *
          Sob.secNormSq k 0 (Icc (s * α) (s * β)) gt)) := by
        gcongr
    _ = 4 ^ (k + 1) * (k.factorial : ℝ) ^ 2 * (1 + A) ^ (2 * k) *
          ((s ^ 2)⁻¹ * (s ^ (2 * k) * Sob.secNormSq k 0 (Icc (s * α) (s * β)) gt)) := by
        ring

end NonUniqueEuler.FaaDiBruno
