import NonUniqueEuler.Defs.Infra.SobolevOneD
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import NonUniqueEuler.H.Infra.SobolevOneD.LogVariable.Change
import NonUniqueEuler.H.Infra.SobolevOneD.LogVariable.Iterate
import NonUniqueEuler.H.Infra.SobolevOneD.LogVariable.Seq

/-!
# Proof: the radial variable `r` versus the log variable `x = log r` (library I-SOB1)

Proof of `NonUniqueEuler/I/Infra/SobolevOneD/LogVariable.lean` (used by `lem:elliptic`,
`04_ring.tex:888-897`).

* Weak chain rules (`H/.../Step.lean`, `H/.../Iterate.lean`): test functions transform by
  `φ ↦ 1_{(0,∞)} φ ∘ log` and `ψ ↦ ψ ∘ exp`, integrals by `r = e^x`. Iterating
  `∂_x (e^{px} G(e^x)) = p e^{px} G(e^x) + e^{(p+1)x} G'(e^x)` gives
  `∂_x^j (g ∘ exp) = ∑_{p ≤ j} c_{jp} e^{px} (∂_r^p g)(e^x)`; iterating
  `∂_r (r^{-j} V(log r)) = r^{-j-1} (V' - jV)(log r)` gives
  `∂_r^j (u ∘ log) = r^{-j} ∑_{p ≤ j} d_{jp} (∂_x^p u)(log r)`. The coefficients depend only on
  `j`.
* `L²` bounds (`H/.../Change.lean`): `r dr = e^{2x} dx`, and the weights `e^{px}`, `r^{-j}` are
  bounded on the compact intervals; Cauchy–Schwarz for the finite sums.
* Weights (`H/.../Seq.lean`): `(1+ℓ²)^{k-j} ≤ (1+ℓ²)^{k-p}` for `p ≤ j`, so the constants do
  not depend on `ℓ`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Sob

/-- From the radial variable to the log variable, for compactly supported profiles. -/
theorem exists_logNormSq_comp_exp_le (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm ≤ ρp) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℤ) (g : ℝ → ℂ), MemH1On k (Ioi 0) g →
      (∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → g r = 0) →
      MemH1On k univ (fun x => g (Real.exp x)) ∧
        logNormSq k ℓ (fun x => g (Real.exp x)) ≤ C * secNormSq k ℓ (Icc ρm ρp) g := by
  choose c hc using LogVarH.exists_fwd
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℕ → ℕ → ℝ,
      Cc = fun j p => ((j + 1 : ℕ) : ℝ) * (‖c j p‖ ^ 2 * (ρp ^ (2 * p) / ρm ^ 2)) := ⟨_, rfl⟩
  have hρp : 0 ≤ ρp := hρm.le.trans hρ
  have hCc0 : ∀ j p, 0 ≤ Cc j p := fun j p => by
    rw [hCc]
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (sq_nonneg _) (div_nonneg (pow_nonneg hρp _) (sq_nonneg _)))
  refine ⟨1 + ∑ j ∈ Finset.range (k + 1), ∑ p ∈ Finset.range (j + 1), Cc j p,
    add_pos_of_pos_of_nonneg one_pos
      (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun p _ => hCc0 j p),
    fun ℓ g hg hvan => ?_⟩
  obtain ⟨G, hG0, hGL2, hGw, hGchain, hGeq⟩ := LogVarH.exists_seq isOpen_Ioi hg
  have hsub : Icc ρm ρp ⊆ Ioi (0 : ℝ) := fun r hr => lt_of_lt_of_le hρm hr.1
  -- the weak derivatives vanish outside `[ρ₋, ρ₊]`
  have hW : IsOpen (Ioi (0 : ℝ) ∩ (Icc ρm ρp)ᶜ) := isOpen_Ioi.inter isClosed_Icc.isOpen_compl
  have hvan' : ∀ᵐ r, r ∈ Ioi (0 : ℝ) ∩ (Icc ρm ρp)ᶜ → g r = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioi] at hvan
    filter_upwards [hvan] with r hr hr' using hr hr'.1 hr'.2
  have hvanG : ∀ p ≤ k, ∀ᵐ r, r ∈ Ioi (0 : ℝ) → r ∉ Icc ρm ρp → G p r = 0 := by
    intro p hp
    have h := LogVarH.ae_eq_zero_of_hasWeakDerivOn hW inter_subset_left
      (LogVarH.locallyIntegrableOn_of_memLp isOpen_Ioi (hGL2 p hp)) (hGw p hp) hvan'
    filter_upwards [h] with r hr h1 h2 using hr ⟨h1, h2⟩
  -- the terms `e^{px} G_p(e^x)`
  set A : ℕ → ℝ → ℂ := fun p x => (Real.exp (p * x) : ℂ) * G p (Real.exp x) with hA
  have hAb : ∀ p ≤ k, MemLp (A p) 2 volume ∧
      ∫ x, ‖A p x‖ ^ 2 ≤ ρp ^ (2 * p) / ρm ^ 2 * ∫ r in Icc ρm ρp, ‖G p r‖ ^ 2 * r :=
    fun p hp => LogVarH.memLp_expMul_comp_exp hρm (hGL2 p hp) (hvanG p hp) p
  -- the weak derivatives of `g ∘ exp`
  set uj : ℕ → ℝ → ℂ := fun j x => ∑ p ∈ Finset.range (j + 1), c j p * A p x with huj
  have hujw : ∀ j ≤ k, HasWeakDerivOn univ (derivList j) (fun x => g (Real.exp x)) (uj j) := by
    intro j hj
    have h := hc j G (fun p hp => hGchain p (by omega))
      (fun p hp => LogVarH.locallyIntegrableOn_of_memLp isOpen_Ioi (hGL2 p (by omega)))
    rw [hG0] at h
    exact h
  have hujL2 : ∀ j ≤ k, MemLp (uj j) 2 volume := fun j hj =>
    memLp_finsetSum _ fun p hp =>
      (hAb p (by have := Finset.mem_range.1 hp; omega)).1.const_mul (c j p)
  have hu0 : MemLp (fun x => g (Real.exp x)) 2 volume := by
    have e : (fun x => g (Real.exp x)) = A 0 := by
      ext x; simp [hA, hG0]
    rw [e]
    exact (hAb 0 (Nat.zero_le k)).1
  have hmem : MemH1On k univ (fun x => g (Real.exp x)) := by
    refine ⟨by rw [Measure.restrict_univ]; exact hu0, fun j hj => ⟨uj j, ?_, hujw j hj⟩⟩
    rw [Measure.restrict_univ]
    exact hujL2 j hj
  refine ⟨hmem, ?_⟩
  -- the bound
  set b : ℕ → ℝ := fun p => ∫ r in Icc ρm ρp, ‖weakDeriv1On (Ioi 0) p g r‖ ^ 2 * r with hb
  have hb0 : ∀ p, 0 ≤ b p := fun p =>
    setIntegral_nonneg measurableSet_Icc fun r hr => mul_nonneg (sq_nonneg _) (hsub hr).le
  have hbG : ∀ p ≤ k, ∫ r in Icc ρm ρp, ‖G p r‖ ^ 2 * r = b p := by
    intro p hp
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [hGeq p hp] with r hr hrI
    rw [hr (hsub hrI)]
  have ha : ∀ j ≤ k, ∫ x, ‖weakDeriv1On univ j (fun x => g (Real.exp x)) x‖ ^ 2 ≤
      ∑ p ∈ Finset.range (j + 1), Cc j p * b p := by
    intro j hj
    have hae := weakDerivOn_ae_eq isOpen_univ
      (locallyIntegrableOn_univ.2 ((hujL2 j hj).locallyIntegrable (by norm_num))) (hujw j hj)
    have e : ∫ x, ‖weakDeriv1On univ j (fun x => g (Real.exp x)) x‖ ^ 2 =
        ∫ x, ‖uj j x‖ ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      unfold weakDeriv1On
      rw [hx (mem_univ x)]
    rw [e]
    have hA2 : ∀ p < j + 1, Integrable (fun x => ‖A p x‖ ^ 2) := fun p hp =>
      (hAb p (by omega)).1.norm.integrable_sq
    calc ∫ x, ‖uj j x‖ ^ 2
        ≤ ((j + 1 : ℕ) : ℝ) * ∑ p ∈ Finset.range (j + 1), ‖c j p‖ ^ 2 * ∫ x, ‖A p x‖ ^ 2 :=
          LogVarH.integral_norm_sum_sq_le (j + 1) (c j) A hA2
      _ ≤ ((j + 1 : ℕ) : ℝ) * ∑ p ∈ Finset.range (j + 1),
            ‖c j p‖ ^ 2 * (ρp ^ (2 * p) / ρm ^ 2 * b p) := by
          gcongr with p hp
          have hpk : p ≤ k := by have := Finset.mem_range.1 hp; omega
          rw [← hbG p hpk]
          exact (hAb p hpk).2
      _ = ∑ p ∈ Finset.range (j + 1), Cc j p * b p := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hCc]
          ring
  have key := LogVarH.weighted_sum_le k ℓ
    (fun j => ∫ x, ‖weakDeriv1On univ j (fun x => g (Real.exp x)) x‖ ^ 2) b Cc hCc0 hb0 ha
  unfold logNormSq logNormSqOn secNormSq
  rw [Measure.restrict_univ]
  exact key

/-- From the log variable to the radial variable, on a compact interval `[α, β] ⊂ (0, ∞)`. -/
theorem exists_secNormSq_comp_log_le (k : ℕ) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℤ) (u : ℝ → ℂ), MemH1On k univ u →
      (∀ j ≤ k, ∃ h : ℝ → ℂ, LocallyIntegrableOn h (Ioi 0) ∧
          HasWeakDerivOn (Ioi 0) (derivList j) (fun r => u (Real.log r)) h) ∧
        secNormSq k ℓ (Icc α β) (fun r => u (Real.log r)) ≤
          C * logNormSqOn k ℓ (Icc (Real.log α) (Real.log β)) u := by
  choose d hd using LogVarH.exists_rev
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℕ → ℕ → ℝ,
      Cc = fun j p => ((j + 1 : ℕ) : ℝ) * (‖d j p‖ ^ 2 * (β ^ 2 * α⁻¹ ^ (2 * j))) := ⟨_, rfl⟩
  have hCc0 : ∀ j p, 0 ≤ Cc j p := fun j p => by rw [hCc]; positivity
  refine ⟨1 + ∑ j ∈ Finset.range (k + 1), ∑ p ∈ Finset.range (j + 1), Cc j p,
    add_pos_of_pos_of_nonneg one_pos
      (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun p _ => hCc0 j p),
    fun ℓ u hu => ?_⟩
  obtain ⟨U, hU0, hUL2', hUw, hUchain, hUeq⟩ := LogVarH.exists_seq isOpen_univ hu
  have hUL2 : ∀ p ≤ k, MemLp (U p) 2 volume := fun p hp => by
    have := hUL2' p hp
    rwa [Measure.restrict_univ] at this
  have hUli : ∀ p ≤ k, LocallyIntegrable (U p) := fun p hp =>
    (hUL2 p hp).locallyIntegrable (by norm_num)
  -- the weak derivatives of `u ∘ log`
  set Vj : ℕ → ℝ → ℂ := fun j x => ∑ p ∈ Finset.range (j + 1), d j p * U p x with hVj
  set gj : ℕ → ℝ → ℂ := fun j r => ((r⁻¹ : ℝ) : ℂ) ^ j * Vj j (Real.log r) with hgj
  have hgjw : ∀ j ≤ k, HasWeakDerivOn (Ioi 0) (derivList j) (fun r => u (Real.log r)) (gj j) := by
    intro j hj
    have h := hd j U (fun p hp => hUchain p (by omega)) (fun p hp => hUli p (by omega))
    rw [hU0] at h
    exact h
  have hVjL2 : ∀ j ≤ k, MemLp (Vj j) 2 volume := fun j hj =>
    memLp_finsetSum _ fun p hp =>
      (hUL2 p (by have := Finset.mem_range.1 hp; omega)).const_mul (d j p)
  have hgjli : ∀ j ≤ k, LocallyIntegrableOn (gj j) (Ioi 0) := fun j hj =>
    LogVarH.locallyIntegrableOn_comp_log ((hVjL2 j hj).locallyIntegrable (by norm_num)) j
  refine ⟨fun j hj => ⟨gj j, hgjli j hj, hgjw j hj⟩, ?_⟩
  -- the bound
  have hsub : Icc α β ⊆ Ioi (0 : ℝ) := fun r hr => lt_of_lt_of_le hα hr.1
  set J := Icc (Real.log α) (Real.log β) with hJ
  set b : ℕ → ℝ := fun p => ∫ x in J, ‖weakDeriv1On univ p u x‖ ^ 2 with hb
  have hb0 : ∀ p, 0 ≤ b p := fun p =>
    setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
  have hbU : ∀ p ≤ k, ∫ x in J, ‖U p x‖ ^ 2 = b p := by
    intro p hp
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [hUeq p hp] with x hx _
    rw [hx (mem_univ x)]
  have ha : ∀ j ≤ k,
      ∫ r in Icc α β, ‖weakDeriv1On (Ioi 0) j (fun r => u (Real.log r)) r‖ ^ 2 * r ≤
        ∑ p ∈ Finset.range (j + 1), Cc j p * b p := by
    intro j hj
    have hae := weakDerivOn_ae_eq isOpen_Ioi (hgjli j hj) (hgjw j hj)
    have e : ∫ r in Icc α β, ‖weakDeriv1On (Ioi 0) j (fun r => u (Real.log r)) r‖ ^ 2 * r =
        ∫ r in Icc α β, ‖gj j r‖ ^ 2 * r := by
      refine setIntegral_congr_ae measurableSet_Icc ?_
      filter_upwards [hae] with r hr hrI
      unfold weakDeriv1On
      rw [hr (hsub hrI)]
    rw [e]
    have hU2 : ∀ p < j + 1, Integrable (fun x => ‖U p x‖ ^ 2) (volume.restrict J) :=
      fun p hp => ((hUL2 p (by omega)).restrict J).norm.integrable_sq
    have hV2 : IntegrableOn (fun x => ‖Vj j x‖ ^ 2) J :=
      ((hVjL2 j hj).restrict J).norm.integrable_sq
    calc ∫ r in Icc α β, ‖gj j r‖ ^ 2 * r
        ≤ β ^ 2 * α⁻¹ ^ (2 * j) * ∫ x in J, ‖Vj j x‖ ^ 2 :=
          LogVarH.setIntegral_comp_log_le hα hαβ hV2 j
      _ ≤ β ^ 2 * α⁻¹ ^ (2 * j) * (((j + 1 : ℕ) : ℝ) *
            ∑ p ∈ Finset.range (j + 1), ‖d j p‖ ^ 2 * ∫ x in J, ‖U p x‖ ^ 2) := by
          gcongr
          exact LogVarH.integral_norm_sum_sq_le (j + 1) (d j) U hU2
      _ = ∑ p ∈ Finset.range (j + 1), Cc j p * b p := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [hbU p (by have := Finset.mem_range.1 hp; omega), hCc]
          ring
  exact LogVarH.weighted_sum_le k ℓ
    (fun j => ∫ r in Icc α β, ‖weakDeriv1On (Ioi 0) j (fun r => u (Real.log r)) r‖ ^ 2 * r)
    b Cc hCc0 hb0 ha

/-- The restricted log-variable norm is at most the full one. -/
theorem logNormSqOn_le_logNormSq (k : ℕ) (ℓ : ℤ) (J : Set ℝ) {u : ℝ → ℂ}
    (hu : MemH1On k univ u) : logNormSqOn k ℓ J u ≤ logNormSq k ℓ u := by
  obtain ⟨U, -, hUL2, -, -, hUeq⟩ := LogVarH.exists_seq isOpen_univ hu
  unfold logNormSq logNormSqOn
  refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (secWeight_nonneg k j ℓ)
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hL2 : MemLp (weakDeriv1On univ j u) 2 volume := by
    have h := hUL2 j hjk
    rw [Measure.restrict_univ] at h
    refine h.ae_eq ?_
    filter_upwards [hUeq j hjk] with x hx using (hx (mem_univ x)).symm
  rw [Measure.restrict_univ]
  exact setIntegral_le_integral hL2.norm.integrable_sq
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)

end NonUniqueEuler.Sob
