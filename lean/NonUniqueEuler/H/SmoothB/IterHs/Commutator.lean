import NonUniqueEuler.H.SmoothB.IterHs.Energy
import NonUniqueEuler.I.SmoothB.CommR2
import NonUniqueEuler.I.Sec2.BSSmooth
import NonUniqueEuler.I.Sec2.BSBasic

/-!
# Helper for `lem:iter-Hs`: the bound on one top-order energy term

Helper of `P/SmoothB/IterHs.lean` (`B_global_smooth.tex:322-343`). Fix `j`, `|t| ≤ T`, put
`g = ω^{[j+1]}(t)`, `v = v^{[j]}(t)`, `Z = ‖g‖_{H^s}` (`s = n + 2`) and `𝓜 ≥ ‖ω^{[j]}(t)‖_{H^{s-1}}`.

* `timeDeriv_iter_succ`: `∂_t ω^{[j+1]} = -v^{[j]}·∇ω^{[j+1]}` (`lem:iterates`(iv)), for the
  complex-valued slices;
* `comm_bound`: `lem:comm-R2` with `|∇v|_max ≤ V(T)`, `‖∇v‖_{H^{s-1}} = ‖ω^{[j]}(t)‖_{H^{s-1}} ≤ 𝓜`
  (`lem:BS-basic`(d)) and `|∇g| ≤ Ψ(T)` (`lem:iter-lip`):
  `‖[∂^α, v·∇]g‖_{L²} ≤ 2^{s+1}[(V(T) + 𝓜)Z + 𝓜Ψ(T)]`;
* `abs_re_energy_term_le`: for `|α| = s`,
  `|Re ∫ ∂^α g ∂^α ∂_t g| = |Re ∫ ∂^α g [∂^α, v·∇]g| ≤ Z · 2^{s+1}[(V(T) + 𝓜)Z + 𝓜Ψ(T)]`,
  since the transport term `Re ∫ ∂^α g v·∇∂^α g` vanishes (`div v = 0`).
-/

noncomputable section

open MeasureTheory Set Metric Filter ComplexConjugate
open scoped ContDiff ENNReal Topology

namespace NonUniqueEuler.Smooth.IterHsH

open Sob

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

theorem gradEntryMax_le {u : ℂ → ℂ} {M : ℝ}
    (h : ∀ x : ℂ, ∀ i l : Fin 2, |Prelim.gradEntry u i l x| ≤ M) : gradEntryMax u ≤ M :=
  ciSup_le fun x => ciSup_le fun i => ciSup_le fun l => h x i l

theorem gradSupC_le {g : ℂ → ℂ} {M : ℝ} (h : ∀ x : ℂ, Prelim.gradAbs g x ≤ M) :
    gradSupC g ≤ M :=
  ciSup_le h

theorem contDiff_iterVel_slice (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (iterVel ω₀ j t) := by
  have h1 : ContDiff ℝ ∞ (fun x : ℂ => Function.uncurry (iterVel ω₀ j) (t, x)) :=
    (iterates_velocity h hne j).1.comp ((contDiff_const (c := t)).prodMk contDiff_id)
  simpa only [Function.uncurry_apply_pair] using h1

theorem iterVel_eq (ω₀ : ℂ → ℝ) (j : ℕ) (t : ℝ) : iterVel ω₀ j t = velocity (iter ω₀ j t) :=
  rfl

/-- `∂_t ω^{[j+1]}(t, x) = -v^{[j]}(t, x)·∇ω^{[j+1]}(t, x)`, for the complex-valued slices. -/
theorem timeDeriv_iter_succ (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) (x : ℂ) :
    deriv (fun s => (iter ω₀ (j + 1) s x : ℂ)) t =
      -(fderiv ℝ (fun y => (iter ω₀ (j + 1) t y : ℂ)) x (iterVel ω₀ j t x)) := by
  have hsm := (iterates_smooth_support h hne (j + 1)).1
  have hdt : DifferentiableAt ℝ (fun s => iter ω₀ (j + 1) s x) t := by
    have h1 : ContDiff ℝ ∞ (fun s : ℝ => Function.uncurry (iter ω₀ (j + 1)) (s, x)) :=
      hsm.comp (contDiff_id.prodMk contDiff_const)
    exact (h1.differentiable (by simp)) t
  have hdx : DifferentiableAt ℝ (iter ω₀ (j + 1) t) x :=
    ((contDiff_iter_slice h hne (j + 1) t).differentiable (by simp)) x
  have htr := (iterates_flow h hne j).2.2.2.2 t x
  rw [hdt.hasDerivAt.ofReal_comp.deriv, fderiv_ofReal_apply hdx]
  have : deriv (fun τ => iter ω₀ (j + 1) τ x) t =
      -(fderiv ℝ (iter ω₀ (j + 1) t) x (iterVel ω₀ j t x)) := by linarith
  rw [this]
  push_cast
  rfl

/-- `lem:comm-R2` for `u = v^{[j]}(t)`, `g = ω^{[j+1]}(t)`, with the bounds of `lem:iter-lip`
and `lem:BS-basic`(d). -/
theorem comm_bound (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (n j : ℕ) {t T M : ℝ}
    (ht : |t| ≤ T) (hM : normH (n + 1) (fun x => (iter ω₀ j t x : ℂ)) ≤ M)
    {α : ℕ × ℕ} (hα : α.1 + α.2 = n + 2) :
    MemLp (fun x => partialD α (fun y => fderiv ℝ (fun z => (iter ω₀ (j + 1) t z : ℂ)) y
        (iterVel ω₀ j t y)) x -
        fderiv ℝ (partialD α (fun z => (iter ω₀ (j + 1) t z : ℂ))) x (iterVel ω₀ j t x))
        2 volume ∧
      l2 (fun x => partialD α (fun y => fderiv ℝ (fun z => (iter ω₀ (j + 1) t z : ℂ)) y
          (iterVel ω₀ j t y)) x -
          fderiv ℝ (partialD α (fun z => (iter ω₀ (j + 1) t z : ℂ))) x (iterVel ω₀ j t x)) ≤
        2 ^ (n + 3) * ((Vbd ω₀ T + M) * normH (n + 2) (fun z => (iter ω₀ (j + 1) t z : ℂ)) +
          M * Psi ω₀ T) := by
  have hgs := contDiff_iter_slice h hne j t
  have hgc := hasCompactSupport_iter_slice h hne j t
  have hWs := contDiff_iter_sliceC h hne (j + 1) t
  have hWc := hasCompactSupport_iter_sliceC h hne (j + 1) t
  have hvs := contDiff_iterVel_slice h hne j t
  have hTT : |t| ≤ |T| := ht.trans (le_abs_self T)
  have hbdd : ∀ x : ℂ, ∀ i l : Fin 2, |Prelim.gradEntry (iterVel ω₀ j t) i l x| ≤
      Amax ω₀ * (calL ω₀ t + cstar ω₀) := fun x i l => (iter_lip h hne j t x).2.1 i l
  have hL2 : ∀ β : ℕ × ℕ, 1 ≤ β.1 + β.2 → β.1 + β.2 ≤ n + 2 →
      MemLp (partialD β (iterVel ω₀ j t)) 2 volume := fun β h1 _ => by
    rw [iterVel_eq]
    exact (BS.memLp_partialD_velocity_of_smooth hgs hgc h1).1
  obtain ⟨hmem, hle⟩ := comm_R2 (s := n + 2) (by omega) hWs hWc hvs ⟨_, hbdd⟩ hL2 hα
  refine ⟨hmem, hle.trans ?_⟩
  -- the three bounds
  have hA : gradEntryMax (iterVel ω₀ j t) ≤ Vbd ω₀ T := by
    refine (gradEntryMax_le hbdd).trans ?_
    have h1 : 0 ≤ Amax ω₀ * (calL ω₀ t + cstar ω₀) :=
      mul_nonneg (Amax_nonneg ω₀)
        (add_nonneg (calL_nonneg ω₀ t) (le_trans zero_le_two (cstar_ge_two ω₀)))
    have h2 : Vbd ω₀ t = 2 * (Amax ω₀ * (calL ω₀ t + cstar ω₀)) := by
      simp only [Vbd]
      ring
    have h3 := Vbd_mono ω₀ hTT
    linarith
  have hB : Prelim.gradNormH (n + 2 - 1) (iterVel ω₀ j t) ≤ M := by
    rw [show n + 2 - 1 = n + 1 from rfl, iterVel_eq,
      (BS.gradNormH_velocity_of_smooth hgs hgc (n + 1)).2]
    exact hM
  have hC : gradSupC (fun z => (iter ω₀ (j + 1) t z : ℂ)) ≤ Psi ω₀ T := by
    refine gradSupC_le fun x => ?_
    rw [gradAbs_ofReal (((contDiff_iter_slice h hne (j + 1) t).differentiable (by simp)) x)]
    exact norm_fderiv_iter_le h hne (j + 1) ht x
  have hB0 := Prelim.gradNormH_nonneg (n + 2 - 1) (iterVel ω₀ j t)
  have hZ := normH_nonneg (n + 2) (fun z => (iter ω₀ (j + 1) t z : ℂ))
  have hP : 0 ≤ gradSupC (fun z => (iter ω₀ (j + 1) t z : ℂ)) :=
    Real.iSup_nonneg fun x => Prelim.gradAbs_nonneg _ x
  have hpow : (0 : ℝ) ≤ 2 ^ (n + 2 + 1) := by positivity
  rw [show n + 2 + 1 = n + 3 from rfl] at hpow ⊢
  apply mul_le_mul_of_nonneg_left _ hpow
  have e1 : (gradEntryMax (iterVel ω₀ j t) + Prelim.gradNormH (n + 2 - 1) (iterVel ω₀ j t)) *
      normH (n + 2) (fun z => (iter ω₀ (j + 1) t z : ℂ)) ≤
      (Vbd ω₀ T + M) * normH (n + 2) (fun z => (iter ω₀ (j + 1) t z : ℂ)) :=
    mul_le_mul_of_nonneg_right (add_le_add hA hB) hZ
  have e2 : Prelim.gradNormH (n + 2 - 1) (iterVel ω₀ j t) *
      gradSupC (fun z => (iter ω₀ (j + 1) t z : ℂ)) ≤ M * Psi ω₀ T :=
    mul_le_mul hB hC hP (hB0.trans hB)
  linarith

/-- One top-order energy term: for `|α| = s = n + 2`,
`|Re ∫ conj(∂^α g) ∂^α ∂_t g| ≤ ‖g‖_{H^s} · 2^{s+1}[(V(T) + 𝓜)‖g‖_{H^s} + 𝓜Ψ(T)]`
with `g = ω^{[j+1]}(t)`. -/
theorem abs_re_energy_term_le (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (n j : ℕ) {t T M : ℝ}
    (ht : |t| ≤ T) (hM : normH (n + 1) (fun x => (iter ω₀ j t x : ℂ)) ≤ M)
    {α : ℕ × ℕ} (hα : α ∈ Finset.antidiagonal (n + 2)) :
    |(∫ x, conj (partialD α (fun z => (iter ω₀ (j + 1) t z : ℂ)) x) *
        partialD α (fun x => deriv (fun s => (iter ω₀ (j + 1) s x : ℂ)) t) x).re| ≤
      normH (n + 2) (fun z => (iter ω₀ (j + 1) t z : ℂ)) *
        (2 ^ (n + 3) * ((Vbd ω₀ T + M) * normH (n + 2) (fun z => (iter ω₀ (j + 1) t z : ℂ)) +
          M * Psi ω₀ T)) := by
  have hα' : α.1 + α.2 = n + 2 := Finset.mem_antidiagonal.1 hα
  have hgs := contDiff_iter_slice h hne j t
  have hgc := hasCompactSupport_iter_slice h hne j t
  have hWs := contDiff_iter_sliceC h hne (j + 1) t
  have hWc := hasCompactSupport_iter_sliceC h hne (j + 1) t
  have hvs := contDiff_iterVel_slice h hne j t
  set W : ℂ → ℂ := fun z => (iter ω₀ (j + 1) t z : ℂ) with hW
  set v : ℂ → ℂ := iterVel ω₀ j t with hv
  set A : ℂ → ℂ := partialD α W with hA
  set Dv : ℂ → ℂ := fun y => fderiv ℝ W y (v y) with hDv
  set C : ℂ → ℂ := fun x => partialD α Dv x - fderiv ℝ A x (v x) with hC
  have hAs : ContDiff ℝ ∞ A := contDiff_partialD hWs α
  have hAc : HasCompactSupport A := hasCompactSupport_partialD hWs hWc α
  have hDvs : ContDiff ℝ ∞ Dv := (ContDiff.fderiv_right (m := ∞) hWs (by simp)).clm_apply hvs
  have hCc : Continuous C :=
    (contDiff_partialD hDvs α).continuous.sub ((hAs.continuous_fderiv (by simp)).clm_apply
      hvs.continuous)
  have hderivW : (fun x => deriv (fun s => (iter ω₀ (j + 1) s x : ℂ)) t) = fun x => -Dv x :=
    funext (timeDeriv_iter_succ h hne j t)
  rw [hderivW, partialD_neg]
  have hpt : (fun x => conj (A x) * -partialD α Dv x) =
      fun x => -(conj (A x) * fderiv ℝ A x (v x)) - conj (A x) * C x := by
    funext x
    simp only [hC]
    ring
  have hint1 : Integrable (fun x => conj (A x) * fderiv ℝ A x (v x)) :=
    integrable_conj_mul hAs.continuous hAc ((hAs.continuous_fderiv (by simp)).clm_apply
      hvs.continuous)
  have hint2 : Integrable (fun x => conj (A x) * C x) :=
    integrable_conj_mul hAs.continuous hAc hCc
  have hdiv : Prelim.IsWeaklyDivFree v := by
    rw [hv, iterVel_eq]
    exact BS.isWeaklyDivFree_velocity_of_L1 (hgs.continuous.memLp_of_hasCompactSupport hgc)
  have htr := re_integral_conj_mul_fderiv_eq_zero hAs hAc hvs.continuous hdiv
  have hint1' : Integrable (fun x => -(conj (A x) * fderiv ℝ A x (v x))) := hint1.neg
  rw [hpt, integral_sub hint1' hint2, integral_neg, Complex.sub_re, Complex.neg_re, htr,
    neg_zero, zero_sub, abs_neg]
  -- Cauchy–Schwarz and the two bounds
  obtain ⟨hCmem, hCle⟩ := comm_bound h hne n j ht hM hα'
  have hAmem : MemLp A 2 volume := hAs.continuous.memLp_of_hasCompactSupport hAc
  have hAle : l2 A ≤ normH (n + 2) W :=
    l2_partialD_le_normH hWs hWc (antidiagonal_subset_multiIdx _ hα)
  refine (Complex.abs_re_le_norm _).trans ((norm_integral_conj_mul_le hAmem hCmem).trans ?_)
  exact mul_le_mul hAle hCle (l2_nonneg _) (normH_nonneg _ _)

end NonUniqueEuler.Smooth.IterHsH
