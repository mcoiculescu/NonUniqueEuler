import NonUniqueEuler.Vendor.ODE.GlobalPicard
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Helper for `P/Evans/ODE`: second-order linear ODEs `ψ'' = V ψ + F` with complex values

Abstract facts, with no reference to the Evans function (`04_ring.tex`, `def:evans`):
* `gronwall2`: a Grönwall estimate for the pair `(d, d')` when `d'' = W d + R` on `[α, β]`,
  with one-sided derivatives within `[α, β]` (the form of `IsEvansSolution`);
* `sol_bound`, `sol_sub_bound`, `sol_eqOn`: a priori bound, stability and uniqueness;
* `sol_lin_bound`: the estimate behind complex differentiability in a parameter;
* `exists_sol2`: global existence on `ℝ` for continuous `V`, `F` with `V` bounded (from the
  vendored global Picard theorem);
* `contDiff_of_sol2`: `C^∞` regularity of global solutions when `V` and `F` are `C^∞`.
-/

namespace NonUniqueEuler.EvansODE

open Set Function
open scoped ContDiff

/-- Grönwall for the pair `(d, d')` with `d'' = W d + R` on `[α, β]`, `‖W‖ ≤ K`, `1 ≤ K`,
`‖R‖ ≤ ε`. -/
theorem gronwall2 {α β K ε : ℝ} (_hαβ : α ≤ β) (hK : 1 ≤ K) (hε : 0 ≤ ε)
    {d d' W R : ℝ → ℂ}
    (hd : ∀ t ∈ Icc α β, HasDerivWithinAt d (d' t) (Icc α β) t)
    (hd' : ∀ t ∈ Icc α β, HasDerivWithinAt d' (W t * d t + R t) (Icc α β) t)
    (hW : ∀ t ∈ Icc α β, ‖W t‖ ≤ K) (hR : ∀ t ∈ Icc α β, ‖R t‖ ≤ ε) :
    ∀ t ∈ Icc α β, ‖d t‖ ≤ (max ‖d α‖ ‖d' α‖ + ε) * Real.exp (K * (β - α)) ∧
      ‖d' t‖ ≤ (max ‖d α‖ ‖d' α‖ + ε) * Real.exp (K * (β - α)) := by
  set f : ℝ → ℂ × ℂ := fun t => (d t, d' t) with hf_def
  set f' : ℝ → ℂ × ℂ := fun t => (d' t, W t * d t + R t) with hf'_def
  have hderiv : ∀ t ∈ Icc α β, HasDerivWithinAt f (f' t) (Icc α β) t :=
    fun t ht => (hd t ht).prodMk (hd' t ht)
  have hcont : ContinuousOn f (Icc α β) := fun t ht => (hderiv t ht).continuousWithinAt
  have hf' : ∀ x ∈ Ico α β, HasDerivWithinAt f (f' x) (Ici x) x := fun x hx =>
    (hderiv x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hbound : ∀ x ∈ Ico α β, ‖f' x‖ ≤ K * ‖f x‖ + ε := by
    intro x hx
    have hx' := Ico_subset_Icc_self hx
    simp only [hf_def, hf'_def, Prod.norm_mk]
    have h1 : ‖d x‖ ≤ max ‖d x‖ ‖d' x‖ := le_max_left _ _
    have h2 : ‖d' x‖ ≤ max ‖d x‖ ‖d' x‖ := le_max_right _ _
    have hm : 0 ≤ max ‖d x‖ ‖d' x‖ := le_trans (norm_nonneg _) h1
    refine max_le ?_ ?_
    · nlinarith
    · calc ‖W x * d x + R x‖ ≤ ‖W x‖ * ‖d x‖ + ‖R x‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul]
        _ ≤ K * max ‖d x‖ ‖d' x‖ + ε := by
            gcongr
            · exact hW x hx'
            · exact hR x hx'
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le hcont hf' le_rfl hbound
  intro t ht
  have h1 := hgr t ht
  have hfa : ‖f α‖ = max ‖d α‖ ‖d' α‖ := by simp [hf_def]
  rw [hfa, gronwallBound_of_K_ne_0 (by linarith : K ≠ 0)] at h1
  set δ := max ‖d α‖ ‖d' α‖ with hδ
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hx0 : 0 ≤ t - α := by linarith [ht.1]
  have hexp1 : Real.exp (K * (t - α)) ≤ Real.exp (K * (β - α)) := by
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) hK0
  have hexp0 : 1 ≤ Real.exp (K * (t - α)) := Real.one_le_exp (mul_nonneg hK0 hx0)
  have hεK : ε / K ≤ ε := div_le_self hε hK
  have hb : δ * Real.exp (K * (t - α)) + ε / K * (Real.exp (K * (t - α)) - 1) ≤
      (δ + ε) * Real.exp (K * (β - α)) := by
    have hεK0 : 0 ≤ ε / K := div_nonneg hε hK0
    have e1 : δ * Real.exp (K * (t - α)) ≤ δ * Real.exp (K * (β - α)) :=
      mul_le_mul_of_nonneg_left hexp1 hδ0
    have e2 : ε / K * (Real.exp (K * (t - α)) - 1) ≤ ε * Real.exp (K * (β - α)) := by
      calc ε / K * (Real.exp (K * (t - α)) - 1) ≤ ε / K * Real.exp (K * (β - α)) := by
            apply mul_le_mul_of_nonneg_left _ hεK0; linarith
        _ ≤ ε * Real.exp (K * (β - α)) :=
            mul_le_mul_of_nonneg_right hεK (Real.exp_pos _).le
    nlinarith
  have hft : ‖f t‖ = max ‖d t‖ ‖d' t‖ := by simp [hf_def]
  rw [hft] at h1
  exact ⟨(le_max_left _ _).trans (h1.trans hb), (le_max_right _ _).trans (h1.trans hb)⟩

/-- A priori bound for a solution of `ψ'' = V ψ` on `[α, β]`. -/
theorem sol_bound {α β K : ℝ} (hαβ : α ≤ β) (hK : 1 ≤ K) {V ψ ψ' : ℝ → ℂ}
    (h1 : ∀ t ∈ Icc α β, HasDerivWithinAt ψ (ψ' t) (Icc α β) t)
    (h2 : ∀ t ∈ Icc α β, HasDerivWithinAt ψ' (V t * ψ t) (Icc α β) t)
    (hV : ∀ t ∈ Icc α β, ‖V t‖ ≤ K) :
    ∀ t ∈ Icc α β, ‖ψ t‖ ≤ max ‖ψ α‖ ‖ψ' α‖ * Real.exp (K * (β - α)) ∧
      ‖ψ' t‖ ≤ max ‖ψ α‖ ‖ψ' α‖ * Real.exp (K * (β - α)) := by
  have h := gronwall2 (R := fun _ => 0) (ε := 0) hαβ hK le_rfl h1
    (fun t ht => by simpa using h2 t ht) hV (fun t _ => by simp)
  intro t ht
  simpa using h t ht

/-- Stability: two solutions with the same initial data at `α`, of `ψ₁'' = V₁ ψ₁` and
`ψ₂'' = V₂ ψ₂`, with `‖V₂‖ ≤ K`, `‖V₁ - V₂‖ ≤ η` and `‖ψ₁‖ ≤ C` on `[α, β]`. -/
theorem sol_sub_bound {α β K η C : ℝ} (hαβ : α ≤ β) (hK : 1 ≤ K) (hη : 0 ≤ η) (hC : 0 ≤ C)
    {V₁ V₂ ψ₁ ψ₁' ψ₂ ψ₂' : ℝ → ℂ}
    (h₁ : ∀ t ∈ Icc α β, HasDerivWithinAt ψ₁ (ψ₁' t) (Icc α β) t)
    (h₁' : ∀ t ∈ Icc α β, HasDerivWithinAt ψ₁' (V₁ t * ψ₁ t) (Icc α β) t)
    (h₂ : ∀ t ∈ Icc α β, HasDerivWithinAt ψ₂ (ψ₂' t) (Icc α β) t)
    (h₂' : ∀ t ∈ Icc α β, HasDerivWithinAt ψ₂' (V₂ t * ψ₂ t) (Icc α β) t)
    (hi : ψ₁ α = ψ₂ α) (hi' : ψ₁' α = ψ₂' α)
    (hV₂ : ∀ t ∈ Icc α β, ‖V₂ t‖ ≤ K) (hV : ∀ t ∈ Icc α β, ‖V₁ t - V₂ t‖ ≤ η)
    (hψ₁ : ∀ t ∈ Icc α β, ‖ψ₁ t‖ ≤ C) :
    ∀ t ∈ Icc α β, ‖ψ₁ t - ψ₂ t‖ ≤ η * C * Real.exp (K * (β - α)) ∧
      ‖ψ₁' t - ψ₂' t‖ ≤ η * C * Real.exp (K * (β - α)) := by
  have h := gronwall2 (d := fun t => ψ₁ t - ψ₂ t) (d' := fun t => ψ₁' t - ψ₂' t)
    (W := V₂) (R := fun t => (V₁ t - V₂ t) * ψ₁ t) (ε := η * C) hαβ hK (mul_nonneg hη hC)
    (fun t ht => (h₁ t ht).sub (h₂ t ht))
    (fun t ht => ((h₁' t ht).sub (h₂' t ht)).congr_deriv (by ring))
    hV₂
    (fun t ht => by
      rw [norm_mul]
      exact mul_le_mul (hV t ht) (hψ₁ t ht) (norm_nonneg _) hη)
  intro t ht
  have := h t ht
  simp only [hi, hi', sub_self, norm_zero, max_self, zero_add] at this
  exact this

/-- Uniqueness of solutions of `ψ'' = V ψ` on `[α, β]` with given initial data at `α`. -/
theorem sol_eqOn {α β K : ℝ} (hαβ : α ≤ β) (hK : 1 ≤ K) {V ψ₁ ψ₁' ψ₂ ψ₂' : ℝ → ℂ}
    (h₁ : ∀ t ∈ Icc α β, HasDerivWithinAt ψ₁ (ψ₁' t) (Icc α β) t)
    (h₁' : ∀ t ∈ Icc α β, HasDerivWithinAt ψ₁' (V t * ψ₁ t) (Icc α β) t)
    (h₂ : ∀ t ∈ Icc α β, HasDerivWithinAt ψ₂ (ψ₂' t) (Icc α β) t)
    (h₂' : ∀ t ∈ Icc α β, HasDerivWithinAt ψ₂' (V t * ψ₂ t) (Icc α β) t)
    (hi : ψ₁ α = ψ₂ α) (hi' : ψ₁' α = ψ₂' α) (hV : ∀ t ∈ Icc α β, ‖V t‖ ≤ K) :
    EqOn ψ₁ ψ₂ (Icc α β) ∧ EqOn ψ₁' ψ₂' (Icc α β) := by
  have h := gronwall2 (d := fun t => ψ₁ t - ψ₂ t) (d' := fun t => ψ₁' t - ψ₂' t)
    (W := V) (R := fun _ => 0) (ε := 0) hαβ hK le_rfl
    (fun t ht => (h₁ t ht).sub (h₂ t ht))
    (fun t ht => ((h₁' t ht).sub (h₂' t ht)).congr_deriv (by ring)) hV (fun t _ => by simp)
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have := (h t ht).1
    simp only [hi, hi', sub_self, norm_zero, max_self, add_zero, zero_mul] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  · have := (h t ht).2
    simp only [hi, hi', sub_self, norm_zero, max_self, add_zero, zero_mul] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-- Linearization estimate. `ψ₁'' = V₁ ψ₁`, `ψ₀'' = V₀ ψ₀` with the same initial data, and
`φ'' = V₀ φ + Ṽ ψ₀` with `φ(α) = φ'(α) = 0`. Then `d = ψ₁ - ψ₀ - h φ` is small when
`V₁ - V₀ - h Ṽ` and `V₁ - V₀` are. -/
theorem sol_lin_bound {α β K η₁ D₁ η₂ C : ℝ} (hαβ : α ≤ β) (hK : 1 ≤ K) (hη₁ : 0 ≤ η₁)
    (hD₁ : 0 ≤ D₁) (hη₂ : 0 ≤ η₂) (hC : 0 ≤ C) (h : ℂ)
    {V₁ V₀ Vd ψ₁ ψ₁' ψ₀ ψ₀' φ φ' : ℝ → ℂ}
    (h₁ : ∀ t ∈ Icc α β, HasDerivWithinAt ψ₁ (ψ₁' t) (Icc α β) t)
    (h₁' : ∀ t ∈ Icc α β, HasDerivWithinAt ψ₁' (V₁ t * ψ₁ t) (Icc α β) t)
    (h₀ : ∀ t ∈ Icc α β, HasDerivWithinAt ψ₀ (ψ₀' t) (Icc α β) t)
    (h₀' : ∀ t ∈ Icc α β, HasDerivWithinAt ψ₀' (V₀ t * ψ₀ t) (Icc α β) t)
    (hφ : ∀ t ∈ Icc α β, HasDerivWithinAt φ (φ' t) (Icc α β) t)
    (hφ' : ∀ t ∈ Icc α β, HasDerivWithinAt φ' (V₀ t * φ t + Vd t * ψ₀ t) (Icc α β) t)
    (hi : ψ₁ α = ψ₀ α) (hi' : ψ₁' α = ψ₀' α) (hφi : φ α = 0) (hφi' : φ' α = 0)
    (hV₀ : ∀ t ∈ Icc α β, ‖V₀ t‖ ≤ K) (hV₁ : ∀ t ∈ Icc α β, ‖V₁ t - V₀ t‖ ≤ η₁)
    (hdψ : ∀ t ∈ Icc α β, ‖ψ₁ t - ψ₀ t‖ ≤ D₁)
    (hV₂ : ∀ t ∈ Icc α β, ‖V₁ t - V₀ t - h * Vd t‖ ≤ η₂)
    (hψ₀ : ∀ t ∈ Icc α β, ‖ψ₀ t‖ ≤ C) :
    ∀ t ∈ Icc α β, ‖ψ₁ t - ψ₀ t - h * φ t‖ ≤ (η₁ * D₁ + η₂ * C) * Real.exp (K * (β - α)) ∧
      ‖ψ₁' t - ψ₀' t - h * φ' t‖ ≤ (η₁ * D₁ + η₂ * C) * Real.exp (K * (β - α)) := by
  have hgr := gronwall2 (d := fun t => ψ₁ t - ψ₀ t - h * φ t)
    (d' := fun t => ψ₁' t - ψ₀' t - h * φ' t) (W := V₀)
    (R := fun t => (V₁ t - V₀ t) * (ψ₁ t - ψ₀ t) + (V₁ t - V₀ t - h * Vd t) * ψ₀ t)
    (ε := η₁ * D₁ + η₂ * C) hαβ hK (by positivity)
    (fun t ht => ((h₁ t ht).sub (h₀ t ht)).sub ((hφ t ht).const_mul h))
    (fun t ht => (((h₁' t ht).sub (h₀' t ht)).sub ((hφ' t ht).const_mul h)).congr_deriv
      (by ring))
    hV₀
    (fun t ht => by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      gcongr
      · exact hV₁ t ht
      · exact hdψ t ht
      · exact hV₂ t ht
      · exact hψ₀ t ht)
  intro t ht
  have := hgr t ht
  simp only [hi, hi', hφi, hφi', sub_self, mul_zero, norm_zero, max_self, zero_add] at this
  exact this

/-- Global existence on `ℝ` for `ψ'' = V ψ + F` with `V`, `F` continuous and `V` bounded. -/
theorem exists_sol2 {V F : ℝ → ℂ} (hV : Continuous V) (hF : Continuous F) {M : ℝ}
    (hM : ∀ t, ‖V t‖ ≤ M) (t₀ : ℝ) (a b : ℂ) :
    ∃ ψ ψ' : ℝ → ℂ, ψ t₀ = a ∧ ψ' t₀ = b ∧
      ∀ t, HasDerivAt ψ (ψ' t) t ∧ HasDerivAt ψ' (V t * ψ t + F t) t := by
  let f : ℝ → ℂ × ℂ → ℂ × ℂ := fun t Y => (Y.2, V (t + t₀) * Y.1 + F (t + t₀))
  have hf : Continuous (uncurry f) := by
    have hV' : Continuous fun p : ℝ × (ℂ × ℂ) => V (p.1 + t₀) :=
      hV.comp (continuous_fst.add continuous_const)
    have hF' : Continuous fun p : ℝ × (ℂ × ℂ) => F (p.1 + t₀) :=
      hF.comp (continuous_fst.add continuous_const)
    exact (continuous_snd.comp continuous_snd).prodMk
      ((hV'.mul (continuous_fst.comp continuous_snd)).add hF')
  let K : NNReal := ⟨max 1 M, le_trans zero_le_one (le_max_left _ _)⟩
  have hLip : ∀ t, LipschitzWith K (f t) := by
    intro t
    apply LipschitzWith.of_dist_le_mul
    intro Y Y'
    have hKc : ((K : NNReal) : ℝ) = max 1 M := rfl
    rw [dist_eq_norm, dist_eq_norm, hKc, Prod.norm_def, Prod.norm_def]
    simp only [f, Prod.fst_sub, Prod.snd_sub, add_sub_add_right_eq_sub]
    have h1 : ‖Y.1 - Y'.1‖ ≤ max ‖Y.1 - Y'.1‖ ‖Y.2 - Y'.2‖ := le_max_left _ _
    have h2 : ‖Y.2 - Y'.2‖ ≤ max ‖Y.1 - Y'.1‖ ‖Y.2 - Y'.2‖ := le_max_right _ _
    have hm0 : 0 ≤ max ‖Y.1 - Y'.1‖ ‖Y.2 - Y'.2‖ := (norm_nonneg _).trans h1
    have hM1 : 1 ≤ max 1 M := le_max_left _ _
    have hMM : M ≤ max 1 M := le_max_right _ _
    refine max_le ?_ ?_
    · nlinarith
    · rw [← mul_sub, norm_mul]
      have hV0 : 0 ≤ ‖V (t + t₀)‖ := norm_nonneg _
      have hVt : ‖V (t + t₀)‖ ≤ max 1 M := (hM _).trans hMM
      exact mul_le_mul hVt h1 (norm_nonneg _) (by linarith)
  obtain ⟨u, hu0, hu⟩ := Vendor.GlobalPicard.exists_global_solution hf hLip (a, b)
  refine ⟨fun t => (u (t - t₀)).1, fun t => (u (t - t₀)).2, by simp [hu0], by simp [hu0], ?_⟩
  intro t
  have hc : HasDerivAt (fun s => u (s - t₀)) (f (t - t₀) (u (t - t₀))) t :=
    HasDerivAt.comp_sub_const t t₀ (hu (t - t₀))
  have hfst := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hc
  have hsnd := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hc
  simp only [f, sub_add_cancel] at hfst hsnd
  exact ⟨hfst, hsnd⟩

/-- `C^∞` regularity of global solutions of `ψ'' = V ψ + F` for `C^∞` coefficients. -/
theorem contDiff_of_sol2 {V F : ℝ → ℂ} (hV : ContDiff ℝ ∞ V) (hF : ContDiff ℝ ∞ F)
    {ψ ψ' : ℝ → ℂ} (h : ∀ t, HasDerivAt ψ (ψ' t) t ∧ HasDerivAt ψ' (V t * ψ t + F t) t) :
    ContDiff ℝ ∞ ψ ∧ ContDiff ℝ ∞ ψ' := by
  have hd1 : deriv ψ = ψ' := funext fun t => (h t).1.deriv
  have hd2 : deriv ψ' = fun t => V t * ψ t + F t := funext fun t => (h t).2.deriv
  have key : ∀ n : ℕ, ContDiff ℝ n ψ ∧ ContDiff ℝ n ψ' := by
    intro n
    induction n with
    | zero =>
      simp only [CharP.cast_eq_zero, contDiff_zero]
      exact ⟨continuous_iff_continuousAt.2 fun t => (h t).1.continuousAt,
        continuous_iff_continuousAt.2 fun t => (h t).2.continuousAt⟩
    | succ n ih =>
      have hn : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hn, contDiff_succ_iff_deriv, contDiff_succ_iff_deriv, hd1, hd2]
      refine ⟨⟨fun t => (h t).1.differentiableAt, by simp, ih.2⟩,
        ⟨fun t => (h t).2.differentiableAt, by simp, ?_⟩⟩
      exact ((hV.of_le (by exact_mod_cast le_top)).mul ih.1).add
        (hF.of_le (by exact_mod_cast le_top))
  exact ⟨contDiff_infty.2 fun n => (key n).1, contDiff_infty.2 fun n => (key n).2⟩

end NonUniqueEuler.EvansODE
