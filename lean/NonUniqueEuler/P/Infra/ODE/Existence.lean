import NonUniqueEuler.Defs.Infra.ODE
import NonUniqueEuler.Vendor.ODE.GlobalPicard
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Proof of (I-ODE) existence for `ψ'' = V ψ + F` (`I/Infra/ODE/Existence.lean`)

Same declarations as the interface file, now proved.

Proof.
* On a compact interval `[ξ₀ - R, ξ₀ + R]` the coefficients are replaced by their composition
  with the clamp `t ↦ max lo (min hi t)`; the first-order field `(Y.1, Y.2) ↦ (Y.2, V Y.1 + F)`
  is then jointly continuous and globally Lipschitz in `Y`, so the vendored global Picard
  theorem (`Vendor.GlobalPicard.exists_solution_on_compact_interval`) gives a solution on the
  interval (`ExistenceAux.exists_sol_Icc`).
* The solutions on `[ξ₀ - (n+1), ξ₀ + (n+1)]`, `n : ℕ`, agree on the open intervals by
  uniqueness (`ODE_solution_unique_of_mem_Ioo`, again for the clamped, globally Lipschitz
  field; `ExistenceAux.eqOn_Ioo`), so they glue to a global solution
  (`ExistenceAux.exists_global`): `Y t = Y_{⌈|t - ξ₀|⌉₊} t`.
* The compact-interval version extends `V`, `F` continuously by clamping and restricts.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.LinODE

namespace ExistenceAux

/-- Clamp to `[lo, hi]`. -/
def clamp (lo hi t : ℝ) : ℝ := max lo (min hi t)

theorem continuous_clamp (lo hi : ℝ) : Continuous (clamp lo hi) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clamp_of_mem {lo hi t : ℝ} (ht : t ∈ Icc lo hi) : clamp lo hi t = t := by
  simp only [clamp, min_eq_right ht.2, max_eq_right ht.1]

theorem clamp_mem {lo hi : ℝ} (h : lo ≤ hi) (t : ℝ) : clamp lo hi t ∈ Icc lo hi :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

/-- The first-order field of `ψ'' = V ψ + F`. -/
def field (V F : ℝ → ℂ) (t : ℝ) (Y : ℂ × ℂ) : ℂ × ℂ := (Y.2, V t * Y.1 + F t)

theorem continuous_field {V F : ℝ → ℂ} (hV : Continuous V) (hF : Continuous F) :
    Continuous (Function.uncurry (field V F)) := by
  have hV' : Continuous fun p : ℝ × (ℂ × ℂ) => V p.1 := hV.comp continuous_fst
  have hF' : Continuous fun p : ℝ × (ℂ × ℂ) => F p.1 := hF.comp continuous_fst
  exact (continuous_snd.comp continuous_snd).prodMk
    ((hV'.mul (continuous_fst.comp continuous_snd)).add hF')

/-- The Lipschitz constant `max 1 M`. -/
def lipConst (M : ℝ) : NNReal := ⟨max 1 M, le_trans zero_le_one (le_max_left _ _)⟩

theorem lipschitz_field {V F : ℝ → ℂ} {M : ℝ} (hM : ∀ t, ‖V t‖ ≤ M) (t : ℝ) :
    LipschitzWith (lipConst M) (field V F t) := by
  apply LipschitzWith.of_dist_le_mul
  intro Y Y'
  have hKc : ((lipConst M : NNReal) : ℝ) = max 1 M := rfl
  rw [dist_eq_norm, dist_eq_norm, hKc, Prod.norm_def, Prod.norm_def]
  simp only [field, Prod.fst_sub, Prod.snd_sub, add_sub_add_right_eq_sub]
  have h1 : ‖Y.1 - Y'.1‖ ≤ max ‖Y.1 - Y'.1‖ ‖Y.2 - Y'.2‖ := le_max_left _ _
  have h2 : ‖Y.2 - Y'.2‖ ≤ max ‖Y.1 - Y'.1‖ ‖Y.2 - Y'.2‖ := le_max_right _ _
  have hm0 : 0 ≤ max ‖Y.1 - Y'.1‖ ‖Y.2 - Y'.2‖ := (norm_nonneg _).trans h1
  have hM1 : 1 ≤ max 1 M := le_max_left _ _
  have hMM : M ≤ max 1 M := le_max_right _ _
  refine max_le ?_ ?_
  · nlinarith
  · rw [← mul_sub, norm_mul]
    have hVt : ‖V t‖ ≤ max 1 M := (hM _).trans hMM
    exact mul_le_mul hVt h1 (norm_nonneg _) (by linarith)

/-- The clamped coefficient is bounded. -/
theorem exists_bound_clamp {V : ℝ → ℂ} {lo hi : ℝ} (hlh : lo ≤ hi)
    (hV : ContinuousOn V (Icc lo hi)) : ∃ M, ∀ t, ‖V (clamp lo hi t)‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hV
  exact ⟨M, fun t => hM _ (clamp_mem hlh t)⟩

/-- The field with clamped coefficients agrees with the original one on `[lo, hi]`. -/
theorem field_clamp_of_mem {V F : ℝ → ℂ} {lo hi t : ℝ} (ht : t ∈ Icc lo hi) :
    field (fun s => V (clamp lo hi s)) (fun s => F (clamp lo hi s)) t = field V F t := by
  funext Y
  simp only [field, clamp_of_mem ht]

/-- Existence on a compact interval `[ξ₀ - R, ξ₀ + R]` for continuous coefficients. -/
theorem exists_sol_Icc {V F : ℝ → ℂ} (hV : Continuous V) (hF : Continuous F) (ξ₀ : ℝ)
    {R : ℝ} (hR : 0 ≤ R) (x : ℂ × ℂ) :
    ∃ Y : ℝ → ℂ × ℂ, Y ξ₀ = x ∧
      ∀ t ∈ Icc (ξ₀ - R) (ξ₀ + R), HasDerivAt Y (field V F t (Y t)) t := by
  have hlh : ξ₀ - R ≤ ξ₀ + R := by linarith
  obtain ⟨M, hM⟩ := exists_bound_clamp hlh hV.continuousOn
  have hVc : Continuous fun s => V (clamp (ξ₀ - R) (ξ₀ + R) s) :=
    hV.comp (continuous_clamp _ _)
  have hFc : Continuous fun s => F (clamp (ξ₀ - R) (ξ₀ + R) s) :=
    hF.comp (continuous_clamp _ _)
  let t₀ : Icc (ξ₀ - R) (ξ₀ + R) := ⟨ξ₀, by constructor <;> linarith⟩
  obtain ⟨Y, hY0, hY⟩ := Vendor.GlobalPicard.exists_solution_on_compact_interval t₀
    (continuous_field hVc hFc) (lipschitz_field (F := fun s => F (clamp (ξ₀ - R) (ξ₀ + R) s))
      hM) x
  refine ⟨Y, hY0, fun t ht => ?_⟩
  have := hY t ht
  rwa [field_clamp_of_mem ht] at this

/-- Uniqueness on an open interval for a continuous coefficient `V` (any forcing `F`). -/
theorem eqOn_Ioo {V F : ℝ → ℂ} (hV : Continuous V) {lo hi t₀ : ℝ} {Y Z : ℝ → ℂ × ℂ}
    (ht₀ : t₀ ∈ Ioo lo hi)
    (hY : ∀ t ∈ Ioo lo hi, HasDerivAt Y (field V F t (Y t)) t)
    (hZ : ∀ t ∈ Ioo lo hi, HasDerivAt Z (field V F t (Z t)) t) (h0 : Y t₀ = Z t₀) :
    EqOn Y Z (Ioo lo hi) := by
  have hlh : lo ≤ hi := (ht₀.1.trans ht₀.2).le
  obtain ⟨M, hM⟩ := exists_bound_clamp hlh hV.continuousOn
  have hfeq : ∀ t ∈ Ioo lo hi,
      field (fun s => V (clamp lo hi s)) (fun s => F (clamp lo hi s)) t = field V F t :=
    fun t ht => field_clamp_of_mem (Ioo_subset_Icc_self ht)
  refine ODE_solution_unique_of_mem_Ioo (s := fun _ => (univ : Set (ℂ × ℂ)))
    (v := field (fun s => V (clamp lo hi s)) (fun s => F (clamp lo hi s)))
    (fun t _ => (lipschitz_field hM t).lipschitzOnWith) ht₀ (fun t ht => ⟨?_, mem_univ _⟩)
    (fun t ht => ⟨?_, mem_univ _⟩) h0
  · rw [hfeq t ht]; exact hY t ht
  · rw [hfeq t ht]; exact hZ t ht

/-- The open interval `(ξ₀ - (n + 1), ξ₀ + (n + 1))`. -/
def ioo (ξ₀ : ℝ) (n : ℕ) : Set ℝ := Ioo (ξ₀ - (n + 1)) (ξ₀ + (n + 1))

theorem mem_ioo_self (ξ₀ : ℝ) (n : ℕ) : ξ₀ ∈ ioo ξ₀ n := by
  have : (0 : ℝ) < n + 1 := by positivity
  constructor <;> linarith

theorem mem_ioo_ceil (ξ₀ t : ℝ) : t ∈ ioo ξ₀ ⌈|t - ξ₀|⌉₊ := by
  have h1 : |t - ξ₀| ≤ ⌈|t - ξ₀|⌉₊ := Nat.le_ceil _
  have h2 : |t - ξ₀| < (⌈|t - ξ₀|⌉₊ : ℝ) + 1 := by linarith
  have h3 := abs_lt.1 h2
  constructor <;> linarith [h3.1, h3.2]

theorem ioo_mono (ξ₀ : ℝ) {m n : ℕ} (hmn : m ≤ n) : ioo ξ₀ m ⊆ ioo ξ₀ n := by
  have : (m : ℝ) ≤ n := by exact_mod_cast hmn
  intro t ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Global existence for the first-order system with continuous coefficients. -/
theorem exists_global {V F : ℝ → ℂ} (hV : Continuous V) (hF : Continuous F) (ξ₀ : ℝ)
    (x : ℂ × ℂ) :
    ∃ Y : ℝ → ℂ × ℂ, Y ξ₀ = x ∧ ∀ t, HasDerivAt Y (field V F t (Y t)) t := by
  have hloc : ∀ n : ℕ, ∃ Y : ℝ → ℂ × ℂ, Y ξ₀ = x ∧
      ∀ t ∈ Icc (ξ₀ - (n + 1)) (ξ₀ + (n + 1)), HasDerivAt Y (field V F t (Y t)) t :=
    fun n => exists_sol_Icc hV hF ξ₀ (by positivity) x
  choose W hW0 hWd using hloc
  have hWd' : ∀ n, ∀ t ∈ ioo ξ₀ n, HasDerivAt (W n) (field V F t (W n t)) t :=
    fun n t ht => hWd n t (Ioo_subset_Icc_self ht)
  have hle : ∀ m n, m ≤ n → EqOn (W m) (W n) (ioo ξ₀ m) := fun m n hmn =>
    eqOn_Ioo hV (mem_ioo_self ξ₀ m) (hWd' m)
      (fun t ht => hWd' n t (ioo_mono ξ₀ hmn ht)) (by rw [hW0, hW0])
  have hagree : ∀ m n, ∀ t ∈ ioo ξ₀ m, t ∈ ioo ξ₀ n → W m t = W n t := by
    intro m n t hm hn
    rcases le_total m n with h | h
    · exact hle m n h hm
    · exact (hle n m h hn).symm
  refine ⟨fun t => W ⌈|t - ξ₀|⌉₊ t, ?_, fun t => ?_⟩
  · exact hW0 _
  · set n := ⌈|t - ξ₀|⌉₊ with hn
    have htn : t ∈ ioo ξ₀ n := mem_ioo_ceil ξ₀ t
    have heq : (fun s => W ⌈|s - ξ₀|⌉₊ s) =ᶠ[𝓝 t] W n :=
      Filter.eventually_of_mem (Ioo_mem_nhds htn.1 htn.2)
        (fun s hs => hagree _ n s (mem_ioo_ceil ξ₀ s) hs)
    exact (hWd' n t htn).congr_of_eventuallyEq heq

end ExistenceAux

open ExistenceAux in
/-- The pair of components of a global solution of the first-order system solves the
second-order equation. -/
private theorem isInhomSolOn_of_field {V F : ℝ → ℂ} {Y : ℝ → ℂ × ℂ}
    (hY : ∀ t, HasDerivAt Y (field V F t (Y t)) t) :
    IsInhomSolOn V F univ (fun ξ => (Y ξ).1) (fun ξ => (Y ξ).2) := by
  have h1 : ∀ t, HasDerivAt (fun ξ => (Y ξ).1) (Y t).2 t := fun t =>
    (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t (hY t)
  have h2 : ∀ t, HasDerivAt (fun ξ => (Y ξ).2) (V t * (Y t).1 + F t) t := fun t =>
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t (hY t)
  exact ⟨fun ξ _ => (h1 ξ).hasDerivWithinAt, fun ξ _ => (h2 ξ).hasDerivWithinAt⟩

variable {V F : ℝ → ℂ} {s : Set ℝ} {ψ ψ' φ φ' : ℝ → ℂ}

/-- Global existence for continuous coefficients. -/
theorem exists_isInhomSolOn_univ (hV : Continuous V) (hF : Continuous F) (ξ₀ : ℝ) (a b : ℂ) :
    ∃ ψ ψ' : ℝ → ℂ, IsInhomSolOn V F univ ψ ψ' ∧ ψ ξ₀ = a ∧ ψ' ξ₀ = b := by
  obtain ⟨Y, hY0, hY⟩ := ExistenceAux.exists_global hV hF ξ₀ (a, b)
  exact ⟨fun ξ => (Y ξ).1, fun ξ => (Y ξ).2, isInhomSolOn_of_field hY, by simp [hY0],
    by simp [hY0]⟩

/-- Global existence for a continuous coefficient (homogeneous equation). -/
theorem exists_isSolOn_univ (hV : Continuous V) (ξ₀ : ℝ) (a b : ℂ) :
    ∃ ψ ψ' : ℝ → ℂ, IsSolOn V univ ψ ψ' ∧ ψ ξ₀ = a ∧ ψ' ξ₀ = b := by
  obtain ⟨ψ, ψ', h, h0, h0'⟩ := exists_isInhomSolOn_univ hV continuous_const ξ₀ a b
    (F := fun _ => (0 : ℂ))
  exact ⟨ψ, ψ', isInhomSolOn_zero_iff.1 h, h0, h0'⟩

/-- Existence on a compact interval for coefficients continuous there. -/
theorem exists_isInhomSolOn_Icc {α β ξ₀ : ℝ} (hV : ContinuousOn V (Icc α β))
    (hF : ContinuousOn F (Icc α β)) (hξ₀ : ξ₀ ∈ Icc α β) (a b : ℂ) :
    ∃ ψ ψ' : ℝ → ℂ, IsInhomSolOn V F (Icc α β) ψ ψ' ∧ ψ ξ₀ = a ∧ ψ' ξ₀ = b := by
  have hαβ : α ≤ β := hξ₀.1.trans hξ₀.2
  have hVc : Continuous fun t => V (ExistenceAux.clamp α β t) :=
    hV.comp_continuous (ExistenceAux.continuous_clamp α β) (ExistenceAux.clamp_mem hαβ)
  have hFc : Continuous fun t => F (ExistenceAux.clamp α β t) :=
    hF.comp_continuous (ExistenceAux.continuous_clamp α β) (ExistenceAux.clamp_mem hαβ)
  obtain ⟨ψ, ψ', h, h0, h0'⟩ := exists_isInhomSolOn_univ hVc hFc ξ₀ a b
  refine ⟨ψ, ψ', ⟨fun ξ _ => (h.hasDerivWithinAt ξ (mem_univ _)).mono (subset_univ _),
    fun ξ hξ => ?_⟩, h0, h0'⟩
  have := (h.hasDerivWithinAt' ξ (mem_univ _)).mono (subset_univ (Icc α β))
  rwa [ExistenceAux.clamp_of_mem hξ] at this

/-- The chosen global solution is a solution with the prescribed data. -/
theorem sol_spec (hV : Continuous V) (ξ₀ : ℝ) (y₀ : ℂ × ℂ) :
    IsSolOn V univ (fun ξ => (sol V ξ₀ y₀ ξ).1) (fun ξ => (sol V ξ₀ y₀ ξ).2) ∧
      sol V ξ₀ y₀ ξ₀ = y₀ := by
  obtain ⟨ψ, ψ', h, h0, h0'⟩ := exists_isSolOn_univ hV ξ₀ y₀.1 y₀.2
  exact sol_spec_of_exists ⟨fun ξ => (ψ ξ, ψ' ξ), h, Prod.ext h0 h0'⟩

end NonUniqueEuler.LinODE
