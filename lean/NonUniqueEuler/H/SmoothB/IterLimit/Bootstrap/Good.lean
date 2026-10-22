import NonUniqueEuler.H.SmoothB.IterLimit.Bootstrap.Calc
import NonUniqueEuler.Defs.SmoothB.Iteration
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Helper for `prop:iter-limit`, step 5: space–time families with `C^n` spatial derivatives

Helper of `P/SmoothB/IterLimit/Bootstrap.lean` (`B_global_smooth.tex:449-472`). The class
`Good n f` (a stand-in for the manuscript's classes `𝒞^l(T)`, without the time derivatives):
every slice `f(t, ·)` is `C^∞` and every spatial derivative `(t, x) ↦ ∂_x^γ f(t, x)` is `C^n` on
`ℝ × ℝ²`. It is closed under sums (`Good.add`), real-linear maps (`Good.clm`), spatial
derivatives (`Good.partialD`) and products (`Good.mul`). The product rule is proved by induction on
`|γ|`, peeling off one first-order derivative at a time (no binomial Leibniz formula is needed).
-/

noncomputable section

open scoped ContDiff

namespace NonUniqueEuler.Smooth.BootstrapAux

open Sob

/-- `f` has `C^∞` slices, and all its spatial derivatives `∂_x^γ f` are `C^n` in `(t, x)`. -/
structure Good (n : ℕ) (f : ℝ → ℂ → ℂ) : Prop where
  smooth : ∀ t, ContDiff ℝ ∞ (f t)
  cont : ∀ γ : ℕ × ℕ, ContDiff ℝ n (fun p : ℝ × ℂ => spaceD γ f p.1 p.2)

/-- `∂^γ` is additive on smooth functions. -/
theorem partialD_add {f₁ f₂ : ℂ → ℂ} (h₁ : ContDiff ℝ ∞ f₁) (h₂ : ContDiff ℝ ∞ f₂)
    (γ : ℕ × ℕ) : partialD γ (fun x => f₁ x + f₂ x) =
      fun x => partialD γ f₁ x + partialD γ f₂ x :=
  iterDirDeriv_add h₁ h₂ _

theorem Good.add {n : ℕ} {f g : ℝ → ℂ → ℂ} (hf : Good n f) (hg : Good n g) :
    Good n (fun t x => f t x + g t x) where
  smooth t := (hf.smooth t).add (hg.smooth t)
  cont γ := by
    have h : (fun p : ℝ × ℂ => spaceD γ (fun t x => f t x + g t x) p.1 p.2) =
        fun p => spaceD γ f p.1 p.2 + spaceD γ g p.1 p.2 := by
      funext p
      simp only [spaceD]
      rw [partialD_add (hf.smooth p.1) (hg.smooth p.1)]
    rw [h]
    exact (hf.cont γ).add (hg.cont γ)

theorem Good.clm {n : ℕ} {f : ℝ → ℂ → ℂ} (hf : Good n f) (L : ℂ →L[ℝ] ℂ) :
    Good n (fun t x => L (f t x)) where
  smooth t := L.contDiff.comp (hf.smooth t)
  cont γ := by
    have h : (fun p : ℝ × ℂ => spaceD γ (fun t x => L (f t x)) p.1 p.2) =
        fun p => L (spaceD γ f p.1 p.2) := by
      funext p
      simp only [spaceD, partialD]
      rw [iterDirDeriv_clm_comp L (hf.smooth p.1)]
    rw [h]
    exact L.contDiff.comp (hf.cont γ)

theorem Good.partialD {n : ℕ} {f : ℝ → ℂ → ℂ} (hf : Good n f) (δ : ℕ × ℕ) :
    Good n (fun t => Sob.partialD δ (f t)) where
  smooth t := contDiff_partialD (hf.smooth t) δ
  cont γ := by
    have h : (fun p : ℝ × ℂ => spaceD γ (fun t => Sob.partialD δ (f t)) p.1 p.2) =
        fun p => spaceD (γ + δ) f p.1 p.2 := by
      funext p
      simp only [spaceD]
      rw [partialD_partialD (hf.smooth p.1)]
    rw [h]
    exact hf.cont (γ + δ)

/-- Every multi-index of order `k + 1` is `γ' + δ` with `|γ'| = k` and `δ` a unit index. -/
theorem exists_eq_add_unit {γ : ℕ × ℕ} {k : ℕ} (hγ : γ.1 + γ.2 = k + 1) :
    ∃ γ' δ : ℕ × ℕ, γ = γ' + δ ∧ γ'.1 + γ'.2 = k ∧ (δ = (1, 0) ∨ δ = (0, 1)) := by
  obtain ⟨a, b⟩ := γ
  simp only at hγ
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨(0, b - 1), (0, 1), ?_, ?_, Or.inr rfl⟩
    · ext <;> simp; omega
    · simp only; omega
  · refine ⟨(a - 1, b), (1, 0), ?_, ?_, Or.inl rfl⟩
    · ext <;> simp; omega
    · simp only; omega

theorem Good.mul_aux (n k : ℕ) : ∀ {f g : ℝ → ℂ → ℂ}, Good n f → Good n g →
    ∀ γ : ℕ × ℕ, γ.1 + γ.2 = k →
      ContDiff ℝ n (fun p : ℝ × ℂ => spaceD γ (fun t x => f t x * g t x) p.1 p.2) := by
  induction k with
  | zero =>
    intro f g hf hg γ hγ
    obtain ⟨a, b⟩ := γ
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by simp only at hγ; omega
    exact (hf.cont (0, 0)).mul (hg.cont (0, 0))
  | succ k ih =>
    intro f g hf hg γ hγ
    obtain ⟨γ', δ, rfl, hγ', hδ⟩ := exists_eq_add_unit hγ
    have h : (fun p : ℝ × ℂ => spaceD (γ' + δ) (fun t x => f t x * g t x) p.1 p.2) =
        fun p => spaceD γ' (fun t x => Sob.partialD δ (f t) x * g t x) p.1 p.2 +
          spaceD γ' (fun t x => f t x * Sob.partialD δ (g t) x) p.1 p.2 := by
      funext p
      have hfs := hf.smooth p.1
      have hgs := hg.smooth p.1
      simp only [spaceD]
      rw [← partialD_partialD (hfs.mul hgs) γ' δ,
        partialD_unit_mul hδ (hfs.differentiable (by simp)) (hgs.differentiable (by simp)),
        partialD_add ((contDiff_partialD hfs δ).mul hgs) (hfs.mul (contDiff_partialD hgs δ))]
    rw [h]
    exact (ih (hf.partialD δ) hg γ' hγ').add (ih hf (hg.partialD δ) γ' hγ')

theorem Good.mul {n : ℕ} {f g : ℝ → ℂ → ℂ} (hf : Good n f) (hg : Good n g) :
    Good n (fun t x => f t x * g t x) where
  smooth t := (hf.smooth t).mul (hg.smooth t)
  cont γ := Good.mul_aux n _ hf hg γ rfl

end NonUniqueEuler.Smooth.BootstrapAux
