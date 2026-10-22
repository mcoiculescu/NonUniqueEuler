import NonUniqueEuler.H.SmoothB.IterLimit.Equation.Calc
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Helper for `prop:iter-limit`, step 4: families with uniformly convergent derivatives

Helper of `P/SmoothB/IterLimit/Equation.lean` (`B_global_smooth.tex:432-448`). This is the
"Leibniz formula" step of the manuscript ("the integrand is a finite sum of products of
`x`-derivatives of `v^{[j]}` and of `ω^{[j+1]}`, each converging uniformly and bounded"), in a
form that avoids writing the formula out.

`Good S F G` says: every `F n` is `C^∞` on `ℝ × ℝ²`, every slice `G s` is `C^∞` on `ℝ²`, and for
every list `ws` of directions in `{1, i}`, `∂_{ws} F n → ∂_{ws} G` uniformly on `S`. For compact
`S` the class is closed under `∂_1`, `∂_2` (`Good.dirDeriv`), sums (`Good.add`), products
(`Good.mul`; the limits are bounded on `S`, as uniform limits of continuous functions on a compact
set) and real-linear maps (`Good.clm`).
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Uniformity

namespace NonUniqueEuler.Smooth.IterLimitEqAux

open Sob

/-! ### Uniform convergence -/

/-- Reindexing a uniformly convergent sequence by `n ↦ n + 1`. -/
theorem tendstoUniformlyOn_succ {X : Type*} {S : Set X} {F : ℕ → X → ℂ} {f : X → ℂ}
    (h : TendstoUniformlyOn F f atTop S) :
    TendstoUniformlyOn (fun n => F (n + 1)) f atTop S :=
  fun u hu => (tendsto_add_atTop_nat 1).eventually (h u hu)

/-- Products of uniformly convergent sequences with bounded limits converge uniformly. -/
theorem tendstoUniformlyOn_mul {X : Type*} {S : Set X} {f g : ℕ → X → ℂ} {F G : X → ℂ}
    {M : ℝ} (hf : TendstoUniformlyOn f F atTop S) (hg : TendstoUniformlyOn g G atTop S)
    (hF : ∀ p ∈ S, ‖F p‖ ≤ M) (hG : ∀ p ∈ S, ‖G p‖ ≤ M) :
    TendstoUniformlyOn (fun n p => f n p * g n p) (fun p => F p * G p) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at hf hg ⊢
  intro ε hε
  set M' : ℝ := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hpos : 0 < 2 * M' + 2 := by positivity
  set δ : ℝ := min 1 (ε / (2 * M' + 2)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (div_pos hε hpos)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (2 * M' + 2) ≤ ε := by
    have : δ ≤ ε / (2 * M' + 2) := min_le_right _ _
    rwa [le_div_iff₀ hpos] at this
  filter_upwards [hf δ hδ0, hg δ hδ0] with n hn1 hn2 p hp
  have h1 := hn1 p hp
  have h2 := hn2 p hp
  rw [dist_eq_norm] at h1 h2 ⊢
  have hFp : ‖F p‖ ≤ M' := (hF p hp).trans (le_max_left _ _)
  have hgn : ‖g n p‖ ≤ M' + 1 := by
    have : ‖g n p‖ ≤ ‖G p‖ + ‖G p - g n p‖ :=
      calc ‖g n p‖ = ‖G p - (G p - g n p)‖ := by congr 1; ring
        _ ≤ ‖G p‖ + ‖G p - g n p‖ := norm_sub_le _ _
    linarith [(hG p hp).trans (le_max_left M 0)]
  have e : F p * G p - f n p * g n p = F p * (G p - g n p) + (F p - f n p) * g n p := by ring
  calc ‖F p * G p - f n p * g n p‖
      = ‖F p * (G p - g n p) + (F p - f n p) * g n p‖ := by rw [e]
    _ ≤ ‖F p‖ * ‖G p - g n p‖ + ‖F p - f n p‖ * ‖g n p‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ M' * δ + δ * (M' + 1) := by
        gcongr
    _ < δ * (2 * M' + 2) := by nlinarith
    _ ≤ ε := hδε

/-! ### The class of good families -/

/-- `F n → G` with all `x`-derivatives in the directions `1, i`, uniformly on `S`; `F n` is `C^∞`
on `ℝ × ℝ²` and every slice `G s` is `C^∞` on `ℝ²`. -/
structure Good (S : Set (ℝ × ℂ)) (F : ℕ → ℝ → ℂ → ℂ) (G : ℝ → ℂ → ℂ) : Prop where
  smoothF : ∀ n, ContDiff ℝ ∞ (Function.uncurry (F n))
  smoothG : ∀ s, ContDiff ℝ ∞ (G s)
  conv : ∀ ws : List ℂ, (∀ v ∈ ws, v = 1 ∨ v = Complex.I) →
    TendstoUniformlyOn (fun n (p : ℝ × ℂ) => iterDirDeriv ws (F n p.1) p.2)
      (fun p => iterDirDeriv ws (G p.1) p.2) atTop S

variable {S : Set (ℝ × ℂ)} {F F' : ℕ → ℝ → ℂ → ℂ} {G G' : ℝ → ℂ → ℂ}

theorem Good.smoothSlice (hF : Good S F G) (n : ℕ) (s : ℝ) : ContDiff ℝ ∞ (F n s) :=
  contDiff_slice (hF.smoothF n) s

/-- The limits are bounded on a compact `S`. -/
theorem Good.bound (hF : Good S F G) (hS : IsCompact S) :
    ∃ M, ∀ p ∈ S, ‖G p.1 p.2‖ ≤ M := by
  have hc : ContinuousOn (fun p : ℝ × ℂ => G p.1 p.2) S :=
    (hF.conv [] (by simp)).continuousOn
      (Frequently.of_forall fun n => (hF.smoothF n).continuous.continuousOn)
  exact hS.exists_bound_of_continuousOn hc

theorem Good.dirDeriv (hF : Good S F G) {v : ℂ} (hv : v = 1 ∨ v = Complex.I) :
    Good S (fun n s => Sob.dirDeriv v (F n s)) (fun s => Sob.dirDeriv v (G s)) where
  smoothF n := contDiff_iterDirDeriv_uncurry (hF.smoothF n) [v]
  smoothG s := contDiff_dirDeriv (hF.smoothG s) v
  conv ws hws := by
    have h := hF.conv (ws ++ [v]) (by
      intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · exact hws w hw
      · rw [List.mem_singleton.1 hw]; exact hv)
    simpa only [iterDirDeriv_append, iterDirDeriv_cons, iterDirDeriv_nil] using h

theorem Good.add (hF : Good S F G) (hF' : Good S F' G') :
    Good S (fun n s y => F n s y + F' n s y) (fun s y => G s y + G' s y) where
  smoothF n := (hF.smoothF n).add (hF'.smoothF n)
  smoothG s := (hF.smoothG s).add (hF'.smoothG s)
  conv ws hws := by
    have e1 : (fun n (p : ℝ × ℂ) => iterDirDeriv ws (fun y => F n p.1 y + F' n p.1 y) p.2) =
        fun n p => iterDirDeriv ws (F n p.1) p.2 + iterDirDeriv ws (F' n p.1) p.2 := by
      funext n p
      rw [iterDirDeriv_add (hF.smoothSlice n p.1) (hF'.smoothSlice n p.1)]
    have e2 : (fun p : ℝ × ℂ => iterDirDeriv ws (fun y => G p.1 y + G' p.1 y) p.2) =
        fun p => iterDirDeriv ws (G p.1) p.2 + iterDirDeriv ws (G' p.1) p.2 := by
      funext p
      rw [iterDirDeriv_add (hF.smoothG p.1) (hF'.smoothG p.1)]
    rw [e1, e2]
    exact (hF.conv ws hws).add (hF'.conv ws hws)

theorem Good.clm (hF : Good S F G) (L : ℂ →L[ℝ] ℂ) :
    Good S (fun n s y => L (F n s y)) (fun s y => L (G s y)) where
  smoothF n := L.contDiff.comp (hF.smoothF n)
  smoothG s := L.contDiff.comp (hF.smoothG s)
  conv ws hws := by
    have e1 : (fun n (p : ℝ × ℂ) => iterDirDeriv ws (fun y => L (F n p.1 y)) p.2) =
        fun n p => L (iterDirDeriv ws (F n p.1) p.2) := by
      funext n p
      rw [iterDirDeriv_clm_comp L (hF.smoothSlice n p.1)]
    have e2 : (fun p : ℝ × ℂ => iterDirDeriv ws (fun y => L (G p.1 y)) p.2) =
        fun p => L (iterDirDeriv ws (G p.1) p.2) := by
      funext p
      rw [iterDirDeriv_clm_comp L (hF.smoothG p.1)]
    rw [e1, e2]
    exact L.uniformContinuous.comp_tendstoUniformlyOn (hF.conv ws hws)

/-- The Leibniz step: derivatives of products of good families converge. -/
theorem Good.conv_mul (hS : IsCompact S) (ws : List ℂ) :
    (∀ v ∈ ws, v = 1 ∨ v = Complex.I) →
    ∀ {F F' : ℕ → ℝ → ℂ → ℂ} {G G' : ℝ → ℂ → ℂ}, Good S F G → Good S F' G' →
      TendstoUniformlyOn
        (fun n (p : ℝ × ℂ) => iterDirDeriv ws (fun y => F n p.1 y * F' n p.1 y) p.2)
        (fun p => iterDirDeriv ws (fun y => G p.1 y * G' p.1 y) p.2) atTop S := by
  induction ws using List.reverseRecOn with
  | nil =>
    intro _ F F' G G' hF hF'
    obtain ⟨M₁, hM₁⟩ := hF.bound hS
    obtain ⟨M₂, hM₂⟩ := hF'.bound hS
    exact tendstoUniformlyOn_mul (M := max M₁ M₂) (hF.conv [] (by simp)) (hF'.conv [] (by simp))
      (fun p hp => (hM₁ p hp).trans (le_max_left _ _))
      (fun p hp => (hM₂ p hp).trans (le_max_right _ _))
  | append_singleton vs v ih =>
    intro hws F F' G G' hF hF'
    have hvs : ∀ w ∈ vs, w = 1 ∨ w = Complex.I := fun w hw => hws w (by simp [hw])
    have hv : v = 1 ∨ v = Complex.I := hws v (by simp)
    have e1 : (fun n (p : ℝ × ℂ) =>
        iterDirDeriv (vs ++ [v]) (fun y => F n p.1 y * F' n p.1 y) p.2) =
        fun n p => iterDirDeriv vs (fun y => Sob.dirDeriv v (F n p.1) y * F' n p.1 y) p.2 +
          iterDirDeriv vs (fun y => F n p.1 y * Sob.dirDeriv v (F' n p.1) y) p.2 := by
      funext n p
      rw [iterDirDeriv_append_mul (hF.smoothSlice n p.1) (hF'.smoothSlice n p.1)]
    have e2 : (fun p : ℝ × ℂ =>
        iterDirDeriv (vs ++ [v]) (fun y => G p.1 y * G' p.1 y) p.2) =
        fun p => iterDirDeriv vs (fun y => Sob.dirDeriv v (G p.1) y * G' p.1 y) p.2 +
          iterDirDeriv vs (fun y => G p.1 y * Sob.dirDeriv v (G' p.1) y) p.2 := by
      funext p
      rw [iterDirDeriv_append_mul (hF.smoothG p.1) (hF'.smoothG p.1)]
    rw [e1, e2]
    exact (ih hvs (hF.dirDeriv hv) hF').add (ih hvs hF (hF'.dirDeriv hv))

theorem Good.mul (hF : Good S F G) (hF' : Good S F' G') (hS : IsCompact S) :
    Good S (fun n s y => F n s y * F' n s y) (fun s y => G s y * G' s y) where
  smoothF n := (hF.smoothF n).mul (hF'.smoothF n)
  smoothG s := (hF.smoothG s).mul (hF'.smoothG s)
  conv ws hws := Good.conv_mul hS ws hws hF hF'

/-- Restriction of the uniform convergence on `[-T, T] × {x}` to the time variable. -/
theorem tendstoUniformlyOn_slice {Fn : ℕ → ℝ × ℂ → ℂ} {f : ℝ × ℂ → ℂ} {T : ℝ} {x : ℂ}
    (h : TendstoUniformlyOn Fn f atTop (Icc (-T) T ×ˢ {x})) :
    TendstoUniformlyOn (fun n s => Fn n (s, x)) (fun s => f (s, x)) atTop (Ioo (-T) T) :=
  fun u hu => (h u hu).mono fun _ hn s hs => hn (s, x) ⟨Ioo_subset_Icc_self hs, rfl⟩

end NonUniqueEuler.Smooth.IterLimitEqAux
