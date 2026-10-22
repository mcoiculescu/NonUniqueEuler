import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.H.Sec5.Active.Layer.Bridge

/-!
# Helpers for the initial layer of `thm:active`: the size of the linear response

Helper of `P/Sec5/Active/Layer.lean` (fully proved modulo the interface files imported by
`H/Sec5/Active/Layer/Bridge.lean`). Namespace `NonUniqueEuler.OneRing.LayerH`.

* `wlin0_norm_le` (`05_single_ring.tex:979-981`, "Proposition `prop:semigroup` with
  Lemma `lem:bilinear` gives `‖wlin(u)‖_{H^{M-1}} ≤ C^lay_3 κ`"): for a constant `C_S` of
  `prop:semigroup` at level `k`, `w₀ ∈ X^k`, `h` symmetric with `‖h(v)‖_{C^k(N')} ≤ B` on `[0,ū]`
  and `e^{σ(G)u} ≤ E`,
  `‖wlin₀(u)‖_{H^k} ≤ C_S E (‖w₀‖_{H^k} + u C_∇(k) B)`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.LayerH

open RingData

/-- **The size of the linear response** (`05_single_ring.tex:979-981`):
`‖e^{uL}w₀ + ∫₀ᵘe^{(u-v)L}F(v)dv‖_{H^k} ≤ C_S E(‖w₀‖_{H^k} + u C_∇(k) B)`. -/
theorem wlin0_norm_le (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {k : ℕ} (hk : 2 ≤ k) {σ' CS : ℝ} (hCS : IsSemigroupConst χ k σ' CS) (hCS0 : 0 ≤ CS)
    {G ubar : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) (hσ : 0 ≤ Eig.sigma χ G)
    {w₀ : ℂ → ℂ} (hw₀ : Lin.MemXFn k w₀) {h : ℝ → ℂ → ℂ}
    (hh : ∀ v ∈ Icc (0 : ℝ) ubar, MemCk k annN' (h v))
    (hsym : ∀ v ∈ Icc (0 : ℝ) ubar, IsSymFieldOn annN' (h v))
    {B E : ℝ} (hB : ∀ v ∈ Icc (0 : ℝ) ubar, normCk k annN' (h v) ≤ B)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) ubar) (hE : Real.exp (Eig.sigma χ G * u) ≤ E) :
    ‖wlin0 χ k G w₀ h u‖ ≤ CS * E * (Sob.normH k w₀ + u * (Eig.Cnab χ k * B)) := by
  rw [wlin0_def]
  have hCn := Cnab_nonneg χ k
  have hE0 : 0 ≤ E := (Real.exp_pos _).le.trans hE
  -- the free evolution
  have h1 : ‖Lin.S χ k G u (Sect.toY k annN w₀)‖ ≤ CS * E * Sob.normH k w₀ := by
    refine ((hCS G hG u hu.1).2.2 _ (memX_toY hw₀)).trans ?_
    rw [norm_toY hw₀]
    have hn := Sob.normH_nonneg k w₀
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hCS0) hn
  -- the Duhamel integral
  have h2 : ‖∫ v in (0 : ℝ)..u, Lin.S χ k G (u - v) (Sect.toY k annN (forcing χ h v))‖ ≤
      CS * E * (Eig.Cnab χ k * B) * |u - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro v hv
    rw [uIoc_of_le hu.1] at hv
    have hvI : v ∈ Icc (0 : ℝ) ubar := ⟨hv.1.le, hv.2.trans hu.2⟩
    have hF := forcing_memX_norm χ hχ hN hk (hh v hvI) (hsym v hvI)
    have hF' : Sect.toY k annN (forcing χ h v) =
        Sect.toY k annN (fun x => -hGrad (h v) (PhiC χ) x) := rfl
    rw [hF']
    have huv : 0 ≤ u - v := by linarith [hv.2]
    refine ((hCS G hG (u - v) huv).2.2 _ hF.1).trans ?_
    have he : Real.exp (Eig.sigma χ G * (u - v)) ≤ E := by
      refine le_trans ?_ hE
      apply Real.exp_le_exp.2
      have : 0 ≤ v := hv.1.le
      nlinarith
    have hFB : ‖Sect.toY k annN (fun x => -hGrad (h v) (PhiC χ) x)‖ ≤ Eig.Cnab χ k * B :=
      hF.2.trans (mul_le_mul_of_nonneg_left (hB v hvI) hCn)
    have hn := norm_nonneg (Sect.toY k annN (fun x => -hGrad (h v) (PhiC χ) x))
    calc CS * Real.exp (Eig.sigma χ G * (u - v)) *
          ‖Sect.toY k annN (fun x => -hGrad (h v) (PhiC χ) x)‖
        ≤ CS * E * ‖Sect.toY k annN (fun x => -hGrad (h v) (PhiC χ) x)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hCS0) hn
      _ ≤ CS * E * (Eig.Cnab χ k * B) :=
          mul_le_mul_of_nonneg_left hFB (mul_nonneg hCS0 hE0)
  refine (norm_add_le _ _).trans ?_
  rw [sub_zero, abs_of_nonneg hu.1] at h2
  have : CS * E * (Sob.normH k w₀ + u * (Eig.Cnab χ k * B)) =
      CS * E * Sob.normH k w₀ + CS * E * (Eig.Cnab χ k * B) * u := by ring
  rw [this]
  exact add_le_add h1 h2

end NonUniqueEuler.OneRing.LayerH
