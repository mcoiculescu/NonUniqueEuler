import NonUniqueEuler.H.Sec5.Active.Layer.Config
import NonUniqueEuler.H.Sec5.Active.Layer.Comparison

/-!
# Helpers for the initial layer of `thm:active`: the improvement step of the continuity argument

Helper of `P/Sec5/Active/Layer.lean` (fully proved modulo the interface files it imports).
Namespace `NonUniqueEuler.OneRing.LayerH`. Manuscript `05_single_ring.tex:961-988`.

* `layer_core`: on `[0,t] ⊆ [0,ū]`, `t ≤ t̄`, if every trajectory of `ω_r` moves radially by at
  most `a/16` (from `supp ω_r(0) ⊂ 𝒩₋`, so `supp ω_r ⊂ N`) and `‖w‖_{H^n} ≤ 1`, and an
  approximate solution `w_app ∈ C([0,ū];X^{n+1}) ∩ C¹([0,ū];X^n)` with `w_app(0) = w(0)` satisfies
  `‖w_app‖_{H^{n+1}} ≤ W ≤ 1`, `‖R_app‖_{H^n} ≤ R`, while `‖h‖_{C^{n+1}(N')} ≤ H ≤ 1` and
  `‖h‖_{C^0(N')} ≤ H`, then on `[0,t]`: `‖w - w_app‖_{H^n} ≤ t̄e^{Λt̄}R` (`lem:energy`),
  `‖w‖_{H^n} ≤ W + t̄e^{Λt̄}R`, and the displacement is at most `t̄(H + C_BS(W + t̄e^{Λt̄}R))`
  (`lem:reduction`(2), `lem:bilinear`(4)).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

namespace LayerH

/-- **The improvement step** of the continuity argument on the initial layer
(`05_single_ring.tex:961-988`, in the one-step form: the comparison with `w_app = wlin` at level
`n = M-2` both bounds `w - wlin` and closes the bootstrap). -/
theorem layer_core {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {n : ℕ} (hn : 3 ≤ n) {c : RingConfig} {ubar t tb : ℝ} (hc : c.Hyp ubar)
    (ht : t ∈ Icc (0 : ℝ) ubar) (htb : t ≤ tb) (hG : c.G ∈ Icc (0 : ℝ) Gbar)
    (hr : tsupport c.ring0 ⊆ annNm)
    {wapp wapp' : ℝ → ℂ → ℂ} (happ : PathC (n + 1) ubar wapp)
    (happ' : PathC1 n ubar wapp wapp')
    (hreal : ∀ u ∈ Icc (0 : ℝ) ubar, ∀ᵐ x ∂(volume : Measure ℂ), (wapp u x).im = 0)
    (happ0 : wapp 0 =ᵐ[volume] c.pert0 χ)
    {W H R : ℝ} (hW1 : W ≤ 1) (hH1 : H ≤ 1) (hR0 : 0 ≤ R)
    (hwapp : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH (n + 1) (wapp τ) ≤ W)
    (hh : ∀ τ ∈ Icc (0 : ℝ) t, normCk (n + 1) annN' (c.h τ) ≤ H)
    (hh0 : ∀ τ ∈ Icc (0 : ℝ) t, normCk 0 annN' (c.h τ) ≤ H)
    (hR : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH n (Rapp χ c.G c.h wapp wapp' τ) ≤ R)
    (hm : c.MovesRadially t (a / 16)) (hw1 : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH n (c.w χ τ) ≤ 1) :
    (∀ τ ∈ Icc (0 : ℝ) t, Sob.normH n (c.w χ τ - wapp τ) ≤
        tb * (Real.exp (Lam χ n * tb) * R)) ∧
      (∀ τ ∈ Icc (0 : ℝ) t, Sob.normH n (c.w χ τ) ≤ W + tb * (Real.exp (Lam χ n * tb) * R)) ∧
      c.MovesRadially t (tb * (H + CBS * (W + tb * (Real.exp (Lam χ n * tb) * R)))) := by
  have hsupp : c.RingSupportedIn t annN := ringSupported_of_moves hc hr hm le_rfl
  have hΛ : 0 ≤ Lam χ n := (lambda_ge χ hχ hN hn).2.le
  have hIt : ∀ τ ∈ Icc (0 : ℝ) t, τ ∈ Icc (0 : ℝ) ubar := fun τ hτ => ⟨hτ.1, hτ.2.trans ht.2⟩
  set V := tb * (Real.exp (Lam χ n * tb) * R) with hV
  -- `lem:energy` with `w_app`
  have hv : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH n (c.w χ τ - wapp τ) ≤ V := by
    intro τ hτ
    have h1 := v_le_integral hχ hN hn hc ht hG hsupp (w_zero hc χ) happ happ' hreal happ0 hw1
      (fun τ' hτ' => (hwapp τ' hτ').trans hW1) (fun τ' hτ' => (hh τ' hτ').trans hH1)
      (R := fun _ => R) continuousOn_const hR τ hτ
    refine h1.trans ((integral_exp_const_le hΛ hR0 hτ.1).trans ?_)
    have hτb : τ ≤ tb := hτ.2.trans htb
    have he : Real.exp (Lam χ n * τ) ≤ Real.exp (Lam χ n * tb) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτb hΛ)
    have h0 : 0 ≤ Real.exp (Lam χ n * τ) * R := mul_nonneg (Real.exp_pos _).le hR0
    calc τ * (Real.exp (Lam χ n * τ) * R) ≤ tb * (Real.exp (Lam χ n * τ) * R) :=
          mul_le_mul_of_nonneg_right hτb h0
      _ ≤ tb * (Real.exp (Lam χ n * tb) * R) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he hR0) (hτ.1.trans hτb)
  -- the triangle inequality
  have hwB : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH n (c.w χ τ) ≤ W + V := by
    intro τ hτ
    have hmw : Sob.MemH n (c.w χ τ) := memH_w hχ hc τ n
    have hma : Sob.MemH (n + 1) (wapp τ) := (happ.1 τ (hIt τ hτ)).1
    have hma' : Sob.MemH n (wapp τ) := hma.mono_order (Nat.le_succ n)
    have hsplit := (hmw.sub hma').1.add hma'
    rw [sub_add_cancel] at hsplit
    have h2 : Sob.normH n (wapp τ) ≤ W := (normH_mono_order' (Nat.le_succ n) _).trans (hwapp τ hτ)
    linarith [hsplit.2, hv τ hτ]
  refine ⟨hv, hwB, ?_⟩
  -- the displacement
  have hdisp := displacement_le hχ hc ht hsupp (A := H) (B := W + V) hh0
    (fun τ hτ => (normH_mono_order' (by omega) _).trans (hwB τ hτ))
  intro y hy τ hτ
  refine (hdisp y hy τ hτ).trans ?_
  have hHn : 0 ≤ H := (normCk_nonneg _ _ _).trans (hh0 0 ⟨le_rfl, ht.1⟩)
  have hWV : 0 ≤ W + V := (Sob.normH_nonneg _ _).trans (hwB 0 ⟨le_rfl, ht.1⟩)
  have hCBS := CBS_pos
  have h0 : 0 ≤ H + CBS * (W + V) := by positivity
  exact mul_le_mul_of_nonneg_right (hτ.2.trans htb) h0

end LayerH

end OneRing

end NonUniqueEuler
