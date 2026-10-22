import NonUniqueEuler.H.Sec5.Active.Layer.Core
import NonUniqueEuler.H.Sec5.Active.Layer.Lin
import NonUniqueEuler.I.Infra.Continuity.Bootstrap

/-!
# Helpers for the initial layer of `thm:active`: the steps of the proof

Helper of `P/Sec5/Active/Layer.lean` (fully proved modulo the interface files it imports).
Namespace `NonUniqueEuler.OneRing.LayerH`. Manuscript `05_single_ring.tex:953-1020`.

* `jap_pow_le`: `⟨u⟩^p ≤ ⟨t̄⟩^p` for `0 ≤ u ≤ t̄`;
* `field_on_layer`: (Field) gives `‖h(u)‖_{C^M(N')} ≤ (C₀⟨t̄₁⟩^p + e^{σ_max t̄₁})κ` on
  `[0, min(ū,t₁)]` (`05_single_ring.tex:955-957`);
* `wlin_on_layer`: `‖wlin(u)‖_{H^{n+1}} ≤ C_S E(C₀ + t̄₁C_∇(n+1)C_f)κ` (`:979-981`);
* `rapp_on_layer`: `‖R_app‖_{H^n} ≤ C_B(n)W² + C_h(n)HW` for `w_app = wlin` (`:983-985`);
* `layer_bootstrap`: the continuity argument (`Continuity.bootstrap_le`) for the displacement
  and `‖w‖_{H^n}` (`:961-976`);
* `normH_sub_modeFn_le`: the triangle inequality of item 2.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

namespace LayerH

/-- `⟨u⟩^p ≤ ⟨t̄⟩^p` for `0 ≤ u ≤ t̄`. -/
theorem jap_pow_le {u tb : ℝ} (hu : 0 ≤ u) (hut : u ≤ tb) :
    Prelim.jap u ^ pW ≤ Prelim.jap tb ^ pW := by
  have h1 : Prelim.jap u ≤ Prelim.jap tb := by
    unfold Prelim.jap
    apply Real.sqrt_le_sqrt
    nlinarith
  exact pow_le_pow_left₀ (Prelim.jap_nonneg u) h1 _

/-- **(Field) on the layer** (`05_single_ring.tex:955-957`): for `u ∈ [0,u₁]`, `u₁ ≤ min(ū,t̄)`,
`‖h(u)‖_{C^M(N')} ≤ (C₀⟨t̄⟩^p + e^{σ_m t̄})κ` when `0 ≤ σ(G) ≤ σ_m`, `η_b ≤ 1`. -/
theorem field_on_layer {χ : ℝ → ℝ} {s : ℕ} {c : RingConfig} {ubar C₀ κ ηb u₁ tb σm : ℝ}
    (hF : c.ActiveField χ s ubar C₀ κ ηb) (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ)
    (hηb : ηb ∈ Icc (0 : ℝ) etaMax) (hu₁b : u₁ ≤ ubar) (hu₁t : u₁ ≤ tb)
    (hσ0 : 0 ≤ Eig.sigma χ c.G) (hσm : Eig.sigma χ c.G ≤ σm) :
    ∀ u ∈ Icc (0 : ℝ) u₁, normCk (Mact χ s) annN' (c.h u) ≤
      (C₀ * Prelim.jap tb ^ pW + Real.exp (σm * tb)) * κ := by
  intro u hu
  have hσm0 : 0 ≤ σm := hσ0.trans hσm
  have hut : u ≤ tb := hu.2.trans hu₁t
  refine (field_bound hF u ⟨hu.1, hu.2.trans hu₁b⟩).trans ?_
  have h1 : C₀ * κ * Prelim.jap u ^ pW ≤ C₀ * κ * Prelim.jap tb ^ pW :=
    mul_le_mul_of_nonneg_left (jap_pow_le hu.1 hut) (mul_nonneg hC₀ hκ)
  have he : Real.exp (Eig.sigma χ c.G * u) ≤ Real.exp (σm * tb) :=
    Real.exp_le_exp.2 (mul_le_mul hσm hut hu.1 hσm0)
  have h2 : ηb * ahat κ (Eig.sigma χ c.G) u ≤ κ * Real.exp (σm * tb) := by
    unfold ahat
    have hηb1 : ηb ≤ 1 := hηb.2
    have h0 : 0 ≤ κ * Real.exp (Eig.sigma χ c.G * u) := mul_nonneg hκ (Real.exp_pos _).le
    calc ηb * (κ * Real.exp (Eig.sigma χ c.G * u))
        ≤ 1 * (κ * Real.exp (Eig.sigma χ c.G * u)) := mul_le_mul_of_nonneg_right hηb1 h0
      _ = κ * Real.exp (Eig.sigma χ c.G * u) := one_mul _
      _ ≤ κ * Real.exp (σm * tb) := mul_le_mul_of_nonneg_left he hκ
  have h3 : C₀ * κ * Prelim.jap tb ^ pW + κ * Real.exp (σm * tb) =
      (C₀ * Prelim.jap tb ^ pW + Real.exp (σm * tb)) * κ := by ring
  linarith only [h1, h2, h3]

/-- **The size of `wlin` on the layer** (`05_single_ring.tex:979-981`). -/
theorem wlin_on_layer (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {n : ℕ} (hn2 : 2 ≤ n) {σ' CS : ℝ} (hCS : IsSemigroupConst χ (n + 1) σ' CS) (hCS0 : 0 ≤ CS)
    {c : RingConfig} {ubar u₁ tb C₀ κ Cf Em : ℝ} (hc : c.Hyp ubar)
    (hG : c.G ∈ Icc (0 : ℝ) Gbar) (hu₁b : u₁ ≤ ubar) (hu₁t : u₁ ≤ tb) (hκ : 0 ≤ κ)
    (hCf : 0 ≤ Cf) (hX0 : Lin.MemXFn (n + 1) (c.pert0 χ))
    (hw0n : Sob.normH (n + 1) (c.pert0 χ) ≤ C₀ * κ)
    (hh : ∀ u ∈ Icc (0 : ℝ) u₁, normCk (n + 1) annN' (c.h u) ≤ Cf * κ)
    (hexp : ∀ u ∈ Icc (0 : ℝ) u₁, Real.exp (Eig.sigma χ c.G * u) ≤ Em) :
    ∀ u ∈ Icc (0 : ℝ) u₁, Sob.normH (n + 1) (wlin0 χ (n + 1) c.G (c.pert0 χ) c.h u).fn ≤
      CS * Em * (C₀ + tb * (Eig.Cnab χ (n + 1) * Cf)) * κ := by
  intro u hu
  have hI : ∀ v ∈ Icc (0 : ℝ) u₁, v ∈ Icc (0 : ℝ) ubar := fun v hv => ⟨hv.1, hv.2.trans hu₁b⟩
  have hRF := reduction_field hc
  have hpath := hRF.2 (n + 1)
  have hsym : ∀ v ∈ Icc (0 : ℝ) u₁, IsSymFieldOn annN' (c.h v) := by
    intro v hv
    obtain ⟨U, -, hNU, -, -, -, hsU, -⟩ := hRF.1 v (hI v hv)
    exact fun x hx => hsU x (hNU hx)
  have hσ0 : 0 ≤ Eig.sigma χ c.G := by
    obtain ⟨h1, h2, -⟩ := sigma_facts χ hχ hN hG
    linarith only [h1, h2]
  have hCn := Cnab_nonneg χ (n + 1)
  have hEm : 0 ≤ Em := (Real.exp_pos _).le.trans (hexp u hu)
  rw [(Y_memH_fn (wlin0 χ (n + 1) c.G (c.pert0 χ) c.h u)).2]
  have h := wlin0_norm_le χ hχ hN (by omega : 2 ≤ n + 1) hCS hCS0 hG hσ0 hX0
    (ubar := u₁) (fun v hv => hpath.1 v (hI v hv)) hsym (B := Cf * κ) hh hu (hexp u hu)
  refine h.trans ?_
  have hCfκ : 0 ≤ Eig.Cnab χ (n + 1) * (Cf * κ) := mul_nonneg hCn (mul_nonneg hCf hκ)
  have h1 : Sob.normH (n + 1) (c.pert0 χ) + u * (Eig.Cnab χ (n + 1) * (Cf * κ)) ≤
      C₀ * κ + tb * (Eig.Cnab χ (n + 1) * (Cf * κ)) :=
    add_le_add hw0n (mul_le_mul_of_nonneg_right (hu.2.trans hu₁t) hCfκ)
  calc CS * Em * (Sob.normH (n + 1) (c.pert0 χ) + u * (Eig.Cnab χ (n + 1) * (Cf * κ)))
      ≤ CS * Em * (C₀ * κ + tb * (Eig.Cnab χ (n + 1) * (Cf * κ))) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hCS0 hEm)
    _ = CS * Em * (C₀ + tb * (Eig.Cnab χ (n + 1) * Cf)) * κ := by ring

/-- **The residual on the layer** (`05_single_ring.tex:983-985`): for `w_app ∈ X^{n+1}` with
`‖w_app‖_{H^{n+1}} ≤ W` and `‖h‖_{C^n(N')} ≤ H`, `w_app' = L(G)w_app + F`:
`‖R_app‖_{H^n} ≤ C_B(n)W² + C_h(n)HW`. -/
theorem rapp_on_layer (χ : ℝ → ℝ) {n : ℕ} (hn2 : 2 ≤ n) {c : RingConfig} {ubar u₁ W H : ℝ}
    (hc : c.Hyp ubar) (hu₁b : u₁ ≤ ubar) {wapp : ℝ → ℂ → ℂ}
    (hX : ∀ τ ∈ Icc (0 : ℝ) u₁, Lin.MemXFn (n + 1) (wapp τ))
    (hW : ∀ τ ∈ Icc (0 : ℝ) u₁, Sob.normH (n + 1) (wapp τ) ≤ W)
    (hh : ∀ τ ∈ Icc (0 : ℝ) u₁, normCk n annN' (c.h τ) ≤ H) :
    ∀ τ ∈ Icc (0 : ℝ) u₁, Sob.normH n (Rapp χ c.G c.h wapp
        (fun u x => Lin.Lfn χ c.G (wapp u) x + forcing χ c.h u x) τ) ≤
      CB n * W * W + Ch n * H * W := by
  intro τ hτ
  rw [rapp_linPath χ c.G c.h wapp τ]
  have hmemCk : MemCk n annN' (c.h τ) :=
    ((reduction_field hc).2 n).1 τ ⟨hτ.1, hτ.2.trans hu₁b⟩
  refine (rapp_linPath_bound hn2 (hX τ hτ) hmemCk).trans ?_
  have hCB0 : 0 ≤ CB n := (CB_pos n).le
  have hCh0 : 0 ≤ Ch n := (bilinear_Ch hn2).2
  have h1 : Sob.normH n (wapp τ) ≤ W := (normH_mono_order' (Nat.le_succ n) _).trans (hW τ hτ)
  have h2 := hW τ hτ
  have h3 := hh τ hτ
  have hn0 := Sob.normH_nonneg (n + 1) (wapp τ)
  have hW0 : 0 ≤ W := hn0.trans h2
  have hH0 : 0 ≤ H := (normCk_nonneg _ _ _).trans h3
  have e1 : CB n * Sob.normH n (wapp τ) * Sob.normH (n + 1) (wapp τ) ≤ CB n * W * W :=
    mul_le_mul (mul_le_mul_of_nonneg_left h1 hCB0) h2 hn0 (mul_nonneg hCB0 hW0)
  have e2 : Ch n * normCk n annN' (c.h τ) * Sob.normH (n + 1) (wapp τ) ≤ Ch n * H * W :=
    mul_le_mul (mul_le_mul_of_nonneg_left h3 hCh0) h2 hn0 (mul_nonneg hCh0 hH0)
  exact add_le_add e1 e2

/-- **The continuity argument on the layer** (`05_single_ring.tex:961-976`): if the improvement
step holds on `[0,u₁]` (displacement `≤ a/16` and `‖w‖_{H^n} ≤ 1` on `[0,t]` imply
`‖w‖_{H^n} ≤ 1/2` and displacement `≤ D < a/16`), then on `[0,u₁]` the displacement is `≤ a/16`
and `‖w‖_{H^n} ≤ 1`. -/
theorem layer_bootstrap {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {n : ℕ} {c : RingConfig}
    {ubar u₁ D : ℝ} (hc : c.Hyp ubar) (hu₁b : u₁ ≤ ubar) (hD0 : 0 ≤ D) (hD : D < a / 16)
    (h00 : Sob.normH n (c.w χ 0) ≤ 1)
    (core : ∀ t ∈ Icc (0 : ℝ) u₁, c.MovesRadially t (a / 16) →
      (∀ τ ∈ Icc (0 : ℝ) t, Sob.normH n (c.w χ τ) ≤ 1) →
      (∀ τ ∈ Icc (0 : ℝ) t, Sob.normH n (c.w χ τ) ≤ 1 / 2) ∧ c.MovesRadially t D) :
    ∀ u ∈ Icc (0 : ℝ) u₁, c.MovesRadially u (a / 16) ∧
      ∀ τ ∈ Icc (0 : ℝ) u, Sob.normH n (c.w χ τ) ≤ 1 := by
  have ha16 : 0 ≤ a / 16 := hD0.trans hD.le
  have hboot := Continuity.bootstrap_le (ι := Bool) (a := 0) (b := u₁)
    (F := fun i => if i then dispFn c else fun τ => Sob.normH n (c.w χ τ))
    (G := fun i _ => if i then a / 16 else 1)
    (H := fun i _ => if i then D else 1 / 2)
    (by
      intro i
      cases i
      · exact (continuousOn_normH_w hχ hc n).mono (Icc_subset_Icc le_rfl hu₁b)
      · exact (continuous_dispFn hc).continuousOn)
    (by intro i; cases i <;> exact continuousOn_const)
    (by
      intro i τ _
      cases i
      · simp only [Bool.false_eq_true, ↓reduceIte]; norm_num
      · simp only [↓reduceIte]; exact hD)
    (by
      intro i
      cases i
      · simpa using h00
      · simpa using dispFn_zero_le hc ha16)
    (by
      intro t ht hprev i
      have hm : c.MovesRadially t (a / 16) :=
        movesRadially_of_dispFn_le hc fun τ hτ => by simpa using hprev τ hτ true
      have hw1 : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH n (c.w χ τ) ≤ 1 := fun τ hτ => by
        simpa using hprev τ hτ false
      obtain ⟨hwD, hmD⟩ := core t ht hm hw1
      cases i
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hwD t ⟨ht.1, le_rfl⟩
      · simp only [↓reduceIte]
        exact dispFn_le_of_movesRadially hD0 hmD t ⟨ht.1, le_rfl⟩)
  intro u hu
  refine ⟨?_, ?_⟩
  · apply movesRadially_of_dispFn_le hc
    intro τ hτ
    have := hboot τ ⟨hτ.1, hτ.2.trans hu.2⟩ true
    simp only [↓reduceIte] at this
    exact this.trans hD.le
  · intro τ hτ
    have := hboot τ ⟨hτ.1, hτ.2.trans hu.2⟩ false
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    linarith only [this]

/-- **The triangle inequality of item 2**: if `D.fn = w_app - 2Re(Xφ_*)` a.e. (`lem:linear-part`),
then `‖f - 2Re(Xφ_*)‖_{H^n} ≤ ‖f - w_app‖_{H^n} + ‖D‖_{H^{n+1}}`. -/
theorem normH_sub_modeFn_le {χ : ℝ → ℝ} {n : ℕ} {G : ℝ} {f wa : ℂ → ℂ}
    {D : Sect.Y (n + 1) annN} {X : ℂ} (hf : Sob.MemH n f) (hwa : Sob.MemH n wa)
    (hD : D.fn =ᵐ[volume] (wa - modeFn χ G X)) :
    Sob.normH n (f - modeFn χ G X) ≤ Sob.normH n (f - wa) + ‖D‖ := by
  obtain ⟨hmD, hnD⟩ := Y_memH_fn D
  obtain ⟨hm2, hn2⟩ := hmD.congr_ae hD
  have hsplit : f - modeFn χ G X = (f - wa) + (wa - modeFn χ G X) := by abel
  rw [hsplit]
  have hadd := ((hf.sub hwa).1.add (hm2.mono_order (Nat.le_succ n))).2
  have h2 : Sob.normH n (wa - modeFn χ G X) ≤ ‖D‖ := by
    rw [← hnD, ← hn2]
    exact normH_mono_order' (Nat.le_succ n) _
  linarith only [hadd, h2]

end LayerH

end OneRing

end NonUniqueEuler
