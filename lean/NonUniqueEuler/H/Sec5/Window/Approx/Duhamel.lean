import NonUniqueEuler.H.Sec5.Window.Approx.Ops
import NonUniqueEuler.I.Sec4.Duhamel
import NonUniqueEuler.I.Sec4.SemigroupLaw

/-!
# Helpers for `window_approx`: `lem:duhamel` for plane functions

Helper of `P/Sec5/Window/Approx.lean` (`05_single_ring.tex:747-786`: "Lemmas `lem:duhamel` and
`lem:bilinear` give `w^{[j]} ∈ C([0,ū];X^{k_j}) ∩ C¹([0,ū];X^{k_j-1})`, real"). Namespace
`NonUniqueEuler.OneRing.WAppH`.

* `duhFn χ k G f₀ g t`: the function of the Duhamel integral
  `e^{tL}f₀ + ∫₀ᵗ e^{(t-τ)L} g(τ) dτ` in `Y^k(N)`, for a plane-function forcing `g`;
* `duhFn_spec`: for `f₀ ∈ X^{k+1}` real and `g ∈ C([0,T];X^{k+1})` real, `duhFn` lies in
  `C([0,T];X^{k+1}) ∩ C¹([0,T];X^k)` with time derivative `L(G)u + g` (on functions), is real,
  and starts at `f₀` (`Lin.duhamel_spec`, `semigroup_zero`, and the bridges of `Ops.lean`);
* `norm_duhamel_zero_le`: `‖∫₀ᵗ e^{(t-τ)L}g(τ)dτ‖ ≤ ∫₀ᵗ C e^{σ(t-τ)} b(τ) dτ` when
  `‖e^{τL}‖_{X^k} ≤ Ce^{στ}` and `‖g‖ ≤ b`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.WAppH

open RingData Sect Sob

/-- The function of the Duhamel integral `e^{tL}f₀ + ∫₀ᵗ e^{(t-τ)L} g(τ) dτ` in `Y^k(N)`, for a
plane-function forcing `g` (entering through `Sect.toY k annN`). -/
def duhFn (χ : ℝ → ℝ) (k : ℕ) (G : ℝ) (f₀ : Y k annN) (g : ℝ → ℂ → ℂ) (t : ℝ) : ℂ → ℂ :=
  (Lin.duhamel χ k G f₀ (fun v => toY k annN (g v)) t).fn

/-- **`lem:duhamel` for plane functions.** -/
theorem duhFn_spec (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar)
    {T : ℝ} (hT : 0 < T) (k : ℕ) {f₀ : Y (k + 1) annN} (hf₀ : Lin.MemX f₀)
    (hf₀r : f₀.IsReal) {g : ℝ → ℂ → ℂ} (hg : PathC (k + 1) T g)
    (hgr : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure ℂ), (g t x).im = 0) :
    PathC (k + 1) T (duhFn χ (k + 1) G f₀ g) ∧
      PathC1 k T (duhFn χ (k + 1) G f₀ g)
        (fun t => Lin.Lfn χ G (duhFn χ (k + 1) G f₀ g t) + g t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure ℂ), (duhFn χ (k + 1) G f₀ g t x).im = 0) ∧
      duhFn χ (k + 1) G f₀ g 0 = f₀.fn := by
  set gY : ℝ → Y (k + 1) annN := fun v => toY (k + 1) annN (g v) with hgYdef
  set D : ℝ → Y (k + 1) annN := Lin.duhamel χ (k + 1) G f₀ gY with hDdef
  have hgY : ContinuousOn gY (Icc 0 T) := hg.2
  have hgX : ∀ t ∈ Icc (0 : ℝ) T, Lin.MemX (gY t) := fun t ht => MemXFn.memX_toY (hg.1 t ht)
  obtain ⟨hc, hX, hder, -, hreal⟩ := Lin.duhamel_spec χ hχ hG hT k hf₀ hgY hgX
  have hu : ∀ t, duhFn χ (k + 1) G f₀ g t = (D t).fn := fun t => rfl
  have hPC : PathC (k + 1) T (duhFn χ (k + 1) G f₀ g) := by
    refine ⟨fun t ht => memXFn_of_memX (hX t ht), ?_⟩
    refine hc.congr fun t _ => ?_
    exact toY_fn_self (D t)
  refine ⟨hPC, ?_, ?_, ?_⟩
  · have hP' : PathC k T (fun t => Lin.Lfn χ G (duhFn χ (k + 1) G f₀ g t) + g t) :=
      PathC.add (pathC_Lfn χ hχ G hPC) (PathC.mono_level hg (Nat.le_succ k))
    refine ⟨PathC.mono_level hPC (Nat.le_succ k), hP', fun t ht => ?_⟩
    have hd := hder t ht
    have hut := hPC.1 t ht
    have hgt := hg.1 t ht
    have hderiv : toY k annN (Lin.Lfn χ G (duhFn χ (k + 1) G f₀ g t) + g t) =
        Lin.L χ k G (D t) + lowerY k (k + 1) annN (gY t) := by
      rw [toY_add' (memXFn_Lfn χ hχ G hut) (MemXFn.mono hgt (Nat.le_succ k)),
        toY_Lfn χ hχ G hut, hu t, toY_fn_self, hgYdef, lowerY_toY (Nat.le_succ k) hgt]
    rw [hderiv]
    refine hd.congr_of_mem (fun t' _ => ?_) ht
    rw [hu t']
    exact toY_fn_lower (Nat.le_succ k) (D t')
  · intro t ht
    exact hreal hf₀r (fun t ht => toY_isReal (hg.1 t ht) (hgr t ht)) t ht
  · have h0 : D 0 = f₀ := by
      rw [hDdef, Lin.duhamel]
      have hS : Lin.S χ (k + 1) G 0 = ContinuousLinearMap.id ℂ _ :=
        SectorSetting.semigroup_zero (ringPhiSetting χ) (ringPhiSetting_valid hχ) (k + 1) G
      rw [hS, intervalIntegral.integral_same, add_zero, ContinuousLinearMap.id_apply]
    rw [hu 0, h0]

/-- **The norm of a Duhamel integral with zero datum.** -/
theorem norm_duhamel_zero_le (χ : ℝ → ℝ) {k : ℕ} {G : ℝ} {g : ℝ → Y k annN} {C σ t : ℝ}
    {b : ℝ → ℝ} (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hS : ∀ τ : ℝ, 0 ≤ τ → ∀ w : Y k annN, Lin.MemX w →
      ‖Lin.S χ k G τ w‖ ≤ C * Real.exp (σ * τ) * ‖w‖)
    (hgX : ∀ v ∈ Icc (0 : ℝ) t, Lin.MemX (g v)) (hb : ∀ v ∈ Icc (0 : ℝ) t, ‖g v‖ ≤ b v)
    (hbi : IntervalIntegrable (fun v => C * Real.exp (σ * (t - v)) * b v) volume 0 t) :
    ‖Lin.duhamel χ k G 0 g t‖ ≤ ∫ v in (0 : ℝ)..t, C * Real.exp (σ * (t - v)) * b v := by
  rw [Lin.duhamel, map_zero, zero_add]
  refine intervalIntegral.norm_integral_le_of_norm_le ht
    (Eventually.of_forall fun v hv => ?_) hbi
  have hv' : v ∈ Icc (0 : ℝ) t := ⟨hv.1.le, hv.2⟩
  calc ‖Lin.S χ k G (t - v) (g v)‖ ≤ C * Real.exp (σ * (t - v)) * ‖g v‖ :=
        hS (t - v) (by linarith [hv.2]) (g v) (hgX v hv')
    _ ≤ C * Real.exp (σ * (t - v)) * b v :=
        mul_le_mul_of_nonneg_left (hb v hv') (mul_nonneg hC (Real.exp_pos _).le)

end NonUniqueEuler.OneRing.WAppH
