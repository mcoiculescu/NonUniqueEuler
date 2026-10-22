import NonUniqueEuler.H.Sec5.Quiet.Approx.Calculus
import NonUniqueEuler.I.Sec4.Duhamel
import NonUniqueEuler.I.Sec4.SemigroupLaw
import NonUniqueEuler.I.Sec4.RingFacts

/-!
# Helpers for `quiet_approx`: `lem:duhamel` on plane functions

Helper of `P/Sec5/Quiet/Approx.lean` (fully proved). Namespace `NonUniqueEuler.OneRing.QAppH`.

* `duhFn χ k G g t`: the function of `∫₀ᵗ e^{(t-τ)L(G)} g(τ) dτ ∈ Y^k(N)` (`g(τ)` enters through
  `Sect.toY k N`);
* `duhFn_spec` (`lem:duhamel`, `05_single_ring.tex:52-57`): for `g ∈ C([0,T];X^{k+1})`,
  `duhFn ∈ C([0,T];X^{k+1}) ∩ C¹([0,T];X^k)` with `∂_t duhFn = L(G) duhFn + g` (with `L(G)` on
  functions, `Lin.Lfn`), `duhFn(0) = 0`, real for real `g`;
* `duhFn_bound`: `‖duhFn(t)‖_{H^k} ≤ C ∫₀ᵗ e^{σ(t-τ)} ‖g(τ)‖_{H^k} dτ` whenever
  `‖e^{tL}‖_{X^k → X^k} ≤ C e^{σt}` (`prop:semigroup`);
* `duhFn_level`: the Duhamel integrals at two levels `s ≤ s'` have the same function
  (`semigroup_lowerY`); `wlin_fn`: the linear response `wlin` is `duhFn` of the forcing.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.QAppH

open Sect Sob RingData

/-- The function of the Duhamel integral `∫₀ᵗ e^{(t-τ)L(G)} g(τ) dτ` in `Y^k(N)`. -/
def duhFn (χ : ℝ → ℝ) (k : ℕ) (G : ℝ) (g : ℝ → ℂ → ℂ) (t : ℝ) : ℂ → ℂ :=
  (Lin.duhamel χ k G 0 (fun τ => toY k annN (g τ)) t).fn

theorem Y_fn_zero (s : ℕ) (K : Set ℂ) : (0 : Y s K).fn =ᵐ[volume] (0 : ℂ → ℂ) := by
  show ((((0 : Y s K) : SobTuple s).ofLp (idx0 s) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
    =ᵐ[volume] 0
  simpa using (Lp.coeFn_zero ℂ 2 (volume : Measure ℂ))

theorem memX_zero (s : ℕ) : Lin.MemX (0 : Y s annN) := (Lin.Xsub s).zero_mem

/-- A derivative within `[0,T]` (`T > 0`) of a path with values in `X^s` lies in `X^s`. -/
theorem memX_of_hasDerivWithinAt {s : ℕ} {T t : ℝ} (hT : 0 < T) (ht : t ∈ Icc 0 T)
    {p : ℝ → Y s annN} {p' : Y s annN} (hp : ∀ τ ∈ Icc (0 : ℝ) T, Lin.MemX (p τ))
    (hd : HasDerivWithinAt p p' (Icc 0 T) t) : Lin.MemX p' := by
  obtain ⟨L, hL⟩ := exists_memX_iff s
  rw [hL]
  have h1 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt (f := p) t hd
  simp only [ContinuousLinearMap.coe_restrictScalars'] at h1
  have h2 : HasDerivWithinAt (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure ℂ))) (L p')
      (Icc 0 T) t :=
    h1.congr_of_mem (fun τ hτ => ((hL _).1 (hp τ hτ)).symm) ht
  have h3 : HasDerivWithinAt (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure ℂ))) 0 (Icc 0 T) t :=
    hasDerivWithinAt_const _ _ _
  exact (uniqueDiffOn_Icc hT t ht).eq_deriv _ h2 h3

/-- **`lem:duhamel` on plane functions** (`05_single_ring.tex:52-57`). -/
theorem duhFn_spec (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) {T : ℝ} (hT : 0 < T) (k : ℕ) {g : ℝ → ℂ → ℂ}
    (hg : PathC (k + 1) T g) :
    PathC (k + 1) T (duhFn χ (k + 1) G g) ∧
      PathC1 k T (duhFn χ (k + 1) G g) (fun t => Lin.Lfn χ G (duhFn χ (k + 1) G g t) + g t) ∧
      duhFn χ (k + 1) G g 0 =ᵐ[volume] 0 ∧
      ((∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure ℂ), (g t x).im = 0) →
        ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure ℂ), (duhFn χ (k + 1) G g t x).im = 0) := by
  have hxc : ContinuousOn (fun τ => toY (k + 1) annN (g τ)) (Icc 0 T) := hg.2
  have hxX : ∀ t ∈ Icc (0 : ℝ) T, Lin.MemX (toY (k + 1) annN (g t)) := fun t ht =>
    MemXFn.memX_toY (hg.1 t ht)
  obtain ⟨hc, hX, hd, hc', hR⟩ := Lin.duhamel_spec χ hχ hG hT k (memX_zero (k + 1)) hxc hxX
  -- notation
  have hDX : ∀ t ∈ Icc (0 : ℝ) T, Lin.MemXFn (k + 1) (duhFn χ (k + 1) G g t) := fun t ht =>
    memXFn_of_memX (hX t ht)
  have hPC : PathC (k + 1) T (duhFn χ (k + 1) G g) := by
    refine ⟨hDX, hc.congr fun t _ => ?_⟩
    exact toY_fn_self _
  have hlow : ∀ t ∈ Icc (0 : ℝ) T,
      lowerY k (k + 1) annN (Lin.duhamel χ (k + 1) G 0 (fun τ => toY (k + 1) annN (g τ)) t) =
        toY k annN (duhFn χ (k + 1) G g t) := fun t ht => by
    rw [← lowerY_toY (Nat.le_succ k) (hDX t ht), duhFn, toY_fn_self]
  have hVX : ∀ t ∈ Icc (0 : ℝ) T,
      Lin.MemX (Lin.L χ k G (Lin.duhamel χ (k + 1) G 0 (fun τ => toY (k + 1) annN (g τ)) t) +
        lowerY k (k + 1) annN (toY (k + 1) annN (g t))) := fun t ht =>
    memX_of_hasDerivWithinAt hT ht (fun τ hτ => by
      rw [hlow τ hτ]
      exact MemXFn.memX_toY (MemXFn.mono (hDX τ hτ) (Nat.le_succ k))) (hd t ht)
  have hVfn : ∀ t ∈ Icc (0 : ℝ) T,
      (Lin.L χ k G (Lin.duhamel χ (k + 1) G 0 (fun τ => toY (k + 1) annN (g τ)) t) +
        lowerY k (k + 1) annN (toY (k + 1) annN (g t))).fn =ᵐ[volume]
        (Lin.Lfn χ G (duhFn χ (k + 1) G g t) + g t) := by
    intro t ht
    have h1 := Y_fn_add
      (Lin.L χ k G (Lin.duhamel χ (k + 1) G 0 (fun τ => toY (k + 1) annN (g τ)) t))
      (lowerY k (k + 1) annN (toY (k + 1) annN (g t)))
    have h2 := L_fn_ae χ hχ k G
      (Lin.duhamel χ (k + 1) G 0 (fun τ => toY (k + 1) annN (g τ)) t)
    have h3 : (lowerY k (k + 1) annN (toY (k + 1) annN (g t))).fn =ᵐ[volume] g t :=
      ((lowerY_spec (Nat.le_succ k) annN).1 _).trans (MemXFn.toY_fn (hg.1 t ht))
    filter_upwards [h1, h2, h3] with y e1 e2 e3
    rw [e1, e2, e3]
    rfl
  have hu'X : ∀ t ∈ Icc (0 : ℝ) T, Lin.MemXFn k (Lin.Lfn χ G (duhFn χ (k + 1) G g t) + g t) :=
    fun t ht => MemXFn.congr_ae (memXFn_of_memX (hVX t ht)) (hVfn t ht)
  have hu'Y : ∀ t ∈ Icc (0 : ℝ) T, toY k annN (Lin.Lfn χ G (duhFn χ (k + 1) G g t) + g t) =
      Lin.L χ k G (Lin.duhamel χ (k + 1) G 0 (fun τ => toY (k + 1) annN (g τ)) t) +
        lowerY k (k + 1) annN (toY (k + 1) annN (g t)) := fun t ht => by
    rw [← toY_congr_ae (hVfn t ht), toY_fn_self]
  refine ⟨hPC, ⟨PathC.mono_level hPC (Nat.le_succ k),
    ⟨hu'X, hc'.congr fun t ht => hu'Y t ht⟩, fun t ht => ?_⟩, ?_, ?_⟩
  · rw [hu'Y t ht]
    exact (hd t ht).congr_of_mem (fun τ hτ => (hlow τ hτ).symm) ht
  · have h0 : Lin.duhamel χ (k + 1) G 0 (fun τ => toY (k + 1) annN (g τ)) 0 = 0 := by
      simp [Lin.duhamel]
    show (Lin.duhamel χ (k + 1) G 0 (fun τ => toY (k + 1) annN (g τ)) 0).fn =ᵐ[volume] 0
    rw [h0]
    exact Y_fn_zero _ _
  · intro hgR t ht
    have h0R : (0 : Y (k + 1) annN).IsReal := by
      filter_upwards [Y_fn_zero (k + 1) annN] with y hy
      rw [hy]
      simp
    refine hR h0R (fun τ hτ => ?_) t ht
    filter_upwards [MemXFn.toY_fn (hg.1 τ hτ), hgR τ hτ] with y h1 h2
    rw [h1, h2]

/-- **The Duhamel bound** from `‖e^{tL}‖_{X^k → X^k} ≤ C e^{σt}`. -/
theorem duhFn_bound (χ : ℝ → ℝ) {k : ℕ} {G T : ℝ} {g : ℝ → ℂ → ℂ} (hg : PathC k T g)
    {C σ : ℝ} (hC : ∀ t : ℝ, 0 ≤ t → ∀ w : Y k annN, Lin.MemX w →
      ‖Lin.S χ k G t w‖ ≤ C * Real.exp (σ * t) * ‖w‖)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    normH k (duhFn χ k G g t) ≤
      C * ∫ τ in (0 : ℝ)..t, Real.exp (σ * (t - τ)) * normH k (g τ) := by
  rw [duhFn, (Y_memH_fn _).2]
  simp only [Lin.duhamel, map_zero, zero_add]
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hcont : ContinuousOn (fun τ => C * (Real.exp (σ * (t - τ)) * normH k (g τ))) (Icc 0 t) :=
    continuousOn_const.mul ((Continuous.continuousOn (by fun_prop)).mul
      ((PathC.continuousOn_normH hg).mono hsub))
  have hint := hcont.intervalIntegrable_of_Icc (μ := volume) ht.1
  have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun τ => Lin.S χ k G (t - τ) (toY k annN (g τ))) ht.1
    (Eventually.of_forall fun τ hτ => ?_) hint
  · rw [intervalIntegral.integral_const_mul] at h1
    exact h1
  · have hτT : τ ∈ Icc (0 : ℝ) T := hsub (Ioc_subset_Icc_self hτ)
    have h2 := hC (t - τ) (by linarith [hτ.2]) _ (MemXFn.memX_toY (hg.1 τ hτT))
    rw [MemXFn.norm_toY (hg.1 τ hτT)] at h2
    simpa [mul_assoc] using h2

/-- `v ↦ e^{(u-v)L(G)} g(v)` is continuous on `[0,u]` for `g` continuous on `[0,u]` (copied from
the proved helper `H/Sec5/Running/Integrand.lean`). -/
theorem continuousOn_S_comp (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (s : ℕ) (G : ℝ) {u : ℝ}
    {g : ℝ → Y s annN} (hg : ContinuousOn g (Icc 0 u)) :
    ContinuousOn (fun v => Lin.S χ s G (u - v) (g v)) (Icc 0 u) := by
  obtain ⟨B, hB⟩ :=
    (ringPhiSetting χ).semigroup_bound (ringPhiSetting_valid hχ) s (abs_nonneg G) u
  intro v₀ hv₀
  have hmaps : MapsTo (fun v => u - v) (Icc 0 u) (Icc 0 u) := fun v hv =>
    ⟨by linarith [hv.2], by linarith [hv.1]⟩
  have h2 : ContinuousWithinAt (fun v => Lin.S χ s G (u - v) (g v₀)) (Icc 0 u) v₀ := by
    have hc := (ringPhiSetting χ).semigroup_continuousOn (ringPhiSetting_valid hχ) s G (g v₀)
    have h3 : ContinuousWithinAt (fun t => Lin.S χ s G t (g v₀)) (Icc 0 u) (u - v₀) :=
      (hc (u - v₀) (show (0 : ℝ) ≤ u - v₀ by linarith [hv₀.2])).mono Icc_subset_Ici_self
    exact h3.comp (continuousWithinAt_const.sub continuousWithinAt_id) hmaps
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero] at h2 ⊢
  have h1 : Tendsto (fun v => ‖g v - g v₀‖) (𝓝[Icc 0 u] v₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hg v₀ hv₀)
  have hlim : Tendsto (fun v => B * ‖g v - g v₀‖ +
      ‖Lin.S χ s G (u - v) (g v₀) - Lin.S χ s G (u - v₀) (g v₀)‖) (𝓝[Icc 0 u] v₀) (𝓝 0) := by
    simpa using (h1.const_mul B).add h2
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall fun v hv => ?_) hlim
  have hsplit : Lin.S χ s G (u - v) (g v) - Lin.S χ s G (u - v₀) (g v₀) =
      Lin.S χ s G (u - v) (g v - g v₀) +
        (Lin.S χ s G (u - v) (g v₀) - Lin.S χ s G (u - v₀) (g v₀)) := by
    rw [map_sub]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  have hop : ‖Lin.S χ s G (u - v)‖ ≤ B := hB G le_rfl (u - v) (hmaps hv)
  calc ‖Lin.S χ s G (u - v) (g v - g v₀)‖ ≤ ‖Lin.S χ s G (u - v)‖ * ‖g v - g v₀‖ :=
        (Lin.S χ s G (u - v)).le_opNorm _
    _ ≤ B * ‖g v - g v₀‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)

/-- **Compatibility of the levels**: for `g ∈ C([0,T];X^{s'})` and `s ≤ s'`, the Duhamel
integrals in `Y^{s'}(N)` and in `Y^s(N)` have the same function. -/
theorem duhFn_level (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {s s' : ℕ} (hss : s ≤ s') (G : ℝ)
    {T : ℝ} {g : ℝ → ℂ → ℂ} (hg : PathC s' T g) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    duhFn χ s' G g t =ᵐ[volume] duhFn χ s G g t := by
  have key : lowerY s s' annN (Lin.duhamel χ s' G 0 (fun τ => toY s' annN (g τ)) t) =
      Lin.duhamel χ s G 0 (fun τ => toY s annN (g τ)) t := by
    simp only [Lin.duhamel, map_zero, zero_add]
    have hint := ((continuousOn_S_comp χ hχ s' G (u := t)
      (g := fun τ => toY s' annN (g τ)) (hg.2.mono (Icc_subset_Icc le_rfl ht.2)))).intervalIntegrable_of_Icc (μ := volume) ht.1
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le ht.1] at hτ
    have hS : lowerY s s' annN (Lin.S χ s' G (t - τ) (toY s' annN (g τ))) =
        Lin.S χ s G (t - τ) (lowerY s s' annN (toY s' annN (g τ))) :=
      (ringPhiSetting χ).semigroup_lowerY (ringPhiSetting_valid hχ) hss G
        (by linarith [hτ.2]) _
    rw [hS, lowerY_toY hss (hg.1 τ ⟨hτ.1, hτ.2.trans ht.2⟩)]
  have h := (lowerY_spec hss annN).1 (Lin.duhamel χ s' G 0 (fun τ => toY s' annN (g τ)) t)
  rw [key] at h
  exact h.symm

/-- The linear response `wlin` is the Duhamel integral of the forcing. -/
theorem wlin_fn (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) (h : ℝ → ℂ → ℂ) (t : ℝ) :
    (wlin χ s G h t).fn = duhFn χ s G (forcing χ h) t := by
  rw [wlin, wlin0, toY_zero]
  rfl

end NonUniqueEuler.OneRing.QAppH
