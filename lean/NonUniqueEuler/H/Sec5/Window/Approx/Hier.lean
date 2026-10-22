import NonUniqueEuler.H.Sec5.Window.Approx.Step

/-!
# Helpers for `window_approx`: the hierarchy and its induction

Helper of `P/Sec5/Window/Approx.lean` (`05_single_ring.tex:747-798`, `eq:W-hier`,
`eq:W-res`). Namespace `NonUniqueEuler.OneRing.WAppH`.

* `hier χ G h K w1 P1' n = (w_{n+1}, P_{n+1}, P'_{n+1})`: the increment hierarchy (`Step.lean`),
  starting from the linear response `w1` at level `K` with derivative `P1' = L(G)w1 + F`;
  the increment `w_{n+1}` lives at level `K - n`;
* `hierConst CS σi K C0 n = (C_{n+1}, D_{n+1}, E_{n+1})`: its constants (independent of the data);
* `hier_base`: the induction hypothesis at `n = 0` for `w1 = wlin0` (`lem:duhamel`, the forcing
  `F = -h·∇Φ` is a real path in `X^K`), given the bound `‖w1‖_{H^K} ≤ C0 â₁`;
* `hier_spec`: the induction (`hier_step`);
* `hier_final`: the result at level `s + 1` after `N - 1` steps (`K = s + N`), with the residual
  bound `‖R_app‖_{H^s} ≤ K_res â₁𝔟^N`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.WAppH

open RingData Sect Sob Prelim

/-- The increment hierarchy: `hier n = (w_{n+1}, P_{n+1}, P'_{n+1})`. -/
def hier (χ : ℝ → ℝ) (G : ℝ) (h : ℝ → ℂ → ℂ) (K : ℕ) (w1 P1' : ℝ → ℂ → ℂ) :
    ℕ → (ℝ → ℂ → ℂ) × (ℝ → ℂ → ℂ) × (ℝ → ℂ → ℂ)
  | 0 => (w1, w1, P1')
  | n + 1 =>
    ((duhFn χ (K - n - 1) G 0 (gNext h (hier χ G h K w1 P1' n).1 (hier χ G h K w1 P1' n).2.1)),
      fun u => (hier χ G h K w1 P1' n).2.1 u +
        duhFn χ (K - n - 1) G 0 (gNext h (hier χ G h K w1 P1' n).1 (hier χ G h K w1 P1' n).2.1) u,
      fun u => (hier χ G h K w1 P1' n).2.2 u +
        (Lin.Lfn χ G (duhFn χ (K - n - 1) G 0
            (gNext h (hier χ G h K w1 P1' n).1 (hier χ G h K w1 P1' n).2.1) u) +
          gNext h (hier χ G h K w1 P1' n).1 (hier χ G h K w1 P1' n).2.1 u))

/-- The constants `(C_{n+1}, D_{n+1}, E_{n+1})` of the hierarchy. -/
def hierConst (CS : ℕ → ℝ) (σi : ℝ) (K : ℕ) (C0 : ℝ) : ℕ → ℝ × ℝ × ℝ
  | 0 => (C0, C0, 0)
  | n + 1 =>
    (CS (K - n - 1) * ((hierConst CS σi K C0 n).1 * (CB (K - n - 1) *
        (2 * (hierConst CS σi K C0 n).2.1 + (hierConst CS σi K C0 n).1) + Ch (K - n - 1))) *
          (σi + 1),
      (hierConst CS σi K C0 n).2.1 + CS (K - n - 1) * ((hierConst CS σi K C0 n).1 *
        (CB (K - n - 1) * (2 * (hierConst CS σi K C0 n).2.1 + (hierConst CS σi K C0 n).1) +
          Ch (K - n - 1))) * (σi + 1),
      (hierConst CS σi K C0 n).2.2 + CS (K - n - 1) * ((hierConst CS σi K C0 n).1 *
        (CB (K - n - 1) * (2 * (hierConst CS σi K C0 n).2.1 + (hierConst CS σi K C0 n).1) +
          Ch (K - n - 1))) * (σi + 1))

/-- `wlin₀(0) = w₀` (as the function of `toY w₀`). -/
theorem wlin0_zero_fn (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (K : ℕ) (G : ℝ) (w₀ : ℂ → ℂ)
    (h : ℝ → ℂ → ℂ) : (wlin0 χ K G w₀ h 0).fn = (toY K annN w₀).fn := by
  have hS : Lin.S χ K G 0 = ContinuousLinearMap.id ℂ _ :=
    SectorSetting.semigroup_zero (ringPhiSetting χ) (ringPhiSetting_valid hχ) K G
  rw [wlin0_def, hS, intervalIntegral.integral_same, add_zero, ContinuousLinearMap.id_apply]

/-- **The base of the hierarchy**: the linear response `w1 = wlin₀` (`lem:running`), with
`P'_1 = L(G)w1 + F`. -/
theorem hier_base {χ : ℝ → ℝ} {G ubar κ σ ε σi : ℝ} {p Ktop : ℕ} {h : ℝ → ℂ → ℂ}
    {CS : ℕ → ℝ} (hd : HierData χ G ubar κ σ ε σi p Ktop h CS) {K : ℕ} (hK : 2 ≤ K)
    (hKK : K ≤ Ktop) {w₀ : ℂ → ℂ} (hw₀ : Lin.MemXFn K w₀)
    (hw₀r : ∀ᵐ x ∂(volume : Measure ℂ), (w₀ x).im = 0) {C0 : ℝ}
    (hb : ∀ u ∈ Icc (0 : ℝ) ubar, normH K ((wlin0 χ K G w₀ h u).fn) ≤ C0 * ahat κ σ u) :
    HierInv χ G h ubar κ σ ε p K (fun u => (wlin0 χ K G w₀ h u).fn) 0
      (fun u => (wlin0 χ K G w₀ h u).fn) (fun u => (wlin0 χ K G w₀ h u).fn)
      (fun u => Lin.Lfn χ G ((wlin0 χ K G w₀ h u).fn) + forcing χ h u) C0 C0 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have hF : PathC (k + 1) ubar (forcing χ h) :=
    pathC_forcing χ hd.hχ hd.hN hK (CkPathOn.mono_order hd.hh hKK) hd.hsym
  obtain ⟨hP, hP1, hr, -⟩ := duhFn_spec χ hd.hχ hd.hG hd.hu k (MemXFn.memX_toY hw₀)
    (toY_isReal hw₀ hw₀r) hF (fun t _ => forcing_im_ae χ hd.hχ h t)
  have hw1 : ∀ u, (wlin0 χ (k + 1) G w₀ h u).fn = duhFn χ (k + 1) G (toY (k + 1) annN w₀)
      (forcing χ h) u := fun u => rfl
  simp only [hw1] at hb ⊢
  refine ⟨hP, hP, hP1, hr, hr, EventuallyEq.rfl, fun u hu => ?_, hb, fun u hu => ?_,
    fun u hu => ?_, fun u hu => ?_⟩
  · simpa using hb u hu
  · rw [sub_self]
    exact (memXFn_zero _).1
  · rw [sub_self, normH_zero_fn]
    simp
  · refine Eventually.of_forall fun x => ?_
    simp only [Rapp, ringRHS, gNext, forcing, sub_self, Bfn_zero_left, Pi.add_apply,
      Pi.sub_apply, Pi.neg_apply, Pi.zero_apply]
    ring

/-- **The induction of the hierarchy.** -/
theorem hier_spec {χ : ℝ → ℝ} {G ubar κ σ ε σi : ℝ} {p Ktop : ℕ} {h : ℝ → ℂ → ℂ}
    {CS : ℕ → ℝ} (hd : HierData χ G ubar κ σ ε σi p Ktop h CS) {K : ℕ} (hKK : K ≤ Ktop)
    {w1 P1' : ℝ → ℂ → ℂ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (hbase : HierInv χ G h ubar κ σ ε p K w1 0 w1 w1 P1' C0 C0 0) :
    ∀ n : ℕ, n + 2 ≤ K →
      0 ≤ (hierConst CS σi K C0 n).1 ∧ 0 ≤ (hierConst CS σi K C0 n).2.1 ∧
        0 ≤ (hierConst CS σi K C0 n).2.2 ∧
        HierInv χ G h ubar κ σ ε p (K - n) w1 n (hier χ G h K w1 P1' n).1
          (hier χ G h K w1 P1' n).2.1 (hier χ G h K w1 P1' n).2.2
          (hierConst CS σi K C0 n).1 (hierConst CS σi K C0 n).2.1
          (hierConst CS σi K C0 n).2.2 := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨hC0, hC0, le_rfl, ?_⟩
    simpa [hier, hierConst] using hbase
  | succ n ih =>
    intro hn
    obtain ⟨hc1, hc2, hc3, hI⟩ := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, K - n = k + 2 := ⟨K - n - 2, by omega⟩
    have e1 : K - n - 1 = k + 1 := by omega
    have e2 : K - (n + 1) = k + 1 := by omega
    rw [hk] at hI
    have hs := hier_step hd (k := k) (by omega) (by omega) hc1 hc2 hI
    have hσi : 0 ≤ σi := (inv_pos.2 hd.hσ).le.trans hd.hσi
    have hKn : 0 ≤ (hierConst CS σi K C0 n).1 * (CB (k + 1) *
        (2 * (hierConst CS σi K C0 n).2.1 + (hierConst CS σi K C0 n).1) + Ch (k + 1)) :=
      mul_nonneg hc1 (add_nonneg (mul_nonneg (CB_pos _).le (by linarith))
        (bilinear_Ch (k := k + 1) (by omega)).2)
    have hC' : 0 ≤ CS (k + 1) * ((hierConst CS σi K C0 n).1 * (CB (k + 1) *
        (2 * (hierConst CS σi K C0 n).2.1 + (hierConst CS σi K C0 n).1) + Ch (k + 1))) *
          (σi + 1) :=
      mul_nonneg (mul_nonneg (hd.hCS _) hKn) (by linarith)
    simp only [hier, hierConst]
    rw [e1, e2]
    exact ⟨hC', by linarith, by linarith, hs⟩

/-- The norm of a negated function. -/
theorem normH_neg_fn {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) : normH k (-f) = normH k f := by
  have h := (hf.const_smul (-1)).2
  have e : (-1 : ℂ) • f = -f := by funext x; simp
  rw [e] at h
  rw [h]
  simp

/-- **The hierarchy after `N - 1` steps** (`K = s + N`, level `s + 1`): the induction
hypothesis, and the residual bound `‖R_app‖_{H^s} ≤ K_res â₁𝔟^N`. -/
theorem hier_final {χ : ℝ → ℝ} {G ubar κ σ ε σi : ℝ} {p Ktop : ℕ} {h : ℝ → ℂ → ℂ}
    {CS : ℕ → ℝ} (hd : HierData χ G ubar κ σ ε σi p Ktop h CS) {s N : ℕ} (hs : 2 ≤ s)
    (hN : 1 ≤ N) (hK : s + N ≤ Ktop) {w1 P1' : ℝ → ℂ → ℂ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (hbase : HierInv χ G h ubar κ σ ε p (s + N) w1 0 w1 w1 P1' C0 C0 0) :
    0 ≤ (hierConst CS σi (s + N) C0 (N - 1)).1 ∧ 0 ≤ (hierConst CS σi (s + N) C0 (N - 1)).2.1 ∧
      0 ≤ (hierConst CS σi (s + N) C0 (N - 1)).2.2 ∧
      HierInv χ G h ubar κ σ ε p (s + 1) w1 (N - 1) (hier χ G h (s + N) w1 P1' (N - 1)).1
        (hier χ G h (s + N) w1 P1' (N - 1)).2.1 (hier χ G h (s + N) w1 P1' (N - 1)).2.2
        (hierConst CS σi (s + N) C0 (N - 1)).1 (hierConst CS σi (s + N) C0 (N - 1)).2.1
        (hierConst CS σi (s + N) C0 (N - 1)).2.2 ∧
      ∀ u ∈ Icc (0 : ℝ) ubar,
        normH s (Rapp χ G h (hier χ G h (s + N) w1 P1' (N - 1)).2.1
            (hier χ G h (s + N) w1 P1' (N - 1)).2.2 u) ≤
          (hierConst CS σi (s + N) C0 (N - 1)).1 * (CB s * (2 * (hierConst CS σi (s + N) C0
            (N - 1)).2.1 + (hierConst CS σi (s + N) C0 (N - 1)).1) + Ch s) *
            ahat κ σ u * bW κ σ ε (p + 2) u ^ N := by
  obtain ⟨hc1, hc2, hc3, hI⟩ := hier_spec hd (le_trans (by omega) hK) hC0 hbase (N - 1)
    (by omega)
  have e : s + N - (N - 1) = s + 1 := by omega
  rw [e] at hI
  refine ⟨hc1, hc2, hc3, hI, fun u hu => ?_⟩
  obtain ⟨hw, hP, -, hwr, hPr, -, hwb, hPb, -, -, hres⟩ := hI
  obtain ⟨-, -, hgb⟩ := gNext_spec hd (j := s) hs (by omega) hc1 hc2 hw hP hwr hPr hwb hPb
  set c := hierConst CS σi (s + N) C0 (N - 1) with hcdef
  set t := hier χ G h (s + N) w1 P1' (N - 1) with htdef
  obtain ⟨hgP, -, -⟩ := gNext_spec hd (j := s) hs (by omega) hc1 hc2 hw hP hwr hPr hwb hPb
  have hgm : MemH s (gNext h t.1 t.2.1 u) := (hgP.1 u hu).1
  have hneg : MemH s (-(gNext h t.1 t.2.1 u)) := by
    have h0 := (hgm.const_smul (-1)).1
    have e : (-1 : ℂ) • gNext h t.1 t.2.1 u = -(gNext h t.1 t.2.1 u) := by funext x; simp
    rwa [e] at h0
  have h1 : normH s (Rapp χ G h t.2.1 t.2.2 u) = normH s (gNext h t.1 t.2.1 u) := by
    rw [(hneg.congr_ae (hres u hu).symm).2, normH_neg_fn hgm]
  have h2 := hgb u hu
  have hKr : 0 ≤ c.1 * (CB s * (2 * c.2.1 + c.1) + Ch s) :=
    mul_nonneg hc1 (add_nonneg (mul_nonneg (CB_pos _).le (by linarith)) (bilinear_Ch hs).2)
  have hb0 := bW_nonneg (σ := σ) hd.hκ hd.hε (p + 2) u
  have h3 : (ahat κ σ u + ε * jap u ^ p) * bW κ σ ε (p + 2) u ^ (N - 1) ≤
      bW κ σ ε (p + 2) u ^ N := by
    have e : bW κ σ ε (p + 2) u ^ N = bW κ σ ε (p + 2) u * bW κ σ ε (p + 2) u ^ (N - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [e]
    exact mul_le_mul_of_nonneg_right (field_le_bW hd.hε p u) (pow_nonneg hb0 _)
  have hA : 0 ≤ c.1 * (CB s * (2 * c.2.1 + c.1) + Ch s) * ahat κ σ u :=
    mul_nonneg hKr (ahat_nonneg hd.hκ u)
  have h4 := mul_le_mul_of_nonneg_left h3 hA
  rw [h1]
  calc normH s (gNext h t.1 t.2.1 u) ≤ c.1 * (CB s * (2 * c.2.1 + c.1) + Ch s) * ahat κ σ u *
        (ahat κ σ u + ε * jap u ^ p) * bW κ σ ε (p + 2) u ^ (N - 1) := h2
    _ = c.1 * (CB s * (2 * c.2.1 + c.1) + Ch s) * ahat κ σ u *
        ((ahat κ σ u + ε * jap u ^ p) * bW κ σ ε (p + 2) u ^ (N - 1)) := by ring
    _ ≤ _ := h4

end NonUniqueEuler.OneRing.WAppH
