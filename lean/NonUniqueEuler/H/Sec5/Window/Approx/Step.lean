import NonUniqueEuler.H.Sec5.Window.Approx.Duhamel
import NonUniqueEuler.H.Sec5.Window.Approx.Scalar

/-!
# Helpers for `window_approx`: one step of the hierarchy

Helper of `P/Sec5/Window/Approx.lean` (`05_single_ring.tex:747-786`). Namespace
`NonUniqueEuler.OneRing.WAppH`.

The manuscript's hierarchy `w^{[j]} = ∫₀ᵘ e^{(u-v)L} g^{[j]}`,
`g^{[j]} = Σ_{i+l=j} B(w^{[i]},w^{[l]}) - h·∇w^{[j-1]}`, is replaced by the Picard iteration in
*increment* form (a different construction with the same estimates; a recorded deviation), which
is a simple recursion on the pair `(w_n, P_n)`, `P_n = Σ_{m ≤ n} w_m`:
`w_{n+1} = ∫₀ᵘ e^{(u-v)L} g_{n+1}`, `g_{n+1} = B(w_n,P_n) + B(P_n - w_n, w_n) - h·∇w_n`
(`gNext`). Since `B(P_n,P_n) - B(P_{n-1},P_{n-1}) = B(w_n,P_n) + B(P_{n-1},w_n)`, the sum of the
equations telescopes and the residual of `P_n` is exactly `-g_{n+1}` (a.e.).

* `HierData`: the standing hypotheses (field path, its bound `‖h‖ ≤ â₁ + ε⟨u⟩^p`, `𝔟 ≤ 1`, the
  semigroup bounds `‖e^{τL}‖_{X^k} ≤ C_S(k)e^{στ}`);
* `HierInv ℓ n w P P' C D E`: the induction hypothesis at level `ℓ` (`w, P ∈ C([0,ū];X^ℓ)`,
  `P ∈ C¹([0,ū];X^{ℓ-1})` with derivative `P'`, real, `P(0) = w₁(0)`,
  `‖w‖_{H^ℓ} ≤ C â₁𝔟^n`, `‖P‖_{H^ℓ} ≤ D â₁`, `‖P - w₁‖_{H^ℓ} ≤ E â₁𝔟`, `R_app(P) = -g_{n+1}`);
* `gNext_spec`: `g_{n+1} ∈ C([0,ū];X^j)`, real, `‖g_{n+1}‖_{H^j} ≤ K_n â₁(â₁ + ε⟨v⟩^p)𝔟^n`
  (`lem:bilinear`(1),(2));
* `hier_step`: `HierInv (k+2) n → HierInv (k+1) (n+1)` for the next increment.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.WAppH

open RingData Sect Sob Prelim

/-- The forcing of the next increment: `g = B(w,P) + B(P - w, w) - h·∇w`. -/
def gNext (h w P : ℝ → ℂ → ℂ) (u : ℝ) : ℂ → ℂ :=
  Bfn (w u) (P u) + Bfn (P u - w u) (w u) - hGrad (h u) (w u)

/-- The standing hypotheses of the hierarchy. `σ` is `σ(G)`, `σi ≥ σ⁻¹`, `â₁ = ahat κ σ`,
`𝔟 = bW κ σ ε (p+2)`. -/
structure HierData (χ : ℝ → ℝ) (G ubar κ σ ε σi : ℝ) (p Ktop : ℕ) (h : ℝ → ℂ → ℂ)
    (CS : ℕ → ℝ) : Prop where
  hχ : IsAdmissibleCutoff χ
  hN : NumericalHypothesis χ
  hG : G ∈ Icc (0 : ℝ) Gbar
  hu : 0 < ubar
  hκ : 0 ≤ κ
  hσ : 0 < σ
  hσi : σ⁻¹ ≤ σi
  hε : 0 ≤ ε
  hh : CkPathOn Ktop annN' (Icc 0 ubar) h
  hsym : ∀ u ∈ Icc (0 : ℝ) ubar, IsSymFieldOn annN' (h u)
  hfield : ∀ u ∈ Icc (0 : ℝ) ubar, normCk Ktop annN' (h u) ≤ ahat κ σ u + ε * jap u ^ p
  hb : ∀ u ∈ Icc (0 : ℝ) ubar, bW κ σ ε (p + 2) u ≤ 1
  hCS : ∀ k, 0 ≤ CS k
  hS : ∀ (k : ℕ) (τ : ℝ), 0 ≤ τ → ∀ w : Y k annN, Lin.MemX w →
    ‖Lin.S χ k G τ w‖ ≤ CS k * Real.exp (σ * τ) * ‖w‖

/-- The induction hypothesis of the hierarchy at level `ℓ` and step `n`. -/
def HierInv (χ : ℝ → ℝ) (G : ℝ) (h : ℝ → ℂ → ℂ) (ubar κ σ ε : ℝ) (p ℓ : ℕ)
    (w1 : ℝ → ℂ → ℂ) (n : ℕ) (w P P' : ℝ → ℂ → ℂ) (C D E : ℝ) : Prop :=
  PathC ℓ ubar w ∧ PathC ℓ ubar P ∧ PathC1 (ℓ - 1) ubar P P' ∧
    (∀ u ∈ Icc (0 : ℝ) ubar, ∀ᵐ x ∂(volume : Measure ℂ), (w u x).im = 0) ∧
    (∀ u ∈ Icc (0 : ℝ) ubar, ∀ᵐ x ∂(volume : Measure ℂ), (P u x).im = 0) ∧
    P 0 =ᵐ[volume] w1 0 ∧
    (∀ u ∈ Icc (0 : ℝ) ubar, normH ℓ (w u) ≤ C * ahat κ σ u * bW κ σ ε (p + 2) u ^ n) ∧
    (∀ u ∈ Icc (0 : ℝ) ubar, normH ℓ (P u) ≤ D * ahat κ σ u) ∧
    (∀ u ∈ Icc (0 : ℝ) ubar, MemH ℓ (P u - w1 u)) ∧
    (∀ u ∈ Icc (0 : ℝ) ubar, normH ℓ (P u - w1 u) ≤ E * ahat κ σ u * bW κ σ ε (p + 2) u) ∧
    (∀ u ∈ Icc (0 : ℝ) ubar, Rapp χ G h P P' u =ᵐ[volume] -(gNext h w P u))

theorem normH_zero_fn (k : ℕ) : normH k (0 : ℂ → ℂ) = 0 := by
  have h := MemXFn.norm_toY (memXFn_zero k)
  rw [toY_zero, norm_zero] at h
  exact h.symm

theorem memX_zero (k : ℕ) : Lin.MemX (0 : Y k annN) := by
  show ((0 : Y k annN) : SobTuple k) ∈ Lin.Xsub k
  rw [ZeroMemClass.coe_zero]
  exact Submodule.zero_mem _

/-- The arithmetic of the bound of `g_{n+1}`. -/
theorem gNext_arith {CB Ch C D X Y Z nwk nwk1 nPk1 nd nh t1 t2 t3 : ℝ}
    (hCB : 0 ≤ CB) (hCh : 0 ≤ Ch) (hC : 0 ≤ C) (hD : 0 ≤ D) (hX : 0 ≤ X) (hXY : X ≤ Y)
    (hZ : 0 ≤ Z) (hZ1 : Z ≤ 1)
    (hwk : nwk ≤ nwk1) (hw : nwk1 ≤ C * X * Z) (hP : nPk1 ≤ D * X) (hd : nd ≤ D * X + C * X * Z)
    (hh : nh ≤ Y) (hnh : 0 ≤ nh) (hnwk : 0 ≤ nwk) (hnP : 0 ≤ nPk1)
    (ht1 : t1 ≤ CB * nwk * nPk1) (ht2 : t2 ≤ CB * nd * nwk1) (ht3 : t3 ≤ Ch * nh * nwk1) :
    t1 + t2 + t3 ≤ C * (CB * (2 * D + C) + Ch) * X * Y * Z := by
  have hnwk1 : 0 ≤ nwk1 := hnwk.trans hwk
  have hCXZ : 0 ≤ C * X * Z := hnwk1.trans hw
  have e1 : CB * nwk * nPk1 ≤ CB * (C * X * Z) * (D * X) := by
    have := mul_le_mul (hwk.trans hw) hP hnP hCXZ
    calc CB * nwk * nPk1 = CB * (nwk * nPk1) := by ring
      _ ≤ CB * ((C * X * Z) * (D * X)) := mul_le_mul_of_nonneg_left this hCB
      _ = _ := by ring
  have hCXZ' : C * X * Z ≤ C * X := by
    have : 0 ≤ C * X := mul_nonneg hC hX
    nlinarith
  have hdX : D * X + C * X * Z ≤ (D + C) * X := by nlinarith
  have e2 : CB * nd * nwk1 ≤ CB * ((D + C) * X) * (C * X * Z) := by
    have := mul_le_mul (hd.trans hdX) hw hnwk1 (by positivity)
    calc CB * nd * nwk1 = CB * (nd * nwk1) := by ring
      _ ≤ CB * (((D + C) * X) * (C * X * Z)) := mul_le_mul_of_nonneg_left this hCB
      _ = _ := by ring
  have e3 : Ch * nh * nwk1 ≤ Ch * Y * (C * X * Z) := by
    have := mul_le_mul hh hw hnwk1 (hnh.trans hh)
    calc Ch * nh * nwk1 = Ch * (nh * nwk1) := by ring
      _ ≤ Ch * (Y * (C * X * Z)) := mul_le_mul_of_nonneg_left this hCh
      _ = _ := by ring
  have hXXY : X * X ≤ X * Y := mul_le_mul_of_nonneg_left hXY hX
  have hk : 0 ≤ CB * C * (2 * D + C) * Z := by positivity
  have h4 := mul_le_mul_of_nonneg_left hXXY hk
  have hfin : CB * (C * X * Z) * (D * X) + CB * ((D + C) * X) * (C * X * Z) +
      Ch * Y * (C * X * Z) ≤ C * (CB * (2 * D + C) + Ch) * X * Y * Z := by
    have eq1 : CB * (C * X * Z) * (D * X) + CB * ((D + C) * X) * (C * X * Z) =
        CB * C * (2 * D + C) * Z * (X * X) := by ring
    have eq2 : C * (CB * (2 * D + C) + Ch) * X * Y * Z =
        CB * C * (2 * D + C) * Z * (X * Y) + Ch * Y * (C * X * Z) := by ring
    rw [eq1, eq2]
    linarith
  linarith

theorem Y_fn_zero (s : ℕ) (K : Set ℂ) : (0 : Y s K).fn =ᵐ[volume] (0 : ℂ → ℂ) := by
  show ((((0 : Y s K) : SobTuple s).ofLp (idx0 s) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
    =ᵐ[volume] 0
  simpa using (Lp.coeFn_zero ℂ 2 (volume : Measure ℂ))

/-- **The next forcing** `g_{n+1} = B(w,P) + B(P-w,w) - h·∇w`: a real path in `C([0,ū];X^j)`
with `‖g_{n+1}‖_{H^j} ≤ C(C_B(2D+C) + C_h) â₁(â₁ + ε⟨u⟩^p)𝔟^n` (`lem:bilinear`(1),(2)). -/
theorem gNext_spec {χ : ℝ → ℝ} {G ubar κ σ ε σi : ℝ} {p Ktop : ℕ} {h : ℝ → ℂ → ℂ}
    {CS : ℕ → ℝ} (hd : HierData χ G ubar κ σ ε σi p Ktop h CS) {j : ℕ} (hj : 2 ≤ j)
    (hjK : j ≤ Ktop) {n : ℕ} {w P : ℝ → ℂ → ℂ} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hw : PathC (j + 1) ubar w) (hP : PathC (j + 1) ubar P)
    (hwr : ∀ u ∈ Icc (0 : ℝ) ubar, ∀ᵐ x ∂(volume : Measure ℂ), (w u x).im = 0)
    (hPr : ∀ u ∈ Icc (0 : ℝ) ubar, ∀ᵐ x ∂(volume : Measure ℂ), (P u x).im = 0)
    (hwb : ∀ u ∈ Icc (0 : ℝ) ubar, normH (j + 1) (w u) ≤ C * ahat κ σ u * bW κ σ ε (p + 2) u ^ n)
    (hPb : ∀ u ∈ Icc (0 : ℝ) ubar, normH (j + 1) (P u) ≤ D * ahat κ σ u) :
    PathC j ubar (gNext h w P) ∧
      (∀ u ∈ Icc (0 : ℝ) ubar, ∀ᵐ x ∂(volume : Measure ℂ), (gNext h w P u x).im = 0) ∧
      ∀ u ∈ Icc (0 : ℝ) ubar, normH j (gNext h w P u) ≤
        C * (CB j * (2 * D + C) + Ch j) * ahat κ σ u * (ahat κ σ u + ε * jap u ^ p) *
          bW κ σ ε (p + 2) u ^ n := by
  have hhj : CkPathOn j annN' (Icc 0 ubar) h := CkPathOn.mono_order hd.hh hjK
  refine ⟨?_, ?_, ?_⟩
  · have h1 := pathC_Bfn2 hj hw hP
    have h2 := pathC_Bfn2 hj (PathC.sub hP hw) hw
    have h3 := pathC_hGrad hj hw hhj hd.hsym
    exact PathC.sub (PathC.add h1 h2) h3
  · intro u hu
    have hwH : MemH 1 (w u) := (hw.1 u hu).1.mono_order (by omega)
    have hPH : MemH 1 (P u) := (hP.1 u hu).1.mono_order (by omega)
    have hdr : ∀ᵐ x ∂(volume : Measure ℂ), ((P u - w u) x).im = 0 := by
      filter_upwards [hPr u hu, hwr u hu] with x h1 h2
      simp [h1, h2]
    filter_upwards [Bfn_im_ae (hwr u hu) hPH (hPr u hu), Bfn_im_ae hdr hwH (hwr u hu),
      hGrad_im_ae (h u) hwH (hwr u hu)] with x h1 h2 h3
    simp only [gNext, Pi.add_apply, Pi.sub_apply, Complex.add_im, Complex.sub_im, h1, h2, h3]
    ring
  · intro u hu
    have hwX := hw.1 u hu
    have hPX := hP.1 u hu
    obtain ⟨hB1, hb1⟩ := bilinear_B hj hwX hPX
    obtain ⟨hB2, hb2⟩ := bilinear_B hj (MemXFn.sub hPX hwX) hwX
    obtain ⟨hH, -, hb3, -⟩ := bilinear_h hj hwX (hhj.1 u hu)
    have hsum := hB1.1.add hB2.1
    have hdiff := hsum.1.sub hH
    have htri : normH j (gNext h w P u) ≤
        normH j (Bfn (w u) (P u)) + normH j (Bfn (P u - w u) (w u)) +
          normH j (hGrad (h u) (w u)) := by
      have e : gNext h w P u = Bfn (w u) (P u) + Bfn (P u - w u) (w u) - hGrad (h u) (w u) :=
        rfl
      rw [e]
      linarith [hdiff.2, hsum.2]
    have hd' : normH j (P u - w u) ≤ D * ahat κ σ u + C * ahat κ σ u * bW κ σ ε (p + 2) u ^ n := by
      have := ((hPX.1.mono_order (Nat.le_succ j)).sub (hwX.1.mono_order (Nat.le_succ j))).2
      linarith [normH_mono_order' (Nat.le_succ j) (P u), normH_mono_order' (Nat.le_succ j) (w u),
        hwb u hu, hPb u hu]
    have hhb : normCk j annN' (h u) ≤ ahat κ σ u + ε * jap u ^ p :=
      (normCk_mono_order (hd.hh.1 u hu) hjK).trans (hd.hfield u hu)
    have hb0 := bW_nonneg (σ := σ) hd.hκ hd.hε (p + 2) u
    refine htri.trans (gNext_arith (CB_pos j).le (bilinear_Ch hj).2 hC hD
      (ahat_nonneg hd.hκ u)
      (le_add_of_nonneg_right (mul_nonneg hd.hε (pow_nonneg (jap_nonneg u) p)))
      (pow_nonneg hb0 n) (pow_le_one₀ hb0 (hd.hb u hu))
      (normH_mono_order' (Nat.le_succ j) (w u)) (hwb u hu) (hPb u hu) hd' hhb
      (normCk_nonneg _ _ _) (normH_nonneg _ _) (normH_nonneg _ _) hb1 hb2 hb3)

/-- **One step of the hierarchy** (`05_single_ring.tex:747-786`): from the induction hypothesis
at level `k+2` and step `n`, the next increment `w' = ∫₀ᵘ e^{(u-v)L}g_{n+1}` and
`P + w'` satisfy the induction hypothesis at level `k+1` and step `n+1`, with
`C' = C_S(k+1) K_n (σi + 1)`, `K_n = C(C_B(k+1)(2D + C) + C_h(k+1))`. -/
theorem hier_step {χ : ℝ → ℝ} {G ubar κ σ ε σi : ℝ} {p Ktop : ℕ} {h : ℝ → ℂ → ℂ}
    {CS : ℕ → ℝ} (hd : HierData χ G ubar κ σ ε σi p Ktop h CS) {k : ℕ} (hk : 1 ≤ k)
    (hkK : k + 1 ≤ Ktop) {n : ℕ} {w1 w P P' : ℝ → ℂ → ℂ} {C D E : ℝ} (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hI : HierInv χ G h ubar κ σ ε p (k + 2) w1 n w P P' C D E) :
    HierInv χ G h ubar κ σ ε p (k + 1) w1 (n + 1) (duhFn χ (k + 1) G 0 (gNext h w P))
      (fun u => P u + duhFn χ (k + 1) G 0 (gNext h w P) u)
      (fun u => P' u + (Lin.Lfn χ G (duhFn χ (k + 1) G 0 (gNext h w P) u) + gNext h w P u))
      (CS (k + 1) * (C * (CB (k + 1) * (2 * D + C) + Ch (k + 1))) * (σi + 1))
      (D + CS (k + 1) * (C * (CB (k + 1) * (2 * D + C) + Ch (k + 1))) * (σi + 1))
      (E + CS (k + 1) * (C * (CB (k + 1) * (2 * D + C) + Ch (k + 1))) * (σi + 1)) := by
  obtain ⟨hw, hP, hP1, hwr, hPr, hP0, hwb, hPb, hPw1m, hPw1, hres⟩ := hI
  have hKn : 0 ≤ C * (CB (k + 1) * (2 * D + C) + Ch (k + 1)) :=
    mul_nonneg hC (add_nonneg (mul_nonneg (CB_pos _).le (by linarith))
      (bilinear_Ch (k := k + 1) (by omega)).2)
  have hσi : 0 ≤ σi := (inv_pos.2 hd.hσ).le.trans hd.hσi
  have hC' : 0 ≤ CS (k + 1) * (C * (CB (k + 1) * (2 * D + C) + Ch (k + 1))) * (σi + 1) :=
    mul_nonneg (mul_nonneg (hd.hCS _) hKn) (by linarith)
  obtain ⟨hgP, hgr, hgb⟩ := gNext_spec hd (j := k + 1) (by omega) hkK hC hD hw hP hwr hPr hwb hPb
  obtain ⟨hw'P, hw'P1, hw'r, hw'0⟩ :=
    duhFn_spec χ hd.hχ hd.hG hd.hu k (memX_zero (k + 1)) (isReal_zero _ _) hgP hgr
  set g := gNext h w P with hgdef
  set w' := duhFn χ (k + 1) G 0 g with hw'def
  set Kn := C * (CB (k + 1) * (2 * D + C) + Ch (k + 1)) with hKndef
  set C' := CS (k + 1) * Kn * (σi + 1) with hC'def
  -- the bound of the new increment
  have hw'b : ∀ u ∈ Icc (0 : ℝ) ubar,
      normH (k + 1) (w' u) ≤ C' * ahat κ σ u * bW κ σ ε (p + 2) u ^ (n + 1) := by
    intro u hu
    have hnorm : normH (k + 1) (w' u) =
        ‖Lin.duhamel χ (k + 1) G 0 (fun v => toY (k + 1) annN (g v)) u‖ := (Y_memH_fn _).2
    have hsub : ∀ v ∈ Icc (0 : ℝ) u, v ∈ Icc (0 : ℝ) ubar := fun v hv => ⟨hv.1, hv.2.trans hu.2⟩
    have h1 := norm_duhamel_zero_le χ hu.1 (hd.hCS (k + 1)) (hd.hS (k + 1))
      (fun v hv => MemXFn.memX_toY (hgP.1 v (hsub v hv)))
      (b := fun v => Kn * ahat κ σ v * (ahat κ σ v + ε * jap v ^ p) * bW κ σ ε (p + 2) v ^ n)
      (fun v hv => by
        rw [MemXFn.norm_toY (hgP.1 v (hsub v hv))]
        have := hgb v (hsub v hv)
        simpa only [hKndef, mul_assoc] using this)
      (duhamel_hier_integrable _ _ _ _ _ _ p n)
    have h2 := duhamel_hier_le p n (hd.hCS (k + 1)) hKn hd.hκ hd.hσ hd.hε hu.1 (C := CS (k + 1))
      (K := Kn) (κ := κ) (σ := σ) (ε := ε)
    have hab : 0 ≤ ahat κ σ u * bW κ σ ε (p + 2) u ^ (n + 1) :=
      mul_nonneg (ahat_nonneg hd.hκ u) (pow_nonneg (bW_nonneg hd.hκ hd.hε _ u) _)
    have h3 : CS (k + 1) * Kn * (σ⁻¹ + 1) * ahat κ σ u * bW κ σ ε (p + 2) u ^ (n + 1) ≤
        C' * ahat κ σ u * bW κ σ ε (p + 2) u ^ (n + 1) := by
      have hm : CS (k + 1) * Kn * (σ⁻¹ + 1) ≤ C' := by
        rw [hC'def]
        exact mul_le_mul_of_nonneg_left (by linarith [hd.hσi])
          (mul_nonneg (hd.hCS _) hKn)
      have := mul_le_mul_of_nonneg_right hm hab
      linarith [show CS (k + 1) * Kn * (σ⁻¹ + 1) * ahat κ σ u * bW κ σ ε (p + 2) u ^ (n + 1) =
        CS (k + 1) * Kn * (σ⁻¹ + 1) * (ahat κ σ u * bW κ σ ε (p + 2) u ^ (n + 1)) by ring,
        show C' * ahat κ σ u * bW κ σ ε (p + 2) u ^ (n + 1) =
        C' * (ahat κ σ u * bW κ σ ε (p + 2) u ^ (n + 1)) by ring]
    rw [hnorm]
    exact h1.trans (h2.trans h3)
  have hb1 : ∀ u ∈ Icc (0 : ℝ) ubar, bW κ σ ε (p + 2) u ^ (n + 1) ≤ 1 := fun u hu =>
    pow_le_one₀ (bW_nonneg hd.hκ hd.hε _ u) (hd.hb u hu)
  have hbb : ∀ u ∈ Icc (0 : ℝ) ubar, bW κ σ ε (p + 2) u ^ (n + 1) ≤ bW κ σ ε (p + 2) u :=
    fun u hu => by
      rw [pow_succ]
      exact mul_le_of_le_one_left (bW_nonneg hd.hκ hd.hε _ u)
        (pow_le_one₀ (bW_nonneg hd.hκ hd.hε _ u) (hd.hb u hu))
  refine ⟨hw'P, PathC.add (PathC.mono_level hP (by omega)) hw'P, ?_, hw'r, ?_, ?_, hw'b, ?_, ?_,
    ?_, ?_⟩
  · exact PathC1.add (PathC1.mono_level hP1 (show k ≤ k + 2 - 1 by omega)) hw'P1
  · intro u hu
    filter_upwards [hPr u hu, hw'r u hu] with x h1 h2
    simp [h1, h2]
  · show (fun x => P 0 x + w' 0 x) =ᵐ[volume] w1 0
    rw [hw'0]
    filter_upwards [hP0, Y_fn_zero (k + 1) annN] with x h1 h2
    simp only [h1, h2, Pi.zero_apply, add_zero]
  · intro u hu
    have hPm := (hP.1 u hu).1
    have hw'm := (hw'P.1 u hu).1
    have h1 := ((hPm.mono_order (Nat.le_succ (k + 1))).add hw'm).2
    have h2 := normH_mono_order' (Nat.le_succ (k + 1)) (P u)
    have := hw'b u hu
    have hab : 0 ≤ ahat κ σ u := ahat_nonneg hd.hκ u
    have h4 : C' * ahat κ σ u * bW κ σ ε (p + 2) u ^ (n + 1) ≤ C' * ahat κ σ u := by
      have := mul_le_mul_of_nonneg_left (hb1 u hu) (mul_nonneg hC' hab)
      linarith
    show normH (k + 1) (P u + w' u) ≤ (D + C') * ahat κ σ u
    nlinarith [hPb u hu]
  · intro u hu
    have e : P u + w' u - w1 u = (P u - w1 u) + w' u := by abel
    show MemH (k + 1) (P u + w' u - w1 u)
    rw [e]
    exact (((hPw1m u hu).mono_order (Nat.le_succ (k + 1))).add (hw'P.1 u hu).1).1
  · intro u hu
    have e : P u + w' u - w1 u = (P u - w1 u) + w' u := by abel
    show normH (k + 1) (P u + w' u - w1 u) ≤ (E + C') * ahat κ σ u * bW κ σ ε (p + 2) u
    rw [e]
    have h1 := (((hPw1m u hu).mono_order (Nat.le_succ (k + 1))).add (hw'P.1 u hu).1).2
    have h2 := normH_mono_order' (Nat.le_succ (k + 1)) (P u - w1 u)
    have h3 := hw'b u hu
    have hab : 0 ≤ ahat κ σ u := ahat_nonneg hd.hκ u
    have h4 : C' * ahat κ σ u * bW κ σ ε (p + 2) u ^ (n + 1) ≤
        C' * ahat κ σ u * bW κ σ ε (p + 2) u :=
      mul_le_mul_of_nonneg_left (hbb u hu) (mul_nonneg hC' hab)
    have h5 := hPw1 u hu
    have e2 : (E + C') * ahat κ σ u * bW κ σ ε (p + 2) u =
        E * ahat κ σ u * bW κ σ ε (p + 2) u + C' * ahat κ σ u * bW κ σ ε (p + 2) u := by ring
    linarith
  · intro u hu
    have hPX : Lin.MemXFn (k + 2) (P u) := hP.1 u hu
    have hw'X : Lin.MemXFn (k + 1) (w' u) := hw'P.1 u hu
    have r1 := hres u hu
    have r2 := Lfn_add_ae χ hd.hχ (s := k) G (MemXFn.mono hPX (Nat.le_succ (k + 1))) hw'X
    have r3 := hGrad_add_ae (h u) (hPX.1.mono_order (by omega)) (hw'X.1.mono_order (by omega))
    have r4 := Bfn_diff_ae (v₁ := P u + w' u) (v₂ := P u)
      (MemXFn.mono (MemXFn.add (MemXFn.mono hPX (Nat.le_succ (k + 1))) hw'X) (by omega))
      (MemXFn.mono hPX (by omega))
    have e1 : P u + w' u - P u = w' u := add_sub_cancel_left _ _
    have e2 : P u + w' u - w' u = P u := add_sub_cancel_right _ _
    rw [e1] at r4
    filter_upwards [r1, r2, r3, r4] with x h1 h2 h3 h4
    simp only [Rapp, ringRHS, gNext, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, e2] at h1 h2 h3 h4 ⊢
    linear_combination h1 - h2 + h3 - h4

end NonUniqueEuler.OneRing.WAppH
