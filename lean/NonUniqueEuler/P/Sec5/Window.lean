import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.Window.Approx
import NonUniqueEuler.I.Sec5.Lambda
import NonUniqueEuler.I.Sec4.PropU
import NonUniqueEuler.I.Infra.Continuity.Bootstrap
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.H.Sec5.Window.Real
import NonUniqueEuler.H.Sec5.Window.Bounds
import NonUniqueEuler.H.Sec5.Window.Config
import NonUniqueEuler.H.Sec5.Window.Comparison

/-!
# Proof: `lem:window` (the window after the initial layer)

Proof of `OneRing.window`, stated in `I/Sec5/Window.lean` (the statement is copied verbatim).
Manuscript `05_single_ring.tex:678-704` (statement), `:705-861` (proof).

**Structure.**
* The approximate solution `w_app = Σ_{j ≤ N_G} w^{[j]}` with `eq:W-hier`, `eq:W-res` and the bound on
  `w_app - 2Re(c(u)e^{λu}φ_*)` is the sub-interface `window_approx` (`I/Sec5/Window/Approx.lean`).
* Constants: `C_v = C_app 2^{N_G} C♮^{N_G}/σ_b`,
  `C_W = 1 + C_v + C_app + C_app C♮ + C♮ + C_BS C_v + (1 + C_BS(C_v + C_app))/σ_b`,
  `δ_W = min(1/2, 1/(C_app + 1), a/(64C_W))`, and `κ_W ∈ (0,1]` with `C_W x ς(x)^{N_W} ≤ a/64` on
  `(0,κ_W]` (`WindowH.exists_kappa`). (Deviation: the manuscript's `C_W` is assembled from
  `C^{(j)}`, `C_en`, `S_W`; any constant dominating the final collection works; ours is chosen to
  dominate the sums below.)
* `eq:W-small` (`𝔟 ≤ 1`, `‖h‖_{C^{s+1}(N')} ≤ 1`) from `WindowH.window_bookkeeping`.
* The core improvement `core`: if on `[0,t]` every trajectory moves radially by at most `a/16`
  and `‖w‖_{H^s} ≤ 1`, then `supp ω_r ⊂ N` there (`WindowH.ringSupportedIn_of_moves`),
  `lem:energy` gives `‖w - w_app‖_{H^s} ≤ C_v(â^{N_G+1} + κ₁²ς^{(p+2)N_G})`
  (`WindowH.v_le_integral`, `WindowH.v_integral_le`), the collection gives the bound on
  `w - 2Re(ce^{λu}φ_*)` and `‖w‖_{H^s} ≤ C_Wδ₀ + C_Wκ₁ς^{N_W}`, and `lem:reduction`(2),
  `lem:bilinear`(4) give the displacement bound (`WindowH.displacement_le`,
  `WindowH.disp_integral_le`).
* The continuity argument (`Continuity.bootstrap_le`) with the two continuous quantities
  `δ_r(t)` (`WindowH.dispFn`) and `‖w(t)‖_{H^s}` (`WindowH.continuousOn_normH_w`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

set_option maxHeartbeats 1000000 in
/-- **`lem:window`** (`05_single_ring.tex:678-704`). Assume (N1)–(N3). Let `s ≥ 3`,
`σ' ∈ (9/200, σ_b)`, `p = 3`, `N_G`, `M = s + N_G + 2`, `N_W = (p+2)N_G + 1` as in `eq:W-const`,
and `C♮ ≥ 1`. There are `δ_W ∈ (0,1/2]`, `κ_W ∈ (0,1]`, `C_W ≥ 1`, depending only on
`(Φ, G₁, s, σ', C♮)`, such that the following holds. Let `G ∈ [0,G₁]`, `σ = σ(G)`,
`λ = λ_*(G)`, `κ₁ ∈ (0,κ_W]`, `δ₀ ∈ (0,δ_W]`, `η_b ∈ [0,1]`, `T̂₁ = σ⁻¹ log(δ₀/κ₁)`,
`ū ∈ (0,T̂₁]`, and let the configuration be as in `lem:reduction` on `[0,ū]` with this `G`;
`w = ω_r - Φ`, `c` the running coefficient with `w₀ = w(0)`. Assume `‖w(0)‖_{H^{M-2}} ≤ C♮κ₁`,
`supp(Φ + w(0)) ⊂ {(7/8 - 1/64)a ≤ |y| ≤ 5/4 + a/64}`, and on `[0,ū]`
`‖h(u)‖_{C^M(N')} ≤ C♮κ₁⟨u⟩^p + η_bκ₁e^{σu}` and `|c(u)| ≤ C♮κ₁`. With `â₁(u) = κ₁e^{σu}` and
`ρ₁(u) = ⟨u⟩^pe^{-(σ-σ')u}`: for every `u ∈ [0,ū]`, every trajectory of `ω_r` moves radially by
at most `C_Wδ₀ + C_Wκ₁ς(κ₁)^{N_W} ≤ a/32` on `[0,u]`, and
`‖w(u) - 2Re(c(u)e^{λu}φ_*)‖_{H^s} ≤ C_W â₁(u)[ρ₁(u) + â₁(u) + κ₁ς(κ₁)^{N_W} + η_b]`. -/
theorem window (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 3 ≤ s) {σ' : ℝ} (hσ' : σ' ∈ Ioo (9 / 200 : ℝ) (Eig.sigb χ))
    {Cn : ℝ} (hCn : 1 ≤ Cn) :
    ∃ δW κW CW : ℝ, δW ∈ Ioc (0 : ℝ) (1 / 2) ∧ κW ∈ Ioc (0 : ℝ) 1 ∧ 1 ≤ CW ∧
      ∀ (c : RingConfig) (ubar κ₁ δ₀ ηb : ℝ), c.G ∈ Icc (0 : ℝ) Gbar →
        κ₁ ∈ Ioc (0 : ℝ) κW → δ₀ ∈ Ioc (0 : ℝ) δW → ηb ∈ Icc (0 : ℝ) 1 →
        ubar ∈ Ioc (0 : ℝ) (That (Eig.sigma χ c.G) δ₀ κ₁) → c.Hyp ubar →
        Sob.normH (Mact χ s - 2) (c.pert0 χ) ≤ Cn * κ₁ →
        tsupport c.ring0 ⊆ Sect.closedAnnulus ((7 / 8 - 1 / 64) * a) (5 / 4 + a / 64) →
        (∀ u ∈ Icc (0 : ℝ) ubar, normCk (Mact χ s) annN' (c.h u) ≤
          Cn * κ₁ * Prelim.jap u ^ pW + ηb * ahat κ₁ (Eig.sigma χ c.G) u) →
        (∀ u ∈ Icc (0 : ℝ) ubar, ‖runCoef χ c.G (c.pert0 χ) c.h u‖ ≤ Cn * κ₁) →
        ∀ u ∈ Icc (0 : ℝ) ubar,
          c.MovesRadially u (CW * δ₀ + CW * κ₁ * varsigma χ κ₁ ^ NW χ s) ∧
            CW * δ₀ + CW * κ₁ * varsigma χ κ₁ ^ NW χ s ≤ a / 32 ∧
            Sob.normH s (c.w χ u - modeFn χ c.G
                (runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u))) ≤
              CW * ahat κ₁ (Eig.sigma χ c.G) u *
                (rhoOne (Eig.sigma χ c.G) σ' u + ahat κ₁ (Eig.sigma χ c.G) u +
                  κ₁ * varsigma χ κ₁ ^ NW χ s + ηb) := by
  /- ### Structural constants -/
  obtain ⟨Capp, hCapp0, hApp⟩ := window_approx χ hχ hN hs hσ' hCn
  have hU := Eig.propU_a χ hχ hN
  have hσb : 0 < Eig.sigb χ := by linarith [hU.2.2.2.1]
  have hσG : ∀ G ∈ Icc (0 : ℝ) Gbar, Eig.sigb χ ≤ Eig.sigma χ G := by
    obtain ⟨G₀, -, hsb, hmin⟩ := hU.2.2.1
    intro G hG
    rw [hsb]
    exact hmin G hG
  have hΛ := lambda_ge χ hχ hN hs
  have hNG := le_NG χ s
  have hNG2 := two_le_NG χ s
  have ha := WindowH.win_a_pos
  have ha1 := WindowH.win_a_lt_one
  have hCBS := CBS_pos
  have hCn0 : 0 ≤ Cn := by linarith
  have hNW2 : (pW + 2) * NG χ s ≤ NW χ s := Nat.le_succ _
  have hNW3 : (pW + 2) * NG χ s + 1 ≤ NW χ s := le_of_eq rfl
  have hNW1 : pW + 2 ≤ NW χ s := by
    have : pW + 2 ≤ (pW + 2) * NG χ s := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hNW4 : pW + 1 ≤ NW χ s := by omega
  have hN1 : 1 ≤ NG χ s := by omega
  set N := NG χ s with hNdef
  set NWn := NW χ s with hNWdef
  set Cv := Capp * 2 ^ N * Cn ^ N / Eig.sigb χ with hCv
  have hCv0 : 0 ≤ Cv := by positivity
  set CW := 1 + Cv + Capp + Capp * Cn + Cn + CBS * Cv + (1 + CBS * (Cv + Capp)) / Eig.sigb χ
    with hCW
  have hT1 : 0 ≤ Capp * Cn := by positivity
  have hT2 : 0 ≤ CBS * Cv := by positivity
  have hT3 : 0 ≤ (1 + CBS * (Cv + Capp)) / Eig.sigb χ := by positivity
  have hCW0 : 1 ≤ CW := by rw [hCW]; linarith
  have hCW1 : Cv + Capp + Capp * Cn ≤ CW := by rw [hCW]; linarith
  have hCW2 : Cn + CBS * Cv ≤ CW := by rw [hCW]; linarith
  have hCW3 : (1 + CBS * (Cv + Capp)) / Eig.sigb χ ≤ CW := by rw [hCW]; linarith
  have hCW4 : Cv + Capp ≤ CW := by rw [hCW]; linarith
  have hCnCW : Cn ≤ CW := by rw [hCW]; linarith
  have hCWpos : 0 < CW := by linarith
  obtain ⟨κW, hκW, hκWp⟩ := WindowH.exists_kappa (χ := χ) hσb NWn hCWpos
    (by positivity : (0 : ℝ) < a / 64)
  set δW := min (1 / 2) (min (1 / (Capp + 1)) (a / (64 * CW))) with hδW
  have hδW0 : 0 < δW := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  refine ⟨δW, κW, CW, ⟨hδW0, min_le_left _ _⟩, hκW, hCW0, ?_⟩
  /- ### The data -/
  intro c ubar κ₁ δ₀ ηb hG hκ hδ hηb hubar hc hw0 hr hh hcoef
  have hκ0 : 0 < κ₁ := hκ.1
  set σ := Eig.sigma χ c.G with hσdef
  set V := varsigma χ κ₁ with hVdef
  have hσ : Eig.sigb χ ≤ σ := hσG c.G hG
  have hσ0 : 0 < σ := hσb.trans_le hσ
  have hδ1 : δ₀ ≤ 1 / 2 := hδ.2.trans (min_le_left _ _)
  have hδC : δ₀ ≤ 1 / (Capp + 1) := hδ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδa : δ₀ ≤ a / (64 * CW) := hδ.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCWδ : CW * δ₀ ≤ a / 64 := by
    rw [le_div_iff₀ (by positivity)] at hδa
    linarith
  have hCappδ : Capp * δ₀ ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hδC
    nlinarith [hδ.1]
  have hCWκ : CW * κ₁ * V ^ NWn ≤ a / 64 := hκWp κ₁ ⟨hκ.1, hκ.2⟩
  have hT : 0 < That σ δ₀ κ₁ := hubar.1.trans_le hubar.2
  have hbk : ∀ u ∈ Icc (0 : ℝ) ubar, κ₁ ≤ δ₀ ∧ κ₁ ≤ 1 ∧ 1 + u ≤ V ∧ κ₁ ≤ ahat κ₁ σ u ∧
      ahat κ₁ σ u ≤ δ₀ := fun u hu =>
    WindowH.window_bookkeeping hσb hσ hκ.1 hδ.1 (hδ1.trans (by norm_num)) hu.1
      (hu.2.trans hubar.2) hT
  have hκ1 : κ₁ ≤ 1 := (hbk 0 ⟨le_rfl, hubar.1.le⟩).2.1
  have hV1 : 1 ≤ V := WindowH.one_le_varsigma hσb hκ.1 hκ1
  have hV0 : 0 ≤ V := by linarith
  have hjapV : ∀ u ∈ Icc (0 : ℝ) ubar, Prelim.jap u ≤ V := fun u hu =>
    (WindowH.jap_le_one_add hu.1).trans (hbk u hu).2.2.1
  have hCnκ : Cn * κ₁ * V ^ NWn ≤ a / 64 := by
    have : Cn * κ₁ * V ^ NWn ≤ CW * κ₁ * V ^ NWn :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCnCW hκ.1.le) (by positivity)
    linarith
  /- ### `eq:W-small` -/
  have hjp : ∀ u ∈ Icc (0 : ℝ) ubar, Prelim.jap u ^ pW ≤ Prelim.jap u ^ (pW + 2) := fun u _ =>
    pow_le_pow_right₀ (Prelim.one_le_jap u) (by norm_num)
  have hb : ∀ u ∈ Icc (0 : ℝ) ubar,
      ahat κ₁ σ u + Cn * κ₁ * Prelim.jap u ^ (pW + 2) ≤ 1 := by
    intro u hu
    have h1 := (hbk u hu).2.2.2.2
    have h2 : Prelim.jap u ^ (pW + 2) ≤ V ^ NWn :=
      (pow_le_pow_left₀ (Prelim.jap_nonneg u) (hjapV u hu) _).trans
        (pow_le_pow_right₀ hV1 hNW1)
    have h3 : Cn * κ₁ * Prelim.jap u ^ (pW + 2) ≤ Cn * κ₁ * V ^ NWn :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have hRF := reduction_field hc
  have hpath : CkPathOn (Mact χ s) annN' (Icc 0 ubar) c.h := hRF.2 _
  have hsym : ∀ u ∈ Icc (0 : ℝ) ubar, IsSymFieldOn annN' (c.h u) := by
    intro u hu
    obtain ⟨U, -, hNU, -, -, -, hsU, -⟩ := hRF.1 u hu
    exact fun x hx => hsU x (hNU hx)
  have hMs1 : s + 1 ≤ Mact χ s := by rw [Mact_eq]; omega
  have hMs2 : s ≤ Mact χ s - 2 := by rw [Mact_eq]; omega
  have hhb : ∀ u ∈ Icc (0 : ℝ) ubar, normCk (Mact χ s) annN' (c.h u) ≤
      ahat κ₁ σ u + Cn * κ₁ * Prelim.jap u ^ (pW + 2) := by
    intro u hu
    have h1 := hh u hu
    have h2 : ηb * ahat κ₁ σ u ≤ ahat κ₁ σ u :=
      mul_le_of_le_one_left (WindowH.ahat_nonneg hκ.1.le σ u) hηb.2
    have h3 : Cn * κ₁ * Prelim.jap u ^ pW ≤ Cn * κ₁ * Prelim.jap u ^ (pW + 2) :=
      mul_le_mul_of_nonneg_left (hjp u hu) (by positivity)
    linarith
  have hhs : ∀ u ∈ Icc (0 : ℝ) ubar, normCk (s + 1) annN' (c.h u) ≤ 1 := fun u hu =>
    ((normCk_mono_order (hpath.1 u hu) hMs1).trans (hhb u hu)).trans (hb u hu)
  have hh0 : ∀ u ∈ Icc (0 : ℝ) ubar, normCk 0 annN' (c.h u) ≤
      Cn * κ₁ * V ^ pW + ahat κ₁ σ u := by
    intro u hu
    have h1 := (normCk_mono_order (hpath.1 u hu) (Nat.zero_le _)).trans (hh u hu)
    have h2 : ηb * ahat κ₁ σ u ≤ ahat κ₁ σ u :=
      mul_le_of_le_one_left (WindowH.ahat_nonneg hκ.1.le σ u) hηb.2
    have h3 : Cn * κ₁ * Prelim.jap u ^ pW ≤ Cn * κ₁ * V ^ pW :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Prelim.jap_nonneg u) (hjapV u hu) _)
        (by positivity)
    linarith
  /- ### The approximate solution -/
  have hrN : tsupport c.ring0 ⊆ annN := hr.trans WindowH.window_annulus_subset_annN
  have hX0 := WindowH.memXFn_pert0 hχ hc hrN (Mact χ s - 2)
  obtain ⟨wapp, wapp', happ, happ', hreal, happ0, hbds⟩ :=
    hApp c.G ubar κ₁ ηb c.h (c.pert0 χ) hG hubar.1 hκ.1 hηb hpath hsym hX0
      (Filter.Eventually.of_forall fun x => WindowH.pert0_im χ x) hw0 hh hcoef hb
  have hw0eq := WindowH.w_zero hc χ
  set D := CW * δ₀ + CW * κ₁ * V ^ NWn with hD
  have hDa : D ≤ a / 32 := by rw [hD]; linarith
  have hD0 : 0 ≤ D := by
    have := hδ.1
    positivity
  /- ### The core improvement -/
  have core : ∀ t ∈ Icc (0 : ℝ) ubar, c.MovesRadially t (a / 16) →
      (∀ τ ∈ Icc (0 : ℝ) t, Sob.normH s (c.w χ τ) ≤ 1) →
      c.MovesRadially t D ∧ (∀ τ ∈ Icc (0 : ℝ) t, Sob.normH s (c.w χ τ) ≤ D) ∧
        ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH s (c.w χ τ - modeFn χ c.G
            (runCoef χ c.G (c.pert0 χ) c.h τ * Complex.exp (Eig.lam χ c.G * τ))) ≤
          CW * ahat κ₁ σ τ * (rhoOne σ σ' τ + ahat κ₁ σ τ + κ₁ * V ^ NWn + ηb) := by
    intro t ht hm hw1
    have hsupp := WindowH.ringSupportedIn_of_moves hc hr hm
    have hIt : ∀ τ ∈ Icc (0 : ℝ) t, τ ∈ Icc (0 : ℝ) ubar := fun τ hτ => ⟨hτ.1, hτ.2.trans ht.2⟩
    -- `eq:W-v`: `‖w - w_app‖_{H^s} ≤ C_v(â^{N+1} + κ₁²V^{(p+2)N})`
    have hRc : ContinuousOn (fun τ' => Capp * ahat κ₁ σ τ' *
        (ahat κ₁ σ τ' + Cn * κ₁ * Prelim.jap τ' ^ (pW + 2)) ^ N) (Icc 0 t) := by
      have := WindowH.continuous_ahat κ₁ σ
      have := WindowH.continuous_jap
      exact Continuous.continuousOn (by fun_prop)
    have hv : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH s (c.w χ τ - wapp τ) ≤
        Cv * (ahat κ₁ σ τ ^ (N + 1) + κ₁ ^ 2 * V ^ ((pW + 2) * N)) := by
      intro τ hτ
      have h1 := WindowH.v_le_integral hχ hN hs hc ht hG hsupp hw0eq happ happ' hreal happ0 hw1
        (fun τ' hτ' => ((hbds τ' (hIt τ' hτ')).1.trans
          (mul_le_mul_of_nonneg_left (hbk τ' (hIt τ' hτ')).2.2.2.2 hCapp0)).trans hCappδ)
        (fun τ' hτ' => hhs τ' (hIt τ' hτ')) hRc (fun τ' hτ' => (hbds τ' (hIt τ' hτ')).2.2.2)
        τ hτ
      refine h1.trans ?_
      exact WindowH.v_integral_le hσb hσ (hΛ.1 c.G hG) hNG hκ.1 (hδ1.trans (by norm_num)) hCn
        hCapp0 hτ.1 (hbk τ (hIt τ hτ)).2.2.2.2
        (fun τ' hτ' => hjapV τ' ⟨hτ'.1, hτ'.2.trans (hIt τ hτ).2⟩)
    -- the triangle inequalities
    have hmemw : ∀ τ, Sob.MemH s (c.w χ τ) := fun τ => WindowH.memH_w hχ hc τ s
    have hmemapp : ∀ τ ∈ Icc (0 : ℝ) t, Sob.MemH (s + 1) (wapp τ) := fun τ hτ =>
      (happ.1 τ (hIt τ hτ)).1
    have hmemv : ∀ τ ∈ Icc (0 : ℝ) t, Sob.MemH s (c.w χ τ - wapp τ) := fun τ hτ =>
      (Sob.MemH.sub (hmemw τ) (Sob.MemH.mono_order (hmemapp τ hτ) (Nat.le_succ s))).1
    have hwB : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH s (c.w χ τ) ≤
        (Cv + Capp) * ahat κ₁ σ τ + Cv * κ₁ ^ 2 * V ^ ((pW + 2) * N) ∧
        (Cv + Capp) * ahat κ₁ σ τ + Cv * κ₁ ^ 2 * V ^ ((pW + 2) * N) ≤ D := by
      intro τ hτ
      have hsplit := Sob.MemH.add (hmemv τ hτ)
        (Sob.MemH.mono_order (hmemapp τ hτ) (Nat.le_succ s))
      rw [sub_add_cancel] at hsplit
      have happs : Sob.normH s (wapp τ) ≤ Capp * ahat κ₁ σ τ :=
        (Sob.MemH.normH_mono (hmemapp τ hτ) (Nat.le_succ s)).trans (hbds τ (hIt τ hτ)).1
      have hbkτ := hbk τ (hIt τ hτ)
      exact WindowH.collect_w hCapp0 hCv0 hCW4 (WindowH.ahat_nonneg hκ.1.le σ τ)
        (hbkτ.2.2.2.2.trans (hδ1.trans (by norm_num))) hbkτ.2.2.2.2 hκ.1 hκ1 hV1 hNW2
        (by linarith [hsplit.2, hv τ hτ])
    -- the bound on `w - 2Re(ce^{λu}φ_*)`
    have hmode : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH s (c.w χ τ - modeFn χ c.G
          (runCoef χ c.G (c.pert0 χ) c.h τ * Complex.exp (Eig.lam χ c.G * τ))) ≤
        CW * ahat κ₁ σ τ * (rhoOne σ σ' τ + ahat κ₁ σ τ + κ₁ * V ^ NWn + ηb) := by
      intro τ hτ
      obtain ⟨-, hmemm, hbm, -⟩ := hbds τ (hIt τ hτ)
      have hsplit := Sob.MemH.add (hmemv τ hτ) hmemm
      rw [sub_add_sub_cancel] at hsplit
      have hbkτ := hbk τ (hIt τ hτ)
      have hρ : 0 ≤ rhoOne σ σ' τ := by
        unfold rhoOne
        have := Prelim.jap_nonneg τ
        positivity
      exact WindowH.collect_mode hCapp0 hCv0 hCW1 hCn (WindowH.ahat_nonneg hκ.1.le σ τ)
        (hbkτ.2.2.2.2.trans (hδ1.trans (by norm_num))) hbkτ.2.2.2.1 hκ.1 hV1 hρ hηb.1
        (Prelim.jap_nonneg τ) (hjapV τ (hIt τ hτ)) hN1 hNW1 hNW2
        (by linarith [hsplit.2, hv τ hτ])
    -- the displacement
    have hdisp := WindowH.displacement_le hχ hc ht hsupp
      (A := fun τ => Cn * κ₁ * V ^ pW + ahat κ₁ σ τ)
      (B := fun τ => (Cv + Capp) * ahat κ₁ σ τ + Cv * κ₁ ^ 2 * V ^ ((pW + 2) * N))
      (by have := WindowH.continuous_ahat κ₁ σ; exact Continuous.continuousOn (by fun_prop))
      (by have := WindowH.continuous_ahat κ₁ σ; exact Continuous.continuousOn (by fun_prop))
      (fun τ hτ => hh0 τ (hIt τ hτ))
      (fun τ hτ => (Sob.MemH.normH_mono (hmemw τ) (by omega)).trans (hwB τ hτ).1)
    refine ⟨fun y hy τ hτ => (hdisp y hy τ hτ).trans ?_, fun τ hτ => (hwB τ hτ).1.trans
      (hwB τ hτ).2, hmode⟩
    have hbkτ := hbk τ (hIt τ hτ)
    exact WindowH.disp_integral_le hσb hσ hκ.1 hκ1 (by linarith [hbkτ.2.2.1]) hV1
      hbkτ.2.2.2.2 hCn0 hCapp0 hCv0 hCBS.le hCW2 hCW3 hNW4 hNW3
  /- ### The continuity argument -/
  have hw00 : Sob.normH s (c.w χ 0) ≤ 1 := by
    rw [hw0eq]
    have h1 := Sob.MemH.normH_mono hX0.1 hMs2
    have h2 : Cn * κ₁ ≤ Cn * κ₁ * V ^ NWn :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hV1)
    linarith
  have hboot := Continuity.bootstrap_le (ι := Bool) (a := 0) (b := ubar)
    (F := fun i => if i then WindowH.dispFn c else fun τ => Sob.normH s (c.w χ τ))
    (G := fun i _ => if i then a / 16 else 1)
    (H := fun i _ => if i then D else a / 32)
    (by
      intro i
      cases i
      · exact WindowH.continuousOn_normH_w hχ hc s
      · exact (WindowH.continuous_dispFn hc).continuousOn)
    (by intro i; cases i <;> exact continuousOn_const)
    (by
      intro i τ _
      cases i
      · simp only [Bool.false_eq_true, ↓reduceIte]; linarith
      · simp only [↓reduceIte]; linarith)
    (by
      intro i
      cases i
      · simpa using hw00
      · simpa using WindowH.dispFn_zero_le hc (by positivity : (0 : ℝ) ≤ a / 16))
    (by
      intro t ht hprev i
      have hm : c.MovesRadially t (a / 16) :=
        WindowH.movesRadially_of_dispFn_le hc fun τ hτ => by simpa using hprev τ hτ true
      have hw1 : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH s (c.w χ τ) ≤ 1 := fun τ hτ => by
        simpa using hprev τ hτ false
      obtain ⟨hmD, hwD, -⟩ := core t ht hm hw1
      cases i
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact (hwD t ⟨ht.1, le_rfl⟩).trans hDa
      · simp only [↓reduceIte]
        exact WindowH.dispFn_le_of_movesRadially hD0 hmD t ⟨ht.1, le_rfl⟩)
  /- ### Conclusion -/
  intro u hu
  have hm : c.MovesRadially u (a / 16) := by
    apply WindowH.movesRadially_of_dispFn_le hc
    intro τ hτ
    have := hboot τ ⟨hτ.1, hτ.2.trans hu.2⟩ true
    simp only [↓reduceIte] at this
    linarith
  have hw1 : ∀ τ ∈ Icc (0 : ℝ) u, Sob.normH s (c.w χ τ) ≤ 1 := by
    intro τ hτ
    have := hboot τ ⟨hτ.1, hτ.2.trans hu.2⟩ false
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    linarith
  obtain ⟨hmD, -, hmode⟩ := core u hu hm hw1
  exact ⟨hmD, hDa, hmode u ⟨hu.1, le_rfl⟩⟩

end OneRing

end NonUniqueEuler
