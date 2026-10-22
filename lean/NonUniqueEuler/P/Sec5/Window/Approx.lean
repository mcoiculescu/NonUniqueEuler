import NonUniqueEuler.H.Sec5.Window.Approx.Hier
import NonUniqueEuler.H.Sec5.Window.Approx.Mode
import NonUniqueEuler.I.Sec4.PropSemigroup

/-!
# Proof: the approximate solution of `lem:window` (`eq:W-hier`, `eq:W-res`)

Proof of `I/Sec5/Window/Approx.lean` (`05_single_ring.tex:716-798`).

**Deviation (restructured hierarchy).** In place of the manuscript's homogeneous expansion
`w^{[j]}` (`g^{[j]} = Σ_{i+l=j} B(w^{[i]},w^{[l]}) - h·∇w^{[j-1]}`) we use the Picard iteration in
increment form (`H/Sec5/Window/Approx/Step.lean`): `w_1 = w^{[1]} = wlin₀`,
`w_{n+1} = ∫₀ᵘ e^{(u-v)L} g_{n+1}`, `g_{n+1} = B(w_n,P_n) + B(P_n - w_n, w_n) - h·∇w_n`,
`P_n = Σ_{m ≤ n} w_m`. Then `P_{n+1} = e^{uL}w₀ + ∫₀ᵘ e^{(u-v)L}(F + B(P_n,P_n) - h·∇P_n)` is the
`n`-th Picard iterate (a different function from `Σ_{j ≤ n+1} w^{[j]}`), the residual of `P_n`
is exactly `-g_{n+1}`, and the same estimates hold: `‖w_n‖_{H^{k_n}} ≤ C_n â₁𝔟^{n-1}` with
`k_n = K + 1 - n`. We take `w_app = P_{N_G}` (`hier_final` at `K = s + N_G`, level `s + 1`),
`ε_W = C♮κ₁`, `σi = σ_b⁻¹`, `C_S(k)` from `prop:semigroup` for every `k`, and
`C_0 = 2C_φC♮ + C_lin(C♮ρ̄ + 1)` for `w^{[1]}` (`wlin0_bound`, `lem:linear-part`).
The constant `C_app` is a sum of absolute values of the (data-independent) constants of the
hierarchy, so its nonnegativity needs no hypothesis on the data.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- The arithmetic of the bound of `w_app - 2Re(ce^{λu}φ_*)`. -/
private theorem window_approx_arith {D E Cl Cn Kr a ρ η b : ℝ} (ha : 0 ≤ a) (hρ : 0 ≤ ρ)
    (hη : 0 ≤ η) (hb : 0 ≤ b) (hCn : 0 ≤ Cn) :
    E * a * b + Cl * (Cn * (a * ρ) + η * a) ≤
      (|D| + |E| + |Cl| * Cn + |Cl| + |Kr|) * a * (ρ + η + b) := by
  set X := |D| + |E| + |Cl| * Cn + |Cl| + |Kr| with hX
  have hD := abs_nonneg D
  have hE := abs_nonneg E
  have hCl := abs_nonneg Cl
  have hKr := abs_nonneg Kr
  have hClCn : 0 ≤ |Cl| * Cn := mul_nonneg hCl hCn
  have h1 : E * (a * b) ≤ X * (a * b) :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self E]) (mul_nonneg ha hb)
  have h2 : (Cl * Cn) * (a * ρ) ≤ X * (a * ρ) := by
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg ha hρ)
    have := mul_le_mul_of_nonneg_right (le_abs_self Cl) hCn
    linarith
  have h3 : Cl * (η * a) ≤ X * (η * a) :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self Cl]) (mul_nonneg hη ha)
  have e1 : E * a * b + Cl * (Cn * (a * ρ) + η * a) =
      E * (a * b) + (Cl * Cn) * (a * ρ) + Cl * (η * a) := by ring
  have e2 : X * a * (ρ + η + b) = X * (a * b) + X * (a * ρ) + X * (η * a) := by ring
  rw [e1, e2]
  linarith

/-- `x * a ≤ (|D| + |E| + |Cl|Cn + |Cl| + |Kr|) * a` for `x ∈ {D, Kr}`-type terms. -/
private theorem le_capp_mul {x D E Cl Cn Kr a : ℝ} (hx : x ≤ |D| + |E| + |Cl| * Cn + |Cl| + |Kr|)
    (ha : 0 ≤ a) : x * a ≤ (|D| + |E| + |Cl| * Cn + |Cl| + |Kr|) * a :=
  mul_le_mul_of_nonneg_right hx ha

/-- **The approximate solution of `lem:window`** (`05_single_ring.tex:716-798`, `eq:W-hier`,
`eq:W-res`). Assume (N1)–(N3), `s ≥ 3`, `σ' ∈ (9/200, σ_b)`, `C♮ ≥ 1`. There is `C_app ≥ 0`
(depending only on `Φ, G₁, s, σ', C♮`) such that for `G ∈ [0,G₁]`, `ū > 0`, `κ₁ > 0`,
`η_b ∈ [0,1]`, every field path `h ∈ C([0,ū];C^M(N'))`, `3`-fold symmetric on `N'`, and every real
`w₀ ∈ X^{M-2}` with `‖w₀‖_{H^{M-2}} ≤ C♮κ₁`, `‖h(u)‖_{C^M(N')} ≤ C♮κ₁⟨u⟩^p + η_bâ₁(u)`,
`|c(u)| ≤ C♮κ₁` and `𝔟(u) = â₁(u) + C♮κ₁⟨u⟩^{p+2} ≤ 1` on `[0,ū]`, there is a real
`w_app ∈ C([0,ū];X^{s+1}) ∩ C¹([0,ū];X^s)` (derivative `w_app'`) with `w_app(0) = w₀` and, on
`[0,ū]`, `‖w_app‖_{H^{s+1}} ≤ C_app â₁`, `‖w_app - 2Re(ce^{λu}φ_*)‖_{H^s} ≤
C_app â₁(ρ₁ + η_b + 𝔟)` (the difference being in `H^s`) and `‖R_app‖_{H^s} ≤ C_app â₁𝔟^{N_G}`. -/
theorem window_approx (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 3 ≤ s) {σ' : ℝ} (hσ' : σ' ∈ Ioo (9 / 200 : ℝ) (Eig.sigb χ))
    {Cn : ℝ} (hCn : 1 ≤ Cn) :
    ∃ Capp : ℝ, 0 ≤ Capp ∧
      ∀ (G ubar κ₁ ηb : ℝ) (h : ℝ → ℂ → ℂ) (w₀ : ℂ → ℂ), G ∈ Icc (0 : ℝ) Gbar → 0 < ubar →
        0 < κ₁ → ηb ∈ Icc (0 : ℝ) 1 →
        CkPathOn (Mact χ s) annN' (Icc 0 ubar) h →
        (∀ u ∈ Icc (0 : ℝ) ubar, IsSymFieldOn annN' (h u)) →
        Lin.MemXFn (Mact χ s - 2) w₀ → (∀ᵐ x ∂(volume : Measure ℂ), (w₀ x).im = 0) →
        Sob.normH (Mact χ s - 2) w₀ ≤ Cn * κ₁ →
        (∀ u ∈ Icc (0 : ℝ) ubar, normCk (Mact χ s) annN' (h u) ≤
          Cn * κ₁ * Prelim.jap u ^ pW + ηb * ahat κ₁ (Eig.sigma χ G) u) →
        (∀ u ∈ Icc (0 : ℝ) ubar, ‖runCoef χ G w₀ h u‖ ≤ Cn * κ₁) →
        (∀ u ∈ Icc (0 : ℝ) ubar,
          ahat κ₁ (Eig.sigma χ G) u + Cn * κ₁ * Prelim.jap u ^ (pW + 2) ≤ 1) →
        ∃ wapp wapp' : ℝ → ℂ → ℂ,
          PathC (s + 1) ubar wapp ∧ PathC1 s ubar wapp wapp' ∧
          (∀ u ∈ Icc (0 : ℝ) ubar, ∀ᵐ x ∂(volume : Measure ℂ), (wapp u x).im = 0) ∧
          wapp 0 =ᵐ[volume] w₀ ∧
          ∀ u ∈ Icc (0 : ℝ) ubar,
            Sob.normH (s + 1) (wapp u) ≤ Capp * ahat κ₁ (Eig.sigma χ G) u ∧
            Sob.MemH s (wapp u - modeFn χ G
              (runCoef χ G w₀ h u * Complex.exp (Eig.lam χ G * u))) ∧
            Sob.normH s (wapp u - modeFn χ G
                (runCoef χ G w₀ h u * Complex.exp (Eig.lam χ G * u))) ≤
              Capp * ahat κ₁ (Eig.sigma χ G) u *
                (rhoOne (Eig.sigma χ G) σ' u + ηb +
                  (ahat κ₁ (Eig.sigma χ G) u + Cn * κ₁ * Prelim.jap u ^ (pW + 2))) ∧
            Sob.normH s (Rapp χ G h wapp wapp' u) ≤
              Capp * ahat κ₁ (Eig.sigma χ G) u *
                (ahat κ₁ (Eig.sigma χ G) u + Cn * κ₁ * Prelim.jap u ^ (pW + 2)) ^ NG χ s := by
  classical
  -- the constants (independent of the data)
  choose CSf hCSpos hCSspec using fun k : ℕ => Eig.propSemigroup_bounds χ hχ hN k hσ'
  obtain ⟨hσb, hσσ⟩ := WAppH.sigma_lower χ hχ hN
  set N := NG χ s with hNdef
  have hN2 : 2 ≤ N := le_max_left _ _
  have hMK : Mact χ s - 2 = s + N := by
    simp only [Mact, hNdef]
    omega
  have hKM : s + N ≤ Mact χ s := by
    simp only [Mact, hNdef]
    omega
  have hCn0 : 0 ≤ Cn := by linarith
  set σi := (Eig.sigb χ)⁻¹ with hσidef
  set Cl := Clin χ (s + N) σ' (CSf (s + N)) with hCldef
  set C0 := 2 * Eig.phiNormMax χ (s + N) * Cn + Cl * (Cn * WAppH.rhoBar χ σ' + 1) with hC0def
  have hCl : 0 ≤ Cl := WAppH.Clin_nonneg hσ' (hCSpos _).le
  have hC0 : 0 ≤ C0 := by
    have h1 := WAppH.phiNormMax_nonneg χ hχ hN (s + N)
    have h2 := WAppH.rhoBar_nonneg hσ'.2
    positivity
  set c := WAppH.hierConst CSf σi (s + N) C0 (N - 1) with hcdef
  set Kr := c.1 * (CB s * (2 * c.2.1 + c.1) + Ch s) with hKrdef
  refine ⟨|c.2.1| + |c.2.2| + |Cl| * Cn + |Cl| + |Kr|, by positivity, ?_⟩
  intro G ubar κ₁ ηb h w₀ hG hu hκ hηb hh hsym hw₀ hw₀r hw₀b hbd hc hsmall
  rw [hMK] at hw₀ hw₀b
  set σ := Eig.sigma χ G with hσdef
  have hσ : 0 < σ := lt_of_lt_of_le hσb (hσσ G hG)
  -- the standing hypotheses of the hierarchy
  have hd : WAppH.HierData χ G ubar κ₁ σ (Cn * κ₁) σi pW (Mact χ s) h CSf :=
    { hχ := hχ
      hN := hN
      hG := hG
      hu := hu
      hκ := hκ.le
      hσ := hσ
      hσi := inv_anti₀ hσb (hσσ G hG)
      hε := mul_nonneg hCn0 hκ.le
      hh := hh
      hsym := hsym
      hfield := fun u hu' => by
        have h1 := hbd u hu'
        have h2 : ηb * ahat κ₁ σ u ≤ ahat κ₁ σ u :=
          mul_le_of_le_one_left (WAppH.ahat_nonneg hκ.le u) hηb.2
        linarith
      hb := fun u hu' => hsmall u hu'
      hCS := fun k => (hCSpos k).le
      hS := fun k τ hτ w hw => ((hCSspec k) G hG τ hτ).2.2 w hw }
  -- the first term `w^{[1]} = wlin₀`
  have hwl := WAppH.wlin0_bound χ hχ hN hσ' (K := s + N) (by omega) (hCSpos (s + N)).le
    (hCSspec (s + N)) hCn hG hu hκ hηb hw₀ hw₀r hw₀b
    (WAppH.CkPathOn.mono_order hh hKM) hsym
    (fun u hu' => (normCk_mono_order (hh.1 u hu') hKM).trans (hbd u hu')) hc
  have hbase := WAppH.hier_base hd (K := s + N) (by omega) hKM hw₀ hw₀r (C0 := C0)
    (fun u hu' => (hwl u hu').1)
  -- the hierarchy after `N - 1` steps
  obtain ⟨-, -, -, hI, hres⟩ :=
    WAppH.hier_final hd (s := s) (N := N) (by omega) (by omega) hKM hC0 hbase
  obtain ⟨-, hPP, hP1, -, hPr, hP0, -, hPb, hPw1m, hPw1, -⟩ := hI
  set P := (WAppH.hier χ G h (s + N) (fun u => (wlin0 χ (s + N) G w₀ h u).fn)
    (fun u => Lin.Lfn χ G ((wlin0 χ (s + N) G w₀ h u).fn) + forcing χ h u) (N - 1)).2.1
    with hPdef
  set P' := (WAppH.hier χ G h (s + N) (fun u => (wlin0 χ (s + N) G w₀ h u).fn)
    (fun u => Lin.Lfn χ G ((wlin0 χ (s + N) G w₀ h u).fn) + forcing χ h u) (N - 1)).2.2
    with hP'def
  refine ⟨P, P', hPP, hP1, hPr, ?_, fun u hu' => ?_⟩
  · refine hP0.trans ?_
    show (wlin0 χ (s + N) G w₀ h 0).fn =ᵐ[volume] w₀
    rw [WAppH.wlin0_zero_fn χ hχ (s + N) G w₀ h]
    exact WAppH.MemXFn.toY_fn hw₀
  set X := runCoef χ G w₀ h u * Complex.exp (Eig.lam χ G * u) with hXdef
  set Capp := |c.2.1| + |c.2.2| + |Cl| * Cn + |Cl| + |Kr| with hCappdef
  have ha : 0 ≤ ahat κ₁ σ u := WAppH.ahat_nonneg hκ.le u
  have hbW : WAppH.bW κ₁ σ (Cn * κ₁) (pW + 2) u =
      ahat κ₁ σ u + Cn * κ₁ * Prelim.jap u ^ (pW + 2) := rfl
  have hb0 : 0 ≤ ahat κ₁ σ u + Cn * κ₁ * Prelim.jap u ^ (pW + 2) := by
    rw [← hbW]
    exact WAppH.bW_nonneg hκ.le (mul_nonneg hCn0 hκ.le) _ u
  obtain ⟨-, hdm, hdn⟩ := hwl u hu'
  have hPw1m' : Sob.MemH (s + 1) (P u - (wlin0 χ (s + N) G w₀ h u).fn) := hPw1m u hu'
  have hPw1' : Sob.normH (s + 1) (P u - (wlin0 χ (s + N) G w₀ h u).fn) ≤
      c.2.2 * ahat κ₁ σ u * (ahat κ₁ σ u + Cn * κ₁ * Prelim.jap u ^ (pW + 2)) := hPw1 u hu'
  have hsplit : P u - modeFn χ G X =
      (P u - (wlin0 χ (s + N) G w₀ h u).fn) + ((wlin0 χ (s + N) G w₀ h u).fn - modeFn χ G X) :=
    (sub_add_sub_cancel _ _ _).symm
  have hsum := (hPw1m'.mono_order (Nat.le_succ s)).add (hdm.mono_order (by omega : s ≤ s + N))
  rw [← hsplit] at hsum
  refine ⟨?_, hsum.1, ?_, ?_⟩
  · refine (hPb u hu').trans (le_capp_mul ?_ ha)
    have := abs_nonneg c.2.2
    have := abs_nonneg Cl
    have := abs_nonneg Kr
    have := mul_nonneg (abs_nonneg Cl) hCn0
    linarith [le_abs_self c.2.1]
  · have h1 := WAppH.normH_mono_order' (Nat.le_succ s) (P u - (wlin0 χ (s + N) G w₀ h u).fn)
    have h2 := WAppH.normH_mono_order' (by omega : s ≤ s + N)
      ((wlin0 χ (s + N) G w₀ h u).fn - modeFn χ G X)
    have h3 := window_approx_arith (D := c.2.1) (E := c.2.2) (Cl := Cl) (Cn := Cn) (Kr := Kr)
      ha (WAppH.rhoOne_nonneg σ σ' u) hηb.1 hb0 hCn0
    linarith [hsum.2]
  · refine (hres u hu').trans ?_
    rw [hbW]
    have hpow : 0 ≤ ahat κ₁ σ u * (ahat κ₁ σ u + Cn * κ₁ * Prelim.jap u ^ (pW + 2)) ^ N :=
      mul_nonneg ha (pow_nonneg hb0 _)
    have hKr : Kr ≤ Capp := by
      have := abs_nonneg c.2.1
      have := abs_nonneg c.2.2
      have := abs_nonneg Cl
      have := mul_nonneg (abs_nonneg Cl) hCn0
      linarith [le_abs_self Kr]
    have := mul_le_mul_of_nonneg_right hKr hpow
    calc Kr * ahat κ₁ σ u * (ahat κ₁ σ u + Cn * κ₁ * Prelim.jap u ^ (pW + 2)) ^ N =
          Kr * (ahat κ₁ σ u * (ahat κ₁ σ u + Cn * κ₁ * Prelim.jap u ^ (pW + 2)) ^ N) := by ring
      _ ≤ Capp * (ahat κ₁ σ u * (ahat κ₁ σ u + Cn * κ₁ * Prelim.jap u ^ (pW + 2)) ^ N) := this
      _ = _ := by ring

end OneRing

end NonUniqueEuler
