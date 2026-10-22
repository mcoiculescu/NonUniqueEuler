import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.Active.Layer.LinPath
import NonUniqueEuler.I.Sec5.ActiveT1
import NonUniqueEuler.I.Sec5.LinearPart
import NonUniqueEuler.I.Sec5.Running
import NonUniqueEuler.I.Sec4.PropSemigroup
import NonUniqueEuler.H.Sec5.Active.Layer.Steps

/-!
# Proof: the initial layer of `thm:active` (`eq:A-layer` and its consequences)

Proof of `NonUniqueEuler/I/Sec5/Active/Layer.lean` (`05_single_ring.tex:953-1020`). Same
declaration (`active_layer`), statement copied verbatim.

**Structure.** Put `n = M - 2` (so `M - 1 = n + 1`).
* `C_L = C_lin(n+1)` of `lem:linear-part` for a constant `C_S` of `prop:semigroup` at level
  `n + 1 = M - 1` (independent of `C₀`).
* For `C₀ ≥ 1`: `t̄₁ = t̄₁(C₀)`, `E = e^{σ_max t̄₁}`, `C_f = C₀⟨t̄₁⟩^p + E` (so `‖h‖_{C^M(N')} ≤ C_fκ`
  on `[0, min(ū,t₁)]`), `C₃ = C_S E(C₀ + t̄₁C_∇(M-1)C_f)` (`‖wlin‖_{H^{M-1}} ≤ C₃κ`,
  `LayerH.wlin0_norm_le`), `R_c = C_B(n)C₃² + C_h(n)C_fC₃` (`‖R_app‖_{H^n} ≤ R_cκ²`,
  `LayerH.rapp_linPath_bound`), `C₄' = t̄₁e^{Λ(n)t̄₁}R_c` (`‖w - wlin‖_{H^n} ≤ C₄'κ²`),
  `C_d = t̄₁(C_f + C_BS(C₃ + C₄'))` (the displacement), `K = 1 + C_f + 2(C₃ + C₄') + 32C_d/a`,
  `κ_L = 1/K`, and the output constant `C₄ = C_d + C₄' + ‖ℓ_*‖C₄'`.
* The linear response `wlin = wlin₀` at level `n + 1` with `w₀ = w(0)` is an approximate solution
  in `C([0,ū];X^{n+1}) ∩ C¹([0,ū];X^n)` (`wlin0_path`, `I/Sec5/Active/Layer/LinPath.lean`).
* Continuity argument (`Continuity.bootstrap_le`) on `[0, min(ū,t₁)]` for the displacement
  `δ_r` (threshold `a/16`) and `‖w‖_{H^n}` (threshold `1`); the improvement step is
  `LayerH.layer_core` (`lem:energy` at level `n` with `w_app = wlin`, `lem:reduction`(2),
  `lem:bilinear`(4)).
* Conclusion: item 1 from the displacement bound; item 2 from `lem:linear-part` at level `n + 1`
  (`wlin = 2Re(ce^{λu}φ_*) + (1-R)wlin`) and `‖w - wlin‖_{H^n} ≤ C₄'κ²`; item 3 from
  `lem:running` (`ℓ_*(wlin(u)) = c(u)e^{λu}`) and `LayerH.norm_ellFn_sub_le`.

**Deviations**. (1) The two continuity arguments of the manuscript (first at level
`M-1` with `w_app = 0`, then the comparison at level `M-2` with `w_app = wlin`) are merged into one:
the comparison with `wlin` at level `n = M-2` already closes the bootstrap on `‖w‖_{H^{M-2}} ≤ 1`
(it gives `‖w‖_{H^{M-2}} ≤ C₃κ + C₄'κ² ≤ 1/2`), and `lem:energy` at level `M-2` only needs
`‖w‖_{H^{M-2}} ≤ 1`; the bound `‖w‖_{H^{M-1}} ≤ C^lay_1κ` is not needed. (2) The displacement
threshold of the bootstrap is `a/16` (the manuscript uses `a/64`); `lem:annuli` gives
`supp ω_r ⊂ 𝒩 ⊂ N` from `supp ω_r(0) ⊂ 𝒩₋`. (3) `C_L = C_lin(M-1)` (level of `wlin`) instead of
`C_lin(M-2)`; the statement only asks for some `C_L` independent of `C₀`. (4) `κ_L = 1/K` is an
explicit admissible value.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

set_option maxHeartbeats 1000000 in
/-- **The initial layer of `thm:active`** (`05_single_ring.tex:953-1020`, `eq:A-layer`). See the
module docstring: a constant `C_L ≥ 0` independent of `C₀`, and for every `C₀ ≥ 1` numbers
`κ_L > 0`, `C₄ ≥ 0`, such that under (Init), (Field) and `κ ≤ κ_L`, on `[0, min(ū, t₁)]` the
ring moves radially by at most `C₄κ`, `w - 2Re(ce^{λu}φ_*)` is bounded in `H^{M-2}` by
`C_L(C₀κ⟨u⟩^pe^{σ'u} + η_b â(u)) + C₄κ²`, and `|ℓ_*(w(u)) - c(u)e^{λu}| ≤ C₄κ²`. -/
theorem active_layer (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 3 ≤ s) {σ' : ℝ} (hσ' : σ' ∈ Ioo (9 / 200 : ℝ) (Eig.sigb χ)) :
    ∃ CL : ℝ, 0 ≤ CL ∧ ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ κL C₄ : ℝ, 0 < κL ∧ 0 ≤ C₄ ∧
      ∀ (c : RingConfig) (ubar κ ηb : ℝ), c.Hyp ubar → c.G ∈ Icc (0 : ℝ) Gbar →
        0 < κ → κ ≤ κL → ηb ∈ Icc (0 : ℝ) etaMax →
        c.ActiveInit χ s C₀ κ → c.ActiveField χ s ubar C₀ κ ηb →
        ∀ u ∈ Icc (0 : ℝ) (min ubar (tOne χ σ' C₀ c.G)),
          c.MovesRadially u (C₄ * κ) ∧
            Sob.normH (Mact χ s - 2) (c.w χ u - modeFn χ c.G
                (runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u))) ≤
              CL * (C₀ * κ * Prelim.jap u ^ pW * Real.exp (σ' * u) +
                ηb * ahat κ (Eig.sigma χ c.G) u) + C₄ * κ ^ 2 ∧
            ‖Eig.ellFn χ c.G (c.w χ u) -
                runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u)‖ ≤
              C₄ * κ ^ 2 := by
  classical
  /- ### Levels and structural constants -/
  have hM4 := add_four_le_Mact χ s
  set n := Mact χ s - 2 with hn
  have hn3 : 3 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hn1 : Mact χ s - 1 = n + 1 := by omega
  have hnM : n + 1 ≤ Mact χ s := by omega
  have hσ'0 : 0 < σ' := by linarith only [hσ'.1]
  obtain ⟨CS, hCS0, hCS⟩ := Eig.propSemigroup_bounds χ hχ hN (n + 1) hσ'
  have hCS' : IsSemigroupConst χ (n + 1) σ' CS := hCS
  have hCn1 := LayerH.Cnab_nonneg χ (n + 1)
  set CL := Clin χ (n + 1) σ' CS with hCL
  have hCL0 : 0 ≤ CL := by
    have h1 : 0 < Eig.sigb χ - σ' := by linarith only [hσ'.2]
    rw [hCL, Clin]
    positivity
  refine ⟨CL, hCL0, ?_⟩
  intro C₀ hC₀
  /- ### The constants of the layer -/
  have hC₀0 : 0 < C₀ := by linarith only [hC₀]
  set tb := tOneBar χ σ' C₀ with htb
  have htb0 : 0 ≤ tb := (tOneOf_spec hσ'.2 hC₀).1.le
  set Em := Real.exp (sigmaMax χ * tb) with hEm
  have hEm0 : 0 < Em := Real.exp_pos _
  set Cf := C₀ * Prelim.jap tb ^ pW + Em with hCf
  have hjtb : 1 ≤ Prelim.jap tb ^ pW := one_le_pow₀ (Prelim.one_le_jap tb)
  have hC₀Cf : C₀ ≤ Cf := by
    have : C₀ ≤ C₀ * Prelim.jap tb ^ pW := le_mul_of_one_le_right hC₀0.le hjtb
    rw [hCf]; linarith only [this, hEm0]
  have hCf0 : 0 ≤ Cf := by linarith only [hC₀Cf, hC₀0]
  set C3 := CS * Em * (C₀ + tb * (Eig.Cnab χ (n + 1) * Cf)) with hC3
  have hC30 : 0 ≤ C3 := by rw [hC3]; positivity
  have hCB0 : 0 ≤ CB n := (CB_pos n).le
  have hCh0 : 0 ≤ Ch n := (bilinear_Ch hn2).2
  set Rc := CB n * C3 * C3 + Ch n * Cf * C3 with hRc
  have hRc0 : 0 ≤ Rc := by rw [hRc]; positivity
  set Λ := Lam χ n with hΛ
  have hΛ0 : 0 ≤ Λ := (lambda_ge χ hχ hN hn3).2.le
  set C4 := tb * (Real.exp (Λ * tb) * Rc) with hC4
  have hC40 : 0 ≤ C4 := by rw [hC4]; positivity
  have hCBS := CBS_pos
  set Cd := tb * (Cf + CBS * (C3 + C4)) with hCd
  have hCd0 : 0 ≤ Cd := by rw [hCd]; positivity
  obtain ⟨ha0, ha1⟩ := LayerH.a_facts hχ
  set K := 1 + Cf + 2 * (C3 + C4) + 32 * Cd / a with hK
  have hKd : 0 ≤ 32 * Cd / a := by positivity
  have hK1 : 1 ≤ K := by rw [hK]; linarith only [hCf0, hC30, hC40, hKd]
  have hK0 : 0 < K := by linarith only [hK1]
  obtain ⟨-, -, -, -, ⟨⟨Gm, -, hGm⟩, -⟩, -⟩ := Eig.uniform_constants χ hχ hN
  have hEN : 0 ≤ Eig.ellNorm χ := hGm ▸ norm_nonneg (Eig.ell χ 0 Gm)
  refine ⟨1 / K, Cd + C4 + Eig.ellNorm χ * C4, by positivity, by positivity, ?_⟩
  /- ### Smallness -/
  intro c ubar κ ηb hc hG hκ hκL hηb hInit hField
  have hκK : κ * K ≤ 1 := by
    rw [le_div_iff₀ hK0] at hκL
    exact hκL
  have hsmall : ∀ X : ℝ, X ≤ K → X * κ ≤ 1 := by
    intro X hXK
    calc X * κ ≤ K * κ := mul_le_mul_of_nonneg_right hXK hκ.le
      _ = κ * K := mul_comm _ _
      _ ≤ 1 := hκK
  have hκ1 : κ ≤ 1 := by simpa using hsmall 1 hK1
  have hCfκ : Cf * κ ≤ 1 := hsmall Cf (by rw [hK]; linarith only [hC30, hC40, hKd])
  have hC3κ : C3 * κ ≤ 1 := hsmall C3 (by rw [hK]; linarith only [hCf0, hC30, hC40, hKd])
  have hWκ : (C3 + C4) * κ ≤ 1 / 2 := by
    have := hsmall (2 * (C3 + C4)) (by rw [hK]; linarith only [hCf0, hKd])
    linarith only [this]
  have hCdκ : Cd * κ ≤ a / 32 := by
    have h := hsmall (32 * Cd / a) (by rw [hK]; linarith only [hCf0, hC30, hC40])
    have he : 32 * Cd / a * κ = (32 * Cd * κ) / a := by ring
    rw [he, div_le_one ha0] at h
    linarith only [h]
  have hκsq : κ ^ 2 ≤ κ := by nlinarith only [hκ, hκ1]
  /- ### `σ`, `t₁` and the layer `[0, u₁]` -/
  obtain ⟨-, hσb_le, hσmax⟩ := LayerH.sigma_facts χ hχ hN hG
  have hσ0 : 0 ≤ Eig.sigma χ c.G := by linarith only [hσb_le, hσ'0, hσ'.2]
  have hσm0 : 0 ≤ sigmaMax χ := hσ0.trans hσmax
  have ht₁0 : 0 < tOne χ σ' C₀ c.G := (tOneOf_spec (lt_of_lt_of_le hσ'.2 hσb_le) hC₀).1
  have ht₁b : tOne χ σ' C₀ c.G ≤ tb := (active_tOne χ hχ hN hσ' hC₀ hG hκ).1
  have hubar : 0 < ubar := hc.T_pos
  set u₁ := min ubar (tOne χ σ' C₀ c.G) with hu₁
  have hu₁b : u₁ ≤ ubar := min_le_left _ _
  have hu₁t : u₁ ≤ tb := (min_le_right _ _).trans ht₁b
  have hI : ∀ u ∈ Icc (0 : ℝ) u₁, u ∈ Icc (0 : ℝ) ubar := fun u hu => ⟨hu.1, hu.2.trans hu₁b⟩
  /- ### The field on the layer -/
  have hRF := reduction_field hc
  have hpathM := hRF.2 (Mact χ s)
  have hpath := hRF.2 (n + 1)
  have hsym : ∀ u ∈ Icc (0 : ℝ) ubar, IsSymFieldOn annN' (c.h u) := by
    intro u hu
    obtain ⟨U, -, hNU, -, -, -, hsU, -⟩ := hRF.1 u hu
    exact fun x hx => hsU x (hNU hx)
  have hexp : ∀ u ∈ Icc (0 : ℝ) u₁, Real.exp (Eig.sigma χ c.G * u) ≤ Em := fun u hu =>
    Real.exp_le_exp.2 (mul_le_mul hσmax (hu.2.trans hu₁t) hu.1 hσm0)
  have hhM : ∀ u ∈ Icc (0 : ℝ) u₁, normCk (Mact χ s) annN' (c.h u) ≤ Cf * κ :=
    LayerH.field_on_layer hField hC₀0.le hκ.le hηb hu₁b hu₁t hσ0 hσmax
  have hhk : ∀ k ≤ Mact χ s, ∀ u ∈ Icc (0 : ℝ) u₁, normCk k annN' (c.h u) ≤ Cf * κ :=
    fun k hk u hu => (normCk_mono_order (hpathM.1 u (hI u hu)) hk).trans (hhM u hu)
  /- ### The initial datum and the linear response -/
  have hr : tsupport c.ring0 ⊆ annNm := hInit.2
  have hrN : tsupport c.ring0 ⊆ annN := by
    obtain ⟨-, h2, h3, h4, -⟩ := annuli_chain
    exact hr.trans (h2.trans ((h3.trans interior_subset).trans h4))
  have hX0 := LayerH.memXFn_pert0 hχ hc hrN (n + 1)
  have hreal0 : ∀ᵐ x ∂(volume : Measure ℂ), (c.pert0 χ x).im = 0 :=
    Filter.Eventually.of_forall (LayerH.pert0_im χ)
  have hw0n : Sob.normH (n + 1) (c.pert0 χ) ≤ C₀ * κ := by
    rw [← hn1]; exact hInit.1
  obtain ⟨happ, happ', hrealapp, happ0⟩ :=
    wlin0_path χ hχ hN (k := n) hG hubar hX0 hreal0 hpath hsym
  have hwappB : ∀ u ∈ Icc (0 : ℝ) u₁,
      Sob.normH (n + 1) (wlin0 χ (n + 1) c.G (c.pert0 χ) c.h u).fn ≤ C3 * κ :=
    LayerH.wlin_on_layer χ hχ hN hn2 hCS' hCS0.le hc hG hu₁b hu₁t hκ.le hCf0 hX0 hw0n
      (hhk (n + 1) hnM) hexp
  have hR := LayerH.rapp_on_layer χ hn2 hc hu₁b (wapp := fun u => (wlin0 χ (n + 1) c.G
    (c.pert0 χ) c.h u).fn) (fun τ hτ => happ.1 τ (hI τ hτ)) hwappB (hhk n (by omega))
  have hRκ : CB n * (C3 * κ) * (C3 * κ) + Ch n * (Cf * κ) * (C3 * κ) = Rc * κ ^ 2 := by
    rw [hRc]; ring
  rw [hRκ] at hR
  /- ### The improvement step and the continuity argument -/
  have hV : tb * (Real.exp (Lam χ n * tb) * (Rc * κ ^ 2)) = C4 * κ ^ 2 := by
    rw [hC4, hΛ]; ring
  have hC4κ : C4 * κ ^ 2 ≤ C4 * κ := mul_le_mul_of_nonneg_left hκsq hC40
  have hDisp : tb * (Cf * κ + CBS * (C3 * κ + C4 * κ ^ 2)) ≤ Cd * κ := by
    have h1 : CBS * (C3 * κ + C4 * κ ^ 2) ≤ CBS * ((C3 + C4) * κ) :=
      mul_le_mul_of_nonneg_left (by linarith only [hC4κ]) hCBS.le
    have h2 : Cf * κ + CBS * (C3 * κ + C4 * κ ^ 2) ≤ (Cf + CBS * (C3 + C4)) * κ := by
      linarith only [h1]
    calc tb * (Cf * κ + CBS * (C3 * κ + C4 * κ ^ 2)) ≤ tb * ((Cf + CBS * (C3 + C4)) * κ) :=
          mul_le_mul_of_nonneg_left h2 htb0
      _ = Cd * κ := by rw [hCd]; ring
  have core : ∀ t ∈ Icc (0 : ℝ) u₁, c.MovesRadially t (a / 16) →
      (∀ τ ∈ Icc (0 : ℝ) t, Sob.normH n (c.w χ τ) ≤ 1) →
      (∀ τ ∈ Icc (0 : ℝ) t, Sob.normH n (c.w χ τ -
          (wlin0 χ (n + 1) c.G (c.pert0 χ) c.h τ).fn) ≤ C4 * κ ^ 2) ∧
        (∀ τ ∈ Icc (0 : ℝ) t, Sob.normH n (c.w χ τ) ≤ 1 / 2) ∧
        c.MovesRadially t (Cd * κ) := by
    intro t ht hm hw1
    have hIt : ∀ τ ∈ Icc (0 : ℝ) t, τ ∈ Icc (0 : ℝ) u₁ := fun τ hτ => ⟨hτ.1, hτ.2.trans ht.2⟩
    obtain ⟨hv, hwB, hmD⟩ := LayerH.layer_core hχ hN hn3 hc (hI t ht) (ht.2.trans hu₁t) hG hr
      happ happ' hrealapp happ0 (W := C3 * κ) (H := Cf * κ) (R := Rc * κ ^ 2) hC3κ hCfκ
      (by positivity) (fun τ hτ => hwappB τ (hIt τ hτ)) (fun τ hτ => hhk (n + 1) hnM τ (hIt τ hτ))
      (fun τ hτ => hhk 0 (Nat.zero_le _) τ (hIt τ hτ)) (fun τ hτ => hR τ (hIt τ hτ)) hm hw1
    rw [hV] at hv hwB hmD
    exact ⟨hv, fun τ hτ => (hwB τ hτ).trans (by linarith only [hC4κ, hWκ]), hmD.mono hDisp⟩
  have hw00 : Sob.normH n (c.w χ 0) ≤ 1 := by
    rw [LayerH.w_zero hc χ]
    refine (LayerH.normH_mono_order' (Nat.le_succ n) _).trans (hw0n.trans ?_)
    have : C₀ * κ ≤ Cf * κ := mul_le_mul_of_nonneg_right hC₀Cf hκ.le
    linarith only [this, hCfκ]
  have hboot := LayerH.layer_bootstrap hχ hc hu₁b (D := Cd * κ) (by positivity)
    (by linarith only [hCdκ, ha0]) hw00 (fun t ht hm hw1 => (core t ht hm hw1).2)
  /- ### Conclusion -/
  intro u hu
  obtain ⟨hm, hw1⟩ := hboot u hu
  obtain ⟨hv, -, hmD⟩ := core u hu hm hw1
  have hvu := hv u ⟨hu.1, le_rfl⟩
  have huI := hI u hu
  have hκ2 : 0 ≤ κ ^ 2 := sq_nonneg κ
  have hmw : Sob.MemH n (c.w χ u) := LayerH.memH_w hχ hc u n
  have hmapp : Sob.MemH n (wlin0 χ (n + 1) c.G (c.pert0 χ) c.h u).fn :=
    (LayerH.Y_memH_fn (wlin0 χ (n + 1) c.G (c.pert0 χ) c.h u)).1.mono_order (Nat.le_succ n)
  have hC4le : C4 * κ ^ 2 ≤ (Cd + C4 + Eig.ellNorm χ * C4) * κ ^ 2 := by
    have : 0 ≤ (Cd + Eig.ellNorm χ * C4) * κ ^ 2 := by positivity
    linarith only [this]
  refine ⟨hmD.mono ?_, ?_, ?_⟩
  · -- item 1: the displacement
    have : 0 ≤ (C4 + Eig.ellNorm χ * C4) * κ := by positivity
    linarith only [this]
  · -- item 2: `lem:linear-part` and `‖w - wlin‖_{H^n} ≤ C₄'κ²`
    have hbd : ∀ v ∈ Icc (0 : ℝ) ubar, normCk (n + 1) annN' (c.h v) ≤
        C₀ * κ * Prelim.jap v ^ pW + ηb * κ * Real.exp (Eig.sigma χ c.G * v) := by
      intro v hv
      refine (normCk_mono_order (hpathM.1 v hv) hnM).trans
        ((LayerH.field_bound hField v hv).trans (le_of_eq ?_))
      unfold ahat; ring
    obtain ⟨hLP1, hLP2⟩ := linear_part χ hχ hN hσ' pW (k := n + 1) (by omega) hCS0.le hCS' hG
      hubar (by positivity : (0 : ℝ) ≤ C₀ * κ) hκ.le hηb.1 hX0 hreal0 hw0n hpath hsym hbd u huI
    have hae : (wlin0 χ (n + 1) c.G (c.pert0 χ) c.h u -
        Eig.R χ (n + 1) c.G (wlin0 χ (n + 1) c.G (c.pert0 χ) c.h u)).fn =ᵐ[volume]
        ((wlin0 χ (n + 1) c.G (c.pert0 χ) c.h u).fn - modeFn χ c.G
          (runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u))) := by
      filter_upwards [hLP1] with x hx
      rw [Pi.sub_apply, hx]
      ring
    have hmain := LayerH.normH_sub_modeFn_le hmw hmapp hae
    have h3 : ηb * ahat κ (Eig.sigma χ c.G) u = ηb * κ * Real.exp (Eig.sigma χ c.G * u) := by
      unfold ahat; ring
    rw [h3]
    linarith only [hmain, hvu, hLP2, hC4le]
  · -- item 3: `lem:running` and `|ℓ_*(w - wlin)| ≤ ‖ℓ_*‖‖w - wlin‖`
    obtain ⟨-, -, hell, -⟩ := running χ hχ hN (s := n + 1) hG hubar hX0 hreal0 hpath hsym u huI
    rw [← hell]
    have hsuppu : c.RingSupportedIn u annN := LayerH.ringSupported_of_moves hc hr hm le_rfl
    have hws : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → c.w χ u x = 0 := by
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      have h1 : c.ringPart u x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (hsuppu u ⟨hu.1, le_rfl⟩ h))
      have h2 : ringPhi χ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (LayerH.tsupport_ringPhi_subset_annN hχ h))
      simp [RingConfig.w, h1, h2]
    have hkey := LayerH.norm_ellFn_sub_le χ hχ hN hG hmw hmapp hws
      (LayerH.Y_fn_zero_outside (wlin0 χ (n + 1) c.G (c.pert0 χ) c.h u))
    have hellle : ‖Eig.ell χ 0 c.G‖ ≤ Eig.ellNorm χ :=
      ((Eig.uniform_constants χ hχ hN).2.2.2.2.2.2.2.2 c.G hG).2.2.2.1
    have hnn := Sob.normH_nonneg n (c.w χ u - (wlin0 χ (n + 1) c.G (c.pert0 χ) c.h u).fn)
    have h5 : ‖Eig.ell χ 0 c.G‖ *
        Sob.normH n (c.w χ u - (wlin0 χ (n + 1) c.G (c.pert0 χ) c.h u).fn) ≤
        Eig.ellNorm χ * (C4 * κ ^ 2) := mul_le_mul hellle hvu hnn hEN
    have h6 : Eig.ellNorm χ * (C4 * κ ^ 2) ≤ (Cd + C4 + Eig.ellNorm χ * C4) * κ ^ 2 := by
      have : 0 ≤ (Cd + C4) * κ ^ 2 := by positivity
      linarith only [this]
    exact hkey.trans (h5.trans h6)

end OneRing

end NonUniqueEuler
