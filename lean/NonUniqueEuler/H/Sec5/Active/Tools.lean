import NonUniqueEuler.H.Sec5.Active.Basic
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec4.PropU
import NonUniqueEuler.I.Sec4.Annuli
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec5.Lambda
import NonUniqueEuler.I.Sec5.Setting
import NonUniqueEuler.I.Sec5.ReductionEq
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.ReIm
import NonUniqueEuler.I.Infra.CkNorm.Basic

/-!
# Helpers for `thm:active`: Sobolev, `C^k` and support tools

Helper of `P/Sec5/Active.lean` (fully proved, modulo the interface files it imports).

* `normH_mono_order'`: `‖f‖_{H^k} ≤ ‖f‖_{H^{k'}}` for `k ≤ k'` (no membership needed: the
  `H^k` norm is a sum over fewer multi-indices);
* `modeFn_add`, `modeFn_bound`: `2Re(Xφ_*)` is additive in `X`, lies in `H^k`, and
  `‖2Re(Xφ_*)‖_{H^k} ≤ 2 C_φ |X|`, `C_φ = Eig.phiNormMax χ k'`, `k ≤ k'`;
* `normCk_congr_of_eqOn`: `C^k(K)` norms only see a neighbourhood of `K`;
* `field_bound`: (Field) gives `‖h(u)‖_{C^M(N')} ≤ C₀κ⟨u⟩^p + η_b â(u)`;
* `sigma_facts`: `0 < σ_b ≤ σ(G) ≤ σ_max`;
* `norm_exp_lam`: `|e^{λu}| = e^{σu}`;
* `tsupport_ringPart_of_moves`, `ringSupported_of_moves`, `memXFn_w_of_moves`: a radial
  displacement `≤ a/16` keeps `supp ω_r` in `𝒩 ⊂ N`, hence `w(τ) ∈ X^k`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.ActiveH

open RingData

/-! ### Sobolev norms and the mode `2Re(Xφ_*)` -/

/-- `‖f‖_{H^k} ≤ ‖f‖_{H^{k'}}` for `k ≤ k'`, with no membership hypothesis. -/
theorem normH_mono_order' {k k' : ℕ} (hk : k ≤ k') (f : ℂ → ℂ) :
    Sob.normH k f ≤ Sob.normH k' f := by
  unfold Sob.normH Sob.normHOn
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum_of_subset_of_nonneg (Sob.multiIdx_mono hk)
    (fun _ _ _ => sq_nonneg _)

theorem modeFn_add (χ : ℝ → ℝ) (G : ℝ) (X Y : ℂ) :
    modeFn χ G (X + Y) = modeFn χ G X + modeFn χ G Y := by
  funext x
  simp only [modeFn, Pi.add_apply, add_mul, Complex.add_re]
  push_cast
  ring

theorem phiNormMax_nonneg (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    (k : ℕ) : 0 ≤ Eig.phiNormMax χ k := by
  obtain ⟨-, -, -, -, -, h, -⟩ := Eig.uniform_constants χ hχ hN
  obtain ⟨⟨G, -, hG⟩, -⟩ := h k
  rw [← hG]
  exact Sob.normH_nonneg _ _

/-- `2Re(Xφ_*(G)) ∈ H^k` and `‖2Re(Xφ_*(G))‖_{H^k} ≤ 2 C_φ |X|` with `C_φ = Eig.phiNormMax χ k'`,
`k ≤ k'`, `G ∈ [0,G₁]`. -/
theorem modeFn_bound (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {k k' : ℕ} (hk : k ≤ k') (X : ℂ) :
    Sob.MemH k (modeFn χ G X) ∧
      Sob.normH k (modeFn χ G X) ≤ 2 * Eig.phiNormMax χ k' * ‖X‖ := by
  have hphi : Sob.MemH k (Eig.phi χ G) := ((Eig.eigendata_phi χ hχ hN hG).2.1 k).1
  have hphiN : Sob.normH k (Eig.phi χ G) ≤ Eig.phiNormMax χ k' := by
    refine (normH_mono_order' hk _).trans ?_
    exact ((Eig.uniform_constants χ hχ hN).2.2.2.2.2.2.2.2 G hG).2.2.2.2 k'
  obtain ⟨hXm, hXn⟩ := hphi.const_smul X
  obtain ⟨hre, -, hsq⟩ := hXm.re_im
  set g : ℂ → ℂ := fun x => (((X • Eig.phi χ G) x).re : ℂ) with hg
  have hgle : Sob.normH k g ≤ Sob.normH k (X • Eig.phi χ G) := by
    have h1 : Sob.normH k g ^ 2 ≤ Sob.normH k (X • Eig.phi χ G) ^ 2 := by
      rw [← hsq]; nlinarith [sq_nonneg (Sob.normH k fun x => (((X • Eig.phi χ G) x).im : ℂ))]
    exact (pow_le_pow_iff_left₀ (Sob.normH_nonneg _ _) (Sob.normH_nonneg _ _)
      (by norm_num)).1 h1
  have heq : modeFn χ G X = (2 : ℂ) • g := by
    funext x
    simp only [modeFn, hg, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  obtain ⟨h2m, h2n⟩ := hre.const_smul (2 : ℂ)
  rw [heq]
  refine ⟨h2m, ?_⟩
  rw [h2n, hXn] at *
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  have := Sob.normH_nonneg k (Eig.phi χ G)
  calc 2 * Sob.normH k g ≤ 2 * (‖X‖ * Sob.normH k (Eig.phi χ G)) := by
        rw [hXn] at hgle; linarith
    _ ≤ 2 * Eig.phiNormMax χ k' * ‖X‖ := by
        have := norm_nonneg X
        nlinarith

/-- The triangle inequality around the mode: for `f ∈ H^k`,
`‖f‖_{H^k} ≤ ‖f - 2Re(Xφ_*)‖_{H^k} + 2C_φ|X|`. -/
theorem normH_le_modeFn (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {k k' : ℕ} (hk : k ≤ k') {f : ℂ → ℂ}
    (hf : Sob.MemH k f) (X : ℂ) :
    Sob.normH k f ≤ Sob.normH k (f - modeFn χ G X) + 2 * Eig.phiNormMax χ k' * ‖X‖ := by
  obtain ⟨hm, hn⟩ := modeFn_bound χ hχ hN hG hk X
  have hsub := (hf.sub hm).1
  have h := (hsub.add hm).2
  have hfe : f - modeFn χ G X + modeFn χ G X = f := by abel
  rw [hfe] at h
  linarith

/-- Changing the mode: for `f ∈ H^k`,
`‖f - 2Re(Xφ_*)‖_{H^k} ≤ ‖f - 2Re((X + Y)φ_*)‖_{H^k} + 2C_φ|Y|`. -/
theorem normH_sub_modeFn_le (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {k k' : ℕ} (hk : k ≤ k')
    {f : ℂ → ℂ} (hf : Sob.MemH k f) (X Y : ℂ) :
    Sob.normH k (f - modeFn χ G X) ≤
      Sob.normH k (f - modeFn χ G (X + Y)) + 2 * Eig.phiNormMax χ k' * ‖Y‖ := by
  obtain ⟨hmY, hnY⟩ := modeFn_bound χ hχ hN hG hk Y
  have hmXY := (modeFn_bound χ hχ hN hG hk (X + Y)).1
  have hsub := (hf.sub hmXY).1
  have h := (hsub.add hmY).2
  have hfe : f - modeFn χ G (X + Y) + modeFn χ G Y = f - modeFn χ G X := by
    rw [modeFn_add]; abel
  rw [hfe] at h
  linarith

/-! ### `C^k` norms and the field -/

/-- `C^k(K)` norms only see the values on an open set containing `K`. -/
theorem normCk_congr_of_eqOn {k : ℕ} {K U : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U)
    {f g : ℂ → ℂ} (hfg : ∀ x ∈ U, f x = g x) : normCk k K f = normCk k K g := by
  unfold normCk normCkE supIterDerivE
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  refine iSup_congr fun x => iSup_congr fun hx => ?_
  have h : f =ᶠ[𝓝 x] g := Filter.eventuallyEq_of_mem (hU.mem_nhds (hKU hx)) hfg
  rw [(h.iteratedFDeriv ℝ q).eq_of_nhds]

/-- (Field) gives `‖h(u)‖_{C^M(N')} ≤ C₀κ⟨u⟩^p + η_b â(u)` on `[0,ū]`. -/
theorem field_bound {χ : ℝ → ℝ} {s : ℕ} {c : RingConfig} {ubar C₀ κ ηb : ℝ}
    (hF : c.ActiveField χ s ubar C₀ κ ηb) :
    ∀ u ∈ Icc (0 : ℝ) ubar, normCk (Mact χ s) annN' (c.h u) ≤
      C₀ * κ * Prelim.jap u ^ pW + ηb * ahat κ (Eig.sigma χ c.G) u := by
  intro u hu
  obtain ⟨h₁, h₂, hh⟩ := hF
  obtain ⟨⟨U, hU, hNU, heq⟩, hm₁, hn₁, hm₂, hn₂⟩ := hh u hu
  rw [normCk_congr_of_eqOn hU hNU (g := h₁ u + h₂ u) (fun x hx => by
    rw [heq x hx]; rfl)]
  exact ((hm₁.add hm₂).2).trans (add_le_add hn₁ hn₂)

/-! ### `σ` and `λ` -/

/-- `0 < σ_b ≤ σ(G) ≤ σ_max` for `G ∈ [0,G₁]` (`prop:U`(a), `eq:Lambda`). -/
theorem sigma_facts (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) :
    0 < Eig.sigb χ ∧ Eig.sigb χ ≤ Eig.sigma χ G ∧ Eig.sigma χ G ≤ sigmaMax χ := by
  obtain ⟨-, -, ⟨G₀, -, hb, hmin⟩, hpos, -⟩ := Eig.propU_a χ hχ hN
  have hmax := (lambda_consts χ hχ hN (le_refl 3)).2.2.2.2
  refine ⟨by linarith, hb ▸ hmin G hG, hmax.2 ⟨G, hG, rfl⟩⟩

/-- `|e^{λu}| = e^{σu}`. -/
theorem norm_exp_lam (χ : ℝ → ℝ) (G u : ℝ) :
    ‖Complex.exp (Eig.lam χ G * u)‖ = Real.exp (Eig.sigma χ G * u) := by
  rw [Complex.norm_exp]
  simp [Eig.sigma, Complex.mul_re]

/-! ### Supports -/

/-- `0 < a < 1`. -/
theorem a_facts {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) : 0 < a ∧ a < 1 :=
  ⟨(ringFacts_of_admissible hχ).2.2.2.2.2.2.1, (ringFacts_of_admissible hχ).2.2.2.2.2.2.2⟩

/-- A radial displacement `≤ a/16` on `[0,t]` from `supp ω_r(0) ⊂ 𝒩₋` keeps `supp ω_r(τ)` in
`𝒩` (`lem:annuli`). -/
theorem tsupport_ringPart_of_moves {c : RingConfig} {T t δ : ℝ} (hc : c.Hyp T)
    (h0 : tsupport c.ring0 ⊆ annNm) (hmove : c.MovesRadially t δ) (hδ : δ ≤ a / 16) :
    ∀ τ ∈ Icc (0 : ℝ) t, tsupport (c.ringPart τ) ⊆ annNn := by
  intro τ hτ
  have hT' : ∀ y' ∈ tsupport (c.ringPart τ), ∃ y ∈ tsupport c.ring0, |‖y'‖ - ‖y‖| ≤ a / 16 := by
    intro y' hy'
    obtain ⟨y, hy, -, hyy⟩ := RingConfig.setting_movesRadially_tsupport hc hmove τ hτ y' hy'
    exact ⟨y, hy, hyy.trans hδ⟩
  exact (annuli_slack hT').2 h0

/-- The same, in `N`: `c.RingSupportedIn t annN`. -/
theorem ringSupported_of_moves {c : RingConfig} {T t δ : ℝ} (hc : c.Hyp T)
    (h0 : tsupport c.ring0 ⊆ annNm) (hmove : c.MovesRadially t δ) (hδ : δ ≤ a / 16) :
    c.RingSupportedIn t annN := by
  intro τ hτ
  obtain ⟨-, -, h3, h4, -⟩ := annuli_chain
  exact (tsupport_ringPart_of_moves hc h0 hmove hδ τ hτ).trans
    ((h3.trans interior_subset).trans h4)

/-- With a displacement `≤ a/16` on `[0,t]`, `0 < t ≤ T`, `w(τ) ∈ X^k` for `τ ∈ [0,t]`
(`lem:reduction`(3)). -/
theorem memXFn_w_of_moves (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {c : RingConfig} {T t δ : ℝ}
    (hc : c.Hyp T) (ht : 0 < t) (htT : t ≤ T) (h0 : tsupport c.ring0 ⊆ annNm)
    (hmove : c.MovesRadially t δ) (hδ : δ ≤ a / 16) (k : ℕ) :
    ∀ τ ∈ Icc (0 : ℝ) t, Lin.MemXFn k (c.w χ τ) := by
  have hct : c.Hyp t := hc.mono ht htT
  have hpe := (reduction_eq χ hχ hct (ringSupported_of_moves hc h0 hmove hδ)).2
  exact fun τ hτ => (hpe k).1.1 τ hτ

end NonUniqueEuler.OneRing.ActiveH
