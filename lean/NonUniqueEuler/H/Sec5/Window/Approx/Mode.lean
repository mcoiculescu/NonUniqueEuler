import NonUniqueEuler.H.Sec5.Window.Approx.Scalar
import NonUniqueEuler.H.Sec5.Window.Approx.Bridge
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec4.PropU
import NonUniqueEuler.I.Sec5.LinearPart
import NonUniqueEuler.I.Infra.Sobolev.ReIm

/-!
# Helpers for `window_approx`: the mode and the first term `w^{[1]}`

Helper of `P/Sec5/Window/Approx.lean` (`05_single_ring.tex:758-764`, the case `j = 1` of
`eq:W-hier`). Namespace `NonUniqueEuler.OneRing.WAppH`.

* `modeFn_bound` (copy of `ActiveH.modeFn_bound`): `‖2Re(Xφ_*)‖_{H^k} ≤ 2C_φ|X|`;
* `sigma_lower`: `0 < σ_b ≤ σ(G)` (`prop:U`); `norm_exp_lam`: `|e^{λu}| = e^{σu}`;
* `rhoBar`, `rhoOne_le`: `ρ₁(u) ≤ ρ̄ = p! e^{σ_b-σ'}/(σ_b-σ')^p` (`eq:W-const`);
* `wlin0_bound`: for the linear response `w^{[1]} = wlin₀` (`lem:linear-part` at
  `A = C♮κ₁`, `κ = κ₁`), `‖w^{[1]}‖_{H^K} ≤ (2C_φC♮ + C_lin(C♮ρ̄ + 1)) â₁`, and
  `w^{[1]} - 2Re(c e^{λu}φ_*) ∈ H^K` with `H^K` norm `≤ C_lin(C♮ â₁ρ₁ + η_b â₁)`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.WAppH

open RingData Sect Sob Prelim

theorem phiNormMax_nonneg (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    (k : ℕ) : 0 ≤ Eig.phiNormMax χ k := by
  obtain ⟨-, -, -, -, -, h, -⟩ := Eig.uniform_constants χ hχ hN
  obtain ⟨⟨G, -, hG⟩, -⟩ := h k
  rw [← hG]
  exact normH_nonneg _ _

/-- `2Re(Xφ_*(G)) ∈ H^k` and `‖2Re(Xφ_*(G))‖_{H^k} ≤ 2 C_φ |X|`, `C_φ = Eig.phiNormMax χ k'`,
`k ≤ k'` (copy of `ActiveH.modeFn_bound`). -/
theorem modeFn_bound (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {k k' : ℕ} (hk : k ≤ k') (X : ℂ) :
    MemH k (modeFn χ G X) ∧ normH k (modeFn χ G X) ≤ 2 * Eig.phiNormMax χ k' * ‖X‖ := by
  have hphi : MemH k (Eig.phi χ G) := ((Eig.eigendata_phi χ hχ hN hG).2.1 k).1
  have hphiN : normH k (Eig.phi χ G) ≤ Eig.phiNormMax χ k' := by
    refine (normH_mono_order' hk _).trans ?_
    exact ((Eig.uniform_constants χ hχ hN).2.2.2.2.2.2.2.2 G hG).2.2.2.2 k'
  obtain ⟨hXm, hXn⟩ := hphi.const_smul X
  obtain ⟨hre, -, hsq⟩ := hXm.re_im
  set g : ℂ → ℂ := fun x => (((X • Eig.phi χ G) x).re : ℂ) with hg
  have hgle : normH k g ≤ normH k (X • Eig.phi χ G) := by
    have h1 : normH k g ^ 2 ≤ normH k (X • Eig.phi χ G) ^ 2 := by
      rw [← hsq]; nlinarith [sq_nonneg (normH k fun x => (((X • Eig.phi χ G) x).im : ℂ))]
    exact (pow_le_pow_iff_left₀ (normH_nonneg _ _) (normH_nonneg _ _) (by norm_num)).1 h1
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
  have := normH_nonneg k (Eig.phi χ G)
  calc 2 * normH k g ≤ 2 * (‖X‖ * normH k (Eig.phi χ G)) := by
        rw [hXn] at hgle; linarith
    _ ≤ 2 * Eig.phiNormMax χ k' * ‖X‖ := by
        have := norm_nonneg X
        nlinarith

/-- `0 < σ_b ≤ σ(G)` on `[0,G₁]` (`prop:U`). -/
theorem sigma_lower (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    0 < Eig.sigb χ ∧ ∀ G ∈ Icc (0 : ℝ) Gbar, Eig.sigb χ ≤ Eig.sigma χ G := by
  obtain ⟨-, -, ⟨G₀, -, hb, hmin⟩, hpos, -⟩ := Eig.propU_a χ hχ hN
  exact ⟨by linarith, fun G hG => hb ▸ hmin G hG⟩

/-- `|e^{λu}| = e^{σu}`. -/
theorem norm_exp_lam (χ : ℝ → ℝ) (G u : ℝ) :
    ‖Complex.exp (Eig.lam χ G * u)‖ = Real.exp (Eig.sigma χ G * u) := by
  rw [Complex.norm_exp]
  simp [Eig.sigma, Complex.mul_re]

/-- `ρ̄ = p! e^{σ_b - σ'}/(σ_b - σ')^p` (a bound for `sup_{u ≥ 0} ⟨u⟩^p e^{-(σ_b-σ')u}`). -/
def rhoBar (χ : ℝ → ℝ) (σ' : ℝ) : ℝ :=
  (pW.factorial : ℝ) * Real.exp (Eig.sigb χ - σ') / (Eig.sigb χ - σ') ^ pW

theorem rhoBar_nonneg {χ : ℝ → ℝ} {σ' : ℝ} (hσ' : σ' < Eig.sigb χ) : 0 ≤ rhoBar χ σ' := by
  unfold rhoBar
  have : 0 < Eig.sigb χ - σ' := by linarith
  positivity

/-- `ρ₁(u) = ⟨u⟩^p e^{-(σ-σ')u} ≤ ρ̄` for `u ≥ 0` and `σ ≥ σ_b > σ'`. -/
theorem rhoOne_le {χ : ℝ → ℝ} {σ σ' u : ℝ} (hσ' : σ' < Eig.sigb χ) (hσ : Eig.sigb χ ≤ σ)
    (hu : 0 ≤ u) : rhoOne σ σ' u ≤ rhoBar χ σ' := by
  unfold rhoOne rhoBar
  have hδ : 0 < Eig.sigb χ - σ' := by linarith
  have h1 : Real.exp (-((σ - σ') * u)) ≤ Real.exp (-((Eig.sigb χ - σ') * u)) := by
    apply Real.exp_le_exp.2
    nlinarith
  calc jap u ^ pW * Real.exp (-((σ - σ') * u)) ≤
        jap u ^ pW * Real.exp (-((Eig.sigb χ - σ') * u)) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg (jap_nonneg u) _)
    _ ≤ _ := jap_pow_mul_exp_le hδ pW hu

theorem rhoOne_nonneg (σ σ' u : ℝ) : 0 ≤ rhoOne σ σ' u :=
  mul_nonneg (pow_nonneg (jap_nonneg u) _) (Real.exp_pos _).le

/-- `κ⟨u⟩^p e^{σ'u} = â₁(u)ρ₁(u)`. -/
theorem ahat_mul_rhoOne (κ σ σ' u : ℝ) :
    κ * jap u ^ pW * Real.exp (σ' * u) = ahat κ σ u * rhoOne σ σ' u := by
  unfold ahat rhoOne
  have : Real.exp (σ' * u) = Real.exp (σ * u) * Real.exp (-((σ - σ') * u)) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]
  ring

theorem Clin_nonneg {χ : ℝ → ℝ} {k : ℕ} {σ' CS : ℝ} (hσ' : σ' ∈ Ioo (9 / 200 : ℝ) (Eig.sigb χ))
    (hCS : 0 ≤ CS) : 0 ≤ Clin χ k σ' CS := by
  unfold Clin
  have h1 : 0 < σ' := by linarith [hσ'.1]
  have h2 : 0 < Eig.sigb χ - σ' := by linarith [hσ'.2]
  have h3 : 0 ≤ Eig.Cnab χ k := by
    unfold Eig.Cnab
    exact mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (normH_nonneg _ _)
  positivity

/-- **The first term of the hierarchy** (`05_single_ring.tex:758-764`). -/
theorem wlin0_bound (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {σ' : ℝ} (hσ' : σ' ∈ Ioo (9 / 200 : ℝ) (Eig.sigb χ)) {K : ℕ} (hK : 2 ≤ K)
    {CS : ℝ} (hCS0 : 0 ≤ CS) (hCS : IsSemigroupConst χ K σ' CS) {Cn : ℝ} (hCn : 1 ≤ Cn)
    {G ubar κ₁ ηb : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) (hu : 0 < ubar) (hκ : 0 < κ₁)
    (hηb : ηb ∈ Icc (0 : ℝ) 1) {w₀ : ℂ → ℂ} (hw₀ : Lin.MemXFn K w₀)
    (hw₀r : ∀ᵐ x ∂(volume : Measure ℂ), (w₀ x).im = 0) (hw₀b : normH K w₀ ≤ Cn * κ₁)
    {h : ℝ → ℂ → ℂ} (hh : CkPathOn K annN' (Icc 0 ubar) h)
    (hsym : ∀ u ∈ Icc (0 : ℝ) ubar, IsSymFieldOn annN' (h u))
    (hbd : ∀ u ∈ Icc (0 : ℝ) ubar, normCk K annN' (h u) ≤
      Cn * κ₁ * jap u ^ pW + ηb * ahat κ₁ (Eig.sigma χ G) u)
    (hc : ∀ u ∈ Icc (0 : ℝ) ubar, ‖runCoef χ G w₀ h u‖ ≤ Cn * κ₁) :
    ∀ u ∈ Icc (0 : ℝ) ubar,
      normH K ((wlin0 χ K G w₀ h u).fn) ≤
          (2 * Eig.phiNormMax χ K * Cn + Clin χ K σ' CS * (Cn * rhoBar χ σ' + 1)) *
            ahat κ₁ (Eig.sigma χ G) u ∧
        MemH K ((wlin0 χ K G w₀ h u).fn -
          modeFn χ G (runCoef χ G w₀ h u * Complex.exp (Eig.lam χ G * u))) ∧
        normH K ((wlin0 χ K G w₀ h u).fn -
            modeFn χ G (runCoef χ G w₀ h u * Complex.exp (Eig.lam χ G * u))) ≤
          Clin χ K σ' CS * (Cn * (ahat κ₁ (Eig.sigma χ G) u * rhoOne (Eig.sigma χ G) σ' u) +
            ηb * ahat κ₁ (Eig.sigma χ G) u) := by
  intro u hu'
  set σ := Eig.sigma χ G with hσdef
  have hbd' : ∀ u ∈ Icc (0 : ℝ) ubar, normCk K annN' (h u) ≤
      Cn * κ₁ * jap u ^ pW + ηb * κ₁ * Real.exp (Eig.sigma χ G * u) := fun u hu => by
    have := hbd u hu
    simp only [ahat] at this
    linarith [mul_assoc ηb κ₁ (Real.exp (Eig.sigma χ G * u))]
  obtain ⟨hdec, hnorm⟩ := linear_part χ hχ hN hσ' pW hK hCS0 hCS hG hu
    (by positivity : (0 : ℝ) ≤ Cn * κ₁) hκ.le hηb.1 hw₀ hw₀r hw₀b hh hsym hbd' u hu'
  set W := wlin0 χ K G w₀ h u with hWdef
  set X := runCoef χ G w₀ h u * Complex.exp (Eig.lam χ G * u) with hXdef
  have hdiff : W.fn - modeFn χ G X =ᵐ[volume] (W - Eig.R χ K G W).fn := by
    filter_upwards [hdec] with x hx
    simp only [Pi.sub_apply, hx]
    ring
  obtain ⟨hRm, hRn⟩ := Y_memH_fn (W - Eig.R χ K G W)
  obtain ⟨hDm, hDn⟩ := hRm.congr_ae hdiff.symm
  have hrw : Cn * κ₁ * jap u ^ pW * Real.exp (σ' * u) + ηb * κ₁ * Real.exp (σ * u) =
      Cn * (ahat κ₁ σ u * rhoOne σ σ' u) + ηb * ahat κ₁ σ u := by
    rw [← ahat_mul_rhoOne κ₁ σ σ' u]
    unfold ahat
    ring
  have hbound2 : normH K (W.fn - modeFn χ G X) ≤
      Clin χ K σ' CS * (Cn * (ahat κ₁ σ u * rhoOne σ σ' u) + ηb * ahat κ₁ σ u) := by
    rw [hDn, hRn, ← hrw]
    exact hnorm
  refine ⟨?_, hDm, hbound2⟩
  -- the bound of `w^{[1]}`
  obtain ⟨hMm, hMn⟩ := modeFn_bound χ hχ hN hG (le_refl K) X
  have hsplit := hDm.add hMm
  have e : W.fn - modeFn χ G X + modeFn χ G X = W.fn := sub_add_cancel _ _
  rw [e] at hsplit
  have hX : ‖X‖ ≤ Cn * ahat κ₁ σ u := by
    rw [hXdef, norm_mul, norm_exp_lam]
    have h1 := hc u hu'
    calc ‖runCoef χ G w₀ h u‖ * Real.exp (σ * u) ≤ Cn * κ₁ * Real.exp (σ * u) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Cn * ahat κ₁ σ u := by unfold ahat; ring
  obtain ⟨hσb, hσσ⟩ := sigma_lower χ hχ hN
  have hρ := rhoOne_le (σ := σ) hσ'.2 (hσσ G hG) hu'.1
  have hClin := Clin_nonneg (k := K) hσ' hCS0
  have hphi := phiNormMax_nonneg χ hχ hN K
  have ha := ahat_nonneg hκ.le (σ := σ) u
  have hCn0 : 0 ≤ Cn := by linarith
  have h1 : 2 * Eig.phiNormMax χ K * ‖X‖ ≤ 2 * Eig.phiNormMax χ K * (Cn * ahat κ₁ σ u) :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have h2 : Cn * (ahat κ₁ σ u * rhoOne σ σ' u) + ηb * ahat κ₁ σ u ≤
      (Cn * rhoBar χ σ' + 1) * ahat κ₁ σ u := by
    have := mul_le_mul_of_nonneg_left hρ (mul_nonneg hCn0 ha)
    have := mul_le_mul_of_nonneg_right hηb.2 ha
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 hClin
  calc normH K W.fn ≤ normH K (W.fn - modeFn χ G X) + normH K (modeFn χ G X) := hsplit.2
    _ ≤ Clin χ K σ' CS * (Cn * (ahat κ₁ σ u * rhoOne σ σ' u) + ηb * ahat κ₁ σ u) +
        2 * Eig.phiNormMax χ K * (Cn * ahat κ₁ σ u) := add_le_add hbound2 (hMn.trans h1)
    _ ≤ Clin χ K σ' CS * ((Cn * rhoBar χ σ' + 1) * ahat κ₁ σ u) +
        2 * Eig.phiNormMax χ K * (Cn * ahat κ₁ σ u) := by linarith
    _ = _ := by ring

end NonUniqueEuler.OneRing.WAppH
