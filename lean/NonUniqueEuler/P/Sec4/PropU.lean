import NonUniqueEuler.H.Sec4.PropU.Quant

/-!
# Proof: `prop:U` (regularity of the eigendata in `G`)

Proof of `I/Sec4/PropU.lean` (`04_ring.tex:1340-1354`, proof `:1355-1428`). Same declarations,
statements copied verbatim.

* (a) (restructuring R9: continuity instead of real-analyticity). The `λ_*(G)` are bounded on
  `[0,G₁]`: `λ_*(G)` lies in the spectrum of `L_3(G)` on `X^0_3` (`lam_SU`), so
  `|λ_*(G)| ≤ ‖L_3(G)‖`, and `L_3(G) = -3iΩ(·;0) - 3iGr⁻² + k_3𝒢_3` is affine in `G`
  (`radialMul_add`). Every cluster point of `λ_*(G')` as `G' → G` is a zero of `E_3(·;R_c²G)`
  (joint continuity, `evans_continuousOn`) with real part `≥ 211/2500`, hence equals `λ_*(G)` by
  the uniqueness in (N1) (`hypN_lamC`); by compactness `λ_*` is continuous
  (`H/Sec4/PropU/LamCont.lean`). Then `σ = Re λ_*` is continuous, its extrema on the compact
  `[0,G₁]` are attained, and `σ_b = σ(G₀) > 211/2500`.
* (b) In ring units, `ψ_*(G) = ψ(·;λ_*(G),G)` is continuous in `G` (Picard, `LinODE.continuousOn_sol`),
  all `r`-derivatives of `g_*(G)` are jointly continuous (`I/Sec4/PropU/GstarDeriv.lean`); so
  `n_*`, `J`, the representer norm `‖ℓ_*(G)‖` (radial integrals over compact intervals) and
  `‖φ_*(G)‖_{H^k}` (`I/Infra/AngularFourier/NormHCont.lean`) are continuous
  (`H/Sec4/PropU/Quant.lean`). The formulas `pout_* = -6e^{3ξ₂}ψ_*(ξ₂)/n_*`,
  `pin_3[φ_*] = -6e^{-3ξ₁}/n_*`, `β = n_*e^{-3ξ₁}/J` (`lem:adjoint`(3),(4)) give continuity, and
  `lem:adjoint`(5), `n_* > 0`, `J ≠ 0` give positivity.
* (c) `β pout_* = 6/∂_λE^Φ_3(λ_*;G)` from the same formulas and `thm:evans-simple`(1), and
  `∂_λE^Φ_3(λ;G) = ∂_λE_3(λ;R_c²G)` (`evans_units_deriv`) (`H/Sec4/PropU/Basic.lean`).
-/

noncomputable section

open Set ComplexConjugate

namespace NonUniqueEuler

namespace Eig

open RingData

namespace PropUH

/-- `pout_*(G) = n_*⁻¹ (-6 e^{3ξ₂} ψ_*(ξ₂))` (`lem:adjoint`(3)). -/
theorem pout_formula {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) :
    pout χ G = ((nstar χ G : ℝ) : ℂ)⁻¹ * (-2 * ((3 : ℕ) : ℂ) *
      ((Real.exp ((3 : ℕ) * (ringPhiSetting χ).ξ₂) : ℝ) : ℂ) *
        (ringPhiSetting χ).psi 3 (lam χ G) G (ringPhiSetting χ).ξ₂) := by
  obtain ⟨-, hz, hE, -, hE', -⟩ := eig_facts hχ hN hG
  rw [pout_eq hχ hN hG, (SectorSetting.adjoint_stream _ (ringPhiSetting_valid hχ) 3 (by norm_num)
    _ hz G hE hE').2.2.2.1]

/-- `β(G) = n_* e^{-3ξ₁}/J` (`lem:adjoint`(3),(4)). -/
theorem beta_formula {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) :
    beta χ G = ((nstar χ G : ℝ) : ℂ) * (-(-2 * ((3 : ℕ) : ℂ) *
      ((Real.exp (-((3 : ℕ) * (ringPhiSetting χ).ξ₁)) : ℝ) : ℂ)) / (2 * ((3 : ℕ) : ℂ) * J χ G)) := by
  obtain ⟨-, hz, hE, -, hE', -⟩ := eig_facts hχ hN hG
  have hS := ringPhiSetting_valid hχ
  rw [beta_eq, (SectorSetting.adjoint_beta _ hS 3 (by norm_num) _ hz G hE hE').1,
    (SectorSetting.adjoint_stream _ hS 3 (by norm_num) _ hz G hE hE').2.2.1]
  rfl

/-- `pout_*(G) ≠ 0` and `β(G) ≠ 0` (`lem:adjoint`(5)). -/
theorem pout_beta_ne_zero {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) : pout χ G ≠ 0 ∧ beta χ G ≠ 0 := by
  obtain ⟨-, hz, hE, -, hE', -⟩ := eig_facts hχ hN hG
  obtain ⟨hp, -, hb⟩ :=
    SectorSetting.adjoint_ne_zero _ (ringPhiSetting_valid hχ) 3 (by norm_num) _ hz G hE hE'
  have hn : ((nstar χ G : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (nstar_pos hχ hN hG).ne'
  rw [pout_eq hχ hN hG, beta_eq]
  exact ⟨mul_ne_zero (inv_ne_zero hn) hp, mul_ne_zero hn hb⟩

end PropUH

/-- **`prop:U`(a)** in the form of R9 (`04_ring.tex:1343-1345`): `λ_*` and `σ = Re λ_*` are
continuous on `[0,G₁]`, `σ_b = min σ` is attained, `σ_b > 211/2500`, and `max σ` is attained. -/
theorem propU_a (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (lam χ) (Icc 0 Gbar) ∧ ContinuousOn (sigma χ) (Icc 0 Gbar) ∧
      (∃ G₀ ∈ Icc (0 : ℝ) Gbar, sigb χ = sigma χ G₀ ∧ ∀ G ∈ Icc (0 : ℝ) Gbar, sigma χ G₀ ≤ sigma χ G) ∧
      211 / 2500 < sigb χ ∧
      ∃ G₁ ∈ Icc (0 : ℝ) Gbar, ∀ G ∈ Icc (0 : ℝ) Gbar, sigma χ G ≤ sigma χ G₁ := by
  have hlam := PropUH.lam_continuousOn hχ hN
  have hσ : ContinuousOn (sigma χ) (Icc 0 Gbar) := Complex.continuous_re.comp_continuousOn hlam
  have hne : (Icc (0 : ℝ) Gbar).Nonempty := ⟨0, le_rfl, PropUH.Gbar_nonneg⟩
  obtain ⟨G₀, hG₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hσ
  obtain ⟨G₁, hG₁, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hσ
  have hsigb : sigb χ = sigma χ G₀ := by
    refine IsLeast.csInf_eq ⟨mem_image_of_mem _ hG₀, ?_⟩
    rintro _ ⟨G, hG, rfl⟩
    exact isMinOn_iff.1 hmin G hG
  refine ⟨hlam, hσ, ⟨G₀, hG₀, hsigb, fun G hG => isMinOn_iff.1 hmin G hG⟩, ?_,
    ⟨G₁, hG₁, fun G hG => isMaxOn_iff.1 hmax G hG⟩⟩
  rw [hsigb]
  exact (PropUH.eig_facts hχ hN hG₀).1

/-- **`prop:U`(b)** (`04_ring.tex:1346-1349`): `|pout_*|`, `|pin_3[φ_*]|`, `|J|`, `|β|`,
`‖ℓ_*(G)‖_{(X^0)^*}` and `‖φ_*(G)‖_{H^k}` (`k ≥ 0`) are continuous on `[0,G₁]`, and the first four
are positive. -/
theorem propU_b (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (fun G => ‖pout χ G‖) (Icc 0 Gbar) ∧
      ContinuousOn (fun G => ‖pinPhi χ G‖) (Icc 0 Gbar) ∧
      ContinuousOn (fun G => ‖J χ G‖) (Icc 0 Gbar) ∧
      ContinuousOn (fun G => ‖beta χ G‖) (Icc 0 Gbar) ∧
      ContinuousOn (fun G => ‖ell χ 0 G‖) (Icc 0 Gbar) ∧
      (∀ k : ℕ, ContinuousOn (fun G => Sob.normH k (phi χ G)) (Icc 0 Gbar)) ∧
      ∀ G ∈ Icc (0 : ℝ) Gbar,
        0 < ‖pout χ G‖ ∧ 0 < ‖pinPhi χ G‖ ∧ 0 < ‖J χ G‖ ∧ 0 < ‖beta χ G‖ := by
  have hS := ringPhiSetting_valid hχ
  have hn := PropUH.nstar_continuousOn hχ hN
  have hnC : ContinuousOn (fun G => ((nstar χ G : ℝ) : ℂ)) (Icc 0 Gbar) :=
    Complex.continuous_ofReal.comp_continuousOn hn
  have hn0 : ∀ G ∈ Icc (0 : ℝ) Gbar, ((nstar χ G : ℝ) : ℂ) ≠ 0 := fun G hG =>
    Complex.ofReal_ne_zero.2 (PropUH.nstar_pos hχ hN hG).ne'
  have hJ := PropUH.J_continuousOn hχ hN
  -- `ψ_*(G)(ξ₂)` is continuous in `G`
  have hψ : ContinuousOn (fun G => (ringPhiSetting χ).psi 3 (lam χ G) G (ringPhiSetting χ).ξ₂)
      (Icc 0 Gbar) := by
    have hpath : ContinuousOn (fun G : ℝ => ((ringPhiSetting χ).ξ₂, lam χ G, G)) (Icc 0 Gbar) :=
      continuousOn_const.prodMk ((PropUH.lam_continuousOn hχ hN).prodMk continuousOn_id)
    have h0 := (SectorSetting.PropUH.psi_continuousOn_param _ hS 3).comp hpath
      fun G hG => ⟨mem_univ _, (PropUH.eig_facts hχ hN hG).2.1, mem_univ _⟩
    exact h0.congr fun G _ => rfl
  refine ⟨?_, ?_, hJ.norm, ?_, PropUH.normEll_continuousOn hχ hN,
    fun k => PropUH.normH_phi_continuousOn hχ hN k, fun G hG => ?_⟩
  · -- `pout_*`
    have h : ContinuousOn (fun G => ((nstar χ G : ℝ) : ℂ)⁻¹ * (-2 * ((3 : ℕ) : ℂ) *
        ((Real.exp ((3 : ℕ) * (ringPhiSetting χ).ξ₂) : ℝ) : ℂ) *
          (ringPhiSetting χ).psi 3 (lam χ G) G (ringPhiSetting χ).ξ₂)) (Icc 0 Gbar) :=
      (hnC.inv₀ hn0).mul (continuousOn_const.mul hψ)
    exact h.norm.congr fun G hG => by rw [PropUH.pout_formula hχ hN hG]
  · -- `pin_3[φ_*]`
    have h : ContinuousOn (fun G => ((-(6 * Real.exp (-3 * (ξL - ξR)) / nstar χ G) : ℝ) : ℂ))
        (Icc 0 Gbar) :=
      Complex.continuous_ofReal.comp_continuousOn
        (((continuousOn_const (c := 6 * Real.exp (-3 * (ξL - ξR)))).div hn
          fun G hG => (PropUH.nstar_pos hχ hN hG).ne').neg)
    exact h.norm.congr fun G hG => by rw [pinPhi_eq χ hχ hN hG]
  · -- `β`
    have h : ContinuousOn (fun G => ((nstar χ G : ℝ) : ℂ) * (-(-2 * ((3 : ℕ) : ℂ) *
        ((Real.exp (-((3 : ℕ) * (ringPhiSetting χ).ξ₁)) : ℝ) : ℂ)) /
          (2 * ((3 : ℕ) : ℂ) * J χ G))) (Icc 0 Gbar) :=
      hnC.mul (continuousOn_const.div (continuousOn_const.mul hJ) fun G hG =>
        mul_ne_zero (by norm_num) (PropUH.J_ne_zero hχ hN hG))
    exact h.norm.congr fun G hG => by rw [PropUH.beta_formula hχ hN hG]
  · -- positivity
    obtain ⟨hp, hb⟩ := PropUH.pout_beta_ne_zero hχ hN hG
    refine ⟨norm_pos_iff.2 hp, ?_, norm_pos_iff.2 (PropUH.J_ne_zero hχ hN hG), norm_pos_iff.2 hb⟩
    rw [pinPhi_eq χ hχ hN hG, norm_pos_iff, Complex.ofReal_ne_zero, neg_ne_zero]
    exact (div_pos (mul_pos (by norm_num) (Real.exp_pos _)) (PropUH.nstar_pos hχ hN hG)).ne'

/-- **`prop:U`(c)** (`04_ring.tex:1350-1352`): for `G ∈ [0,G₁]`,
`|β(G)| |pout_*(G)| = 6/|∂_λE_3(λ_*(G); R_c²G)|`, with `E_3` of Hypothesis (N). -/
theorem propU_c (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) :
    ‖beta χ G‖ * ‖pout χ G‖ = 6 / ‖deriv (fun z => evans χ 3 z (Rc ^ 2 * G)) (lam χ G)‖ :=
  PropUH.norm_beta_mul_norm_pout hχ hN hG

end Eig

end NonUniqueEuler
