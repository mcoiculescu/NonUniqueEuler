import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec4.EvansBasic
import NonUniqueEuler.I.Sec4.PropSU
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Infra.Polar.RadialDeriv
import NonUniqueEuler.I.Sec2.PolarConvention
import NonUniqueEuler.H.Sec5.Seed.Field.Calc

/-!
# Proof: the seed field `V` of `lem:seed` and `eq:seed-first`

Proof of `I/Sec5/Seed/Field.lean` (`05_single_ring.tex:1152-1191`).

Construction (as in the manuscript, with `h(r) = c(r) g_s(r) r⁻³`):
* `g_s(r) = n_*⁻¹ M_λ(r) ψ_*(log r)` is `C^∞` on `(0,∞)` (`seedProf_contDiffOn`: `psi_spec`,
  `contDiffOn_Omega`, `Re(λ + 3iΩ) = Re λ > 0` by `lam_SU`);
* `c ∈ C^∞(ℝ)`, `c = 1` on `[a,1]`, `tsupport c ⊆ [3a/4, 1 + a/4]` (`SeedFieldH.exists_cutoff`);
* `ψ_seed(x) = -2 Re(c(|x|) g_s(|x|) |x|⁻³ x³)`, `V = ∇^⊥ψ_seed`, `K = {x | |x| ∈ tsupport c}`.

`eq:seed-first`: `DΦ(y)v = Φ'(r) ⟨y, v⟩/r` (`Polar.hasFDerivAt_comp_norm`), `⟨y, V y⟩ = -∂_θψ_seed(y)`
(`Prelim.inner_perpGrad_radial_angular`), `∂_θψ_seed(y) = -2 Re(3i c g_s r⁻³ y³)`
(`hasDerivAt_re_mul_rot_pow`), and `c = 1` where `Φ' ≠ 0` (`ringPhiSetting_valid`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff

namespace NonUniqueEuler

namespace OneRing

open RingData

namespace SeedFieldH

/-- `G = 0` is an admissible circulation: `0 ≤ Ḡ`. -/
theorem zero_mem_Icc_Gbar : (0 : ℝ) ∈ Icc (0 : ℝ) Gbar := by
  refine ⟨le_rfl, ?_⟩
  unfold Gbar
  positivity

/-- `Re λ_*(0) > 0`. -/
theorem lam_re_pos (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    0 < (Eig.lam χ 0).re := by
  have h := (Eig.lam_SU χ hχ hN zero_mem_Icc_Gbar 0).1
  linarith

/-- The seed profile `g_s(r) r⁻³ = n_*⁻¹ M_λ(r) ψ_*(log r) r⁻³` is `C^∞` on `(0,∞)`
(`05_single_ring.tex:1162-1166`). -/
theorem seedProf_contDiffOn (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) :
    ContDiffOn ℝ ∞ (fun r : ℝ => ((Eig.nstar χ 0 : ℝ) : ℂ)⁻¹ *
      ((ringPhiSetting χ).Mres (3 : ℕ) (Eig.lam χ 0) 0 r *
        (ringPhiSetting χ).psi 3 (Eig.lam χ 0) 0 (Real.log r)) * ((r : ℂ) ^ 3)⁻¹) (Ioi 0) := by
  set S := ringPhiSetting χ
  have hS : S.Valid := ringPhiSetting_valid hχ
  have hlam := lam_re_pos χ hχ hN
  have hψ : ContDiff ℝ ∞ (S.psi 3 (Eig.lam χ 0) 0) :=
    (SectorSetting.psi_spec S hS 3 (by norm_num) (Eig.lam χ 0) hlam 0).2.2.2.1
  have hΩ : ContDiffOn ℝ ∞ (S.Omega 0) (Ioi 0) := SectorSetting.contDiffOn_Omega S hS 0
  have hden : ContDiffOn ℝ ∞ (fun r : ℝ => Eig.lam χ 0 +
      Complex.I * (((3 : ℕ) : ℤ) : ℂ) * ((S.Omega 0 r : ℝ) : ℂ)) (Ioi 0) :=
    contDiffOn_const.add (contDiffOn_const.mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn hΩ))
  have hM : ContDiffOn ℝ ∞ (fun r : ℝ => S.Mres (3 : ℕ) (Eig.lam χ 0) 0 r) (Ioi 0) := by
    refine hden.inv ?_
    intro r _ h0
    have h1 := congrArg Complex.re h0
    simp at h1
    linarith
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi 0) :=
    Real.contDiffOn_log.mono fun r hr => ne_of_gt hr
  have hP : ContDiffOn ℝ ∞ (fun r : ℝ => S.psi 3 (Eig.lam χ 0) 0 (Real.log r)) (Ioi 0) :=
    hψ.comp_contDiffOn hlog
  have hinv : ContDiffOn ℝ ∞ (fun r : ℝ => ((r : ℂ) ^ 3)⁻¹) (Ioi 0) := by
    refine (Complex.ofRealCLM.contDiff.pow 3).contDiffOn.inv ?_
    intro r hr
    exact pow_ne_zero 3 (Complex.ofReal_ne_zero.2 (ne_of_gt hr))
  exact (contDiffOn_const.mul (hM.mul hP)).mul hinv

/-- `∂_θ` of `Re(h₀ y³)`: `d/dθ Re(h₀ (O_θ y)³)|_{θ=0} = Re(3i h₀ y³)`. -/
theorem hasDerivAt_re_mul_rot_pow (h₀ y : ℂ) :
    HasDerivAt (fun θ : ℝ => (h₀ * (rot θ y) ^ 3).re) (3 * Complex.I * h₀ * y ^ 3).re 0 := by
  have e1 : HasDerivAt (fun w : ℂ => Complex.exp (w * Complex.I) * y)
      (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) * Complex.I * y) ((0 : ℝ) : ℂ) :=
    ((hasDerivAt_mul_const Complex.I).cexp).mul_const y
  have e2 := (e1.fun_pow 3).const_mul h₀
  have hval : h₀ * (((3 : ℕ) : ℂ) * (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) * y) ^ (3 - 1) *
      (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) * Complex.I * y)) = 3 * Complex.I * h₀ * y ^ 3 := by
    simp
    ring
  exact (e2.congr_deriv hval).real_of_complex

/-- The ring is radial: `Φ(x) = Φ(|x|)`. -/
theorem ringPhi_eq_comp_norm {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    ringPhi χ = fun x => (ringPhiSetting χ).omR ‖x‖ := by
  have hrad := (ringFacts_of_admissible hχ).2.2.1
  funext x
  have hx : rot (Complex.arg x) ((‖x‖ : ℝ) : ℂ) = x := by
    rw [rot, mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I x
  show ringPhi χ x = ringPhi χ ((‖x‖ : ℝ) : ℂ)
  conv_lhs => rw [← hx]
  exact hrad _ _

/-- `DΦ(y)v = Φ'(|y|) ⟨y, v⟩/|y|` for `y ≠ 0`. -/
theorem fderiv_ringPhi_apply {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {y : ℂ} (hy : y ≠ 0)
    (v : ℂ) :
    fderiv ℝ (ringPhi χ) y v =
      (ringPhiSetting χ).dom ‖y‖ / ‖y‖ * inner ℝ y v := by
  have hΦ : ContDiff ℝ ∞ (ringPhi χ) := (ringFacts_of_admissible hχ).1
  have hd : DifferentiableAt ℝ (ringPhiSetting χ).omR ‖y‖ := by
    have := ((hΦ.differentiable (by simp)) _).comp ‖y‖
      Complex.ofRealCLM.differentiableAt
    exact this
  have hF := Polar.hasFDerivAt_comp_norm hy hd.hasDerivAt
  rw [ringPhi_eq_comp_norm hχ, hF.fderiv]
  simp [SectorSetting.dom]

end SeedFieldH

/-- **The seed field** (`05_single_ring.tex:1152-1191`, step 1 of `lem:seed` and
`eq:seed-first`). Assume (N1)–(N3). There are a `C^∞` vector field `V` and a compact
`K ⊆ {a/2 < |y| < 2}` with `V = 0` off `K`, `div V = 0`, `V ∘ O = O ∘ V` (`O = O_{2π/3}`) and
`V·∇Φ = 2 Re φ_*(0)`. -/
theorem seedField_exists (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ∃ (V : ℂ → ℂ) (K : Set ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧ IsCompact K ∧
      K ⊆ {y : ℂ | a / 2 < ‖y‖ ∧ ‖y‖ < 2} ∧ (∀ y ∉ K, V y = 0) ∧
      (∀ x : ℂ, Prelim.divergence V x = 0) ∧
      (∀ x : ℂ, V (rot (2 * Real.pi / 3) x) = rot (2 * Real.pi / 3) (V x)) ∧
      ∀ y : ℂ, fderiv ℝ (ringPhi χ) y (V y) = 2 * (Eig.phi χ 0 y).re := by
  have hRF := ringFacts_of_admissible hχ
  have ha : 0 < a := hRF.2.2.2.2.2.2.1
  have ha1 : a < 1 := hRF.2.2.2.2.2.2.2
  obtain ⟨c, hc, hc1, hcs⟩ := SeedFieldH.exists_cutoff ha ha1
  set f : ℝ → ℂ := fun r => ((Eig.nstar χ 0 : ℝ) : ℂ)⁻¹ *
      ((ringPhiSetting χ).Mres (3 : ℕ) (Eig.lam χ 0) 0 r *
        (ringPhiSetting χ).psi 3 (Eig.lam χ 0) 0 (Real.log r)) * ((r : ℂ) ^ 3)⁻¹ with hf_def
  have hf : ContDiffOn ℝ ∞ f (Ioi 0) := SeedFieldH.seedProf_contDiffOn χ hχ hN
  set ψ : ℂ → ℝ := fun x => -2 * ((c ‖x‖ : ℂ) * f ‖x‖ * x ^ 3).re with hψ_def
  set K : Set ℂ := {y : ℂ | ‖y‖ ∈ tsupport c} with hK_def
  -- `c` vanishes off its topological support
  have hc0 : ∀ r : ℝ, r ∉ tsupport c → c r = 0 := fun r hr =>
    image_eq_zero_of_notMem_tsupport hr
  have hc0' : ∀ r : ℝ, r < 3 * a / 4 → c r = 0 := fun r hr =>
    hc0 r fun h => absurd (hcs h).1 (not_le.2 hr)
  -- smoothness of `ψ`
  have hk : ContDiff ℝ ∞ (fun x : ℂ => (c ‖x‖ : ℂ) * f ‖x‖) :=
    SeedFieldH.contDiff_cutoff_radial hc (by positivity) hc0' hf
  have hψ : ContDiff ℝ ∞ ψ :=
    contDiff_const.mul (Complex.reCLM.contDiff.comp (hk.mul (contDiff_id.pow 3)))
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  refine ⟨Prelim.perpGrad ψ, K, SeedFieldH.contDiff_perpGrad hψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `K` is compact
    refine isCompact_of_isClosed_isBounded ((isClosed_tsupport c).preimage continuous_norm) ?_
    refine (isBounded_closedBall (x := (0 : ℂ)) (r := 1 + a / 4)).subset ?_
    intro y hy
    rw [mem_closedBall_zero_iff]
    exact (hcs hy).2
  · -- `K ⊆ {a/2 < |y| < 2}`
    intro y hy
    have h := hcs hy
    constructor
    · linarith [h.1]
    · linarith [h.2]
  · -- `V = 0` off `K`
    intro y hy
    apply SeedFieldH.perpGrad_eq_zero_of_eventuallyEq
    have hU : IsOpen {x : ℂ | ‖x‖ ∉ tsupport c} :=
      ((isClosed_tsupport c).preimage continuous_norm).isOpen_compl
    filter_upwards [hU.mem_nhds hy] with x hx
    simp [hψ_def, hc0 _ hx]
  · -- `div V = 0`
    intro x
    exact SeedFieldH.divergence_perpGrad (hψ.contDiffAt.of_le (by norm_cast))
  · -- `V ∘ O = O ∘ V`
    intro x
    refine SeedFieldH.perpGrad_rot hψd ?_ x
    intro z
    have hz3 : (rot (2 * Real.pi / 3) z) ^ 3 = z ^ 3 := by
      rw [rot, mul_pow, ← Complex.exp_nat_mul]
      have : ((3 : ℕ) : ℂ) * (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) =
          2 * Real.pi * Complex.I := by
        push_cast
        ring
      rw [this, Complex.exp_two_pi_mul_I, one_mul]
    simp only [hψ_def, Polar.norm_rot, hz3]
  · -- `eq:seed-first`
    intro y
    by_cases hy0 : y = 0
    · subst hy0
      have hV0 : Prelim.perpGrad ψ 0 = 0 := by
        apply SeedFieldH.perpGrad_eq_zero_of_eventuallyEq
        have hU : IsOpen {x : ℂ | ‖x‖ ∉ tsupport c} :=
          ((isClosed_tsupport c).preimage continuous_norm).isOpen_compl
        have h0 : (0 : ℂ) ∈ {x : ℂ | ‖x‖ ∉ tsupport c} := by
          intro h
          have := (hcs h).1
          simp at this
          linarith
        filter_upwards [hU.mem_nhds h0] with x hx
        simp [hψ_def, hc0 _ hx]
      rw [hV0, map_zero]
      simp [Eig.phi, Ang.ofProfile, Ang.angPhase]
    · set r : ℝ := ‖y‖ with hr_def
      have hr : 0 < r := norm_pos_iff.2 hy0
      have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
      -- `DΦ(y)(V y) = Φ'(r)/r ⟨y, V y⟩`
      rw [SeedFieldH.fderiv_ringPhi_apply hχ hy0]
      -- `⟨y, V y⟩ = -∂_θψ(y)`
      have hang := (Prelim.inner_perpGrad_radial_angular hy0 (hψd y)).1
      have hinner : inner ℝ y (Prelim.perpGrad ψ y) =
          -deriv (fun θ : ℝ => ψ (rot θ y)) 0 := by
        have hdiv : y / ((‖y‖ : ℝ) : ℂ) = (‖y‖⁻¹ : ℝ) • y := by
          rw [Complex.real_smul, div_eq_inv_mul, Complex.ofReal_inv]
        rw [hdiv, real_inner_smul_right, real_inner_comm] at hang
        have hr' : (‖y‖ : ℝ) ≠ 0 := hr.ne'
        field_simp at hang
        linarith
      -- `∂_θψ(y) = -2 Re(3i c f y³)`
      have hθ : deriv (fun θ : ℝ => ψ (rot θ y)) 0 =
          -2 * (3 * Complex.I * ((c r : ℂ) * f r) * y ^ 3).re := by
        have heq : (fun θ : ℝ => ψ (rot θ y)) =
            fun θ : ℝ => -2 * (((c r : ℂ) * f r) * (rot θ y) ^ 3).re := by
          funext θ
          simp only [hψ_def, Polar.norm_rot, hr_def]
        rw [heq]
        exact ((SeedFieldH.hasDerivAt_re_mul_rot_pow _ y).const_mul (-2)).deriv
      rw [hinner, hθ]
      -- the profile identity
      simp only [Eig.phi, Ang.ofProfile, Ang.angPhase, Eig.gstar, SectorSetting.gStar,
        SectorSetting.kcoef]
      rw [← hr_def]
      by_cases hd : (ringPhiSetting χ).dom r = 0
      · simp [hd]
      · have hrI : r ∈ Icc a 1 := by
          by_contra hn
          exact hd ((ringPhiSetting_valid hχ).dom_eq_zero r hr hn)
        rw [hc1 r hrI]
        have key : ((Eig.nstar χ 0 : ℝ) : ℂ)⁻¹ *
            ((ringPhiSetting χ).Mres (3 : ℕ) (Eig.lam χ 0) 0 r *
              (Complex.I * (((3 : ℕ) : ℤ) : ℂ) * (((ringPhiSetting χ).dom r : ℝ) : ℂ) /
                (r : ℂ)) *
              (ringPhiSetting χ).psi 3 (Eig.lam χ 0) 0 (Real.log r) *
              (y / (r : ℂ)) ^ (3 : ℤ)) =
            (((ringPhiSetting χ).dom r / r : ℝ) : ℂ) *
              (3 * Complex.I * (((1 : ℝ) : ℂ) * f r) * y ^ 3) := by
          rw [hf_def]
          simp only [zpow_ofNat]
          push_cast
          field_simp
        rw [key, Complex.re_ofReal_mul]
        ring

end OneRing

end NonUniqueEuler
