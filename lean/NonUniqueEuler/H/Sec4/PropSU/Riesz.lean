import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.SemigroupLaw
import NonUniqueEuler.I.Infra.AngularFourier.Symmetry
import NonUniqueEuler.H.Sec4.PropSU.Spectrum

/-!
# Helpers for `P/Sec4/PropSU`: the Riesz projection `Eig.R` sector by sector

R2 replacement of the second paragraph of `prop:SU` (`04_ring.tex:1259-1267`, `:1289-1295`) and
the formula of `def:eigendata` (`04_ring.tex:1320-1330`).

* `R_decomp`: `R(G)w = ℓ_*(G)(w) n_*⁻¹ g_*e^{3iθ} + conj(ℓ_*(G)(conj w)) n_*⁻¹ conj(g_*)e^{-3iθ}`,
  an identity of elements of `Y^s(N)` (`P_3 φ_* = φ_*`, `conj φ_*` lies in the sector `-3`);
* `ellFn_eq_ellStarY`, `conj_ellFn_conj_eq`: `ℓ_*(G)(w) = n_* ℓ_*(w_3)` only sees the sector-`3`
  component `P_3 w`, and `conj(ℓ_*(G)(conj w)) = n_* conj(ℓ_*(conj w_{-3}))` only `P_{-3} w`
  (`angularSector_secProj_ae`, `angularSector_conj`);
* `R_sector_core`: the five assertions of `Eig.R_sector`. Idempotence and the commutation with
  `e^{tL(G)}` are checked sector by sector (`Y_ext_of_secProj`, `semigroup_sector`), from
  `P² = P` and `L P = P L = λ P` of the simple spectral projections (`evansSimple_riesz`,
  `evansSimple_riesz_conj`).
-/

noncomputable section

open MeasureTheory Set ComplexConjugate

namespace NonUniqueEuler.PropSUH

open RingData Sect

/-- `ℓ_*` on profiles only sees the a.e. class on `(0, ∞)`. -/
theorem ellStar_congr_ae (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) {h₁ h₂ : ℝ → ℂ}
    (h : h₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] h₂) : S.ellStar ℓ z G h₁ = S.ellStar ℓ z G h₂ := by
  unfold SectorSetting.ellStar
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with r hr
  rw [hr]

/-- `Commute P A → Commute P (c • A)` for continuous linear operators. -/
theorem commute_smul_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P A : E →L[ℂ] E} (h : Commute P A) (c : ℂ) : Commute P (c • A) := by
  have h' := h.eq
  show P * (c • A) = (c • A) * P
  refine ContinuousLinearMap.ext fun x => ?_
  have hx : P (A x) = A (P x) := by
    rw [← mul_apply_eq_comp, h', mul_apply_eq_comp]
  simp only [mul_apply_eq_comp, smul_apply, map_smul, hx]

/-- The Evans function of `Φ` vanishes at `λ_*(G)`, simply (`eq:evans-units`, (N1)). -/
theorem evansPhi_lam (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) :
    0 < (Eig.lam χ G).re ∧ (ringPhiSetting χ).evans 3 (Eig.lam χ G) G = 0 ∧
      deriv (fun w => (ringPhiSetting χ).evans 3 w G) (Eig.lam χ G) ≠ 0 := by
  obtain ⟨h211, hE, hE', -⟩ := hypN_lamC χ hN.n1 hN.n2 (Rc_sq_mul_mem hG)
  have hz : 0 < (Eig.lam χ G).re := by
    have : 211 / 2500 < (Eig.lam χ G).re := h211
    linarith
  refine ⟨hz, ?_, ?_⟩
  · rw [evans_units hχ 3 (by norm_num) _ hz G]
    exact hE
  · rw [evans_units_deriv hχ 3 (by norm_num) _ hz G]
    exact hE'

/-- The ring-units annulus `N` as a closed annulus with `0 < a/2 < 2`: elements of `Y^s(N)` are
determined by their sector projections. -/
theorem Y_annN_ext {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {s : ℕ} {w v : Y s annN}
    (h : ∀ ℓ : ℤ, secProj s annN ℓ w = secProj s annN ℓ v) : w = v :=
  Y_ext_of_secProj (ringPhiSetting_valid hχ).ρm_pos (ringPhiSetting_valid hχ).ρm_lt_ρp h

/-! ### Typed aliases

The objects of the sector setting of `Φ` live on `Ysec s (ringPhiSetting χ).Nstar ((3 : ℕ) : ℤ)`,
which is definitionally (not syntactically) `Ysec s annN 3`. The aliases below fix the syntactic
type `Ysec s annN (±3)`, so that rewriting works; they are unfolded by `rfl`. -/

/-- `n_*⁻¹ g_* e^{3iθ} ∈ X^s_3` (`= φ_*`). -/
def u3 (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Ysec s annN 3 :=
  (((Eig.nstar χ G : ℝ) : ℂ))⁻¹ • (ringPhiSetting χ).gStarY s 3 (Eig.lam χ G) G

/-- `n_*⁻¹ conj(g_*) e^{-3iθ} ∈ X^s_{-3}` (`= conj φ_*`). -/
def v3 (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Ysec s annN (-3) :=
  (((Eig.nstar χ G : ℝ) : ℂ))⁻¹ • (ringPhiSetting χ).gStarBarY s 3 (Eig.lam χ G) G

/-- The Riesz projection of `L_3(G)` at `λ_*(G)` on `X^s_3`. -/
def P3 (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Ysec s annN 3 →L[ℂ] Ysec s annN 3 :=
  (ringPhiSetting χ).rieszSec s 3 (Eig.lam χ G) G

/-- The Riesz projection of `L_{-3}(G)` at `conj λ_*(G)` on `X^s_{-3}`. -/
def Pm3 (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Ysec s annN (-3) →L[ℂ] Ysec s annN (-3) :=
  (ringPhiSetting χ).rieszSecBar s 3 (Eig.lam χ G) G

/-- `ℓ_*` on `X^s_3`. -/
def e3 (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Ysec s annN 3 →L[ℂ] ℂ :=
  (ringPhiSetting χ).ellStarY s 3 (Eig.lam χ G) G

/-- `h ↦ conj(ℓ_*(conj h))` on `X^s_{-3}`. -/
def em3 (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Ysec s annN (-3) →L[ℂ] ℂ :=
  (ringPhiSetting χ).ellStarBarY s 3 (Eig.lam χ G) G

/-- `g_* e^{3iθ} ∈ X^s_3`. -/
def g3 (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Ysec s annN 3 :=
  (ringPhiSetting χ).gStarY s 3 (Eig.lam χ G) G

/-- `conj(g_*) e^{-3iθ} ∈ X^s_{-3}`. -/
def gm3 (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Ysec s annN (-3) :=
  (ringPhiSetting χ).gStarBarY s 3 (Eig.lam χ G) G

theorem P3_apply (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) (g : Ysec s annN 3) :
    P3 χ s G g = e3 χ s G g • g3 χ s G := rfl

theorem Pm3_apply (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) (g : Ysec s annN (-3)) :
    Pm3 χ s G g = em3 χ s G g • gm3 χ s G := rfl

theorem u3_eq (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) :
    u3 χ s G = (((Eig.nstar χ G : ℝ) : ℂ))⁻¹ • g3 χ s G := rfl

theorem v3_eq (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) :
    v3 χ s G = (((Eig.nstar χ G : ℝ) : ℂ))⁻¹ • gm3 χ s G := rfl

section R

variable (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
  (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ)

include hχ hN hG

/-- The facts of `thm:evans-simple` used here, in the typed aliases. -/
theorem riesz_facts :
    (∀ g : Ysec s annN 3, e3 χ s G g =
        (ringPhiSetting χ).ellStar 3 (Eig.lam χ G) G (Polar.angularSector g.fn 3)) ∧
      (∀ g : Ysec s annN (-3), em3 χ s G g =
        (ringPhiSetting χ).ellStarBar 3 (Eig.lam χ G) G (Polar.angularSector g.fn (-3))) ∧
      (g3 χ s G).fn =ᵐ[volume] Ang.ofProfile 3 ((ringPhiSetting χ).gStar 3 (Eig.lam χ G) G) ∧
      (gm3 χ s G).fn =ᵐ[volume]
        Ang.ofProfile (-3) (fun r => conj ((ringPhiSetting χ).gStar 3 (Eig.lam χ G) G r)) ∧
      Dunford.IsSimpleSpectralProj (Lin.Lsec χ s 3 G) (P3 χ s G) (Eig.lam χ G) ∧
      Dunford.IsSimpleSpectralProj (Lin.Lsec χ s (-3) G) (Pm3 χ s G) (conj (Eig.lam χ G)) := by
  set S := ringPhiSetting χ with hSdef
  have hS : S.Valid := ringPhiSetting_valid hχ
  obtain ⟨hz, hE, hE'⟩ := evansPhi_lam χ hχ hN hG
  have hR := (S.evansSimple_riesz hS 3 (by norm_num) _ hz G hE hE').2 s
  have hRc := S.evansSimple_riesz_conj hS 3 (by norm_num) _ hz G hE hE' s
  have hEig := (S.eigen_of_evans_eq_zero hS 3 (by norm_num) _ hz G hE).2.2.2.2 s
  exact ⟨fun g => hR.1 g, fun g => hRc.1 g, hEig.1, hRc.2.1, hR.2.2.1, hRc.2.2.2.2.2.1⟩

/-- `R(G)w = ℓ_*(G)(w) • n_*⁻¹ g_*e^{3iθ} + conj(ℓ_*(G)(conj w)) • n_*⁻¹ conj(g_*)e^{-3iθ}` in
`Y^s(N)` (`def:eigendata`, `04_ring.tex:1320-1321`). -/
theorem R_decomp (w : Y s annN) :
    Eig.R χ s G w =
      Eig.ellFn χ G w.fn • inclSec s annN 3 (u3 χ s G) +
        conj (Eig.ellFn χ G fun y => conj (w.fn y)) • inclSec s annN (-3) (v3 χ s G) := by
  obtain ⟨-, -, hg3, hgm3, -, -⟩ := riesz_facts χ hχ hN hG s
  set n : ℂ := ((Eig.nstar χ G : ℝ) : ℂ) with hn
  apply Y_ext_fn
  have hRw := Eig.R_spec_of_exists (Eig.exists_R χ hχ hN hG s) w
  have hu : (inclSec s annN 3 (u3 χ s G)).fn =ᵐ[volume]
      fun x => n⁻¹ * Ang.ofProfile 3 ((ringPhiSetting χ).gStar 3 (Eig.lam χ G) G) x := by
    filter_upwards [Ysec_fn_smul (n⁻¹) (g3 χ s G), hg3] with x h1 h2
    rw [Y.fn_inclSec, u3_eq, h1, Pi.smul_apply, h2, smul_eq_mul]
  have hv : (inclSec s annN (-3) (v3 χ s G)).fn =ᵐ[volume]
      fun x => n⁻¹ *
        Ang.ofProfile (-3) (fun r => conj ((ringPhiSetting χ).gStar 3 (Eig.lam χ G) G r)) x := by
    filter_upwards [Ysec_fn_smul (n⁻¹) (gm3 χ s G), hgm3] with x h1 h2
    rw [Y.fn_inclSec, v3_eq, h1, Pi.smul_apply, h2, smul_eq_mul]
  filter_upwards [hRw, Y_fn_add (Eig.ellFn χ G w.fn • inclSec s annN 3 (u3 χ s G))
        (conj (Eig.ellFn χ G fun y => conj (w.fn y)) • inclSec s annN (-3) (v3 χ s G)),
      Y_fn_smul (Eig.ellFn χ G w.fn) (inclSec s annN 3 (u3 χ s G)),
      Y_fn_smul (conj (Eig.ellFn χ G fun y => conj (w.fn y))) (inclSec s annN (-3) (v3 χ s G)),
      hu, hv]
    with x h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.add_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, h5,
    h6]
  unfold Eig.RFn Eig.phi
  rw [map_mul, conj_ofProfile, map_inv₀, hn, Complex.conj_ofReal]
  rfl

/-- `ℓ_*(G)(w) = n_* ℓ_*((P_3 w)_3)`: the functional only sees the sector `3`. -/
theorem ellFn_eq_e3 (w : Y s annN) :
    Eig.ellFn χ G w.fn = ((Eig.nstar χ G : ℝ) : ℂ) * e3 χ s G (secProj s annN 3 w) := by
  obtain ⟨he3, -, -, -, -, -⟩ := riesz_facts χ hχ hN hG s
  unfold Eig.ellFn
  rw [he3 (secProj s annN 3 w)]
  congr 1
  apply ellStar_congr_ae
  exact (angularSector_secProj_ae isRotInvariant_annN 3 w).symm

/-- `conj(ℓ_*(G)(conj w)) = n_* conj(ℓ_*(conj (P_{-3} w)_{-3}))`: only the sector `-3` counts. -/
theorem conj_ellFn_conj_eq_em3 (w : Y s annN) :
    conj (Eig.ellFn χ G fun y => conj (w.fn y)) =
      ((Eig.nstar χ G : ℝ) : ℂ) * em3 χ s G (secProj s annN (-3) w) := by
  obtain ⟨-, hem3, -, -, -, -⟩ := riesz_facts χ hχ hN hG s
  rw [hem3 (secProj s annN (-3) w)]
  unfold Eig.ellFn SectorSetting.ellStarBar
  rw [map_mul, Complex.conj_ofReal]
  congr 2
  apply ellStar_congr_ae
  have hk := angularSector_secProj_ae isRotInvariant_annN (-3) w
  filter_upwards [hk] with r hr
  have hc := Ang.angularSector_conj w.fn (-3) r
  rw [neg_neg] at hc
  rw [hc]
  exact congrArg conj hr.symm

/-- **The five assertions of `Eig.R_sector`** (`04_ring.tex:1259-1267`, R2), with the typed
aliases. -/
theorem R_sector_core :
    (∀ w : Y s annN, secProj s annN 3 (Eig.R χ s G w) = P3 χ s G (secProj s annN 3 w)) ∧
      (∀ w : Y s annN, secProj s annN (-3) (Eig.R χ s G w) = Pm3 χ s G (secProj s annN (-3) w)) ∧
      (∀ ℓ : ℤ, ℓ ≠ 3 → ℓ ≠ -3 → ∀ w : Y s annN, secProj s annN ℓ (Eig.R χ s G w) = 0) ∧
      Eig.R χ s G * Eig.R χ s G = Eig.R χ s G ∧
      ∀ t : ℝ, 0 ≤ t → Lin.S χ s G t * Eig.R χ s G = Eig.R χ s G * Lin.S χ s G t := by
  have hS : (ringPhiSetting χ).Valid := ringPhiSetting_valid hχ
  obtain ⟨-, -, -, -, hP3, hPm3⟩ := riesz_facts χ hχ hN hG s
  have hn0 : ((Eig.nstar χ G : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Eig.eigendata_phi χ hχ hN hG).1.ne'
  have hK : IsRotInvariant annN := isRotInvariant_annN
  have h3m3 : (3 : ℤ) ≠ -3 := by norm_num
  -- the three sector identities
  have hA : ∀ w : Y s annN, secProj s annN 3 (Eig.R χ s G w) = P3 χ s G (secProj s annN 3 w) := by
    intro w
    rw [R_decomp χ hχ hN hG s w, map_add, map_smul, map_smul, secProj_inclSec_self hK,
      secProj_inclSec_ne hK h3m3, smul_zero, add_zero, P3_apply,
      ellFn_eq_e3 χ hχ hN hG s w, u3_eq, smul_smul]
    congr 1
    field_simp
  have hB : ∀ w : Y s annN,
      secProj s annN (-3) (Eig.R χ s G w) = Pm3 χ s G (secProj s annN (-3) w) := by
    intro w
    rw [R_decomp χ hχ hN hG s w, map_add, map_smul, map_smul, secProj_inclSec_self hK,
      secProj_inclSec_ne hK h3m3.symm, smul_zero, zero_add, Pm3_apply,
      conj_ellFn_conj_eq_em3 χ hχ hN hG s w, v3_eq, smul_smul]
    congr 1
    field_simp
  have hC : ∀ ℓ : ℤ, ℓ ≠ 3 → ℓ ≠ -3 → ∀ w : Y s annN, secProj s annN ℓ (Eig.R χ s G w) = 0 := by
    intro ℓ h3 hm3 w
    rw [R_decomp χ hχ hN hG s w, map_add, map_smul, map_smul, secProj_inclSec_ne hK h3,
      secProj_inclSec_ne hK hm3, smul_zero, smul_zero, add_zero]
  refine ⟨hA, hB, hC, ?_, ?_⟩
  · -- idempotence
    refine ContinuousLinearMap.ext fun w => ?_
    rw [mul_apply_eq_comp]
    apply Y_annN_ext hχ
    intro ℓ
    by_cases h3 : ℓ = 3
    · subst h3
      rw [hA, hA, ← mul_apply_eq_comp, hP3.idem]
    by_cases hm3 : ℓ = -3
    · subst hm3
      rw [hB, hB, ← mul_apply_eq_comp, hPm3.idem]
    · rw [hC ℓ h3 hm3, hC ℓ h3 hm3]
  · -- commutation with `e^{tL(G)}`
    intro t ht
    refine ContinuousLinearMap.ext fun w => ?_
    rw [mul_apply_eq_comp, mul_apply_eq_comp]
    apply Y_annN_ext hχ
    intro ℓ
    have hsg : ∀ w : Y s annN, secProj s annN ℓ (Lin.S χ s G t w) =
        NormedSpace.exp ((t : ℂ) • Lin.Lsec χ s ℓ G) (secProj s annN ℓ w) :=
      ((ringPhiSetting χ).semigroup_sector hS s G ht ℓ).1
    by_cases h3 : ℓ = 3
    · subst h3
      have hc : Commute (P3 χ s G) (Lin.Lsec χ s 3 G) :=
        hP3.proj_mul.trans hP3.mul_proj.symm
      have hce := (commute_smul_right hc (t : ℂ)).exp_right
      rw [hsg, hA, hA, hsg, ← mul_apply_eq_comp, ← mul_apply_eq_comp, hce.eq]
    by_cases hm3 : ℓ = -3
    · subst hm3
      have hc : Commute (Pm3 χ s G) (Lin.Lsec χ s (-3) G) :=
        hPm3.proj_mul.trans hPm3.mul_proj.symm
      have hce := (commute_smul_right hc (t : ℂ)).exp_right
      rw [hsg, hB, hB, hsg, ← mul_apply_eq_comp, ← mul_apply_eq_comp, hce.eq]
    · rw [hsg, hC ℓ h3 hm3, hC ℓ h3 hm3, map_zero]

end R

end NonUniqueEuler.PropSUH
