import NonUniqueEuler.H.Sec4.Eigendata.Representer
import NonUniqueEuler.H.Sec4.Eigendata.Functional
import NonUniqueEuler.I.Sec4.Adjoint
import NonUniqueEuler.I.Infra.Sobolev.Symmetry

/-!
# Proof: the claims inside `def:eigendata` and the remark after it

Proof of `I/Sec4/Eigendata.lean` (same declarations, statements copied verbatim).
Manuscript: `def:eigendata` (`04_ring.tex:1303-1324`) and the remark after it
(`04_ring.tex:1326-1338`).

Structure of the proof (helpers in `H/Sec4/Eigendata/*`):
* `EigendataH.lamFacts`: under (N), `λ_*(G) = λ_*^c(R_c²G)` is a simple zero of `E^Φ_3(·;G)` with
  `Re > 211/2500` (`hypN_lamC`, `evans_units`, `evans_units_deriv`), and `J ≠ 0`
  (`evansSimple_riesz`);
* `EigendataH.gstar_facts` (`lem:resolvent`(2)), `nstar_pos`, `memXFn_phi`: `n_* > 0` and
  `φ_* ∈ X^s` (smooth, compactly supported in `N`, `3`-fold symmetric);
* `EigendataH.ellFn_phi`, `ellFn_conj_phi`: `ℓ_*(G)(φ_*) = n_* n_*⁻¹ ℓ_*(g_*) = 1`, and `conj φ_*`
  has no sector-`3` component;
* `EigendataH.ellFn_eq_integral`: the representer formula `ℓ_*(G)(f) = ∫ f conj(ellRep)` for
  `f ∈ L²` vanishing off `N` (polar coordinates). It gives the boundedness of `ℓ_*(G)` on every
  `Y^s(N)` (`EigendataH.exists_pairing`), hence `exists_ell`, `exists_R`, and the norm identity of
  `ell_representer` (Cauchy–Schwarz, equality at `w = ellRep`);
* `pinPhi_eq`: `pin_3[φ_*] = n_*⁻¹ pin_3[g_*e^{3iθ}] = n_*⁻¹ pin_*`, `pin_* = -6e^{-3ξ₁}`
  (`lem:adjoint`(3), `adjoint_stream`), `ξ₁ = ξL - ξR`.
-/

noncomputable section

open MeasureTheory Set Real ComplexConjugate

namespace NonUniqueEuler

namespace Eig

open RingData Sect

/-- `def:eigendata` (`04_ring.tex:1305-1316`): `n_*(G) > 0`, `φ_*(G) ∈ X^s` for every `s` (and
`Eig.phiY χ s G` is it), `ℓ_*(G)(φ_*(G)) = 1` and `ℓ_*(G)(conj φ_*(G)) = 0`. -/
theorem eigendata_phi (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) :
    0 < nstar χ G ∧
      (∀ s : ℕ, Lin.MemXFn s (phi χ G)) ∧
      (∀ s : ℕ, (phiY χ s G).fn =ᵐ[volume] phi χ G ∧ Lin.MemX (phiY χ s G)) ∧
      ellFn χ G (phi χ G) = 1 ∧
      ellFn χ G (fun x => conj (phi χ G x)) = 0 := by
  have hL := EigendataH.lamFacts hχ hN hG
  have hX := EigendataH.memXFn_phi hL
  refine ⟨EigendataH.nstar_pos hL, hX, fun s => ?_, EigendataH.ellFn_phi hL,
    EigendataH.ellFn_conj_phi χ G⟩
  have hex : ∃ w : Y s annN, w.fn =ᵐ[volume] phi χ G :=
    EigendataH.exists_Y_of_memH (hX s).1 (hX s).2.1
  have hfn : (phiY χ s G).fn =ᵐ[volume] phi χ G := toY_spec hex
  exact ⟨hfn, EigendataH.mem_YsymSub_of_fn _
    (EigendataH.isMFoldSymmetricC_congr hfn (hX s).2.2)⟩

/-- `def:eigendata` (`04_ring.tex:1313-1317`): the formula `ℓ_*(G)(w) = n_*(G) ℓ_*(w_3)` is a
bounded functional on `Y^s(N)` for every `s` (on `X^0`, and on `L²(N) = Y^0(N)`), so the chosen
`Eig.ell χ s G` is it. -/
theorem exists_ell (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) :
    ∃ T : Y s annN →L[ℂ] ℂ, ∀ w : Y s annN, T w = ellFn χ G w.fn := by
  have hL := EigendataH.lamFacts hχ hN hG
  obtain ⟨T, hT, -⟩ := EigendataH.exists_pairing s annN (EigendataH.memLp_ellRep hL).star
  refine ⟨T, fun w => ?_⟩
  rw [hT, EigendataH.ellFn_eq_integral hL (EigendataH.Y_memLp_fn w)
    (EigendataH.Y_fn_zero_outside w)]
  rfl

/-- `def:eigendata` (`04_ring.tex:1320-1321`): the formula
`R(G)w = ℓ_*(G)(w)φ_* + conj(ℓ_*(G)(conj w)) conj φ_*` is a bounded operator on `Y^s(N)`, so the
chosen `Eig.R χ s G` is it. -/
theorem exists_R (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) :
    ∃ T : Y s annN →L[ℂ] Y s annN, ∀ w : Y s annN, (T w).fn =ᵐ[volume] RFn χ G w.fn := by
  have hL := EigendataH.lamFacts hχ hN hG
  have hX := EigendataH.memXFn_phi hL s
  obtain ⟨T₁, hT₁, -⟩ := EigendataH.exists_pairing s annN (EigendataH.memLp_ellRep hL).star
  obtain ⟨T₂, hT₂, -⟩ := EigendataH.exists_pairing s annN (EigendataH.memLp_ellRep hL)
  -- the elements `φ_*` and `conj φ_*` of `Y^s(N)`
  obtain ⟨u, hu⟩ := EigendataH.exists_Y_of_memH (K := annN) hX.1 hX.2.1
  have hXc : Sob.MemH s (fun x => conj (phi χ G x)) := (Sob.MemH.conj hX.1).1
  have hXcK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → conj (phi χ G x) = 0 := by
    filter_upwards [hX.2.1] with x hx hxK
    rw [hx hxK, map_zero]
  obtain ⟨v, hv⟩ := EigendataH.exists_Y_of_memH (K := annN) hXc hXcK
  refine ⟨T₁.smulRight u + T₂.smulRight v, fun w => ?_⟩
  -- the two coefficients
  have h1 : T₁ w = ellFn χ G w.fn := by
    rw [hT₁, EigendataH.ellFn_eq_integral hL (EigendataH.Y_memLp_fn w)
      (EigendataH.Y_fn_zero_outside w)]
    rfl
  have hwc : MemLp (fun x => conj (w.fn x)) 2 volume := (EigendataH.Y_memLp_fn w).star
  have hwcK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → conj (w.fn x) = 0 := by
    filter_upwards [EigendataH.Y_fn_zero_outside w] with x hx hxK
    rw [hx hxK, map_zero]
  have h2 : T₂ w = conj (ellFn χ G fun y => conj (w.fn y)) := by
    rw [hT₂, EigendataH.ellFn_eq_integral hL hwc hwcK, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hsum := EigendataH.Y_fn_add (T₁.smulRight u w) (T₂.smulRight v w)
  have hs1 := EigendataH.Y_fn_smul (T₁ w) u
  have hs2 := EigendataH.Y_fn_smul (T₂ w) v
  filter_upwards [hsum, hs1, hs2, hu, hv] with x hx hx1 hx2 hux hvx
  rw [add_apply, hx, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, hx1, hx2, hux, hvx, h1, h2, RFn]

/-- `def:eigendata` (`04_ring.tex:1320-1321`): `R(G)w = 2 Re(ℓ_*(G)(w) φ_*(G))` for real `w`. -/
theorem R_of_isReal (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) {w : Y s annN} (hw : w.IsReal) :
    (R χ s G w).fn =ᵐ[volume] fun x => ((2 * (ell χ s G w * phi χ G x).re : ℝ) : ℂ) := by
  have hspec := R_spec_of_exists (exists_R χ hχ hN hG s) w
  have hell := ell_spec_of_exists (exists_ell χ hχ hN hG s) w
  have hconj : (fun y => conj (w.fn y)) =ᵐ[volume] w.fn := by
    filter_upwards [hw] with y hy
    exact Complex.conj_eq_iff_im.2 hy
  have he := EigendataH.ellFn_congr_ae χ G hconj
  filter_upwards [hspec] with x hx
  rw [hx, RFn, he, hell, ← map_mul, Complex.add_conj]

/-- The remark after `def:eigendata` (`04_ring.tex:1329-1331`, by `lem:adjoint`(3)):
`pin_3[φ_*(G)] = -6e^{-3(ξL-ξR)}/n_*(G)`, real and negative. -/
theorem pinPhi_eq (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) :
    pinPhi χ G = ((-(6 * Real.exp (-3 * (ξL - ξR)) / nstar χ G) : ℝ) : ℂ) := by
  have hL := EigendataH.lamFacts hχ hN hG
  obtain ⟨-, -, hpin, -, -, hpinBS⟩ := SectorSetting.adjoint_stream _ hL.valid 3 (by norm_num) _
    hL.re_pos G hL.evans hL.deriv
  have hmom : pinPhi χ G =
      ((nstar χ G : ℝ) : ℂ)⁻¹ * BS.pin 3 (Ang.ofProfile 3 (gstar χ G)) := by
    unfold pinPhi BS.pin Multipole.moment
    have hpt : ∀ y : ℂ, phi χ G y * y ^ (-3 : ℤ) =
        ((nstar χ G : ℝ) : ℂ)⁻¹ * (Ang.ofProfile 3 (gstar χ G) y * (y ^ 3)⁻¹) := fun y => by
      rw [phi, zpow_neg, zpow_ofNat]
      ring
    simp_rw [hpt, integral_const_mul]
    ring
  have hn : ((nstar χ G : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (EigendataH.nstar_pos hL).ne'
  rw [hmom]
  have hpinBS' : BS.pin 3 (Ang.ofProfile 3 (gstar χ G)) =
      (ringPhiSetting χ).pinStar 3 (lam χ G) G := by
    rw [hpinBS]
    rfl
  rw [hpinBS', hpin, ringPhiSetting_ξ₁]
  push_cast
  field_simp
  ring_nf

/-- The remark after `def:eigendata` (`04_ring.tex:1333-1338`): `ℓ_*(G)` on `L²(N)` is represented
by `ellRep χ G ∈ X^0`, `ℓ_*(G)(w) = ∫ w conj(ellRep)`, so its norm on `L²(N)` (which equals its
norm on `X^0`) is `‖ellRep‖_{L²}`. -/
theorem ell_representer (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) :
    Lin.MemXFn 0 (ellRep χ G) ∧
      (∀ w : Y 0 annN, ell χ 0 G w = ∫ x, w.fn x * conj (ellRep χ G x)) ∧
      ‖ell χ 0 G‖ = Sob.l2 (ellRep χ G) := by
  have hL := EigendataH.lamFacts hχ hN hG
  have hE := EigendataH.memLp_ellRep hL
  have hint : ∀ w : Y 0 annN, ell χ 0 G w = ∫ x, w.fn x * conj (ellRep χ G x) := fun w => by
    rw [ell_spec_of_exists (exists_ell χ hχ hN hG 0) w,
      EigendataH.ellFn_eq_integral hL (EigendataH.Y_memLp_fn w) (EigendataH.Y_fn_zero_outside w)]
  refine ⟨EigendataH.memXFn_ellRep hL, hint, ?_⟩
  obtain ⟨T, hT, hTn⟩ := EigendataH.exists_pairing 0 annN hE.star
  have hTe : ell χ 0 G = T := by
    ext w
    rw [hint w, hT w]
    rfl
  have hl2 : Sob.l2 (fun x => conj (ellRep χ G x)) = Sob.l2 (ellRep χ G) :=
    EigendataH.l2_conj _
  have hnn : 0 ≤ Sob.l2 (ellRep χ G) := ENNReal.toReal_nonneg
  rw [hTe]
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ hnn fun w => ?_) ?_
  · have := hTn w
    have h' : Sob.l2 (star (ellRep χ G)) = Sob.l2 (ellRep χ G) := hl2
    rwa [h'] at this
  · -- equality at `w = ellRep`
    obtain ⟨w₀, hw₀⟩ := EigendataH.exists_Y_of_memH (K := annN)
      (EigendataH.memXFn_ellRep hL).1 (EigendataH.memXFn_ellRep hL).2.1
    have hnorm : ‖w₀‖ = Sob.l2 (ellRep χ G) := by
      rw [← (EigendataH.Y_memH_fn w₀).2, (Sob.normH_zero (EigendataH.Y_memLp_fn w₀)).2]
      unfold Sob.l2
      rw [eLpNorm_congr_ae hw₀]
    have hval : T w₀ = ((Sob.l2 (ellRep χ G) ^ 2 : ℝ) : ℂ) := by
      rw [← hTe, hint w₀, ← EigendataH.integral_mul_conj_self hE]
      refine integral_congr_ae ?_
      filter_upwards [hw₀] with x hx
      rw [hx]
    have hle := T.le_opNorm w₀
    rw [hval, hnorm, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hle
    rcases hnn.lt_or_eq with hpos | hzero
    · nlinarith
    · linarith [norm_nonneg T]

end Eig

end NonUniqueEuler
