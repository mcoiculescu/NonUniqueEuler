import NonUniqueEuler.H.Sec4.Edge.Core

/-!
# Helpers for `P/Sec4/Edge`: the energy identity and the conclusion of `lem:edge`

Manuscript `04_ring.tex:745-769`. With the notation of `H/Sec4/Edge/Core.lean`:
* `energy`: `Re λ · ‖g‖²_W = -ℓ Im ∫ ς ψ ḡ r` (`04_ring.tex:752-757`), i.e.
  `Re λ · N = -ℓ Im T`, from `iℓψ = r(λ + iℓΩ)e` (the first term `-iℓ∫Ω|g|²Wr` is imaginary);
* `core`: `Re λ ≤ ½ Z_n^{1/2}` whenever `ψ` reproduces itself through the kernel on `I` and
  `N > 0` (`04_ring.tex:758-769`).
-/

noncomputable section

open MeasureTheory Set ComplexConjugate

namespace NonUniqueEuler.EdgeH

open SectorSetting

variable {S : SectorSetting}

/-- The energy identity `Re λ · N = -ℓ Im T`. -/
theorem energy (hS : S.Valid) {ℓ : ℤ} {z : ℂ} (hz : 0 < z.re) (G : ℝ) {ψ : ℝ → ℂ}
    (hψc : ContinuousOn ψ (Ioi 0)) :
    z.re * ∫ r in Icc S.r₁ S.r₂, |S.dom r| * ‖efun S ℓ z G ψ r‖ ^ 2 * r ^ 2 =
      -(ℓ : ℝ) * (∫ r in Icc S.r₁ S.r₂, ψ r * conj (gw S (efun S ℓ z G ψ) r)).im := by
  have hec : ContinuousOn (efun S ℓ z G ψ) (Icc S.r₁ S.r₂) :=
    (continuousOn_efun hS hz G hψc).mono (Icc_subset_Ioi hS)
  have hu : ContinuousOn (fun r => |S.dom r| * ‖efun S ℓ z G ψ r‖ ^ 2 * r ^ 2)
      (Icc S.r₁ S.r₂) :=
    ((continuous_dom hS).abs.continuousOn.mul (hec.norm.pow 2)).mul
      (continuous_pow 2).continuousOn
  have hpt : ∀ r ∈ Icc S.r₁ S.r₂,
      Complex.I * (ℓ : ℂ) * (ψ r * conj (gw S (efun S ℓ z G ψ) r)) =
        mres S ℓ z G r * (((|S.dom r| * ‖efun S ℓ z G ψ r‖ ^ 2 * r ^ 2 : ℝ)) : ℂ) := by
    intro r hr
    have hr0 := pos_of_mem_Icc hS hr
    have hmul := efun_mul (S := S) (ℓ := ℓ) hz G ψ hr0.ne'
    have hee : efun S ℓ z G ψ r * conj (efun S ℓ z G ψ r) =
        ((‖efun S ℓ z G ψ r‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [gw, map_mul, Complex.conj_ofReal]
    push_cast at hee ⊢
    linear_combination (-(((|S.dom r| : ℝ) : ℂ) * conj (efun S ℓ z G ψ r) * (r : ℂ))) * hmul +
      (mres S ℓ z G r * ((|S.dom r| : ℝ) : ℂ) * (r : ℂ) ^ 2) * hee
  have hT : Complex.I * (ℓ : ℂ) *
      (∫ r in Icc S.r₁ S.r₂, ψ r * conj (gw S (efun S ℓ z G ψ) r)) =
        ∫ r in Icc S.r₁ S.r₂,
          mres S ℓ z G r * (((|S.dom r| * ‖efun S ℓ z G ψ r‖ ^ 2 * r ^ 2 : ℝ)) : ℂ) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Icc hpt
  have hint : Integrable (fun r =>
      mres S ℓ z G r * (((|S.dom r| * ‖efun S ℓ z G ψ r‖ ^ 2 * r ^ 2 : ℝ)) : ℂ))
      (volume.restrict (Icc S.r₁ S.r₂)) :=
    (((continuousOn_mres hS ℓ z G).mono (Icc_subset_Ioi hS)).mul
      (Complex.continuous_ofReal.comp_continuousOn hu)).integrableOn_compact isCompact_Icc
  have hre := integral_re hint
  simp only [RCLike.re_to_complex, Complex.re_mul_ofReal, mres_re] at hre
  rw [integral_const_mul] at hre
  have h2 : (Complex.I * (ℓ : ℂ) *
      (∫ r in Icc S.r₁ S.r₂, ψ r * conj (gw S (efun S ℓ z G ψ) r))).re =
        -(ℓ : ℝ) * (∫ r in Icc S.r₁ S.r₂, ψ r * conj (gw S (efun S ℓ z G ψ) r)).im := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.intCast_re,
      Complex.intCast_im]
    ring
  rw [hT] at h2
  linarith

/-- The conclusion of `lem:edge` in terms of `ψ`. -/
theorem core (hS : S.Valid) (hsplit : S.EdgeSplit) {ℓ : ℤ} (hℓ : ℓ ≠ 0) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) {ψ : ℝ → ℂ} (hψc : ContinuousOn ψ (Ioi 0))
    (hψ : ∀ r ∈ Icc S.r₁ S.r₂, ψ r = -(((2 * |(ℓ : ℝ)|)⁻¹ : ℝ) : ℂ) *
        ∫ ρ in Icc S.r₁ S.r₂, (K0 ℓ.natAbs r ρ : ℂ) * fw S (efun S ℓ z G ψ) ρ)
    (hN : 0 < ∫ r in Icc S.r₁ S.r₂, |S.dom r| * ‖efun S ℓ z G ψ r‖ ^ 2 * r ^ 2) :
    z.re ≤ 1 / 2 * Real.sqrt (S.Zedge ℓ.natAbs) := by
  have hE := energy hS (ℓ := ℓ) hz G hψc
  set e := efun S ℓ z G ψ with he_def
  set n := ℓ.natAbs with hn_def
  set c : ℝ := (2 * |(ℓ : ℝ)|)⁻¹ with hc_def
  have hec : ContinuousOn e (Icc S.r₁ S.r₂) :=
    (continuousOn_efun hS hz G hψc).mono (Icc_subset_Ioi hS)
  set N := ∫ r in Icc S.r₁ S.r₂, |S.dom r| * ‖e r‖ ^ 2 * r ^ 2 with hN_def
  set T := ∫ r in Icc S.r₁ S.r₂, ψ r * conj (gw S e r) with hT_def
  have hTB : T = ((-c : ℝ) : ℂ) * Bform S n (fw S e) (gw S e) := by
    rw [hT_def, Bform, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    rw [hψ r hr]
    push_cast
    ring
  have hherm := B_herm hS n (continuousOn_fw hS hec) (continuousOn_gw hS hec)
  have hX := B_sub hS hsplit n hec
  set B := Bform S n (fw S e) (gw S e) with hB_def
  set B' := Bform S n (gw S e) (fw S e) with hB'_def
  set α := alphaI S n e with hα_def
  set β := betaI S n e with hβ_def
  have hB' : B' = conj B := by rw [hherm, Complex.conj_conj]
  have hw : β * conj α = conj (α * conj β) := by rw [map_mul, Complex.conj_conj, mul_comm]
  have hBim : B.im = 2 * (α * conj β).im := by
    rw [hB', hw] at hX
    have h := congrArg Complex.im hX
    simp only [Complex.sub_im, Complex.conj_im, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.sub_re, Complex.conj_re] at h
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    linarith
  have hTim : T.im = -c * (2 * (α * conj β).im) := by
    rw [hTB, Complex.im_ofReal_mul, hBim]
  have hℓabs : 0 < |(ℓ : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hℓ)
  have hcpos : 0 < c := by rw [hc_def]; positivity
  have hc2 : 2 * c * |(ℓ : ℝ)| = 1 := by
    rw [hc_def]
    field_simp
  have hw_le : |(α * conj β).im| ≤ ‖α‖ * ‖β‖ :=
    (Complex.abs_im_le_norm _).trans (le_of_eq (by rw [norm_mul, Complex.norm_conj]))
  have h1 : z.re * N ≤ ‖α‖ * ‖β‖ := by
    rw [hE, hTim]
    calc -(ℓ : ℝ) * (-c * (2 * (α * conj β).im)) = (2 * c * ℓ) * (α * conj β).im := by ring
      _ ≤ |(2 * c * ℓ) * (α * conj β).im| := le_abs_self _
      _ = |(α * conj β).im| := by
        rw [abs_mul (2 * c * (ℓ : ℝ)), abs_mul (2 * c), abs_mul 2, abs_two, abs_of_pos hcpos, hc2,
          one_mul]
      _ ≤ ‖α‖ * ‖β‖ := hw_le
  set Np := ∫ r in Icc S.r₁ S.r₂, (‖e r‖ * r) ^ 2 * dp S r with hNp_def
  set Nn := ∫ r in Icc S.r₁ S.r₂, (‖e r‖ * r) ^ 2 * dn S r with hNn_def
  have hα : ‖α‖ ^ 2 ≤ Zp S n * Np := norm_alpha_sq_le hS n hec
  have hβ : ‖β‖ ^ 2 ≤ Zn S n * Nn := norm_beta_sq_le hS n hec
  have hNs : N = Np + Nn := N_eq_add hS hec
  have hZ : S.Zedge n = Zp S n * Zn S n := Zedge_eq_mul hS n
  have hNp : 0 ≤ Np :=
    setIntegral_nonneg measurableSet_Icc fun r _ => mul_nonneg (sq_nonneg _) (dp_nonneg r)
  have hNn : 0 ≤ Nn :=
    setIntegral_nonneg measurableSet_Icc fun r _ => mul_nonneg (sq_nonneg _) (dn_nonneg r)
  have hZp := Zp_nonneg (S := S) n
  have hZn := Zn_nonneg (S := S) n
  have hZnn : 0 ≤ S.Zedge n := by rw [hZ]; exact mul_nonneg hZp hZn
  have hsq : (‖α‖ * ‖β‖) ^ 2 ≤ (Real.sqrt (S.Zedge n) * (N / 2)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hZnn, hZ, hNs]
    calc ‖α‖ ^ 2 * ‖β‖ ^ 2 ≤ (Zp S n * Np) * (Zn S n * Nn) :=
          mul_le_mul hα hβ (sq_nonneg _) (mul_nonneg hZp hNp)
      _ = Zp S n * Zn S n * (Np * Nn) := by ring
      _ ≤ Zp S n * Zn S n * ((Np + Nn) / 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (Np - Nn)]) (mul_nonneg hZp hZn)
  have hNnn : 0 ≤ N := hN.le
  have h2 : ‖α‖ * ‖β‖ ≤ Real.sqrt (S.Zedge n) * (N / 2) :=
    le_of_pow_le_pow_left₀ two_ne_zero
      (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) hsq
  have h3 : z.re * N ≤ (1 / 2 * Real.sqrt (S.Zedge n)) * N := by
    have : Real.sqrt (S.Zedge n) * (N / 2) = (1 / 2 * Real.sqrt (S.Zedge n)) * N := by ring
    linarith
  exact le_of_mul_le_mul_right h3 hN

end NonUniqueEuler.EdgeH
