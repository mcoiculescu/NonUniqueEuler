import NonUniqueEuler.H.Sec4.Dilation.Psi
import NonUniqueEuler.I.Infra.Sobolev.Symmetry

/-!
# Proof: `lem:dilation` (dilations of the profile)

Proof of `I/Sec4/Dilation.lean` (same declarations, statements copied verbatim). Manuscript
`lem:dilation`, `04_ring.tex:653-712`.

Structure (helpers in `H/Sec4/Dilation/*`):
* `dilate_valid`: `DilationH.dilate_valid'`;
* (1) `dilate_Omega`: `DilationH.Omega_dilate` (`Circ_{ω̄_R}(r) = R⁻²Circ_{ω̄}(Rr)`,
  `DilationH.circ_dilate`); `dilate_LsecFn`: `k^{ω̄_R}_ℓ = R² k^{ω̄}_ℓ(R·)`
  (`DilationH.kcoef_dilate`) and `𝒢_ℓ(g(R·)) = R⁻²(𝒢_ℓ g)(R·)` (`DilationH.green_comp_mul`);
  `dilate_linFn`: the weak angular derivative commutes with `𝒮_R` (`MemH.weakPartial_comp_smul`)
  and the coupling term is conjugated pointwise (`DilationH.couplingFn_dilate`:
  `∇ω̄_R = R(∇ω̄)(R·)`, `K(z) = R K(Rz)`, `∫ f(Rx) dx = R⁻² ∫ f`);
* (2) `dilate_evans`: `DilationH.evans_dilate` (`ψ^{ω̄_R}(ξ) = ψ^{ω̄}(ξ + log R)` by uniqueness
  for the initial value problem);
* (3) `dilate_eigendata`: `g^{ω̄_R}_* = R² g_*(R·)` (`DilationH.gStar_dilate`), so
  `n₁ = R n₀`, `pout^R = R^{-ℓ} pout`, `pin^R = R^ℓ pin`, `J^R = J`, `β^R = R^ℓ β`
  (changes of variables `u = Rρ`); dividing by the normalizations gives the factors of the
  statement. These identities hold without the simple-zero hypotheses, which are not used.

**Deviation.** For (3) the manuscript computes `β` through `β = -pin_*/(2ℓJ)`
(`lem:adjoint`(4)); here `β = ℓ_*(b)` is transformed directly (`b^{ω̄_R}(r) = R^{ℓ+2}b(Rr)`),
which avoids the adjoint lemma. The answer is the same.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace DilationH

open SectorSetting

/-- The coupling term is conjugated by `𝒮_R` pointwise:
`𝒦^{ω̄_R}(w(R·))(y) = (𝒦^{ω̄} w)(Ry)`. -/
theorem couplingFn_dilate (S : SectorSetting) (hS : S.Valid) {R : ℝ} (hR : 0 < R)
    (w : ℂ → ℂ) (y : ℂ) :
    (S.dilate R).couplingFn (fun x => w ((R : ℂ) * x)) y = S.couplingFn w ((R : ℂ) * y) := by
  have hR0 : R ≠ 0 := hR.ne'
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0
  have hd : ∀ v : ℂ, fderiv ℝ (S.dilate R).om y v = R * fderiv ℝ S.om ((R : ℂ) * y) v := by
    intro v
    have hf : HasFDerivAt S.om (fderiv ℝ S.om (R • y)) (R • y) :=
      ((hS.contDiff.differentiable (by simp)) (R • y)).hasFDerivAt
    have h2 : HasFDerivAt (fun x : ℂ => R • x) (R • ContinuousLinearMap.id ℝ ℂ) y :=
      (hasFDerivAt_id y).const_smul R
    have h3 := hf.comp y h2
    have he : (S.dilate R).om = S.om ∘ fun x : ℂ => R • x := by
      funext x
      simp [dilate, Complex.real_smul]
    rw [he, h3.fderiv]
    simp [Complex.real_smul]
  have hK : ∀ x : ℂ, fderiv ℝ (S.dilate R).om y (biotSavartKernel (y - x)) =
      R ^ 2 * fderiv ℝ S.om ((R : ℂ) * y) (biotSavartKernel ((R : ℂ) * y - (R : ℂ) * x)) := by
    intro x
    have e : biotSavartKernel (y - x) =
        R • biotSavartKernel ((R : ℂ) * y - (R : ℂ) * x) := by
      rw [Complex.real_smul, ← mul_sub, biotSavartKernel_mul hR0, ← mul_assoc,
        mul_inv_cancel₀ hRc, one_mul]
    rw [hd, e, map_smul, smul_eq_mul]
    ring
  simp only [couplingFn]
  congr 1
  set F : ℂ → ℂ := fun u => ((R ^ 2 : ℝ) : ℂ) *
    (((fderiv ℝ S.om ((R : ℂ) * y) (biotSavartKernel ((R : ℂ) * y - u)) : ℝ) : ℂ) * w u) with hF
  have h1 : (fun x => ((fderiv ℝ (S.dilate R).om y (biotSavartKernel (y - x)) : ℝ) : ℂ) *
      w ((R : ℂ) * x)) = fun x => F (R • x) := by
    funext x
    rw [hK, hF]
    simp only [Complex.real_smul]
    push_cast
    ring
  rw [h1, Measure.integral_comp_smul volume F R, Complex.finrank_real_complex, hF,
    integral_const_mul, abs_of_pos (by positivity), Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity), Complex.ofReal_one, one_mul]

theorem poutStar_dilate (S : SectorSetting) (hS : S.Valid) {R : ℝ} (hR : 0 < R) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (z : ℂ) (hz : 0 < z.re) (G : ℝ) :
    (S.dilate R).poutStar ℓ z G = (((R ^ ℓ)⁻¹ : ℝ) : ℂ) * S.poutStar ℓ z (R ^ 2 * G) := by
  simp only [poutStar, gStar_dilate S hS hR ℓ hℓ z hz G]
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have h1 : (fun ρ : ℝ => (ρ : ℂ) ^ (ℓ + 1) *
      (((R ^ 2 : ℝ) : ℂ) * S.gStar ℓ z (R ^ 2 * G) (R * ρ))) =
      fun ρ => (((R ^ 2 / R ^ (ℓ + 1)) : ℝ) : ℂ) *
        (((R * ρ : ℝ) : ℂ) ^ (ℓ + 1) * S.gStar ℓ z (R ^ 2 * G) (R * ρ)) := by
    funext ρ
    push_cast
    rw [mul_pow]
    field_simp
  rw [h1, integral_const_mul,
    integral_Ioi_comp_mul (fun u => (u : ℂ) ^ (ℓ + 1) * S.gStar ℓ z (R ^ 2 * G) u) hR,
    ← mul_assoc]
  congr 1
  push_cast
  field_simp
  ring

theorem pinStar_dilate (S : SectorSetting) (hS : S.Valid) {R : ℝ} (hR : 0 < R) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (z : ℂ) (hz : 0 < z.re) (G : ℝ) :
    (S.dilate R).pinStar ℓ z G = ((R ^ ℓ : ℝ) : ℂ) * S.pinStar ℓ z (R ^ 2 * G) := by
  simp only [pinStar, gStar_dilate S hS hR ℓ hℓ z hz G]
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have e : ∀ ρ : ℝ, ((R * ρ : ℝ) : ℂ) ^ ((1 : ℤ) - ℓ) =
      (R : ℂ) / (R : ℂ) ^ ℓ * (ρ : ℂ) ^ ((1 : ℤ) - ℓ) := by
    intro ρ
    rw [Complex.ofReal_mul, mul_zpow, zpow_sub₀ hR0, zpow_one, zpow_natCast]
  have h1 : (fun ρ : ℝ => (ρ : ℂ) ^ ((1 : ℤ) - ℓ) *
      (((R ^ 2 : ℝ) : ℂ) * S.gStar ℓ z (R ^ 2 * G) (R * ρ))) =
      fun ρ => ((R ^ (ℓ + 1) : ℝ) : ℂ) *
        (((R * ρ : ℝ) : ℂ) ^ ((1 : ℤ) - ℓ) * S.gStar ℓ z (R ^ 2 * G) (R * ρ)) := by
    funext ρ
    rw [e]
    push_cast
    field_simp
    ring
  rw [h1, integral_const_mul,
    integral_Ioi_comp_mul (fun u => (u : ℂ) ^ ((1 : ℤ) - ℓ) * S.gStar ℓ z (R ^ 2 * G) u) hR,
    ← mul_assoc]
  congr 1
  push_cast
  field_simp
  ring

theorem J_dilate (S : SectorSetting) (hS : S.Valid) {R : ℝ} (hR : 0 < R) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (z : ℂ) (hz : 0 < z.re) (G : ℝ) :
    (S.dilate R).J ℓ z G = S.J ℓ z (R ^ 2 * G) := by
  simp only [J]
  have h1 : EqOn (fun r : ℝ => (S.dilate R).gStar ℓ z G r * (S.dilate R).psi ℓ z G (Real.log r) *
      (S.dilate R).Mres ℓ z G r * (r : ℂ))
      (fun r => ((R : ℝ) : ℂ) * (S.gStar ℓ z (R ^ 2 * G) (R * r) *
        S.psi ℓ z (R ^ 2 * G) (Real.log (R * r)) * S.Mres ℓ z (R ^ 2 * G) (R * r) *
          ((R * r : ℝ) : ℂ))) (Ioi 0) := by
    intro r hr
    simp only
    rw [gStar_dilate S hS hR ℓ hℓ z hz G, (dilate_psi S hS hR ℓ hℓ z hz G (Real.log r)).1,
      Mres_dilate S hR, Real.log_mul hR.ne' (ne_of_gt hr), add_comm (Real.log R)]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul,
    integral_Ioi_comp_mul (fun u => S.gStar ℓ z (R ^ 2 * G) u *
      S.psi ℓ z (R ^ 2 * G) (Real.log u) * S.Mres ℓ z (R ^ 2 * G) u * (u : ℂ)) hR,
    ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hR.ne', Complex.ofReal_one, one_mul]

theorem betaStar_dilate (S : SectorSetting) (hS : S.Valid) {R : ℝ} (hR : 0 < R) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (z : ℂ) (hz : 0 < z.re) (G : ℝ) :
    (S.dilate R).betaStar ℓ z G = ((R ^ ℓ : ℝ) : ℂ) * S.betaStar ℓ z (R ^ 2 * G) := by
  simp only [betaStar, ellStar, J_dilate S hS hR ℓ hℓ z hz G]
  have h1 : EqOn (fun r : ℝ => (S.dilate R).bfun ℓ r * (S.dilate R).psi ℓ z G (Real.log r) *
      (S.dilate R).Mres ℓ z G r * (r : ℂ))
      (fun r => ((R ^ (ℓ + 1) : ℝ) : ℂ) * (S.bfun ℓ (R * r) *
        S.psi ℓ z (R ^ 2 * G) (Real.log (R * r)) * S.Mres ℓ z (R ^ 2 * G) (R * r) *
          ((R * r : ℝ) : ℂ))) (Ioi 0) := by
    intro r hr
    simp only
    rw [bfun_dilate S hR ℓ hr, (dilate_psi S hS hR ℓ hℓ z hz G (Real.log r)).1,
      Mres_dilate S hR, Real.log_mul hR.ne' (ne_of_gt hr), add_comm (Real.log R)]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul,
    integral_Ioi_comp_mul (fun u => S.bfun ℓ u *
      S.psi ℓ z (R ^ 2 * G) (Real.log u) * S.Mres ℓ z (R ^ 2 * G) u * (u : ℂ)) hR]
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  push_cast
  field_simp
  ring

end DilationH

namespace SectorSetting

/-- The dilation of a sector setting by `R > 0` is a sector setting. -/
theorem dilate_valid (S : SectorSetting) (hS : S.Valid) {R : ℝ} (hR : 0 < R) :
    (S.dilate R).Valid := by
  exact DilationH.dilate_valid' S hS hR

/-- `lem:dilation`(1): `Ω^{ω̄_R}(r;G) = Ω^{ω̄}(Rr;R²G)`. -/
theorem dilate_Omega (S : SectorSetting) (hS : S.Valid) {R : ℝ} (hR : 0 < R) (G r : ℝ) :
    (S.dilate R).Omega G r = S.Omega (R ^ 2 * G) (R * r) := by
  exact DilationH.Omega_dilate S hR G r

/-- `lem:dilation`(1), sector by sector: `L^{ω̄_R}_ℓ(G) 𝒮_R = 𝒮_R L^{ω̄}_ℓ(R²G)` on profiles,
i.e. `k^{ω̄_R}_ℓ𝒢_ℓ𝒮_R = 𝒮_Rk^{ω̄}_ℓ𝒢_ℓ` and `Ω^{ω̄_R}(·;G)𝒮_R = 𝒮_RΩ^{ω̄}(·;R²G)`. -/
theorem dilate_LsecFn (S : SectorSetting) (hS : S.Valid) {R : ℝ} (hR : 0 < R) (ℓ : ℤ) (G : ℝ)
    (g : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    (S.dilate R).LsecFn ℓ G (fun ρ => g (R * ρ)) r = S.LsecFn ℓ (R ^ 2 * G) g (R * r) := by
  simp only [LsecFn, KsecFn, DilationH.Omega_dilate S hR, DilationH.kcoef_dilate S hR,
    DilationH.green_comp_mul ℓ g hR]
  have h : ((R ^ 2 : ℝ) : ℂ) * (((R ^ 2)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity), Complex.ofReal_one]
  linear_combination (S.kcoef ℓ (R * r) * green ℓ g (R * r)) * h

/-- `lem:dilation`(1) on `ℝ²`: `L^{ω̄_R}(G) = 𝒮_R L^{ω̄}(R²G) 𝒮_R⁻¹`, i.e.
`L^{ω̄_R}(G)(w(R·)) = (L^{ω̄}(R²G)w)(R·)` (almost everywhere) for `w ∈ H¹`. -/
theorem dilate_linFn (S : SectorSetting) (hS : S.Valid) {R : ℝ} (hR : 0 < R) (G : ℝ)
    {w : ℂ → ℂ} (hw : Sob.MemH 1 w) :
    (S.dilate R).linFn G (fun y => w ((R : ℂ) * y)) =ᵐ[volume]
      fun y => S.linFn (R ^ 2 * G) w ((R : ℂ) * y) := by
  have hR0 : R ≠ 0 := hR.ne'
  have hwR : (fun y => w ((R : ℂ) * y)) = fun y => w (R • y) := by
    funext y
    rw [Complex.real_smul]
  have h01 := Sob.MemH.weakPartial_comp_smul hw hR0 (γ := (0, 1)) (by decide)
  have h10 := Sob.MemH.weakPartial_comp_smul hw hR0 (γ := (1, 0)) (by decide)
  filter_upwards [h01, h10] with y hy01 hy10
  simp only [linFn, transportPartFn, DilationH.couplingFn_dilate S hS hR w y]
  congr 1
  have hn : ‖(R : ℂ) * y‖ = R * ‖y‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  rw [DilationH.Omega_dilate S hR, hn]
  congr 1
  simp only [Ang.thetaDeriv]
  rw [hwR, hy01, hy10]
  simp only [Complex.real_smul, Complex.re_ofReal_mul, Complex.im_ofReal_mul, zero_add, add_zero,
    pow_one]
  push_cast
  ring

/-- `lem:dilation`(2): `E^{ω̄_R}_ℓ(λ;G) = E^{ω̄}_ℓ(λ;R²G)` for `ℓ ≥ 1`, `Re λ > 0`, where
`E^{ω̄_R}` is computed with `(ξ₁ - log R, ξ₂ - log R)`. -/
theorem dilate_evans (S : SectorSetting) (hS : S.Valid) {R : ℝ} (hR : 0 < R) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (z : ℂ) (hz : 0 < z.re) (G : ℝ) :
    (S.dilate R).evans ℓ z G = S.evans ℓ z (R ^ 2 * G) := by
  exact DilationH.evans_dilate S hS hR ℓ hℓ z hz G

/-- `lem:dilation`(3): at a simple zero `λ_*` of `E^{ω̄}_ℓ(·;R²G)`, for the eigenprofiles
normalized in `L²(ℝ²)` (normalizing factors `n₀`, `n₁`), `|pout_*|`, `|pin_*|`, `|J|`, `|β|` for
`(ω̄_R, G)` equal `R^{-(ℓ+1)}`, `R^{ℓ-1}`, `R^{-2}`, `R^{ℓ+1}` times those for `(ω̄, R²G)`; and
`|β pout_*|` is invariant. -/
theorem dilate_eigendata (S : SectorSetting) (hS : S.Valid) {R : ℝ} (hR : 0 < R) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (z : ℂ) (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z (R ^ 2 * G) = 0)
    (hE' : deriv (fun w => S.evans ℓ w (R ^ 2 * G)) z ≠ 0) :
    let n₀ := Sob.l2 (Ang.ofProfile ℓ (S.gStar ℓ z (R ^ 2 * G)))
    let n₁ := Sob.l2 (Ang.ofProfile ℓ ((S.dilate R).gStar ℓ z G))
    ‖(S.dilate R).poutStar ℓ z G‖ / n₁ =
        R ^ (-((ℓ : ℤ) + 1)) * (‖S.poutStar ℓ z (R ^ 2 * G)‖ / n₀) ∧
      ‖(S.dilate R).pinStar ℓ z G‖ / n₁ =
        R ^ ((ℓ : ℤ) - 1) * (‖S.pinStar ℓ z (R ^ 2 * G)‖ / n₀) ∧
      ‖(S.dilate R).J ℓ z G‖ / n₁ ^ 2 = R ^ (-2 : ℤ) * (‖S.J ℓ z (R ^ 2 * G)‖ / n₀ ^ 2) ∧
      ‖(S.dilate R).betaStar ℓ z G‖ * n₁ =
        R ^ ((ℓ : ℤ) + 1) * (‖S.betaStar ℓ z (R ^ 2 * G)‖ * n₀) ∧
      ‖(S.dilate R).betaStar ℓ z G‖ * ‖(S.dilate R).poutStar ℓ z G‖ =
        ‖S.betaStar ℓ z (R ^ 2 * G)‖ * ‖S.poutStar ℓ z (R ^ 2 * G)‖ := by
  intro n₀ n₁
  have hR0 : R ≠ 0 := hR.ne'
  have hn : n₁ = R * n₀ := by
    show Sob.l2 (Ang.ofProfile ℓ ((S.dilate R).gStar ℓ z G)) =
      R * Sob.l2 (Ang.ofProfile ℓ (S.gStar ℓ z (R ^ 2 * G)))
    rw [DilationH.ofProfile_gStar_dilate S hS hR ℓ hℓ z hz G,
      DilationH.l2_const_mul _ (fun x => Ang.ofProfile ℓ (S.gStar ℓ z (R ^ 2 * G)) ((R : ℂ) * x)),
      DilationH.l2_comp_mul _ hR, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
      ← mul_assoc, sq, mul_assoc R R R⁻¹, mul_inv_cancel₀ hR0, mul_one]
  have hRl : 0 < R ^ ℓ := pow_pos hR ℓ
  have hnorm : ∀ (c : ℝ) (p : ℂ), 0 < c → ‖(c : ℂ) * p‖ = c * ‖p‖ := by
    intro c p hc
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [hn, DilationH.poutStar_dilate S hS hR ℓ hℓ z hz G,
    DilationH.pinStar_dilate S hS hR ℓ hℓ z hz G, DilationH.J_dilate S hS hR ℓ hℓ z hz G,
    DilationH.betaStar_dilate S hS hR ℓ hℓ z hz G, hnorm _ _ (inv_pos.2 hRl),
    hnorm _ (S.pinStar ℓ z (R ^ 2 * G)) hRl, hnorm _ (S.betaStar ℓ z (R ^ 2 * G)) hRl]
  have hz1 : R ^ (-((ℓ : ℤ) + 1)) = (R ^ ℓ)⁻¹ * R⁻¹ := by
    rw [zpow_neg, show ((ℓ : ℤ) + 1) = ((ℓ + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      pow_succ, mul_inv]
  have hz2 : R ^ ((ℓ : ℤ) - 1) = R ^ ℓ * R⁻¹ := by
    rw [zpow_sub₀ hR0, zpow_natCast, zpow_one, div_eq_mul_inv]
  have hz3 : R ^ (-2 : ℤ) = (R ^ 2)⁻¹ := by
    rw [zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
  have hz4 : R ^ ((ℓ : ℤ) + 1) = R ^ ℓ * R := by
    rw [zpow_add_one₀ hR0, zpow_natCast]
  have hRl' : R ^ ℓ * (R ^ ℓ)⁻¹ = 1 := mul_inv_cancel₀ hRl.ne'
  rw [hz1, hz2, hz3, hz4]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring
  · rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring
  · rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, mul_inv]
    ring
  · ring
  · linear_combination (‖S.betaStar ℓ z (R ^ 2 * G)‖ * ‖S.poutStar ℓ z (R ^ 2 * G)‖) * hRl'

end SectorSetting

end NonUniqueEuler
