import NonUniqueEuler.H.Sec4.Edge.Setup

/-!
# Helpers for `P/Sec4/Edge`: the energy argument of `lem:edge`

Manuscript `04_ring.tex:730-769`. Let `I = [r₁, r₂]`, `n = |ℓ|`, `c = (2n)⁻¹`, and let
`ψ` be continuous on `(0,∞)` with `ψ(r) = -c ∫_I K0(r,ρ) ω̄'(ρ) e(ρ) ρ dρ` on `I`, where
`e = iℓψ/(r(λ + iℓΩ))` (`efun`); this is the situation of the proof, with `ψ = 𝒢_ℓ g` and
`g = ω̄' e` (`g = M_λ k_ℓ ψ`). The manuscript's weighted quantities are
* `‖g‖²_W = ∫_I |ω̄'| |e|² r² = N` (`N = N₊ + N₋`, `N_eq_add`),
* `∫ ς ψ ḡ r = T = ∫_I ψ conj(|ω̄'| e r)`, and `Re λ · N = -ℓ Im T` (`energy`),
* `T = -c B(ω̄' e r, |ω̄'| e r)` with the Hermitian form `B` of the kernel (`Bform`, `B_herm`),
* `B(f,g) - B(g,f) = 2(α β̄ - β ᾱ)`, `α = ∫_I ρ^n d⁺ e ρ`, `β = ∫_I ρ^{-n} d⁻ e ρ` (`B_sub`):
  this is the manuscript's `Im ∫ςψḡr = 2 Im X_ab` (the diagonal terms are real), written so that
  only the cross terms, where the kernel factorizes, appear;
* Cauchy–Schwarz: `|α|² ≤ Z₊ N₊`, `|β|² ≤ Z₋ N₋` (`norm_alpha_sq_le`, `norm_beta_sq_le`).
The conclusion `core` is `Re λ ≤ ½ Z_n^{1/2}` when `N > 0`.
-/

noncomputable section

open MeasureTheory Set ComplexConjugate

namespace NonUniqueEuler.EdgeH

open SectorSetting

variable {S : SectorSetting}

/-- `e(r) = iℓψ(r) / (r(λ + iℓΩ(r;G)))`. -/
def efun (S : SectorSetting) (ℓ : ℤ) (z : ℂ) (G : ℝ) (ψ : ℝ → ℂ) (r : ℝ) : ℂ :=
  Complex.I * (ℓ : ℂ) * ψ r / ((r : ℂ) * mres S ℓ z G r)

/-- `ω̄'(ρ) e(ρ) ρ`. -/
def fw (S : SectorSetting) (e : ℝ → ℂ) (ρ : ℝ) : ℂ := ((S.dom ρ : ℝ) : ℂ) * e ρ * (ρ : ℂ)

/-- `|ω̄'(ρ)| e(ρ) ρ`. -/
def gw (S : SectorSetting) (e : ℝ → ℂ) (ρ : ℝ) : ℂ := ((|S.dom ρ| : ℝ) : ℂ) * e ρ * (ρ : ℂ)

/-- `α = ∫_I ρ^n d⁺(ρ) e(ρ) ρ dρ`. -/
def alphaI (S : SectorSetting) (n : ℕ) (e : ℝ → ℂ) : ℂ :=
  ∫ ρ in Icc S.r₁ S.r₂, ((ρ ^ n * dp S ρ : ℝ) : ℂ) * e ρ * (ρ : ℂ)

/-- `β = ∫_I ρ^{-n} d⁻(ρ) e(ρ) ρ dρ`. -/
def betaI (S : SectorSetting) (n : ℕ) (e : ℝ → ℂ) : ℂ :=
  ∫ ρ in Icc S.r₁ S.r₂, (((ρ ^ n)⁻¹ * dn S ρ : ℝ) : ℂ) * e ρ * (ρ : ℂ)

/-- The form `B(f,g) = ∫_I (∫_I K0(x,y) f(y) dy) conj(g(x)) dx`. -/
def Bform (S : SectorSetting) (n : ℕ) (f g : ℝ → ℂ) : ℂ :=
  ∫ x in Icc S.r₁ S.r₂, (∫ y in Icc S.r₁ S.r₂, (K0 n x y : ℂ) * f y) * conj (g x)

/-! ### Continuity -/

theorem continuousOn_efun (hS : S.Valid) {ℓ : ℤ} {z : ℂ} (hz : 0 < z.re) (G : ℝ) {ψ : ℝ → ℂ}
    (hψc : ContinuousOn ψ (Ioi 0)) : ContinuousOn (efun S ℓ z G ψ) (Ioi 0) := by
  refine (continuousOn_const.mul hψc).div
    (Complex.continuous_ofReal.continuousOn.mul (continuousOn_mres hS ℓ z G)) ?_
  intro r hr
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 (ne_of_gt hr)) (mres_ne_zero hz G r)

theorem efun_mul {ℓ : ℤ} {z : ℂ} (hz : 0 < z.re) (G : ℝ) (ψ : ℝ → ℂ) {r : ℝ} (hr : r ≠ 0) :
    (r : ℂ) * mres S ℓ z G r * efun S ℓ z G ψ r = Complex.I * (ℓ : ℂ) * ψ r := by
  have h : (r : ℂ) * mres S ℓ z G r ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 hr) (mres_ne_zero hz G r)
  rw [efun, mul_div_cancel₀ _ h]

variable {e : ℝ → ℂ}

theorem continuousOn_fw (hS : S.Valid) (he : ContinuousOn e (Icc S.r₁ S.r₂)) :
    ContinuousOn (fw S e) (Icc S.r₁ S.r₂) :=
  ((Complex.continuous_ofReal.comp (continuous_dom hS)).continuousOn.mul he).mul
    Complex.continuous_ofReal.continuousOn

theorem continuousOn_gw (hS : S.Valid) (he : ContinuousOn e (Icc S.r₁ S.r₂)) :
    ContinuousOn (gw S e) (Icc S.r₁ S.r₂) :=
  ((Complex.continuous_ofReal.comp (continuous_dom hS).abs).continuousOn.mul he).mul
    Complex.continuous_ofReal.continuousOn

theorem continuousOn_alpha_integrand (hS : S.Valid) (n : ℕ)
    (he : ContinuousOn e (Icc S.r₁ S.r₂)) :
    ContinuousOn (fun ρ : ℝ => ((ρ ^ n * dp S ρ : ℝ) : ℂ) * e ρ * (ρ : ℂ)) (Icc S.r₁ S.r₂) :=
  ((Complex.continuous_ofReal.comp ((continuous_pow n).mul (continuous_dp hS))).continuousOn.mul
    he).mul Complex.continuous_ofReal.continuousOn

theorem continuousOn_inv_pow (hS : S.Valid) (n : ℕ) :
    ContinuousOn (fun ρ : ℝ => (ρ ^ n)⁻¹) (Icc S.r₁ S.r₂) :=
  ((continuous_pow n).continuousOn).inv₀ fun _ hρ => pow_ne_zero n (pos_of_mem_Icc hS hρ).ne'

theorem continuousOn_beta_integrand (hS : S.Valid) (n : ℕ)
    (he : ContinuousOn e (Icc S.r₁ S.r₂)) :
    ContinuousOn (fun ρ : ℝ => (((ρ ^ n)⁻¹ * dn S ρ : ℝ) : ℂ) * e ρ * (ρ : ℂ))
      (Icc S.r₁ S.r₂) :=
  ((Complex.continuous_ofReal.comp_continuousOn
    ((continuousOn_inv_pow hS n).mul (continuous_dn hS).continuousOn)).mul he).mul
    Complex.continuous_ofReal.continuousOn

/-! ### The Hermitian form -/

theorem continuousOn_prod_integrand (hS : S.Valid) (n : ℕ) {f g : ℝ → ℂ}
    (hf : ContinuousOn f (Icc S.r₁ S.r₂)) (hg : ContinuousOn g (Icc S.r₁ S.r₂)) :
    ContinuousOn (fun p : ℝ × ℝ => (K0 n p.1 p.2 : ℂ) * f p.2 * conj (g p.1))
      (Icc S.r₁ S.r₂ ×ˢ Icc S.r₁ S.r₂) := by
  have hK : ContinuousOn (fun p : ℝ × ℝ => (K0 n p.1 p.2 : ℂ)) (Icc S.r₁ S.r₂ ×ˢ Icc S.r₁ S.r₂) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_K0 hS.r₁_pos n)
  have hf2 : ContinuousOn (fun p : ℝ × ℝ => f p.2) (Icc S.r₁ S.r₂ ×ˢ Icc S.r₁ S.r₂) :=
    hf.comp continuousOn_snd fun p hp => hp.2
  have hg1 : ContinuousOn (fun p : ℝ × ℝ => conj (g p.1)) (Icc S.r₁ S.r₂ ×ˢ Icc S.r₁ S.r₂) :=
    Complex.continuous_conj.comp_continuousOn (hg.comp continuousOn_fst fun p hp => hp.1)
  exact (hK.mul hf2).mul hg1

theorem outer_integrable (hS : S.Valid) (n : ℕ) {f g : ℝ → ℂ}
    (hf : ContinuousOn f (Icc S.r₁ S.r₂)) (hg : ContinuousOn g (Icc S.r₁ S.r₂)) :
    Integrable (fun x => (∫ y in Icc S.r₁ S.r₂, (K0 n x y : ℂ) * f y) * conj (g x))
      (volume.restrict (Icc S.r₁ S.r₂)) := by
  have hprod := integrable_prod_Icc (continuousOn_prod_integrand hS n hf hg)
  refine hprod.integral_prod_left.congr (Filter.Eventually.of_forall fun x => ?_)
  exact integral_mul_const (conj (g x)) (fun y => (K0 n x y : ℂ) * f y)

theorem B_herm (hS : S.Valid) (n : ℕ) {f g : ℝ → ℂ}
    (hf : ContinuousOn f (Icc S.r₁ S.r₂)) (hg : ContinuousOn g (Icc S.r₁ S.r₂)) :
    Bform S n f g = conj (Bform S n g f) :=
  integral_kernel_conj_symm (K0 n) (K0_symm n) f g
    (integrable_prod_Icc (continuousOn_prod_integrand hS n hf hg))

/-- The inner integrals: only the cross terms survive (`K0_mul_cross`). -/
theorem inner_id (hS : S.Valid) (hsplit : S.EdgeSplit) (n : ℕ)
    (he : ContinuousOn e (Icc S.r₁ S.r₂)) {r : ℝ} (hr : r ∈ Icc S.r₁ S.r₂) :
    ((|S.dom r| : ℝ) : ℂ) * (∫ ρ in Icc S.r₁ S.r₂, (K0 n r ρ : ℂ) * fw S e ρ) -
        ((S.dom r : ℝ) : ℂ) * (∫ ρ in Icc S.r₁ S.r₂, (K0 n r ρ : ℂ) * gw S e ρ) =
      2 * (((r ^ n)⁻¹ * dn S r : ℝ) : ℂ) * alphaI S n e -
        2 * ((r ^ n * dp S r : ℝ) : ℂ) * betaI S n e := by
  have hr0 := pos_of_mem_Icc hS hr
  have hK : ContinuousOn (fun ρ => ((K0 n r ρ : ℝ) : ℂ)) (Icc S.r₁ S.r₂) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_K0_right hS.r₁_pos n r)
  have i1 : IntegrableOn (fun ρ => ((|S.dom r| : ℝ) : ℂ) * ((K0 n r ρ : ℂ) * fw S e ρ))
      (Icc S.r₁ S.r₂) :=
    (continuousOn_const.mul (hK.mul (continuousOn_fw hS he))).integrableOn_compact isCompact_Icc
  have i2 : IntegrableOn (fun ρ => ((S.dom r : ℝ) : ℂ) * ((K0 n r ρ : ℂ) * gw S e ρ))
      (Icc S.r₁ S.r₂) :=
    (continuousOn_const.mul (hK.mul (continuousOn_gw hS he))).integrableOn_compact isCompact_Icc
  have i3 : IntegrableOn (fun ρ => 2 * (((r ^ n)⁻¹ * dn S r : ℝ) : ℂ) *
      (((ρ ^ n * dp S ρ : ℝ) : ℂ) * e ρ * (ρ : ℂ))) (Icc S.r₁ S.r₂) :=
    (continuousOn_const.mul (continuousOn_alpha_integrand hS n he)).integrableOn_compact
      isCompact_Icc
  have i4 : IntegrableOn (fun ρ => 2 * ((r ^ n * dp S r : ℝ) : ℂ) *
      ((((ρ ^ n)⁻¹ * dn S ρ : ℝ) : ℂ) * e ρ * (ρ : ℂ))) (Icc S.r₁ S.r₂) :=
    (continuousOn_const.mul (continuousOn_beta_integrand hS n he)).integrableOn_compact
      isCompact_Icc
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub i1 i2, alphaI, betaI,
    ← integral_const_mul, ← integral_const_mul, ← integral_sub i3 i4]
  refine setIntegral_congr_fun measurableSet_Icc fun ρ hρ => ?_
  have hρ0 := pos_of_mem_Icc hS hρ
  have hk' := congrArg (fun x : ℝ => (x : ℂ)) (K0_mul_cross hsplit n hr0 hρ0)
  simp only [fw, gw]
  push_cast at hk' ⊢
  linear_combination (e ρ * (ρ : ℂ)) * hk'

/-- `B(ω̄'eρ, |ω̄'|eρ) - B(|ω̄'|eρ, ω̄'eρ) = 2(αβ̄ - βᾱ)`. -/
theorem B_sub (hS : S.Valid) (hsplit : S.EdgeSplit) (n : ℕ)
    (he : ContinuousOn e (Icc S.r₁ S.r₂)) :
    Bform S n (fw S e) (gw S e) - Bform S n (gw S e) (fw S e) =
      2 * (alphaI S n e * conj (betaI S n e) - betaI S n e * conj (alphaI S n e)) := by
  have hint1 := outer_integrable hS n (continuousOn_fw hS he) (continuousOn_gw hS he)
  have hint2 := outer_integrable hS n (continuousOn_gw hS he) (continuousOn_fw hS he)
  have hpt : ∀ x ∈ Icc S.r₁ S.r₂,
      (∫ y in Icc S.r₁ S.r₂, (K0 n x y : ℂ) * fw S e y) * conj (gw S e x) -
          (∫ y in Icc S.r₁ S.r₂, (K0 n x y : ℂ) * gw S e y) * conj (fw S e x) =
        (2 * alphaI S n e) * conj ((((x ^ n)⁻¹ * dn S x : ℝ) : ℂ) * e x * (x : ℂ)) -
          (2 * betaI S n e) * conj (((x ^ n * dp S x : ℝ) : ℂ) * e x * (x : ℂ)) := by
    intro x hx
    have h := inner_id hS hsplit n he hx
    have hg : conj (gw S e x) = ((|S.dom x| : ℝ) : ℂ) * conj (e x) * (x : ℂ) := by
      simp only [gw, map_mul, Complex.conj_ofReal]
    have hf : conj (fw S e x) = ((S.dom x : ℝ) : ℂ) * conj (e x) * (x : ℂ) := by
      simp only [fw, map_mul, Complex.conj_ofReal]
    rw [hg, hf]
    simp only [map_mul, Complex.conj_ofReal]
    linear_combination (conj (e x) * (x : ℂ)) * h
  have i5 : Integrable (fun x : ℝ => (2 * alphaI S n e) *
      conj ((((x ^ n)⁻¹ * dn S x : ℝ) : ℂ) * e x * (x : ℂ))) (volume.restrict (Icc S.r₁ S.r₂)) :=
    (continuousOn_const.mul (Complex.continuous_conj.comp_continuousOn
      (continuousOn_beta_integrand hS n he))).integrableOn_compact isCompact_Icc
  have i6 : Integrable (fun x : ℝ => (2 * betaI S n e) *
      conj (((x ^ n * dp S x : ℝ) : ℂ) * e x * (x : ℂ))) (volume.restrict (Icc S.r₁ S.r₂)) :=
    (continuousOn_const.mul (Complex.continuous_conj.comp_continuousOn
      (continuousOn_alpha_integrand hS n he))).integrableOn_compact isCompact_Icc
  rw [Bform, Bform, ← integral_sub hint1 hint2, setIntegral_congr_fun measurableSet_Icc hpt,
    integral_sub i5 i6, integral_const_mul, integral_const_mul, integral_conj, integral_conj]
  rw [alphaI, betaI]
  ring

/-! ### Cauchy–Schwarz -/

theorem norm_alpha_sq_le (hS : S.Valid) (n : ℕ) (he : ContinuousOn e (Icc S.r₁ S.r₂)) :
    ‖alphaI S n e‖ ^ 2 ≤ Zp S n * ∫ r in Icc S.r₁ S.r₂, (‖e r‖ * r) ^ 2 * dp S r := by
  have hen : ContinuousOn (fun r => ‖e r‖ * r) (Icc S.r₁ S.r₂) :=
    he.norm.mul continuousOn_id
  have h1 : ‖alphaI S n e‖ ≤ ∫ r in Icc S.r₁ S.r₂, r ^ n * (‖e r‖ * r) * dp S r := by
    refine (norm_integral_le_integral_norm _).trans
      (le_of_eq (setIntegral_congr_fun measurableSet_Icc fun r hr => ?_))
    have hr0 := pos_of_mem_Icc hS hr
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hr0.le n) (dp_nonneg r)),
      abs_of_pos hr0]
    ring
  have i1 : Integrable (fun r : ℝ => (r ^ n) ^ 2 * dp S r) (volume.restrict (Icc S.r₁ S.r₂)) :=
    (((continuous_pow n).pow 2).mul (continuous_dp hS)).continuousOn.integrableOn_compact
      isCompact_Icc
  have i2 : Integrable (fun r : ℝ => (‖e r‖ * r) ^ 2 * dp S r)
      (volume.restrict (Icc S.r₁ S.r₂)) :=
    ((hen.pow 2).mul (continuous_dp hS).continuousOn).integrableOn_compact isCompact_Icc
  have i3 : Integrable (fun r : ℝ => r ^ n * (‖e r‖ * r) * dp S r)
      (volume.restrict (Icc S.r₁ S.r₂)) :=
    (((continuous_pow n).continuousOn.mul hen).mul (continuous_dp hS).continuousOn).integrableOn_compact
      isCompact_Icc
  have h2 := sq_integral_mul_le (μ := volume.restrict (Icc S.r₁ S.r₂)) (A := fun r => r ^ n)
    (B := fun r => ‖e r‖ * r) (w := dp S) (Filter.Eventually.of_forall dp_nonneg) i1 i2 i3
  calc ‖alphaI S n e‖ ^ 2 ≤ (∫ r in Icc S.r₁ S.r₂, r ^ n * (‖e r‖ * r) * dp S r) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem norm_beta_sq_le (hS : S.Valid) (n : ℕ) (he : ContinuousOn e (Icc S.r₁ S.r₂)) :
    ‖betaI S n e‖ ^ 2 ≤ Zn S n * ∫ r in Icc S.r₁ S.r₂, (‖e r‖ * r) ^ 2 * dn S r := by
  have hen : ContinuousOn (fun r => ‖e r‖ * r) (Icc S.r₁ S.r₂) :=
    he.norm.mul continuousOn_id
  have hinv := continuousOn_inv_pow hS n
  have h1 : ‖betaI S n e‖ ≤ ∫ r in Icc S.r₁ S.r₂, (r ^ n)⁻¹ * (‖e r‖ * r) * dn S r := by
    refine (norm_integral_le_integral_norm _).trans
      (le_of_eq (setIntegral_congr_fun measurableSet_Icc fun r hr => ?_))
    have hr0 := pos_of_mem_Icc hS hr
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (inv_nonneg.2 (pow_nonneg hr0.le n)) (dn_nonneg r)),
      abs_of_pos hr0]
    ring
  have i1 : Integrable (fun r : ℝ => ((r ^ n)⁻¹) ^ 2 * dn S r)
      (volume.restrict (Icc S.r₁ S.r₂)) :=
    ((hinv.pow 2).mul (continuous_dn hS).continuousOn).integrableOn_compact isCompact_Icc
  have i2 : Integrable (fun r : ℝ => (‖e r‖ * r) ^ 2 * dn S r)
      (volume.restrict (Icc S.r₁ S.r₂)) :=
    ((hen.pow 2).mul (continuous_dn hS).continuousOn).integrableOn_compact isCompact_Icc
  have i3 : Integrable (fun r : ℝ => (r ^ n)⁻¹ * (‖e r‖ * r) * dn S r)
      (volume.restrict (Icc S.r₁ S.r₂)) :=
    ((hinv.mul hen).mul (continuous_dn hS).continuousOn).integrableOn_compact isCompact_Icc
  have h2 := sq_integral_mul_le (μ := volume.restrict (Icc S.r₁ S.r₂)) (A := fun r => (r ^ n)⁻¹)
    (B := fun r => ‖e r‖ * r) (w := dn S) (Filter.Eventually.of_forall dn_nonneg) i1 i2 i3
  calc ‖betaI S n e‖ ^ 2 ≤ (∫ r in Icc S.r₁ S.r₂, (r ^ n)⁻¹ * (‖e r‖ * r) * dn S r) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem N_eq_add (hS : S.Valid) (he : ContinuousOn e (Icc S.r₁ S.r₂)) :
    ∫ r in Icc S.r₁ S.r₂, |S.dom r| * ‖e r‖ ^ 2 * r ^ 2 =
      (∫ r in Icc S.r₁ S.r₂, (‖e r‖ * r) ^ 2 * dp S r) +
        ∫ r in Icc S.r₁ S.r₂, (‖e r‖ * r) ^ 2 * dn S r := by
  have hen : ContinuousOn (fun r => ‖e r‖ * r) (Icc S.r₁ S.r₂) :=
    he.norm.mul continuousOn_id
  have i1 : Integrable (fun r : ℝ => (‖e r‖ * r) ^ 2 * dp S r)
      (volume.restrict (Icc S.r₁ S.r₂)) :=
    ((hen.pow 2).mul (continuous_dp hS).continuousOn).integrableOn_compact isCompact_Icc
  have i2 : Integrable (fun r : ℝ => (‖e r‖ * r) ^ 2 * dn S r)
      (volume.restrict (Icc S.r₁ S.r₂)) :=
    ((hen.pow 2).mul (continuous_dn hS).continuousOn).integrableOn_compact isCompact_Icc
  rw [← integral_add i1 i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only
  rw [abs_dom_eq]
  ring

end NonUniqueEuler.EdgeH
