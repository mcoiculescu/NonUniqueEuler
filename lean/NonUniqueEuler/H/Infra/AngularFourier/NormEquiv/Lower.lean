import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.Sectors
import NonUniqueEuler.I.Infra.AngularFourier.Parseval
import NonUniqueEuler.I.Infra.SobolevOneD.Basic

/-!
# Helper for `P/Infra/AngularFourier/NormEquiv`: the lower bound `c ∑_ℓ ‖g_ℓ‖²_{k,ℓ} ≤ ‖w‖²_{H^k}`

Manuscript `lem:norm-equiv` (`04_ring.tex:851-863`), lower bound: the polar derivatives
`∂_θ^n ∂_r^i w` (`i + n ≤ k`) are bounded in `L²` by `C ‖w‖_{H^k}` (`polar_iter`); by Parseval
in `θ` (`hasSum_angularSector_sq`) and `angularSector_polar`,
`‖∂_θ^n ∂_r^i w‖²_{L²} = 2π ∑_ℓ ℓ^{2n} ‖∂_r^i g_ℓ‖²_{L²(r dr)}`; summing over `i + n ≤ k` and
using `2^{-p}(1+x)^p ≤ ∑_{n ≤ p} x^n` (`pow_weights`) gives the claim, including summability.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang.NormEquivAux

open Sob

/-- Reindexing `∑_{|γ| ≤ k}` as `∑_{j ≤ k} ∑_{n ≤ k - j}`. -/
theorem sum_multiIdx (k : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ p ∈ multiIdx k, f p.1 p.2 =
      ∑ j ∈ Finset.range (k + 1), ∑ n ∈ Finset.range (k - j + 1), f j n := by
  rw [multiIdx, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
  omega

/-- `2^{-k} ∑_{j ≤ k} (1+x)^{k-j} a_j ≤ ∑_{i+n ≤ k} x^n a_i`. -/
theorem weights_lower (k : ℕ) {x : ℝ} (hx : 0 ≤ x) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) :
    (2 : ℝ)⁻¹ ^ k * ∑ j ∈ Finset.range (k + 1), (1 + x) ^ (k - j) * a j ≤
      ∑ p ∈ multiIdx k, x ^ p.2 * a p.1 := by
  rw [sum_multiIdx k (fun j n => x ^ n * a j), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← Finset.sum_mul]
  have hw := (pow_weights hx (k - j)).1
  have h2 : (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ (k - j) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.sub_le k j)
  have h1 : 0 ≤ (1 + x) ^ (k - j) := pow_nonneg (by linarith) _
  have ha' := ha j
  calc (2 : ℝ)⁻¹ ^ k * ((1 + x) ^ (k - j) * a j)
        ≤ (2 : ℝ)⁻¹ ^ (k - j) * ((1 + x) ^ (k - j) * a j) := by gcongr
    _ = ((2 : ℝ)⁻¹ ^ (k - j) * (1 + x) ^ (k - j)) * a j := by ring
    _ ≤ (∑ n ∈ Finset.range (k - j + 1), x ^ n) * a j := by gcongr

theorem norm_sq_mul_pow (ℓ : ℤ) (n : ℕ) (z : ℂ) :
    ‖((ℓ : ℂ) * Complex.I) ^ n * z‖ ^ 2 = ((ℓ : ℝ) ^ 2) ^ n * ‖z‖ ^ 2 := by
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast, mul_pow,
    ← pow_mul, ← pow_mul, mul_comm n 2, pow_mul, sq_abs]
  ring

/-- The lower bound of `lem:norm-equiv`, with summability of the sector norms. -/
theorem lower_bound (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) :
    ∃ c : ℝ, 0 < c ∧ ∀ w : ℂ → ℂ, MemH k w → (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → w x = 0) →
      Summable (fun ℓ : ℤ => secNormSq k ℓ (Icc ρm ρp) (Polar.angularSector w ℓ)) ∧
        c * ∑' ℓ : ℤ, secNormSq k ℓ (Icc ρm ρp) (Polar.angularSector w ℓ) ≤ normH k w ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := polar_iter k (ρp := ρp) hρm
  set B : ℝ := 2 ^ k * (2 * π)⁻¹ * ((multiIdx k).card * C ^ 2 + 1) with hBdef
  have hB : 0 < B := by positivity
  refine ⟨B⁻¹, inv_pos.2 hB, fun w hw hwK => ?_⟩
  set a : ℤ → ℕ → ℝ := fun ℓ j =>
    ∫ r in Icc ρm ρp, ‖weakDeriv1On (Ioi 0) j (Polar.angularSector w ℓ) r‖ ^ 2 * r with hadef
  have ha : ∀ ℓ j, 0 ≤ a ℓ j := fun ℓ j =>
    setIntegral_nonneg measurableSet_Icc fun r hr =>
      mul_nonneg (sq_nonneg _) (hρm.le.trans hr.1)
  have hIcc : Icc ρm ρp ⊆ Ioi (0 : ℝ) := fun r hr => lt_of_lt_of_le hρm hr.1
  -- Parseval for each polar derivative
  have hp : ∀ p ∈ multiIdx k, HasSum (fun ℓ : ℤ => 2 * π * (((ℓ : ℝ) ^ 2) ^ p.2 * a ℓ p.1))
      (l2 (thetaDeriv^[p.2] (radDeriv^[p.1] w)) ^ 2) := by
    intro p hpk
    have hpk' := mem_multiIdx.1 hpk
    obtain ⟨hm, -, -⟩ := hC w hw hwK p.1 p.2 hpk'
    have hL2 : MemLp (thetaDeriv^[p.2] (radDeriv^[p.1] w)) 2 volume :=
      (memH_iff.1 (hm.mono_order (Nat.zero_le _))).1
    have hs := hasSum_angularSector_sq hL2
    convert hs using 1
    funext ℓ
    congr 1
    have e1 := angularSector_polar hρm hw hwK ℓ p.1 p.2 hpk'
    have hsupp := weakDeriv1On_supp hρm hw hwK ℓ (i := p.1) (by omega)
    symm
    calc ∫ r in Ioi 0, ‖Polar.angularSector (thetaDeriv^[p.2] (radDeriv^[p.1] w)) ℓ r‖ ^ 2 * r
        = ∫ r in Ioi 0, ((ℓ : ℝ) ^ 2) ^ p.2 *
            (‖weakDeriv1On (Ioi 0) p.1 (Polar.angularSector w ℓ) r‖ ^ 2 * r) := by
          refine integral_congr_ae ?_
          filter_upwards [e1] with r hr
          rw [hr, norm_sq_mul_pow]
          ring
      _ = ((ℓ : ℝ) ^ 2) ^ p.2 *
            ∫ r in Ioi 0, ‖weakDeriv1On (Ioi 0) p.1 (Polar.angularSector w ℓ) r‖ ^ 2 * r :=
          integral_const_mul _ _
      _ = ((ℓ : ℝ) ^ 2) ^ p.2 * a ℓ p.1 := by
          rw [hadef]
          congr 1
          refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
            measurableSet_Ioi.nullMeasurableSet hIcc ?_
          rw [ae_restrict_iff' measurableSet_Ioi] at hsupp
          filter_upwards [hsupp] with r hr hr'
          rw [hr hr'.1 hr'.2]
          simp
  set T : ℤ → ℝ := fun ℓ => ∑ p ∈ multiIdx k, ((ℓ : ℝ) ^ 2) ^ p.2 * a ℓ p.1 with hTdef
  set S0 : ℝ := ∑ p ∈ multiIdx k, l2 (thetaDeriv^[p.2] (radDeriv^[p.1] w)) ^ 2 with hS0
  have hT : HasSum T ((2 * π)⁻¹ * S0) := by
    have h1 := (hasSum_sum hp).mul_left (2 * π)⁻¹
    have hfun : (fun ℓ : ℤ => (2 * π)⁻¹ *
        ∑ p ∈ multiIdx k, 2 * π * (((ℓ : ℝ) ^ 2) ^ p.2 * a ℓ p.1)) = T := by
      funext ℓ
      rw [hTdef, ← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    rw [hfun] at h1
    exact h1
  have hle : ∀ ℓ : ℤ, secNormSq k ℓ (Icc ρm ρp) (Polar.angularSector w ℓ) ≤ 2 ^ k * T ℓ := by
    intro ℓ
    have hw' := weights_lower k (sq_nonneg (ℓ : ℝ)) (a ℓ) (ha ℓ)
    have heq : secNormSq k ℓ (Icc ρm ρp) (Polar.angularSector w ℓ) =
        ∑ j ∈ Finset.range (k + 1), (1 + (ℓ : ℝ) ^ 2) ^ (k - j) * a ℓ j := rfl
    rw [heq]
    have h2 : (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
    calc ∑ j ∈ Finset.range (k + 1), (1 + (ℓ : ℝ) ^ 2) ^ (k - j) * a ℓ j
        = 2 ^ k * ((2 : ℝ)⁻¹ ^ k *
            ∑ j ∈ Finset.range (k + 1), (1 + (ℓ : ℝ) ^ 2) ^ (k - j) * a ℓ j) := by
          rw [← mul_assoc, h2, one_mul]
      _ ≤ 2 ^ k * T ℓ := by gcongr
  have hnn : ∀ ℓ : ℤ, 0 ≤ secNormSq k ℓ (Icc ρm ρp) (Polar.angularSector w ℓ) := fun ℓ =>
    secNormSq_nonneg k ℓ measurableSet_Icc (fun r hr => Set.mem_Ici.2 (le_of_lt (hIcc hr))) _
  have hsum : Summable (fun ℓ : ℤ => secNormSq k ℓ (Icc ρm ρp) (Polar.angularSector w ℓ)) :=
    Summable.of_nonneg_of_le hnn hle (hT.summable.mul_left _)
  refine ⟨hsum, ?_⟩
  -- the tsum bound
  have htsum : ∑' ℓ : ℤ, secNormSq k ℓ (Icc ρm ρp) (Polar.angularSector w ℓ) ≤
      2 ^ k * ((2 * π)⁻¹ * S0) := by
    calc ∑' ℓ : ℤ, secNormSq k ℓ (Icc ρm ρp) (Polar.angularSector w ℓ)
        ≤ ∑' ℓ : ℤ, 2 ^ k * T ℓ := Summable.tsum_le_tsum hle hsum (hT.summable.mul_left _)
      _ = 2 ^ k * ((2 * π)⁻¹ * S0) := by rw [tsum_mul_left, hT.tsum_eq]
  have hS : S0 ≤ (multiIdx k).card * C ^ 2 * normH k w ^ 2 := by
    calc S0 ≤ ∑ p ∈ multiIdx k, (C * normH k w) ^ 2 := by
          refine Finset.sum_le_sum fun p hpk => ?_
          obtain ⟨hm, -, hn⟩ := hC w hw hwK p.1 p.2 (mem_multiIdx.1 hpk)
          have h1 := hm.l2_le
          have h0 := l2_nonneg (thetaDeriv^[p.2] (radDeriv^[p.1] w))
          exact pow_le_pow_left₀ h0 (h1.trans hn) 2
      _ = (multiIdx k).card * C ^ 2 * normH k w ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hfin : ∑' ℓ : ℤ, secNormSq k ℓ (Icc ρm ρp) (Polar.angularSector w ℓ) ≤
      B * normH k w ^ 2 := by
    have hn2 := sq_nonneg (normH k w)
    have hpi : 0 < (2 * π)⁻¹ := by positivity
    calc _ ≤ 2 ^ k * ((2 * π)⁻¹ * S0) := htsum
      _ ≤ 2 ^ k * ((2 * π)⁻¹ * ((multiIdx k).card * C ^ 2 * normH k w ^ 2)) := by gcongr
      _ ≤ B * normH k w ^ 2 := by
          rw [hBdef]
          have : (2 : ℝ) ^ k * ((2 * π)⁻¹ * ((multiIdx k).card * C ^ 2 * normH k w ^ 2)) +
              2 ^ k * (2 * π)⁻¹ * normH k w ^ 2 =
              2 ^ k * (2 * π)⁻¹ * ((multiIdx k).card * C ^ 2 + 1) * normH k w ^ 2 := by ring
          have h3 : 0 ≤ 2 ^ k * (2 * π)⁻¹ * normH k w ^ 2 := by positivity
          linarith
  calc B⁻¹ * ∑' ℓ : ℤ, secNormSq k ℓ (Icc ρm ρp) (Polar.angularSector w ℓ)
      ≤ B⁻¹ * (B * normH k w ^ 2) := by gcongr
    _ = normH k w ^ 2 := by rw [← mul_assoc, inv_mul_cancel₀ hB.ne', one_mul]

end NonUniqueEuler.Ang.NormEquivAux
