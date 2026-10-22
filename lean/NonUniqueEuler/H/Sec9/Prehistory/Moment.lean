import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.Multipole.Moments
import NonUniqueEuler.I.Sec6.RegionsBasic

/-!
# Helpers for `P/Sec9/Prehistory`: `q_j = 2π pout_3[w_j] + 2π pout_3[ν^in_j]` and the ring part

Helper file of `P/Sec9/Prehistory.lean` (`lem:prehistory`, `09_relay.tex:1059-1075`).
In ring-`j` units, `D_j(t) = S_j(t) ⊔ D_{j+1}(t)` gives
`Q_m[ω_{≥j}(t)] = A_jr_j^{m+2}(Q_m[Φ + w_j(t)] + Q_m[ν^in_j])`; `Q_m[Φ] = 0` (radial), and
`conj Q_m[g] = 2π pout_m[g]` for real `g`.

* `integrable_moment`, `Qm_add`, `omegaGe_split`, `conjQm_split`: additivity of `Q_3` and the
  splitting `ω_{≥j}(t) = ω(t)1_{S_j(t)} + ω_{≥j+1}(t)` (copied from `H/Sec9/Deep/Split.lean`, proof
  proof `Sec9/Deep`; helper files may not be imported across proofs);
* `integral_sub_of_integral_eq_zero`, `Qm_Phi_eq_zero`, `Qm_scaleVort`, `conjQm_omegaRing_eq`:
  `conj Q_3[ω(t)1_{S_j(t)}]/(A_jr_j⁵) = 2π pout_3[w_j(t)]` (copied from
  `H/Sec9/KickTrue/RingMoment.lean`, proof `Sec9/KickTrue`);
* `conjQm_div_eq_pout_units`: `conj Q_3[g]/(A_jr_j⁵) = 2π pout_3[A_j⁻¹g(r_j·)]`;
* `q_eq`: `q_j(t) = 2π pout_3[w_j(t)] + 2π pout_3[ν^in_j(t)]` (`1 ≤ j ≤ n`, `t ≥ 0`);
* `norm_two_pi_pout_w_le`: `|2π pout_3[w_j(t)]| = |Q_3[w_j(t)]| ≤ 2³‖w_j(t)‖_{L¹}` when
  `S_j(t) ⊂ N_j` (`w_j(t)` supported in `N ⊂ B̄₂`).
Everything here is proved.
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate

namespace NonUniqueEuler

namespace Relay

namespace PrehistoryAux

open RingData Datum

/-! ### Additivity of `Q_3` and the splitting of `ω_{≥j}` (from `H/Sec9/Deep/Split.lean`) -/

/-- The integrand `g(y) y³` of `Q_3[g]` is integrable for continuous compactly supported real `g`. -/
theorem integrable_moment {g : ℂ → ℝ} (hc : Continuous g) (hs : HasCompactSupport g) :
    Integrable (fun y : ℂ => ((g y : ℝ) : ℂ) * y ^ 3) := by
  have hc' : Continuous (fun y : ℂ => ((g y : ℝ) : ℂ) * y ^ 3) := by fun_prop
  refine hc'.integrable_of_hasCompactSupport ?_
  have h : HasCompactSupport (fun y : ℂ => ((g y : ℝ) : ℂ)) := hs.comp_left Complex.ofReal_zero
  exact h.mul_right

/-- Additivity of `Q_3` on real functions with integrable moment integrands. -/
theorem Qm_add {g h : ℂ → ℝ} (hg : Integrable (fun y : ℂ => ((g y : ℝ) : ℂ) * y ^ 3))
    (hh : Integrable (fun y : ℂ => ((h y : ℝ) : ℂ) * y ^ 3)) :
    BS.Qm 3 (fun x => ((g x + h x : ℝ) : ℂ)) =
      BS.Qm 3 (fun x => ((g x : ℝ) : ℂ)) + BS.Qm 3 (fun x => ((h x : ℝ) : ℂ)) := by
  unfold BS.Qm
  rw [← integral_add hg hh]
  congr 1
  funext y
  push_cast
  ring

/-- `ω_{≥j}(t) = ω(t)1_{S_j(t)} + ω_{≥j+1}(t)` for `1 ≤ j ≤ n` and `t ≥ 0` (`09_relay.tex:1036-1039`,
from `lem:regions-basic`(3)); both parts are continuous with compact support (`ω_{≥n+1} = 0`). -/
theorem omegaGe_split (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {j : ℕ}
    (hj : 1 ≤ j) (hjn : j ≤ P.n) {t : ℝ} (ht : 0 ≤ t) :
    (∀ x, P.omegaGe j t x = P.omegaRing j t x + P.omegaGe (j + 1) t x) ∧
      Continuous (P.omegaRing j t) ∧ HasCompactSupport (P.omegaRing j t) ∧
      Continuous (P.omegaGe (j + 1) t) ∧ HasCompactSupport (P.omegaGe (j + 1) t) := by
  have hjI : j ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨hj, hjn⟩
  obtain ⟨-, -, hsum, -, -, -, ⟨hcd, hcs, -, -⟩, -⟩ := P.regions_basic_three hP hN hjI ht
  have hnext : (∀ x, P.omegaGe (j + 1) t x = ∑ i ∈ Finset.Icc (j + 1) P.n, P.omegaRing i t x) ∧
      Continuous (P.omegaGe (j + 1) t) ∧ HasCompactSupport (P.omegaGe (j + 1) t) := by
    rcases Nat.lt_or_ge j P.n with hlt | hge
    · have hjI' : j + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨by omega, hlt⟩
      obtain ⟨-, -, hsum', -, -, -, -, ⟨hcd', hcs', -, -⟩⟩ :=
        P.regions_basic_three hP hN hjI' ht
      exact ⟨fun x => by rw [hsum'], hcd'.continuous, hcs'⟩
    · have hjeq : j + 1 = P.n + 1 := by omega
      rw [hjeq, P.omegaGe_succ_n]
      refine ⟨fun x => ?_, continuous_const, HasCompactSupport.zero⟩
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, Pi.zero_apply]
  obtain ⟨hnsum, hnc, hns⟩ := hnext
  refine ⟨fun x => ?_, hcd.continuous, hcs, hnc, hns⟩
  rw [hsum, hnsum, ← Finset.insert_Icc_add_one_left_eq_Icc hjn]
  exact Finset.sum_insert (by simp)

/-- `conj Q_3[ω_{≥j}(t)] = conj Q_3[ω(t)1_{S_j(t)}] + conj Q_3[ω_{≥j+1}(t)]` (`09_relay.tex:1063-1066`). -/
theorem conjQm_split (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {j : ℕ}
    (hj : 1 ≤ j) (hjn : j ≤ P.n) {t : ℝ} (ht : 0 ≤ t) :
    conj (BS.Qm 3 fun x => ((P.omegaGe j t x : ℝ) : ℂ)) =
      conj (BS.Qm 3 fun x => ((P.omegaRing j t x : ℝ) : ℂ)) +
        conj (BS.Qm 3 fun x => ((P.omegaGe (j + 1) t x : ℝ) : ℂ)) := by
  obtain ⟨hsplit, hc1, hs1, hc2, hs2⟩ := omegaGe_split P hP hN hj hjn ht
  have hfun : (fun x => ((P.omegaGe j t x : ℝ) : ℂ)) =
      fun x => ((P.omegaRing j t x + P.omegaGe (j + 1) t x : ℝ) : ℂ) := by
    funext x
    rw [hsplit x]
  rw [hfun, Qm_add (integrable_moment hc1 hs1) (integrable_moment hc2 hs2), map_add]

/-! ### The ring part (from `H/Sec9/KickTrue/RingMoment.lean`) -/

/-- `∫(f - g) = ∫f` when `g` is integrable with `∫g = 0`. -/
theorem integral_sub_of_integral_eq_zero {f g : ℂ → ℂ} (hg : Integrable g)
    (hg0 : ∫ y, g y = 0) : ∫ y, (f y - g y) = ∫ y, f y := by
  by_cases hf : Integrable f
  · rw [integral_sub hf hg, hg0, sub_zero]
  · have hfg : ¬ Integrable (fun y => f y - g y) := by
      intro h
      apply hf
      refine (h.add hg).congr (Filter.Eventually.of_forall fun y => ?_)
      simp
    rw [integral_undef hf, integral_undef hfg]

/-- `Q_3[Φ] = 0` and `Φ(y)y³` is integrable (`Φ ∈ C_c^∞` radial, `lem:ring-facts`). -/
theorem Qm_Phi_eq_zero {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    Integrable (fun y : ℂ => ((ringPhi χ y : ℝ) : ℂ) * y ^ 3) ∧
      ∫ y : ℂ, ((ringPhi χ y : ℝ) : ℂ) * y ^ 3 = 0 := by
  obtain ⟨hcd, hcs, hrad, -⟩ := ringFacts_of_admissible hχ
  have hc : Continuous (ringPhi χ) := hcd.continuous
  constructor
  · exact integrable_moment hc hcs
  · have hrot : ∀ θ : ℝ, (fun x => ((ringPhi χ (rot θ x) : ℝ) : ℂ)) =ᵐ[volume]
        fun x => ((ringPhi χ x : ℝ) : ℂ) := by
      intro θ
      exact Filter.Eventually.of_forall fun x => by simp only [hrad θ x]
    have h := Multipole.moment_eq_zero_of_rot_invariant (g := fun x => ((ringPhi χ x : ℝ) : ℂ))
      hrot (l := (3 : ℤ)) (by norm_num)
    have h2 := BS.Qm_eq_moment 3 (fun y => ((ringPhi χ y : ℝ) : ℂ))
    simp only [BS.Qm] at h2
    rw [h2]
    exact_mod_cast h

/-- Scaling of `Q_3`: `Q_3[A⁻¹ g(r ·)] = A⁻¹ r⁻⁵ Q_3[g]` for `r > 0`. -/
theorem Qm_scaleVort (A r : ℝ) (hr : 0 < r) (g : ℂ → ℝ) :
    ∫ y : ℂ, ((scaleVort A r g y : ℝ) : ℂ) * y ^ 3 =
      ((A⁻¹ * (r ^ 5)⁻¹ : ℝ) : ℂ) * ∫ x : ℂ, ((g x : ℝ) : ℂ) * x ^ 3 := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hpt : ∀ y : ℂ, ((scaleVort A r g y : ℝ) : ℂ) * y ^ 3 =
      ((A⁻¹ * (r ^ 3)⁻¹ : ℝ) : ℂ) *
        ((fun x : ℂ => ((g x : ℝ) : ℂ) * x ^ 3) (r • y)) := by
    intro y
    simp only [scaleVort, Complex.real_smul]
    push_cast
    field_simp
  have hsc : ∫ x : ℂ, ((g (r • x) : ℝ) : ℂ) * (r • x) ^ 3 =
      |((r ^ 2)⁻¹)| • ∫ x : ℂ, ((g x : ℝ) : ℂ) * x ^ 3 := by
    have := Measure.integral_comp_smul (volume : Measure ℂ)
      (fun x : ℂ => ((g x : ℝ) : ℂ) * x ^ 3) r
    rwa [Complex.finrank_real_complex] at this
  simp_rw [hpt]
  rw [integral_const_mul, hsc]
  rw [abs_of_pos (by positivity : (0 : ℝ) < (r ^ 2)⁻¹), Complex.real_smul, ← mul_assoc]
  congr 1
  push_cast
  field_simp

/-- `conj Q_3[ω(t)1_{S_j(t)}]/(A_j r_j⁵) = 2π pout_3[w_j(t)]` for a valid approximation and every
level `j` and time `t` (`Φ` radial, `w_j(t)` real). -/
theorem conjQm_omegaRing_eq (P : Approx) (hP : P.Valid) (j : ℕ) (t : ℝ) :
    conj (BS.Qm 3 fun x => ((P.omegaRing j t x : ℝ) : ℂ)) /
        ((P.A j * P.r j ^ (3 + 2) : ℝ) : ℂ) =
      2 * Real.pi * BS.pout 3 (P.w j t) := by
  have hA := hP.A_pos j
  have hr := hP.r_pos j
  obtain ⟨hΦi, hΦ0⟩ := Qm_Phi_eq_zero hP.admissible
  have hw : P.w j t = fun y => ((P.wR j t y : ℝ) : ℂ) := rfl
  have hsplit : (fun y : ℂ => ((P.wR j t y : ℝ) : ℂ) * y ^ 3) = fun y =>
      ((P.unitsVort j (P.omegaRing j t) y : ℝ) : ℂ) * y ^ 3 -
        ((ringPhi P.χ y : ℝ) : ℂ) * y ^ 3 := by
    funext y
    simp only [Approx.wR]
    push_cast
    ring
  have hQ : BS.Qm 3 (fun y => ((P.wR j t y : ℝ) : ℂ)) =
      (((P.A j)⁻¹ * (P.r j ^ 5)⁻¹ : ℝ) : ℂ) * BS.Qm 3 (fun x => ((P.omegaRing j t x : ℝ) : ℂ)) := by
    simp only [BS.Qm]
    rw [hsplit, integral_sub_of_integral_eq_zero hΦi hΦ0]
    exact Qm_scaleVort _ _ hr _
  rw [hw, BS.two_pi_mul_pout_ofReal, hQ, map_mul, Complex.conj_ofReal, div_eq_inv_mul]
  congr 1
  push_cast
  ring

/-! ### The inner part and the splitting of `q_j` -/

/-- `conj Q_3[g]/(A_j r_j⁵) = 2π pout_3[A_j⁻¹g(r_j·)]` (scaling to ring-`j` units; `g` real). -/
theorem conjQm_div_eq_pout_units (P : Approx) (hP : P.Valid) (j : ℕ) (g : ℂ → ℝ) :
    conj (BS.Qm 3 fun x => ((g x : ℝ) : ℂ)) / ((P.A j * P.r j ^ (3 + 2) : ℝ) : ℂ) =
      2 * Real.pi * BS.pout 3 (fun y => ((P.unitsVort j g y : ℝ) : ℂ)) := by
  have hA := hP.A_pos j
  have hr := hP.r_pos j
  have hQ : BS.Qm 3 (fun y => ((P.unitsVort j g y : ℝ) : ℂ)) =
      (((P.A j)⁻¹ * (P.r j ^ 5)⁻¹ : ℝ) : ℂ) * BS.Qm 3 (fun x => ((g x : ℝ) : ℂ)) := by
    simp only [BS.Qm]
    exact Qm_scaleVort _ _ hr _
  rw [BS.two_pi_mul_pout_ofReal, hQ, map_mul, Complex.conj_ofReal, div_eq_inv_mul]
  congr 1
  push_cast
  ring

/-- **`q_j(t) = 2π pout_3[w_j(t)] + 2π pout_3[ν^in_j(t)]`** for `1 ≤ j ≤ n` and `t ≥ 0`
(`09_relay.tex:1063-1066`, `:1072-1081`; `D_j(t) = S_j(t) ⊔ D_{j+1}(t)`, `Q_3[Φ] = 0`). -/
theorem q_eq (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {j : ℕ}
    (hj : 1 ≤ j) (hjn : j ≤ P.n) {t : ℝ} (ht : 0 ≤ t) :
    P.q j t = 2 * Real.pi * BS.pout 3 (P.w j t) +
      2 * Real.pi * BS.pout 3 (fun y => ((P.nuIn j t y : ℝ) : ℂ)) := by
  simp only [Approx.q]
  rw [conjQm_split P hP hN hj hjn ht, add_div, conjQm_omegaRing_eq P hP j t,
    conjQm_div_eq_pout_units P hP j]
  rfl

/-- **`|2π pout_3[w_j(t)]| ≤ 2³‖w_j(t)‖_{L¹}`** if `S_j(t) ⊂ N_j`, `t ≥ 0` (`09_relay.tex:1067-1069`:
`w_j(t)` is supported in `N ⊂ B̄₂`, and `2π pout_3[w] = conj Q_3[w]` for real `w`). -/
theorem norm_two_pi_pout_w_le (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 P.n) {t : ℝ} (ht : 0 ≤ t) (hS : P.PertDefined j t) :
    ‖2 * Real.pi * BS.pout 3 (P.w j t)‖ ≤ 2 ^ 3 * (eLpNorm (P.wR j t) 1 volume).toReal := by
  obtain ⟨hcd, hcs, hsupp, -⟩ := P.regions_basic_four hP hN hj ht hS
  have hc : Continuous (P.wR j t) := hcd.continuous
  have hw : P.w j t = fun y => ((P.wR j t y : ℝ) : ℂ) := rfl
  have hint : Integrable (fun y => ((P.wR j t y : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp hc).integrable_of_hasCompactSupport
      (hcs.comp_left Complex.ofReal_zero)
  have hz : ∀ᵐ y : ℂ ∂volume, (2 : ℝ) < ‖y‖ → ((P.wR j t y : ℝ) : ℂ) = 0 := by
    refine Filter.Eventually.of_forall fun y hy => ?_
    have hy' : y ∉ tsupport (P.wR j t) := fun hy' => by
      have := (hsupp hy').2
      linarith
    rw [image_eq_zero_of_notMem_tsupport hy', Complex.ofReal_zero]
  have hm := Multipole.norm_moment_le hint (by norm_num : (0 : ℝ) ≤ 2) hz 3
  have hL1 : ∫ y, ‖((P.wR j t y : ℝ) : ℂ)‖ = (eLpNorm (P.wR j t) 1 volume).toReal := by
    simp_rw [Complex.norm_real]
    rw [integral_norm_eq_lintegral_enorm hc.aestronglyMeasurable, eLpNorm_one_eq_lintegral_enorm]
  rw [hL1] at hm
  rw [hw, BS.two_pi_mul_pout_ofReal, Complex.norm_conj, BS.Qm_eq_moment]
  calc _ ≤ _ := hm
    _ = _ := by ring

end PrehistoryAux

end Relay

end NonUniqueEuler
