import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec6.RegionsBasic

/-!
# Helpers for `P/Sec9/Deep`: the splitting `q_{k+1} = q^ring + q^deep`

Helper file of `P/Sec9/Deep.lean` (`lem:deep`(1), `09_relay.tex:1134-1150`).
* `integrable_moment`, `Qm_add`: `Q_3` is additive on continuous compactly supported real functions;
* `omegaGe_split`: `ω_{≥j}(t) = ω(t)1_{S_j(t)} + ω_{≥j+1}(t)` for `1 ≤ j ≤ n`, `t ≥ 0`
  (`lem:regions-basic`(3)), with the regularity of both parts;
* `qKick_split`: `q_{k+1}(t) = q^ring + conj Q_3[ω_{≥k+2}(t)]/(A_{k+1}r_{k+1}^5)`;
* `kick_time_succ`: `T_{k+2} + (T_pin + μ(τ_K + T̂_{k+1}))/A_{k+2} = T_{k+1} + τ_K/A_{k+1}`
  (the kick time of ring `k+1` is `T_pin + μ(τ_K + T_g)`, `09_relay.tex:1144-1149`);
* `deepTerm_eq`, `deepTerm_eq_of_succ_eq_n`: the second term is `q^deep(τ_K)`.
Everything here is proved.
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate

namespace NonUniqueEuler

namespace Relay

namespace DeepAux

open RingData Datum

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

/-- `conj Q_3[ω_{≥j}(t)] = conj Q_3[ω(t)1_{S_j(t)}] + conj Q_3[ω_{≥j+1}(t)]` (`09_relay.tex:1139-1141`). -/
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

/-- `q_{k+1}(t) = q^ring(τ_K) + conj Q_3[ω_{≥k+2}(t)]/(A_{k+1}r_{k+1}^5)` at `t = T_{k+1} + τ_K/A_{k+1}`
(`t ≥ 0`). -/
theorem qKick_split (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k < P.n) {τK : ℝ} (ht : 0 ≤ P.T (k + 1) + τK / P.A (k + 1)) :
    P.qKick k τK = P.qRing k τK +
      conj (BS.Qm 3 fun x =>
          ((P.omegaGe (k + 1 + 1) (P.T (k + 1) + τK / P.A (k + 1)) x : ℝ) : ℂ)) /
        ((P.A (k + 1) * P.r (k + 1) ^ (3 + 2) : ℝ) : ℂ) := by
  simp only [Approx.qKick, Approx.q, Approx.qRing]
  rw [conjQm_split P hP hN (by omega) hkn ht, add_div]

/-- The kick time of ring `k+1`: `T_{k+2} + (T_pin + μ(τ_K + T̂_{k+1}))/A_{k+2} = T_{k+1} + τ_K/A_{k+1}`
for `1 ≤ k`, `k + 1 < n` (`09_relay.tex:1144-1149`: `T_{k+1} - T_{k+2} = T_pin/A_{k+2} + T_g/A_{k+1}`). -/
theorem kick_time_succ (P : Approx) (hP : P.Valid) {k : ℕ} (hk : 1 ≤ k) (hkn1 : k + 1 < P.n)
    (τK : ℝ) :
    P.T (k + 1 + 1) + (P.Tpin + P.μ * (τK + P.That (k + 1))) / P.A (k + 1 + 1) =
      P.T (k + 1) + τK / P.A (k + 1) := by
  have hA1 : P.A (k + 1) ≠ 0 := (hP.A_pos (k + 1)).ne'
  have hμ : P.μ ≠ 0 := by linarith [hP.datumParams.one_lt_μ]
  have hAs : P.A (k + 1 + 1) = P.μ * P.A (k + 1) := amp_succ _ _ (by omega : 1 ≤ k + 1)
  have hT1 : P.T (k + 1) = P.tsh (k + 1) + P.That (k + 1) / P.A (k + 1) := P.T_of_ne (by omega)
  have htsh : P.tsh (k + 1) = P.T (k + 1 + 1) + P.Tpin / P.A (k + 1 + 1) := P.tsh_eq_T_add hkn1
  rw [hT1, htsh, hAs]
  field_simp
  ring

/-- For `k + 1 < n`: `conj Q_3[ω_{≥k+2}(t)]/(A_{k+1}r_{k+1}^5) = q^deep(τ_K)`, using
`A_{k+2}r_{k+2}^5 = μ s_{k+1}^5 A_{k+1}r_{k+1}^5` (`09_relay.tex:1141-1143`) and `kick_time_succ`. -/
theorem deepTerm_eq (P : Approx) (hP : P.Valid) {k : ℕ} (hk : 1 ≤ k) (hkn1 : k + 1 < P.n)
    (τK : ℝ) :
    conj (BS.Qm 3 fun x =>
          ((P.omegaGe (k + 1 + 1) (P.T (k + 1) + τK / P.A (k + 1)) x : ℝ) : ℂ)) /
        ((P.A (k + 1) * P.r (k + 1) ^ (3 + 2) : ℝ) : ℂ) = P.qDeep k τK := by
  have hA1 : P.A (k + 1) ≠ 0 := (hP.A_pos (k + 1)).ne'
  have hr1 : P.r (k + 1) ≠ 0 := (hP.r_pos (k + 1)).ne'
  have hs1 : P.s (k + 1) ≠ 0 := (hP.s_pos (k + 1)).ne'
  have hμ : P.μ ≠ 0 := by linarith [hP.datumParams.one_lt_μ]
  have hAs : P.A (k + 1 + 1) = P.μ * P.A (k + 1) := amp_succ _ _ (by omega : 1 ≤ k + 1)
  have hrs : P.r (k + 1 + 1) = P.s (k + 1) * P.r (k + 1) := radius_succ _ _ (by omega : 1 ≤ k + 1)
  simp only [Approx.qDeep, Approx.qKick, Approx.q]
  rw [kick_time_succ P hP hk hkn1 τK, hAs, hrs]
  have hA1' : ((P.A (k + 1) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hA1
  have hr1' : ((P.r (k + 1) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr1
  have hs1' : ((P.s (k + 1) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs1
  have hμ' : ((P.μ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hμ
  push_cast
  field_simp

/-- For `k + 1 = n`: the second term vanishes (`D_{n+1} = ∅`), as does `q^deep`. -/
theorem deepTerm_eq_of_succ_eq_n (P : Approx) {k : ℕ} (hkn : k + 1 = P.n) (τK : ℝ) :
    conj (BS.Qm 3 fun x =>
          ((P.omegaGe (k + 1 + 1) (P.T (k + 1) + τK / P.A (k + 1)) x : ℝ) : ℂ)) /
        ((P.A (k + 1) * P.r (k + 1) ^ (3 + 2) : ℝ) : ℂ) = P.qDeep k τK := by
  rw [P.qDeep_of_succ_eq_n hkn, show k + 1 + 1 = P.n + 1 by omega, P.omegaGe_succ_n]
  simp [BS.Qm]

end DeepAux

end Relay

end NonUniqueEuler
