import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec8.Coupling
import NonUniqueEuler.I.Sec8.KickInstance
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec9.Detuning

/-!
# Proof: `cor:amp` (two-sided bound on the amplitude `κ♯_k`)

Proof of `I/Sec9/Amp.lean` (`09_relay.tex:996-1023`).

Steps (following `09_relay.tex:1009-1023`):
1. `|c^in_k| = e^{x_kT_pin}|A^in(T_pin)|` (`coupling_two`, `kick_instance`: `Re ζ₀ = x_k > 0`);
2. `G_k, G_{k+1} ∈ [0,G₁]` (`standing_levels`), so `c_N ≤ |β(G_k)||pout_*(G_{k+1})| ≤ C_N`
   (`uniform_constants`, via the attained extrema), hence
   `(15/16)c_Ns_k⁵δ₀ ≤ |β_k||q_s| ≤ (17/16)C_Ns_k⁵δ₀`;
3. the lower bound uses `e^{x_kT_pin} ≥ 1`, the upper bound `x_k ≤ 17σ/16` (`detuning`).
The real-number cores are `AmpAux.lower_core` and `AmpAux.upper_core`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace AmpAux

/-- Real core of the lower bound of `cor:amp`: with `u = (|z|(μ-1))⁻¹`,
`c_Nδ₀s⁵u/22 ≤ (15/320)c_Nδ₀s⁵u ≤ ½|A| ≤ ½|c| ≤ κ`. -/
theorem lower_core {κ c e a bq cN δ s5 Z m : ℝ} (hκ : 1 / 2 * c ≤ κ) (hc : c = e * a)
    (he : 1 ≤ e) (ha : 0 ≤ a) (hA : bq / (10 * Z * m) ≤ a) (hbq : 15 / 16 * cN * s5 * δ ≤ bq)
    (hcN : 0 ≤ cN) (hδ : 0 ≤ δ) (hs5 : 0 ≤ s5) (hZ : 0 ≤ Z) (hm : 0 ≤ m) :
    cN * δ / (22 * Z * m) * s5 ≤ κ := by
  have hu : 0 ≤ (Z * m)⁻¹ := inv_nonneg.2 (mul_nonneg hZ hm)
  have hA' : bq * (Z * m)⁻¹ / 10 ≤ a := by
    have e1 : bq / (10 * Z * m) = bq * (Z * m)⁻¹ / 10 := by ring
    rw [← e1]; exact hA
  have h1 : 15 / 16 * cN * s5 * δ * (Z * m)⁻¹ ≤ bq * (Z * m)⁻¹ :=
    mul_le_mul_of_nonneg_right hbq hu
  have hX : 0 ≤ cN * s5 * δ * (Z * m)⁻¹ := mul_nonneg (mul_nonneg (mul_nonneg hcN hs5) hδ) hu
  have hca : a ≤ c := by rw [hc]; exact le_mul_of_one_le_left ha he
  have e2 : cN * δ / (22 * Z * m) * s5 = cN * s5 * δ * (Z * m)⁻¹ / 22 := by ring
  have e3 : 15 / 16 * cN * s5 * δ * (Z * m)⁻¹ = 15 / 16 * (cN * s5 * δ * (Z * m)⁻¹) := by ring
  rw [e2]
  rw [e3] at h1
  linarith

/-- Real core of the upper bound of `cor:amp`: with `u = (|z|(μ-1))⁻¹` and `E = e^{17σT_pin/16}`,
`κ ≤ (3/2)e|A| ≤ (3/2)·3·(17/16)C_Nδ₀μs⁵uE ≤ 5C_Nδ₀μs⁵uE`. -/
theorem upper_core {κ c e a b q CN δ s5 Z m μ E : ℝ} (hκ : κ ≤ 3 / 2 * c) (hc : c = e * a)
    (he : e ≤ E) (ha : 0 ≤ a) (hA : a ≤ 3 * b * q * μ / (Z * m))
    (hbq : b * q ≤ 17 / 16 * CN * s5 * δ) (hCN : 0 ≤ CN) (hδ : 0 ≤ δ) (hs5 : 0 ≤ s5)
    (hZ : 0 ≤ Z) (hm : 0 ≤ m) (hμ : 0 ≤ μ) (hE : 0 ≤ E) :
    κ ≤ 5 * CN * δ * μ / (Z * m) * E * s5 := by
  have hu : 0 ≤ (Z * m)⁻¹ := inv_nonneg.2 (mul_nonneg hZ hm)
  have hA' : a ≤ 3 * μ * (Z * m)⁻¹ * (b * q) := by
    have e1 : 3 * b * q * μ / (Z * m) = 3 * μ * (Z * m)⁻¹ * (b * q) := by ring
    rw [← e1]; exact hA
  have h3 : 0 ≤ 3 * μ * (Z * m)⁻¹ := mul_nonneg (mul_nonneg (by norm_num) hμ) hu
  have h1 : 3 * μ * (Z * m)⁻¹ * (b * q) ≤ 3 * μ * (Z * m)⁻¹ * (17 / 16 * CN * s5 * δ) :=
    mul_le_mul_of_nonneg_left hbq h3
  set Y := CN * s5 * δ * μ * (Z * m)⁻¹ with hY
  have hY0 : 0 ≤ Y := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCN hs5) hδ) hμ) hu
  have e2 : 3 * μ * (Z * m)⁻¹ * (17 / 16 * CN * s5 * δ) = 51 / 16 * Y := by rw [hY]; ring
  have haY : a ≤ 51 / 16 * Y := by linarith
  have hcE : c ≤ E * a := by rw [hc]; exact mul_le_mul_of_nonneg_right he ha
  have hEa : E * a ≤ E * (51 / 16 * Y) := mul_le_mul_of_nonneg_left haY hE
  have hEY : 0 ≤ E * Y := mul_nonneg hE hY0
  have e3 : 5 * CN * δ * μ / (Z * m) * E * s5 = 5 * (E * Y) := by rw [hY]; ring
  have e4 : E * (51 / 16 * Y) = 51 / 16 * (E * Y) := by ring
  rw [e3]
  rw [e4] at hEa
  linarith

end AmpAux

/-- **`cor:amp`** (`09_relay.tex:996-1007`). Assume (SA), (Det), `1 ≤ k < n`, the clock defined up
to level `k+1`, `D_{k+1}(t) ⊂ B_{ar_k/8}` on `[0, t♯_k]`, `S_k(t♯_k) ⊂ N_k`,
`½|c^in_k| ≤ κ♯_k ≤ (3/2)|c^in_k|`, and for some `q_s` with
`|q_s| ∈ [15/16, 17/16]·2π|pout_*(G_{k+1})|δ₀` the two-sided bound
`|β_k||q_s|/(10|z|(μ-1)) ≤ |A^in(T_pin)| ≤ 3|β_k||q_s|μ/(|z|(μ-1))`.
Then `K_lo s_k⁵ ≤ κ♯_k ≤ K_up s_k⁵`. -/
theorem amp (S : Standing) (hS : S.Holds) (hDet : S.Det) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (hin : ∀ t ∈ Icc (0 : ℝ) (S.P.tsh k), S.P.HInDefined k t)
    (hSk : S.P.PertDefined k (S.P.tsh k))
    (hk1 : 1 / 2 * ‖S.P.cinK k‖ ≤ S.P.ksh k) (hk2 : S.P.ksh k ≤ 3 / 2 * ‖S.P.cinK k‖) {qs : ℂ}
    (hqs : ‖qs‖ ∈ Icc (15 / 16 * (2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ * S.P.δ₀))
      (17 / 16 * (2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ * S.P.δ₀)))
    (hA : ‖S.P.betaK k‖ * ‖qs‖ / (10 * ‖S.z‖ * (S.P.μ - 1)) ≤ ‖S.P.Ain k S.P.Tpin‖ ∧
      ‖S.P.Ain k S.P.Tpin‖ ≤ 3 * ‖S.P.betaK k‖ * ‖qs‖ * S.P.μ / (‖S.z‖ * (S.P.μ - 1))) :
    S.Klo * S.P.s k ^ (3 + 2) ≤ S.P.ksh k ∧ S.P.ksh k ≤ S.Kup * S.P.s k ^ (3 + 2) := by
  -- levels, detuning, coupling
  obtain ⟨-, -, hG, hlev⟩ := standing_levels S hS
  have hkI : k ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hk, hkn.le⟩
  have hk1I : k + 1 ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨by omega, hkn⟩
  have hGk := (hlev k hkI).2.1
  have hGk1 := (hlev (k + 1) hk1I).2.1
  obtain ⟨-, -, hdet⟩ := detuning S hS hDet
  obtain ⟨-, -, -, -, hxle, -⟩ := hdet k hkI
  obtain ⟨-, hre, hxpos, -, -⟩ := Kick.kick_instance S.P hS.valid hS.hN hG hk hkn hc hin
  obtain ⟨-, -, -, -, hcin⟩ := Kick.coupling_two S.P hS.valid hS.hN hG hk hkn hc hin
  have hTpin := hS.Tpin_pos
  have hμ1 := hS.one_lt_μ
  have hδ := hS.δ₀_pos
  have hs := hS.valid.s_pos k
  -- `|c^in_k| = e^{x_kT_pin}|A^in(T_pin)|`
  have hnorm : ‖S.P.cinK k‖ = Real.exp (S.P.xk k * S.P.Tpin) * ‖S.P.Ain k S.P.Tpin‖ := by
    rw [hcin, norm_mul, Complex.norm_exp, Complex.re_mul_ofReal, hre]
  -- `c_N ≤ |β(G_k)||pout_*(G_{k+1})| ≤ C_N`
  obtain ⟨hβmin, hβmax, hpmin, hpmax, -, -, hcN, -, -⟩ :=
    Eig.uniform_constants S.P.χ hS.admissible hS.hN
  set B := ‖Eig.beta S.P.χ (S.P.G k)‖ with hB
  set Pk := ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ with hPk
  have hβinf : sInf ((fun G => ‖Eig.beta S.P.χ G‖) '' Icc 0 Gbar) ≤ B :=
    hβmin.2 ⟨S.P.G k, hGk, rfl⟩
  have hpinf : sInf ((fun G => ‖Eig.pout S.P.χ G‖) '' Icc 0 Gbar) ≤ Pk :=
    hpmin.2 ⟨S.P.G (k + 1), hGk1, rfl⟩
  have hβsup : B ≤ sSup ((fun G => ‖Eig.beta S.P.χ G‖) '' Icc 0 Gbar) :=
    hβmax.2 ⟨S.P.G k, hGk, rfl⟩
  have hpsup : Pk ≤ sSup ((fun G => ‖Eig.pout S.P.χ G‖) '' Icc 0 Gbar) :=
    hpmax.2 ⟨S.P.G (k + 1), hGk1, rfl⟩
  have hβinf0 : 0 ≤ sInf ((fun G => ‖Eig.beta S.P.χ G‖) '' Icc 0 Gbar) := by
    obtain ⟨G, -, hG'⟩ := hβmin.1
    rw [← hG']; exact norm_nonneg _
  have hpinf0 : 0 ≤ sInf ((fun G => ‖Eig.pout S.P.χ G‖) '' Icc 0 Gbar) := by
    obtain ⟨G, -, hG'⟩ := hpmin.1
    rw [← hG']; exact norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hPk0 : 0 ≤ Pk := norm_nonneg _
  have hcNle : Eig.cN S.P.χ ≤ B * Pk := mul_le_mul hβinf hpinf hpinf0 hB0
  have hCNge : B * Pk ≤ Eig.CN S.P.χ := mul_le_mul hβsup hpsup hPk0 (hB0.trans hβsup)
  have hCN0 : 0 ≤ Eig.CN S.P.χ := (mul_nonneg hB0 hPk0).trans hCNge
  -- `|β_k| = |β(G_k)|s_k⁵/(2π)`
  have hpi := Real.pi_pos
  have hbetaK : ‖S.P.betaK k‖ = B * S.P.s k ^ (3 + 2) / (2 * Real.pi) := by
    simp only [Approx.betaK, hB, norm_div, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs, Complex.norm_ofNat, abs_of_pos hpi]
  have hs5 : 0 ≤ S.P.s k ^ (3 + 2) := pow_nonneg hs.le _
  -- `(15/16)c_Ns_k⁵δ₀ ≤ |β_k||q_s| ≤ (17/16)C_Ns_k⁵δ₀`
  have hbq_lo : 15 / 16 * Eig.cN S.P.χ * S.P.s k ^ (3 + 2) * S.P.δ₀ ≤ ‖S.P.betaK k‖ * ‖qs‖ := by
    have hb0 : 0 ≤ ‖S.P.betaK k‖ := norm_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hqs.1 hb0
    have e1 : ‖S.P.betaK k‖ * (15 / 16 * (2 * Real.pi * Pk * S.P.δ₀)) =
        15 / 16 * (B * Pk) * S.P.s k ^ (3 + 2) * S.P.δ₀ := by
      rw [hbetaK]; field_simp
    have h2 : 15 / 16 * Eig.cN S.P.χ * S.P.s k ^ (3 + 2) * S.P.δ₀ ≤
        15 / 16 * (B * Pk) * S.P.s k ^ (3 + 2) * S.P.δ₀ := by
      have h3 := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcNle (mul_nonneg hs5 hδ.le)) (show (0 : ℝ) ≤ 15 / 16 by norm_num)
      calc 15 / 16 * Eig.cN S.P.χ * S.P.s k ^ (3 + 2) * S.P.δ₀
          = 15 / 16 * (Eig.cN S.P.χ * (S.P.s k ^ (3 + 2) * S.P.δ₀)) := by ring
        _ ≤ 15 / 16 * (B * Pk * (S.P.s k ^ (3 + 2) * S.P.δ₀)) := h3
        _ = 15 / 16 * (B * Pk) * S.P.s k ^ (3 + 2) * S.P.δ₀ := by ring
    linarith
  have hbq_up : ‖S.P.betaK k‖ * ‖qs‖ ≤ 17 / 16 * Eig.CN S.P.χ * S.P.s k ^ (3 + 2) * S.P.δ₀ := by
    have hb0 : 0 ≤ ‖S.P.betaK k‖ := norm_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hqs.2 hb0
    have e1 : ‖S.P.betaK k‖ * (17 / 16 * (2 * Real.pi * Pk * S.P.δ₀)) =
        17 / 16 * (B * Pk) * S.P.s k ^ (3 + 2) * S.P.δ₀ := by
      rw [hbetaK]; field_simp
    have h2 : 17 / 16 * (B * Pk) * S.P.s k ^ (3 + 2) * S.P.δ₀ ≤
        17 / 16 * Eig.CN S.P.χ * S.P.s k ^ (3 + 2) * S.P.δ₀ := by
      have h3 := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hCNge (mul_nonneg hs5 hδ.le)) (show (0 : ℝ) ≤ 17 / 16 by norm_num)
      calc 17 / 16 * (B * Pk) * S.P.s k ^ (3 + 2) * S.P.δ₀
          = 17 / 16 * (B * Pk * (S.P.s k ^ (3 + 2) * S.P.δ₀)) := by ring
        _ ≤ 17 / 16 * (Eig.CN S.P.χ * (S.P.s k ^ (3 + 2) * S.P.δ₀)) := h3
        _ = 17 / 16 * Eig.CN S.P.χ * S.P.s k ^ (3 + 2) * S.P.δ₀ := by ring
    linarith
  -- the exponential factor
  have he1 : 1 ≤ Real.exp (S.P.xk k * S.P.Tpin) :=
    Real.one_le_exp (mul_nonneg hxpos.le hTpin.le)
  have heE : Real.exp (S.P.xk k * S.P.Tpin) ≤ Real.exp (17 * S.sigma0 * S.P.Tpin / 16) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hxle hTpin.le
    linarith
  constructor
  · rw [Standing.Klo_def]
    exact AmpAux.lower_core hk1 hnorm he1 (norm_nonneg _) hA.1 hbq_lo hcN.le hδ.le hs5
      (norm_nonneg _) (by linarith)
  · rw [Standing.Kup_def]
    exact AmpAux.upper_core hk2 hnorm heE (norm_nonneg _) hA.2 hbq_up hCN0 hδ.le hs5
      (norm_nonneg _) (by linarith) (by linarith) (Real.exp_pos _).le

end Relay

end NonUniqueEuler
