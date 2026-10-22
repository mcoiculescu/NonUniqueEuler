import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec9.Relay
import NonUniqueEuler.H.Sec9.Oprime.MajBound

/-!
# Proof of `lem:Oprime` (the field of the quiet outer rings on the active ring)

Proof of `I/Sec9/Oprime.lean` (`09_relay.tex:605-738`). Same declaration, same statement.

* `k = 1`: `h^out_1 = 0` (`P.hOut_one`, `P.etaOut_one`) and `η_{b,1} = 0`.
* `k = j+1 ≥ 2`, `u ∈ [0, A_k(t - t♯_k)]`, `t' = t♯_k + u/A_k`, so `A_kt' = t̄♯_k + u`:
  `eq:Op-red` (`OprimeH.op_red`): `η^out_k(A_kt') ≤ 2C_OC_Qb_{j,k}maj_j(A_jt')`;
  `prop:relay` (`relay` with `j`, `τ = A_jt`, hypotheses `OprimeH.relayHyp`):
  `maj_j ≤ 2maj^in_j`; and `OprimeH.majIn_le`: `maj^in_j(A_jt') ≤ C_Mε_jâ_k(u)B/(σ_b(μ-1))`,
  `C_op = 4C_OC_QC_MB`. With `b_{j,j+1}ε_j = s_j^{2m}` this is `η_{b,k}â_k(u)`.
* `η_{b,k} ≤ η_b` because `s_{k-1} ≤ s̄` and `C_op ≥ 0`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- `0 ∈ C^k(U)`. -/
private theorem memCk_zero_fun (k : ℕ) (U : Set ℂ) : MemCk k U (0 : ℂ → ℂ) where
  near := ⟨univ, isOpen_univ, subset_univ _, contDiff_zero_fun.contDiffOn⟩
  finite := by
    refine normCkE_ne_top_of_bound (fun _ => 0) fun q _ x _ => ?_
    rw [show (0 : ℂ → ℂ) = fun _ => (0 : ℂ) from rfl, iteratedFDeriv_fun_zero]
    simp

/-- **`lem:Oprime`** (`09_relay.tex:605-631`) with **`eq:etab`**: under (SA), (Det), `C₀ ≥ 1`,
`K₁ > 0`, `C_F ∈ (0, C₀]` and the hypotheses `S.OprimeHyp C₀ K₁ C_F k t` (`t ∈ Ph_k`), for every
`u ∈ [0, A_k(t - t♯_k)]`: `h^out_k(t̄♯_k + u) ∈ C^{M_h}(N')` and
`‖h^out_k(t̄♯_k + u)‖_{C^{M_h}(N')} ≤ η_{b,k}â_k(u)` (`η_{b,1} = 0`); and `η_{b,k} ≤ η_b`. -/
theorem Oprime (S : Standing) (hS : S.Holds) (hDet : S.Det) {C₀ K₁ CF : ℝ} (hC₀ : 1 ≤ C₀)
    (hK₁ : 0 < K₁) (hCF : CF ∈ Ioc 0 C₀) {k : ℕ} {t : ℝ} (h : S.OprimeHyp C₀ K₁ CF k t) :
    (∀ u ∈ Icc (0 : ℝ) (S.P.activeTime k t), MemCk S.Mh annN' (S.P.hOut k (S.P.tash k + u)) ∧
      S.etaOut k (S.P.tash k + u) ≤ S.etabK C₀ K₁ k * S.ahatK k u) ∧
    S.etabK C₀ K₁ k ≤ S.etab C₀ K₁ := by
  have hsb := OprimeH.sigb_pos hS
  have hμ := hS.one_lt_μ
  have hD0 : 0 < S.sigb * (S.P.μ - 1) := mul_pos hsb (by linarith)
  have hCO := OprimeH.CO_pos S
  have hCQ := OprimeH.CQ_nonneg S
  have hCM := OprimeH.CM_pos S
  have hC2 := OprimeH.one_le_C2 S
  have hCact : 1 ≤ S.Cact C₀ := hC₀.trans (OneRing.le_Cact _ _ _)
  have hIp := OprimeH.Ip_nonneg 3 (9 * S.sigma0 / 64)
  have hB : 0 ≤ 2 * S.CQ * K₁ + 4 * S.C2 + S.sigb * K₁ +
      2 * S.sigb * (2 * S.C2 * S.Cact C₀ + C₀) * Ip 3 (9 * S.sigma0 / 64) := by positivity
  have hCop : 0 ≤ S.Cop C₀ K₁ := by
    rw [OprimeH.Cop_eq]
    positivity
  have hetab : 0 ≤ S.etab C₀ K₁ :=
    div_nonneg (mul_nonneg hCop (pow_nonneg hS.sbar_pos.le _)) hD0.le
  rcases lt_or_ge k 2 with hk | hk
  · -- `k = 1`: no outer ring
    have hk1 : k = 1 := by have := h.one_le; omega
    subst hk1
    refine ⟨fun u _ => ⟨?_, ?_⟩, ?_⟩
    · rw [S.P.hOut_one]
      exact memCk_zero_fun _ _
    · show S.P.etaOut S.Mh 1 _ ≤ _
      rw [S.P.etaOut_one, S.etabK_one, zero_mul]
    · rw [S.etabK_one]
      exact hetab
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj : 1 ≤ j := by omega
    have hetabK : S.etabK C₀ K₁ (j + 1) =
        S.Cop C₀ K₁ * S.P.s j ^ (2 * 3) / (S.sigb * (S.P.μ - 1)) := by
      rw [S.etabK_of_two_le C₀ K₁ hk, Nat.add_sub_cancel]
    refine ⟨fun u hu => ?_, ?_⟩
    · have hAk := hS.valid.A_pos (j + 1)
      have hAj := hS.valid.A_pos j
      have ht'mem : S.P.tsh (j + 1) + u / S.P.A (j + 1) ∈ Icc (S.P.tsh (j + 1)) t := by
        have h1 : u / S.P.A (j + 1) ≤ t - S.P.tsh (j + 1) := by
          rw [div_le_iff₀ hAk, mul_comm]
          exact hu.2
        have h2 := div_nonneg hu.1 hAk.le
        exact ⟨by linarith, by linarith⟩
      have hkt : S.P.A (j + 1) * (S.P.tsh (j + 1) + u / S.P.A (j + 1)) =
          S.P.tash (j + 1) + u := by
        rw [Approx.tash_def]
        field_simp
      obtain ⟨hmem, hred⟩ := OprimeH.op_red hS hj h ht'mem
      rw [hkt] at hmem hred
      refine ⟨hmem, hred.trans ?_⟩
      have h0 : 0 ≤ S.P.tsh (j + 1) + u / S.P.A (j + 1) :=
        (OprimeH.tsh_nonneg hS h).trans ht'mem.1
      have hR := (relay S hS hDet hC₀ hK₁ (OprimeH.relayHyp hS hK₁ hCF hj h)).1
        (S.P.A j * (S.P.tsh (j + 1) + u / S.P.A (j + 1)))
        ⟨mul_nonneg hAj.le h0, mul_le_mul_of_nonneg_left ht'mem.2 hAj.le⟩
      have hM := OprimeH.majIn_le hS hDet hC₀ hK₁ hCF hj h hu
      have hb := OprimeH.b_nonneg hS.valid j (j + 1)
      have h2 : 0 ≤ 2 * S.CO * S.CQ * S.P.b j (j + 1) := by positivity
      calc 2 * S.CO * S.CQ * S.P.b j (j + 1) *
            S.maj j (S.P.A j * (S.P.tsh (j + 1) + u / S.P.A (j + 1)))
          ≤ 2 * S.CO * S.CQ * S.P.b j (j + 1) *
              (2 * (S.CM * S.P.eps j * S.ahatK (j + 1) u *
                (2 * S.CQ * K₁ + 4 * S.C2 + S.sigb * K₁ +
                  2 * S.sigb * (2 * S.C2 * S.Cact C₀ + C₀) * Ip 3 (9 * S.sigma0 / 64)) /
                (S.sigb * (S.P.μ - 1)))) :=
            mul_le_mul_of_nonneg_left (hR.trans (by linarith)) h2
        _ = S.etabK C₀ K₁ (j + 1) * S.ahatK (j + 1) u := by
            rw [hetabK, OprimeH.Cop_eq, ← OprimeH.b_succ_mul_eps hS.valid hj]
            ring
    · rw [hetabK]
      unfold Standing.etab
      refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hCop) hD0.le
      exact pow_le_pow_left₀ (hS.valid.s_pos j).le (OprimeH.s_le_sbar hS.valid hj) _

end Relay

end NonUniqueEuler
