import NonUniqueEuler.I.Sec9.Relay
import NonUniqueEuler.I.Sec9.Detuning
import NonUniqueEuler.I.Sec5.ActiveT1
import NonUniqueEuler.H.Sec9.Oprime.Red
import NonUniqueEuler.H.Sec9.Oprime.Integral

/-!
# Helpers for `lem:Oprime`: the bound of `maj^in_{k-1}` by the envelope of ring `k`

Helper file of `P/Sec9/Oprime.lean` (`09_relay.tex:680-729`). Everything here is proved.
With `k = j+1 ≥ 2`, `τ^act = A_jt♯_k`, `D = σ_b(μ-1)` and
`B = 2C_QK₁ + 4C₂ + σ_bK₁ + 2σ_b(2C₂C(C₀) + C₀)I_m(9σ/64)` (so `C_op = 4C_OC_QC_M B`):

* `detune_facts`: `μσ_k - σ_j ≥ σ_b(μ-1)/2`, `σ_j ≥ 15σ/16`, `σ > 0` (`lem:detuning`);
* `etaIn_le` (`09_relay.tex:691-698`): for `x ≥ 0` with `μx ≤ A_k(t - t♯_k)`,
  `η^in_j(τ^act + x) ≤ C_Mε_j[2C₂κ♯_ke^{μσ_kx} + 4C₂C(C₀)κ♯_k(1+x)^3e^{μσ'x} + 2C_Fκ♯_k(1+x)^3]`
  (`lem:transfer-step`(1) with `s' = s`, the active and inner bounds, `thm:active`'s last assertion,
  `⟨μx⟩^m ≤ 2(1+x)^m`);
* `alg_bound`: the sum of the coefficients is at most `B/D` (`09_relay.tex:726-729`);
* `majIn_le` (`09_relay.tex:680-729`): `maj^in_j(A_j(t♯_k + u/A_k)) ≤ C_Mε_jâ_k(u)B/D` for
  `u ∈ [0, A_k(t - t♯_k)]`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace OprimeH

open RingData Datum

theorem Cop_eq (S : Standing) (C₀ K₁ : ℝ) :
    S.Cop C₀ K₁ = 4 * S.CO * S.CQ * S.CM * (2 * S.CQ * K₁ + 4 * S.C2 + S.sigb * K₁ +
      2 * S.sigb * (2 * S.C2 * S.Cact C₀ + C₀) * Ip 3 (9 * S.sigma0 / 64)) := rfl

/-- `lem:detuning` at the levels `j` and `j+1`. -/
theorem detune_facts {S : Standing} (hS : S.Holds) (hDet : S.Det) {j : ℕ} (hj : 1 ≤ j)
    (hjn : j + 1 ≤ S.P.n) :
    1 / 2 * S.sigb * (S.P.μ - 1) ≤ S.P.μ * S.P.sigma (j + 1) - S.P.sigma j ∧
      15 / 16 * S.sigma0 ≤ S.P.sigma j ∧ 0 < S.sigma0 := by
  obtain ⟨-, -, hd⟩ := detuning S hS hDet
  have hk := hd (j + 1) (Finset.mem_Icc.mpr ⟨by omega, hjn⟩)
  have hjj := hd j (Finset.mem_Icc.mpr ⟨hj, by omega⟩)
  obtain ⟨h1, h2, h3, -⟩ := hk.2.2.2.2.2 j (Finset.mem_Icc.mpr ⟨hj, by omega⟩)
  refine ⟨by linarith, hjj.2.1, ?_⟩
  have h4 := hS.σ'_gt
  have h5 := hS.σ'_lt_sigma
  show 0 < Eig.sigma S.P.χ 0
  linarith

theorem mu_pow_le {S : Standing} (hS : S.Holds) : S.P.μ ^ 3 ≤ 2 := by
  have hμ := hS.one_lt_μ
  have := pow_le_pow_left₀ (by linarith) hS.μ_le 3
  norm_num at this
  linarith

/-- **The integrand of the second term** (`09_relay.tex:691-698`). -/
theorem etaIn_le {S : Standing} {C₀ K₁ CF t : ℝ} (hS : S.Holds) (hC₀ : 1 ≤ C₀) (hCF : 0 ≤ CF)
    {j : ℕ} (hj : 1 ≤ j) (h : S.OprimeHyp C₀ K₁ CF (j + 1) t) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : S.P.μ * x ≤ S.P.activeTime (j + 1) t) :
    S.etaIn j (S.P.A j * S.P.tsh (j + 1) + x) ≤
      S.CM * S.P.eps j * (2 * S.C2 * S.P.ksh (j + 1)) *
          Real.exp (S.P.μ * S.P.sigma (j + 1) * x) +
        S.CM * S.P.eps j * (4 * S.C2 * S.Cact C₀ * S.P.ksh (j + 1)) *
          ((1 + x) ^ 3 * Real.exp (S.P.μ * S.σ' * x)) +
        S.CM * S.P.eps j * (2 * CF * S.P.ksh (j + 1)) * (1 + x) ^ 3 := by
  have hμ := hS.one_lt_μ
  have hAj := hS.valid.A_pos j
  have hAk : S.P.A (j + 1) = S.P.μ * S.P.A j := A_succ S.P hj
  have hAk0 : 0 < S.P.A (j + 1) := hS.valid.A_pos (j + 1)
  set u := S.P.μ * x with hu
  have hu0 : 0 ≤ u := mul_nonneg (by linarith) hx0
  have humem : u ∈ Icc (0 : ℝ) (S.P.activeTime (j + 1) t) := ⟨hu0, hx⟩
  set t'' := S.P.tsh (j + 1) + u / S.P.A (j + 1) with ht''
  have htj : S.P.A j * t'' = S.P.A j * S.P.tsh (j + 1) + x := by
    rw [ht'', hAk, hu]
    field_simp
  have htk : S.P.A (j + 1) * t'' = S.P.tash (j + 1) + u := by
    rw [ht'', Approx.tash_def]
    field_simp
  have ht''mem : t'' ∈ Icc (S.P.tsh (j + 1)) t := by
    have h1 : u / S.P.A (j + 1) ≤ t - S.P.tsh (j + 1) := by
      rw [div_le_iff₀ hAk0, mul_comm]
      exact hx
    have h2 := div_nonneg hu0 hAk0.le
    exact ⟨by linarith, by linarith⟩
  have h0 : 0 ≤ t'' := (tsh_nonneg hS h).trans ht''mem.1
  have ht0 : t'' ∈ Icc (0 : ℝ) t := ⟨h0, ht''mem.2⟩
  have hTS := (transfer_step_one S hS hj (by have := h.le_n; omega) h0
    (pertDefined hS h ht0 (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))
    (hDefined_j hS hj h ht0) (hDefined_k hS hj h ht''mem) S.s).2
  rw [htj, htk] at hTS
  have hact := h.active u humem
  have hinn := h.inner u humem
  have hc := h.clock.ksh_mem le_rfl h.le_n
  have hG := G_mem S hS (Finset.mem_Icc.mpr ⟨by omega, h.le_n⟩)
  have hT1 := (OneRing.active_tOne S.P.χ hS.admissible hS.hN hS.σ'_mem hC₀ hG hc.1).2 u hu0
  have hjap := jap_mul_pow_le hμ.le (mu_pow_le hS) hx0
  have hC2 := one_le_C2 S
  have hCact : 1 ≤ S.Cact C₀ := hC₀.trans (OneRing.le_Cact _ _ _)
  have hksh := hc.1
  have hCM := CM_pos S
  have heps := hS.valid.eps_pos j
  -- the envelope and the transient
  have hA1 : S.ahatK (j + 1) u = S.P.ksh (j + 1) * Real.exp (S.P.μ * S.P.sigma (j + 1) * x) := by
    rw [Standing.ahatK_def, hu]
    congr 2
    ring
  have hA2 : S.ahatK (j + 1) u * S.rhoHatK C₀ (j + 1) u ≤
      S.Cact C₀ * S.P.ksh (j + 1) * (2 * (1 + x) ^ 3) * Real.exp (S.P.μ * S.σ' * x) := by
    have he : Real.exp (S.σ' * u) = Real.exp (S.P.μ * S.σ' * x) := by
      rw [hu]
      congr 1
      ring
    calc S.ahatK (j + 1) u * S.rhoHatK C₀ (j + 1) u
        ≤ OneRing.Cact S.P.χ S.σ' C₀ * S.P.ksh (j + 1) * Prelim.jap u ^ OneRing.pW *
            Real.exp (S.σ' * u) := hT1
      _ ≤ S.Cact C₀ * S.P.ksh (j + 1) * (2 * (1 + x) ^ 3) * Real.exp (S.σ' * u) := by
          have : 0 ≤ S.Cact C₀ * S.P.ksh (j + 1) := by positivity
          show S.Cact C₀ * S.P.ksh (j + 1) * Prelim.jap u ^ 3 * Real.exp (S.σ' * u) ≤ _
          gcongr
      _ = _ := by rw [he]
  have hw : Sob.normH S.s (S.P.w (j + 1) t'') ≤
      2 * S.C2 * (S.P.ksh (j + 1) * Real.exp (S.P.μ * S.P.sigma (j + 1) * x)) +
        2 * S.C2 * (S.Cact C₀ * S.P.ksh (j + 1) * (2 * (1 + x) ^ 3) *
          Real.exp (S.P.μ * S.σ' * x)) := by
    have h2C2 : 0 ≤ 2 * S.C2 := by linarith
    calc Sob.normH S.s (S.P.w (j + 1) t'')
        ≤ 2 * S.C2 * S.ahatK (j + 1) u * (1 + S.rhoHatK C₀ (j + 1) u) := hact
      _ = 2 * S.C2 * S.ahatK (j + 1) u +
            2 * S.C2 * (S.ahatK (j + 1) u * S.rhoHatK C₀ (j + 1) u) := by ring
      _ ≤ _ := by
          exact add_le_add (by rw [hA1]) (mul_le_mul_of_nonneg_left hA2 h2C2)
  have hi : S.etaIn (j + 1) (S.P.tash (j + 1) + u) ≤ CF * S.P.ksh (j + 1) * (2 * (1 + x) ^ 3) := by
    refine hinn.trans ?_
    have hCF0 : 0 ≤ CF * S.P.ksh (j + 1) := mul_nonneg hCF hksh.le
    exact mul_le_mul_of_nonneg_left hjap hCF0
  have hCMe : 0 ≤ S.CM * S.P.eps j := by positivity
  calc S.etaIn j (S.P.A j * S.P.tsh (j + 1) + x)
      ≤ S.CM * S.P.eps j * (Sob.normH S.s (S.P.w (j + 1) t'') +
          S.etaIn (j + 1) (S.P.tash (j + 1) + u)) := hTS
    _ ≤ S.CM * S.P.eps j * ((2 * S.C2 * (S.P.ksh (j + 1) *
            Real.exp (S.P.μ * S.P.sigma (j + 1) * x)) +
          2 * S.C2 * (S.Cact C₀ * S.P.ksh (j + 1) * (2 * (1 + x) ^ 3) *
            Real.exp (S.P.μ * S.σ' * x))) + CF * S.P.ksh (j + 1) * (2 * (1 + x) ^ 3)) :=
        mul_le_mul_of_nonneg_left (add_le_add hw hi) hCMe
    _ = _ := by ring

/-- **The sum of the coefficients** (`09_relay.tex:726-729`): with `E = C_Mε_{k-1}κ♯_k`,
`D = σ_b(μ-1) ≤ σ_b`, `g = μσ_k - σ_{k-1} ≥ D/2` and `C_F ≤ C₀`. -/
theorem alg_bound {E CQ K₁ C2 Cact C₀ CF I D sb g : ℝ} (hE : 0 ≤ E) (hD : 0 < D) (hDsb : D ≤ sb)
    (hg : D / 2 ≤ g) (hK : 0 ≤ K₁) (hC2 : 0 ≤ C2) (hCact : 0 ≤ Cact)
    (hCF0 : 0 ≤ CF) (hCF : CF ≤ C₀) (hI : 0 ≤ I) :
    E * (2 * CQ / D + 1) * K₁ + E * 2 * C2 / g + E * 4 * C2 * Cact * I + E * 2 * CF * I ≤
      E * (2 * CQ * K₁ + 4 * C2 + sb * K₁ + 2 * sb * (2 * C2 * Cact + C₀) * I) / D := by
  have hg0 : 0 < g := by linarith
  have h1 : E * 2 * C2 / g ≤ E * 4 * C2 / D := by
    rw [div_le_div_iff₀ hg0 hD]
    have h2g : D ≤ 2 * g := by linarith
    calc E * 2 * C2 * D ≤ E * 2 * C2 * (2 * g) :=
          mul_le_mul_of_nonneg_left h2g (mul_nonneg (mul_nonneg hE (by norm_num)) hC2)
      _ = E * 4 * C2 * g := by ring
  have h2 : E * K₁ ≤ E * sb * K₁ / D := by
    rw [le_div_iff₀ hD]
    calc E * K₁ * D ≤ E * K₁ * sb := mul_le_mul_of_nonneg_left hDsb (mul_nonneg hE hK)
      _ = E * sb * K₁ := by ring
  have h3 : E * 4 * C2 * Cact * I + E * 2 * CF * I ≤
      E * 2 * sb * (2 * C2 * Cact + C₀) * I / D := by
    rw [le_div_iff₀ hD]
    have hEI : 0 ≤ E * I := mul_nonneg hE hI
    have hC : 0 ≤ 2 * C2 * Cact + C₀ := by
      have : 0 ≤ 2 * C2 * Cact := mul_nonneg (mul_nonneg (by norm_num) hC2) hCact
      linarith
    have hA : E * 4 * C2 * Cact * I + E * 2 * CF * I ≤ E * 2 * (2 * C2 * Cact + C₀) * I := by
      nlinarith [mul_nonneg hEI (sub_nonneg.mpr hCF)]
    have hB : 0 ≤ E * 2 * (2 * C2 * Cact + C₀) * I :=
      mul_nonneg (mul_nonneg (mul_nonneg hE (by norm_num)) hC) hI
    calc (E * 4 * C2 * Cact * I + E * 2 * CF * I) * D
        ≤ E * 2 * (2 * C2 * Cact + C₀) * I * D := mul_le_mul_of_nonneg_right hA hD.le
      _ ≤ E * 2 * (2 * C2 * Cact + C₀) * I * sb := mul_le_mul_of_nonneg_left hDsb hB
      _ = E * 2 * sb * (2 * C2 * Cact + C₀) * I := by ring
  have heq : E * (2 * CQ * K₁ + 4 * C2 + sb * K₁ + 2 * sb * (2 * C2 * Cact + C₀) * I) / D =
      E * (2 * CQ / D + 1) * K₁ - E * K₁ + E * 4 * C2 / D + E * sb * K₁ / D +
        E * 2 * sb * (2 * C2 * Cact + C₀) * I / D := by
    field_simp
    ring
  linarith

/-- **`maj^in_{k-1}` follows the envelope of ring `k`** (`09_relay.tex:680-729`): for
`u ∈ [0, A_k(t - t♯_k)]`, `k = j+1`,
`maj^in_j(A_j(t♯_k + u/A_k)) ≤ C_Mε_jâ_k(u) B/(σ_b(μ-1))`. -/
theorem majIn_le {S : Standing} {C₀ K₁ CF t : ℝ} (hS : S.Holds) (hDet : S.Det) (hC₀ : 1 ≤ C₀)
    (hK₁ : 0 < K₁) (hCF : CF ∈ Ioc 0 C₀) {j : ℕ} (hj : 1 ≤ j)
    (h : S.OprimeHyp C₀ K₁ CF (j + 1) t) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (S.P.activeTime (j + 1) t)) :
    S.majIn j (S.P.A j * (S.P.tsh (j + 1) + u / S.P.A (j + 1))) ≤
      S.CM * S.P.eps j * S.ahatK (j + 1) u *
        (2 * S.CQ * K₁ + 4 * S.C2 + S.sigb * K₁ +
          2 * S.sigb * (2 * S.C2 * S.Cact C₀ + C₀) * Ip 3 (9 * S.sigma0 / 64)) /
        (S.sigb * (S.P.μ - 1)) := by
  have hμ := hS.one_lt_μ
  have hμle := hS.μ_le
  have hμ0 : 0 < S.P.μ := by linarith
  have hAj := hS.valid.A_pos j
  have hAk : S.P.A (j + 1) = S.P.μ * S.P.A j := A_succ S.P hj
  have hsb := sigb_pos hS
  obtain ⟨hgap, hσj, hσ0⟩ := detune_facts hS hDet hj h.le_n
  have hτ' : S.P.A j * (S.P.tsh (j + 1) + u / S.P.A (j + 1)) =
      S.P.A j * S.P.tsh (j + 1) + u / S.P.μ := by
    rw [hAk]
    field_simp
  rw [hτ']
  have hL0 : 0 ≤ u / S.P.μ := div_nonneg hu.1 hμ0.le
  have hμL : S.P.μ * (u / S.P.μ) = u := by field_simp
  have hτa0 : 0 ≤ S.P.A j * S.P.tsh (j + 1) := mul_nonneg hAj.le (tsh_nonneg hS h)
  have hsplit := maj_le_split (σ := S.P.sigma j) (η := S.etaIn j) hτa0
    (le_add_of_nonneg_right hL0) (fun v _ => S.etaIn_nonneg j v)
  rw [add_sub_cancel_left] at hsplit
  -- constants
  have hD0 : 0 < S.sigb * (S.P.μ - 1) := mul_pos hsb (by linarith)
  have hDsb : S.sigb * (S.P.μ - 1) ≤ S.sigb := by nlinarith
  have hg2 : S.sigb * (S.P.μ - 1) / 2 ≤ S.P.μ * S.P.sigma (j + 1) - S.P.sigma j := by linarith
  have hg0 : 0 < S.P.μ * S.P.sigma (j + 1) - S.P.sigma j := by linarith
  have hX0 : 0 < 9 * S.sigma0 / 64 := by linarith
  have hσ'0 : 0 < S.σ' := by linarith [hS.σ'_gt]
  have hσ'σ : S.σ' < 3 / 4 * S.sigma0 := hS.σ'_lt_sigma
  have hXj : 9 * S.sigma0 / 64 ≤ S.P.sigma j := by linarith
  have hXj' : 9 * S.sigma0 / 64 ≤ S.P.sigma j - S.P.μ * S.σ' := by
    have : S.P.μ * S.σ' ≤ 17 / 16 * S.σ' := mul_le_mul_of_nonneg_right hμle hσ'0.le
    linarith
  have hksh0 : 0 ≤ S.P.ksh (j + 1) := S.P.ksh_nonneg _
  have hCM := CM_pos S
  have heps := hS.valid.eps_pos j
  have hC2 := one_le_C2 S
  have hCact : 1 ≤ S.Cact C₀ := hC₀.trans (OneRing.le_Cact _ _ _)
  have hCQ := CQ_nonneg S
  have hCF0 := hCF.1
  have hE : 0 ≤ S.CM * S.P.eps j * S.P.ksh (j + 1) := by positivity
  -- the second term
  have htail := tail_bound (σj := S.P.sigma j) (σk := S.P.sigma (j + 1)) (μ := S.P.μ)
    (σ' := S.σ') (X := 9 * S.sigma0 / 64) (L := u / S.P.μ)
    (α := S.CM * S.P.eps j * (2 * S.C2 * S.P.ksh (j + 1)))
    (β := S.CM * S.P.eps j * (4 * S.C2 * S.Cact C₀ * S.P.ksh (j + 1)))
    (γ := S.CM * S.P.eps j * (2 * CF * S.P.ksh (j + 1)))
    (F := fun x => S.etaIn j (S.P.A j * S.P.tsh (j + 1) + x))
    hL0 hX0 hg0 hXj hXj' (by positivity) (by positivity) (by positivity)
    (fun x hx => etaIn_le hS hC₀ hCF0.le hj h hx.1 (by
      calc S.P.μ * x ≤ S.P.μ * (u / S.P.μ) := mul_le_mul_of_nonneg_left hx.2 hμ0.le
        _ = u := hμL
        _ ≤ _ := hu.2))
  beta_reduce at htail
  -- the first term
  have hCr : 0 ≤ S.Crelay * S.P.eps j := by
    have : 0 ≤ 2 * S.CQ / (S.sigb * (S.P.μ - 1)) := div_nonneg (by linarith) hD0.le
    show 0 ≤ S.CM * (2 * S.CQ / (S.sigb * (S.P.μ - 1)) + 1) * S.P.eps j
    exact mul_nonneg (mul_nonneg hCM.le (by linarith)) heps.le
  have hfirst : S.majIn j (S.P.A j * S.P.tsh (j + 1)) ≤
      S.Crelay * S.P.eps j * (K₁ * S.P.ksh (j + 1)) := by
    rcases lt_or_eq_of_le h.le_n with hlt | hkn
    · have hR := (relay S hS hDet hC₀ hK₁ (relayHyp hS hK₁ hCF hj h)).2.1 hlt
        (S.P.A j * S.P.tsh (j + 1))
        ⟨hτa0, le_min (mul_le_mul_of_nonneg_left h.mem_phase.1 hAj.le) le_rfl⟩
      have hμτ : S.P.μ * (S.P.A j * S.P.tsh (j + 1)) = S.P.tash (j + 1) := by
        rw [Approx.tash_def, hAk]
        ring
      rw [hμτ] at hR
      exact hR.trans (mul_le_mul_of_nonneg_left (h.quiet hlt).2.1 hCr)
    · have h0 : S.P.A j * S.P.tsh (j + 1) = 0 := by rw [hkn, S.P.tsh_n, mul_zero]
      rw [h0, S.majIn_zero]
      exact mul_nonneg hCr (mul_nonneg hK₁.le hksh0)
  have hexp1 : Real.exp (S.P.sigma j * (u / S.P.μ)) ≤ Real.exp (S.P.sigma (j + 1) * u) := by
    rw [Real.exp_le_exp]
    have := mul_nonneg hg0.le hL0
    calc S.P.sigma j * (u / S.P.μ)
        ≤ S.P.μ * S.P.sigma (j + 1) * (u / S.P.μ) := by nlinarith
      _ = S.P.sigma (j + 1) * (S.P.μ * (u / S.P.μ)) := by ring
      _ = S.P.sigma (j + 1) * u := by rw [hμL]
  have hexp2 : Real.exp (S.P.μ * S.P.sigma (j + 1) * (u / S.P.μ)) =
      Real.exp (S.P.sigma (j + 1) * u) := by
    congr 1
    calc S.P.μ * S.P.sigma (j + 1) * (u / S.P.μ)
        = S.P.sigma (j + 1) * (S.P.μ * (u / S.P.μ)) := by ring
      _ = S.P.sigma (j + 1) * u := by rw [hμL]
  have hm0 : 0 ≤ S.majIn j (S.P.A j * S.P.tsh (j + 1)) := majIn_nonneg S j hτa0
  have he0 := (Real.exp_pos (S.P.sigma (j + 1) * u)).le
  have halg := alg_bound (CQ := S.CQ) (K₁ := K₁) (C₀ := C₀) (sb := S.sigb) (C2 := S.C2)
    (Cact := S.Cact C₀) (CF := CF)
    (I := Ip 3 (9 * S.sigma0 / 64)) hE hD0 hDsb hg2 hK₁.le (by linarith) (by linarith) hCF0.le
    hCF.2 (Ip_nonneg 3 _)
  calc S.majIn j (S.P.A j * S.P.tsh (j + 1) + u / S.P.μ)
      ≤ Real.exp (S.P.sigma j * (u / S.P.μ)) * S.majIn j (S.P.A j * S.P.tsh (j + 1)) +
          ∫ x in (0 : ℝ)..(u / S.P.μ), Real.exp (S.P.sigma j * (u / S.P.μ - x)) *
            S.etaIn j (S.P.A j * S.P.tsh (j + 1) + x) := hsplit
    _ ≤ Real.exp (S.P.sigma (j + 1) * u) * (S.Crelay * S.P.eps j * (K₁ * S.P.ksh (j + 1))) +
          Real.exp (S.P.sigma (j + 1) * u) *
            (S.CM * S.P.eps j * (2 * S.C2 * S.P.ksh (j + 1)) /
                (S.P.μ * S.P.sigma (j + 1) - S.P.sigma j) +
              S.CM * S.P.eps j * (4 * S.C2 * S.Cact C₀ * S.P.ksh (j + 1)) *
                Ip 3 (9 * S.sigma0 / 64) +
              S.CM * S.P.eps j * (2 * CF * S.P.ksh (j + 1)) * Ip 3 (9 * S.sigma0 / 64)) := by
        refine add_le_add (mul_le_mul hexp1 hfirst hm0 he0) ?_
        rw [← hexp2]
        exact htail
    _ = Real.exp (S.P.sigma (j + 1) * u) *
          (S.CM * S.P.eps j * S.P.ksh (j + 1) * (2 * S.CQ / (S.sigb * (S.P.μ - 1)) + 1) * K₁ +
            S.CM * S.P.eps j * S.P.ksh (j + 1) * 2 * S.C2 /
              (S.P.μ * S.P.sigma (j + 1) - S.P.sigma j) +
            S.CM * S.P.eps j * S.P.ksh (j + 1) * 4 * S.C2 * S.Cact C₀ *
              Ip 3 (9 * S.sigma0 / 64) +
            S.CM * S.P.eps j * S.P.ksh (j + 1) * 2 * CF * Ip 3 (9 * S.sigma0 / 64)) := by
        simp only [Standing.Crelay]
        ring
    _ ≤ Real.exp (S.P.sigma (j + 1) * u) *
          (S.CM * S.P.eps j * S.P.ksh (j + 1) *
            (2 * S.CQ * K₁ + 4 * S.C2 + S.sigb * K₁ +
              2 * S.sigb * (2 * S.C2 * S.Cact C₀ + C₀) * Ip 3 (9 * S.sigma0 / 64)) /
            (S.sigb * (S.P.μ - 1))) := mul_le_mul_of_nonneg_left halg he0
    _ = _ := by
        rw [Standing.ahatK_def]
        ring

end OprimeH

end Relay

end NonUniqueEuler
