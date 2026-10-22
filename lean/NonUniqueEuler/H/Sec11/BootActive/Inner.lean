import NonUniqueEuler.H.Sec11.BootActive.Basic
import NonUniqueEuler.I.Sec7.InnerField
import NonUniqueEuler.I.Sec7.FieldUnits
import NonUniqueEuler.I.Sec6.Speed
import NonUniqueEuler.I.Sec6.DefClock
import NonUniqueEuler.I.Sec9.ActiveRing

/-!
# Helper for `P/Sec11/BootActive.lean`: the inner field, `eq:boot-inner`

Step 4 of the proof of `prop:bootstrap`, "(Field), inner part" (`11_bootstrap.tex:416-436`): for
`u ∈ [0, ū]`, `h^in_k(t̄♯_k + u) ∈ C^{M_h}(N')` and
`‖h^in_k(t̄♯_k + u)‖_{C^{M_h}(N')} ≤ C_F κ♯_k ⟨u⟩^m` (`eq:boot-inner`).

* `k = n`: `h^in_n = 0` (`D_{n+1} = ∅`, `G_n = 0`).
* `k < n`: at `t'' = t♯_k + u/A_k`, `lem:geometry`(a) gives `D_{k+1}(t'') ⊂ \bar B_R`,
  `R = ϱ_k(t'') < ar_k/8`, with kick time `T_pin + μu` (`kickTime_eq`); `lem:speed` gives
  `‖ω_{≥k+1}(t'')‖_{L¹} ≤ M_vort A_{k+1}r_{k+1}²`; `lem:inner-field` (with the chosen `C_in`) and its
  identity `E_{[k]} = h^in_k(A_kt'')` give `‖h^in_k‖ ≤ C_inμs_k²(R/r_k)^m`; then the algebra of
  `eq:boot-inner` (`inner_alg`) and `κ♯_k ≥ K_lo s_k^{m+2}`.

The identity `h^in_k(A_kt) = E_{[k]}` as functions on `ℂ` (`hIn_eq_unitsField_extField`) is copied
from `P/Sec7/FieldBound.lean` (`Rings.hIn_eq_unitsField_extField`, same proof): `inner_field_eq`
gives it only on `N'`, while `C^{M_h}(N')` norms need it near `N'`; both sides differ by a constant
multiple of `y^⊥/|y|²`, and the identity at the point `1 ∈ N'` kills the constant. All proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace BootActiveH

open RingData Datum

theorem a_lt_one_aux : a < 1 := by
  unfold a
  rw [Real.exp_lt_one_iff]
  norm_num [ξL, ξR]

theorem one_mem_annN' : (1 : ℂ) ∈ annN' := by
  have h := a_lt_one_aux
  show a / 4 ≤ ‖(1 : ℂ)‖ ∧ ‖(1 : ℂ)‖ ≤ 3
  rw [norm_one]
  constructor <;> linarith

/-- The inner field is the non-monopole field of `ω_{≥j+1}(t)` in ring-`j` units, as functions
on `ℂ` (from `inner_field_eq` at the single point `y = 1 ∈ N'`). Copied from
`P/Sec7/FieldBound.lean`. -/
theorem hIn_eq_unitsField_extField {P : Approx} (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    {j : ℕ} (hj : 1 ≤ j) (hjn : j < P.n) {t : ℝ} (ht : 0 ≤ t) (hin : P.HInDefined j t) :
    P.hIn j (P.A j * t) = P.unitsField j (BS.extField (P.omegaGe (j + 1) t)) := by
  have hA := hP.A_pos j
  have hr := hP.r_pos j
  have hτ : P.A j * t / P.A j = t := by field_simp
  have hE : ∀ y, P.unitsField j (BS.extField (P.omegaGe (j + 1) t)) y =
      velocity (P.nuIn j t) y - BS.monopole (P.nuIn j t) y := by
    intro y
    have h3 := (Rings.fields_scaleVort hA hr (P.omegaGe (j + 1) t)).2.2 y
    rw [Approx.unitsField, ← h3]
    rfl
  have hH : ∀ y, P.hIn j (P.A j * t) y =
      velocity (P.nuIn j t) y - (P.G j : ℂ) * (Complex.I * y) / ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    simp only [Approx.hIn, hτ]
  set α : ℝ := ∫ x, P.nuIn j t x with hα
  have hdiff : ∀ y, P.hIn j (P.A j * t) y - P.unitsField j (BS.extField (P.omegaGe (j + 1) t)) y =
      ((α / (2 * Real.pi) - P.G j : ℝ) : ℂ) * (Complex.I * y / ((‖y‖ ^ 2 : ℝ) : ℂ)) := by
    intro y
    rw [hH, hE, BS.monopole, biotSavartKernel]
    by_cases hy : y = 0
    · simp [hy]
    · have hy' : ((‖y‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
        have : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
        exact_mod_cast pow_ne_zero 2 this
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
      push_cast at hy' ⊢
      field_simp
      ring
  have h1 := Rings.inner_field_eq P hP hN hj hjn ht hin 1 one_mem_annN'
  have hc : α / (2 * Real.pi) - P.G j = 0 := by
    have h0 := hdiff 1
    rw [← h1, sub_self] at h0
    simp only [norm_one, one_pow, Complex.ofReal_one, div_one, mul_one] at h0
    have h0' := h0.symm
    rcases mul_eq_zero.1 h0' with h | h
    · exact_mod_cast h
    · exact absurd h Complex.I_ne_zero
  funext y
  have := hdiff y
  rw [hc, Complex.ofReal_zero, zero_mul, sub_eq_zero] at this
  exact this

/-- `h^in_n = 0` (`D_{n+1} = ∅`, `G_n = 0`). -/
theorem hIn_n (P : Approx) (τ : ℝ) : P.hIn P.n τ = 0 := by
  funext y
  simp [Approx.hIn, Approx.nuIn, Approx.omegaGe_succ_n, Approx.unitsVort, scaleVort, velocity,
    Approx.G_n]

theorem supIterDerivE_zero (q : ℕ) : supIterDerivE q annN' (0 : ℂ → ℂ) = 0 := by
  simp only [supIterDerivE]
  refine le_antisymm (iSup₂_le fun x _ => ?_) bot_le
  rw [show (0 : ℂ → ℂ) = fun _ => (0 : ℂ) from rfl, iteratedFDeriv_fun_zero]
  rw [Pi.zero_apply, enorm_eq_nnnorm, nnnorm_zero]; rfl

theorem normCkE_zero (M : ℕ) : normCkE M annN' (0 : ℂ → ℂ) = 0 := by
  simp [normCkE, supIterDerivE_zero]

theorem normCk_zero (M : ℕ) : normCk M annN' (0 : ℂ → ℂ) = 0 := by
  simp [normCk, normCkE_zero]

theorem memCk_zero (M : ℕ) : MemCk M annN' (0 : ℂ → ℂ) :=
  ⟨⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩, by rw [normCkE_zero]; exact ENNReal.zero_ne_top⟩

/-- **`eq:boot-inner`** (`11_bootstrap.tex:416-436`): for `u ∈ [0, A_k(t' - t♯_k)]`,
`h^in_k(t̄♯_k + u) ∈ C^{M_h}(N')` and `η^in_k(t̄♯_k + u) ≤ C_F κ♯_k ⟨u⟩^m`. Hypotheses: (SA), the
clock up to level `k`, `t' ∈ Ph_k`, `t' > t♯_k`, `lem:geometry` with `t'`, and (for `k < n`)
`κ♯_k ≥ K_lo s_k^{m+2}` (Step 3). -/
theorem boot_inner (S : Standing) (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n)
    (hc : S.P.ClockUpTo k) {t' : ℝ} (ht' : t' ∈ S.P.Phase k) (htsh : S.P.tsh k < t')
    (hgeo : S.GeometryConcl t') (hamp : k < S.P.n → S.Klo * S.P.s k ^ (3 + 2) ≤ S.P.ksh k) :
    ∀ u ∈ Icc (0 : ℝ) (S.P.activeTime k t'), MemCk S.Mh annN' (S.P.hIn k (S.P.tash k + u)) ∧
      S.etaIn k (S.P.tash k + u) ≤ S.CF * S.P.ksh k * Prelim.jap u ^ 3 := by
  intro u hu
  have hpos := constPos hS
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hk
  have hCF := hpos.CF_pos
  have hksh := S.P.ksh_nonneg k
  have hj0 := jap_nonneg u
  have hrhs : 0 ≤ S.CF * S.P.ksh k * Prelim.jap u ^ 3 := by positivity
  rcases eq_or_lt_of_le hkn with hkn' | hkn'
  · -- `k = n`: `h^in_n = 0`
    rw [hkn', hIn_n]
    refine ⟨memCk_zero _, ?_⟩
    show normCk S.Mh annN' (S.P.hIn S.P.n (S.P.tash S.P.n + u)) ≤ _
    rw [hIn_n, normCk_zero, ← hkn']
    exact hrhs
  -- `k < n`
  have hP := hS.valid
  have hN := hS.hN
  have hA := A_pos hS k
  have hmem := tsh_add_mem hS hu
  have htsh0 : 0 ≤ S.P.tsh k := (activeConfig_units S hS hk1 hkn hc).1
  set t'' := S.P.tsh k + u / S.P.A k with ht''
  have ht''0 : 0 ≤ t'' := le_trans htsh0 hmem.1
  have hnd : ¬ S.P.DebrisAt k t'' := fun h => absurd h.2 (not_lt.2 (hmem.2.trans ht'.2))
  have hring := hgeo.ring t'' ⟨ht''0, hmem.2⟩ k hk hnd
  have hin : S.P.HInDefined k t'' := hring.2.1
  -- `lem:geometry`(a) on the window `W_k`
  have hc1 : S.P.ClockUpTo (k + 1) := hc.mono (Nat.le_succ k)
  have hTk1 : S.P.T (k + 1) ≤ S.P.tsh k := by
    rw [S.P.tsh_eq_T_add hkn']
    have := div_nonneg hS.Tpin_pos.le (A_pos hS (k + 1)).le
    linarith
  have hwin := hgeo.window k (Finset.mem_Ico.2 ⟨hk1, hkn'⟩) hc1 (hTk1.trans htsh.le)
  have hendW : S.P.endW k = S.P.T k := by simp [Approx.endW, hc]
  have ht''W : t'' ∈ Icc (S.P.T (k + 1)) (min t' (S.P.endW k)) :=
    ⟨hTk1.trans hmem.1, le_min hmem.2 (by rw [hendW]; exact hmem.2.trans ht'.2)⟩
  obtain ⟨hD, hball, -⟩ := hwin.2 t'' ht''W
  -- the radius `R = ϱ_k(t'') = (2 + 2C_*(T_pin + μu)) r_{k+1}`
  have hkick : S.P.kickTime k t'' = S.P.Tpin + S.P.μ * u := by
    rw [(S.P.kickTime_eq hP hk1 hkn').1, ht'', activeTime_tsh_add hS]
  have hC := Cstar_nonneg
  have hμ0 : 0 ≤ S.P.μ := by linarith [hS.one_lt_μ]
  have hX0 : 0 ≤ 2 + 2 * Cstar * (S.P.Tpin + S.P.μ * u) := by
    have := hS.Tpin_pos
    have := mul_nonneg hμ0 hu.1
    positivity
  have hr1 := hP.r_pos (k + 1)
  have hrk := hP.r_pos k
  have hRdef : S.P.confRadius k t'' = (2 + 2 * Cstar * (S.P.Tpin + S.P.μ * u)) * S.P.r (k + 1) := by
    rw [Approx.confRadius, hkick]
  have hR0 : 0 < S.P.confRadius k t'' := by
    rw [hRdef]
    have : 0 < 2 + 2 * Cstar * (S.P.Tpin + S.P.μ * u) := by
      have := hS.Tpin_pos
      have := mul_nonneg hμ0 hu.1
      positivity
    positivity
  have hRle : S.P.confRadius k t'' ≤ a * S.P.r k / 8 := by
    have h1 : ((S.P.confRadius k t'' : ℝ) : ℂ) ∈ closedBall (0 : ℂ) (S.P.confRadius k t'') := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg hR0.le]
    have h2 := hball h1
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hR0.le] at h2
    exact h2.le
  have hsupp : tsupport (S.P.omegaGe (k + 1) t'') ⊆ closedBall 0 (S.P.confRadius k t'') :=
    closure_minimal (Set.support_indicator_subset.trans hD) isClosed_closedBall
  -- `lem:speed`: `‖ω_{≥k+1}(t'')‖_{L¹} ≤ M_vort A_{k+1} r_{k+1}²`
  have hL1 : eLpNorm (S.P.omegaGe (k + 1) t'') 1 volume ≤
      ENNReal.ofReal (Mvort * S.P.A (k + 1) * S.P.r (k + 1) ^ 2) := by
    have h := (Approx.speed S.P hP hN (k := k + 1)
      (Finset.mem_Icc.2 ⟨by omega, by omega⟩) ht''0).1 1 (by simp)
    have e1 : ENNReal.ofReal (1 : ℝ) = 1 := ENNReal.ofReal_one
    have e2 : Mvort ^ ((1 : ℝ) / 1) * S.P.A (k + 1) * S.P.r (k + 1) ^ ((2 : ℝ) / 1) =
        Mvort * S.P.A (k + 1) * S.P.r (k + 1) ^ 2 := by
      rw [div_one, div_one, Real.rpow_one, Real.rpow_two]
    rw [e1, e2] at h
    exact h
  -- `lem:inner-field`
  have hMh : 1 ≤ S.Mh := by rw [Standing.Mh_def]; omega
  have hspec := Rings.innerFieldConst_spec (Rings.inner_field S.P.χ hS.admissible hN S.Mh hMh)
  have hb := hspec.bound S.P rfl hP k hk1 hkn' t'' ht''0 _ hR0 hRle hsupp hL1
  have heq := hIn_eq_unitsField_extField hP hN hk1 hkn' ht''0 hin
  rw [ht'', A_mul_tsh_add hS] at heq
  refine ⟨heq ▸ hb.1, ?_⟩
  show normCk S.Mh annN' (S.P.hIn k (S.P.tash k + u)) ≤ _
  rw [heq]
  refine hb.2.trans ?_
  -- the algebra of `eq:boot-inner`
  have hs := hP.s_pos k
  have hrr : S.P.r (k + 1) = S.P.s k * S.P.r k := by
    rw [Approx.r_def, Approx.r_def, Approx.s_def, radius_succ _ _ hk1]
  have hRr : S.P.confRadius k t'' / S.P.r k = (2 + 2 * Cstar * (S.P.Tpin + S.P.μ * u)) * S.P.s k := by
    rw [hRdef, hrr]
    field_simp
  have halg := inner_alg hC hS.Tpin_pos.le hμ0 hP.datumParams.μ_le_two hu.1
  have hKlo := hpos.Klo_pos
  have hCin : 0 < Rings.Cin S.P.χ S.Mh := hpos.Cin_pos
  have hampk := hamp hkn'
  set X := 2 + 2 * Cstar * (S.P.Tpin + S.P.μ * u) with hX
  set Y := (2 + 2 * Cstar * S.P.Tpin) * (1 + 2 * Cstar) with hY
  have hY0 : 0 ≤ Y := by
    have := hS.Tpin_pos
    positivity
  have hCF' : S.CF = Rings.Cin S.P.χ S.Mh * S.P.μ * Y ^ 3 / S.Klo := by
    rw [Standing.CF_def, hY, mul_pow]
    unfold Standing.Cin
    ring
  calc Rings.Cin S.P.χ S.Mh * S.P.μ * S.P.s k ^ 2 * (S.P.confRadius k t'' / S.P.r k) ^ 3
      = Rings.Cin S.P.χ S.Mh * S.P.μ * S.P.s k ^ (3 + 2) * X ^ 3 := by rw [hRr]; ring
    _ ≤ Rings.Cin S.P.χ S.Mh * S.P.μ * S.P.s k ^ (3 + 2) * (Y * Prelim.jap u) ^ 3 := by
        gcongr
    _ = Rings.Cin S.P.χ S.Mh * S.P.μ * Y ^ 3 / S.Klo * (S.Klo * S.P.s k ^ (3 + 2)) *
          Prelim.jap u ^ 3 := by
        field_simp
    _ ≤ S.CF * S.P.ksh k * Prelim.jap u ^ 3 := by
        rw [← hCF']
        gcongr

end BootActiveH

end Relay

end NonUniqueEuler
