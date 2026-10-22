import NonUniqueEuler.Defs.Sec7.All
import NonUniqueEuler.I.Sec6.Speed
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.H.Sec7.Transfer.Sum
import NonUniqueEuler.H.Sec7.Transfer.Region

/-!
# Proof: `lem:transfer` (fields induced by one ring on another)

Proof of `I/Sec7/Transfer.lean` (`07_several_rings.tex:83-237`). The helpers are in
`H/Sec7/Transfer/` (namespace `NonUniqueEuler.Rings.TransferAux`):
* `PowerSeries` (termwise derivatives of `Σ d_l z^l`), `Fourier` (Cauchy's coefficient estimate on a
  circle), `Series` (the majorant series `U_q`, `V_q` and `tsum_ext_le`), `Fields` (Laurent and power
  series forms of the fields, `eq:derivative-norm` in operator-norm form), `Units` (ring units and
  the scaling rule);
* `Inner`: items (1) (`inner_general_bound`) and (2) (`next_ring_bound`), constants `C1`, `C2`;
* `Region`: item (3) (`inner_region_bound`, constant `M_vort Σ_q C_{3,q}(4/a)^{4+q}`);
* `Outer`: item (4) (`outer_ring_bound`, constant `C4`);
* `Sum`: the identity of item (4) on `B_4 ⊃ N'` (`outer_sum_eq_ball`, via `lem:hollow`), and the
  `C^k` bookkeeping (`memCk_congr_of_eqOn`, `memCk_sum`).

Here `C^T_M = max(C1, C2, C3, 1)` and `C^T_O = max(C4, 1)`. The `H^{s'}` bounds follow from the
`L¹` ones by `‖w‖_{L¹} ≤ C_{L1}‖w‖_{L²} ≤ C_{L1}‖w‖_{H^{s'}}` (`lem:regions-basic`(4),
`Sob.MemH.l2_le`).

Deviations from the manuscript (all harmless, the constants being existential, D11):
* the constants are not the manuscript's `C^{(1)}, …, C^{(4)}`: we bound operator norms of
  derivatives (which are at most the array norms, `norm_iteratedFDeriv_le_arrayNorm`), so the factor
  `2^{q/2}` disappears, and we use the majorants `U_q = Σ_l (l+q)^q 2^{-l}`, `V_q = Σ_l l^q(3/16)^l`
  in place of `S_{m,q}` (only `c_l = 0` for `l < 3`, resp. `d_l = 0` for `l < 2`, is used);
* in item (3) the `L¹` bound is `‖ω_{≥j+1}(t)‖_{L¹} ≤ M_vort A_{j+1}r_{j+1}²` (`lem:speed`,
  `q = 1`) instead of `≤ 2πA_{j+1}r_{j+1}²`;
* the identity of item (4) is proved on the open set `B_4 ⊃ N'` (in ring-`k` units), which is
  needed to transfer the `C^{M_h}(N')` norm; it does not use `S_i(t) ⊂ N_i`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Rings

open RingData Datum TransferAux

/-- `‖w_k(t)‖_{L¹} ≤ max(1, C_{L1}) ‖w_k(t)‖_{H^{s'}}` (`07_several_rings.tex:126-128`). -/
private theorem L1_le_max_normH (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 P.n) {t : ℝ} (ht : 0 ≤ t) (hS : P.PertDefined k t) (s' : ℕ) :
    (eLpNorm (P.wR k t) 1 volume).toReal ≤ max 1 CL1 * Sob.normH s' (P.w k t) := by
  obtain ⟨hsm, hcpt, -, -, hX, -, -, h12⟩ := Approx.regions_basic_four P hP hN hk ht hS
  have hmem2 : MemLp (P.wR k t) 2 volume := hsm.continuous.memLp_of_hasCompactSupport hcpt
  have hl2 : Sob.l2 (P.w k t) ≤ Sob.normH s' (P.w k t) := (hX s').1.l2_le
  have hl2eq : Sob.l2 (P.w k t) = (eLpNorm (P.wR k t) 2 volume).toReal := by
    unfold Sob.l2
    congr 1
    exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun y => by
      simp [Approx.w, Complex.norm_real])
  have h1 : (eLpNorm (P.wR k t) 1 volume).toReal ≤
      CL1 * (eLpNorm (P.wR k t) 2 volume).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmem2.eLpNorm_ne_top) h12
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal CL1_nonneg] at this
  have hm : 0 ≤ max 1 CL1 := le_trans zero_le_one (le_max_left _ _)
  rw [← hl2eq] at h1
  exact h1.trans (mul_le_mul (le_max_right _ _) hl2 (Sob.l2_nonneg _) hm)

/-- `C e x ≤ K max(1, C_{L1}) e x` for `C ≤ K`. -/
private theorem const_le {C K e x : ℝ} (hCK : C ≤ K) (hK : 0 ≤ K) (he : 0 ≤ e) (hx : 0 ≤ x) :
    C * e * x ≤ K * max 1 CL1 * e * x := by
  have h1 : C ≤ K * max 1 CL1 := hCK.trans (le_mul_of_one_le_right hK (le_max_left _ _))
  calc C * e * x = C * (e * x) := by ring
    _ ≤ K * max 1 CL1 * (e * x) := mul_le_mul_of_nonneg_right h1 (mul_nonneg he hx)
    _ = K * max 1 CL1 * e * x := by ring

/-- `C e L ≤ K max(1, C_{L1}) e H` for `C ≤ K` and `L ≤ max(1, C_{L1}) H`. -/
private theorem const_le_H {C K e L H : ℝ} (hCK : C ≤ K) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hL : L ≤ max 1 CL1 * H) (hH : 0 ≤ H) :
    C * e * L ≤ K * max 1 CL1 * e * H := by
  have hm : 0 ≤ max 1 CL1 := le_trans zero_le_one (le_max_left _ _)
  calc C * e * L ≤ C * e * (max 1 CL1 * H) := mul_le_mul_of_nonneg_left hL (mul_nonneg hC he)
    _ = C * (max 1 CL1 * e * H) := by ring
    _ ≤ K * (max 1 CL1 * e * H) :=
        mul_le_mul_of_nonneg_right hCK (mul_nonneg (mul_nonneg hm he) hH)
    _ = K * max 1 CL1 * e * H := by ring

private theorem annN'_nonempty : annN'.Nonempty := by
  refine ⟨1, ?_, ?_⟩ <;> simp only [norm_one]
  · have := a_lt_one'
    linarith
  · norm_num

private theorem annN'_subset_ball : annN' ⊆ ball (0 : ℂ) 4 := fun y hy => by
  have : ‖y‖ ≤ 3 := hy.2
  rw [mem_ball_zero_iff]
  linarith

set_option linter.unusedVariables false in
/-- **`lem:transfer`** (`07_several_rings.tex:83-114`), existence of the constants. Under
(N1)–(N3), for an admissible cutoff `χ` and an integer `M_h ≥ 1`, there are `C^T_M, C^T_O` such that
items (1)–(4) hold, with `C_M = C^T_M max(1,C_{L1})`, `C_O = C^T_O max(1,C_{L1})`, for every valid
approximation with cutoff `χ` and every time `t ≥ 0` (`Rings.IsTransferConst`). -/
theorem transfer (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    (Mh : ℕ) (hMh : 1 ≤ Mh) :
    ∃ CTM CTO : ℝ, IsTransferConst χ Mh CTM CTO := by
  have ha := a_pos'
  set C3 : ℝ := Mvort * ∑ q ∈ Finset.range (Mh + 1), BS.cExtMultipole 3 q * (4 / a) ^ (3 + 1 + q)
    with hC3
  have hC3' : 0 ≤ C3 := by
    have hc : ∀ q, 0 < BS.cExtMultipole 3 q := fun q =>
      (BS.cExtMultipole_finite (m := 3) (by norm_num) q).2.2
    exact mul_nonneg Mvort_pos.le (Finset.sum_nonneg fun q _ => (mul_pos (hc q) (by positivity)).le)
  set KM : ℝ := max (max (C1 Mh) (C2 Mh)) (max C3 1) with hKM
  set KO : ℝ := max (C4 Mh) 1 with hKO
  have hKM1 : 1 ≤ KM := le_trans (le_max_right C3 1) (le_max_right _ _)
  have hKO1 : 1 ≤ KO := le_max_right _ _
  have hKM0 : 0 ≤ KM := le_trans zero_le_one hKM1
  have hKO0 : 0 ≤ KO := le_trans zero_le_one hKO1
  have hC1 : C1 Mh ≤ KM := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : C2 Mh ≤ KM := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC3K : C3 ≤ KM := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC4 : C4 Mh ≤ KO := le_max_left _ _
  refine ⟨KM, KO, ?_⟩
  refine
    { CTM_pos := lt_of_lt_of_le zero_lt_one hKM1
      CTO_pos := lt_of_lt_of_le zero_lt_one hKO1
      inner_general := ?_
      next_ring := ?_
      inner_region := ?_
      outer_ring := ?_
      outer_sum := ?_ }
  · -- item (1)
    intro P _ hP j hj _ g hg hsym hsupp
    obtain ⟨hmem, hle⟩ := inner_general_bound P hP Mh hj hg hsym hsupp
    refine ⟨hmem, hle.trans (const_le hC1 hKM0 (hP.eps_pos j).le ?_)⟩
    exact Real.sSup_nonneg (by rintro _ ⟨y, -, rfl⟩; exact norm_nonneg _)
  · -- item (2)
    intro P hPχ hP j hj hjn t ht hS
    have hN' : NumericalHypothesis P.χ := hPχ ▸ hN
    obtain ⟨hmem, hle⟩ := next_ring_bound P hP hN' Mh hj hjn ht hS
    have hk : j + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    refine ⟨hmem, hle.trans (const_le hC2 hKM0 (hP.eps_pos j).le ENNReal.toReal_nonneg),
      fun s' => hle.trans ?_⟩
    exact const_le_H hC2 (C2_nonneg Mh) (hP.eps_pos j).le
      (L1_le_max_normH P hP hN' hk ht hS s') (Sob.normH_nonneg _ _)
  · -- item (3)
    intro P hPχ hP j hj hjn t ht R hR hRa hD
    have hN' : NumericalHypothesis P.χ := hPχ ▸ hN
    have hk : j + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hsupp : tsupport (P.omegaGe (j + 1) t) ⊆ closedBall 0 R :=
      closure_minimal (Set.support_indicator_subset.trans hD) isClosed_closedBall
    have hL1 : eLpNorm (P.omegaGe (j + 1) t) 1 volume ≤
        ENNReal.ofReal (Mvort * P.A (j + 1) * P.r (j + 1) ^ 2) := by
      have h := (Approx.speed P hP hN' hk ht).1 1 (Set.mem_insert 1 _)
      simp only [div_one, ENNReal.ofReal_one, Real.rpow_one, Real.rpow_two] at h
      exact h
    obtain ⟨hmem, hle⟩ := inner_region_bound P hP hN' Mh hj hjn ht hR hRa hsupp hL1
    refine ⟨hmem, hle.trans (le_of_eq_of_le ?_ (const_le hC3K hKM0 (hP.eps_pos j).le
      (pow_nonneg (div_nonneg hR.le (hP.r_pos _).le) 3)))⟩
    have hs := hP.s_pos j
    have hr := hP.r_pos j
    rw [Approx.eps_def, r_succ' P hj, hC3]
    field_simp
  · -- item (4)
    intro P hPχ hP i k hi hik hkn t ht hS
    have hN' : NumericalHypothesis P.χ := hPχ ▸ hN
    have hiI : i ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨hi, by omega⟩
    have hb : 0 ≤ P.b i k := by
      rw [Approx.b_def]
      have hμ : 0 < P.μ := by linarith [hP.datumParams.one_lt_μ]
      exact (mul_pos (zpow_pos hμ _) (div_pos (hP.r_pos k) (hP.r_pos i))).le
    obtain ⟨hmem, hle⟩ := outer_ring_bound P hP hN' Mh hi hik hkn ht hS
    refine ⟨hmem, hle.trans (const_le hC4 hKO0 hb ENNReal.toReal_nonneg), fun s' => hle.trans ?_⟩
    exact const_le_H hC4 (C4_nonneg Mh) hb (L1_le_max_normH P hP hN' hiI ht hS s')
      (Sob.normH_nonneg _ _)
  · -- the sum in item (4)
    intro P hPχ hP k hk hkn t ht hS
    have hN' : NumericalHypothesis P.χ := hPχ ▸ hN
    have hF : ∀ i ∈ Finset.Ico 1 k,
        MemCk Mh annN' (P.unitsField k (velocity (P.wPhys i t))) ∧
          normCk Mh annN' (P.unitsField k (velocity (P.wPhys i t))) ≤
            C4 Mh * P.b i k * (eLpNorm (P.wR i t) 1 volume).toReal := fun i hi =>
      outer_ring_bound P hP hN' Mh (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2 hkn ht
        (hS i hi)
    have hsum := memCk_sum annN'_nonempty (Finset.Ico 1 k)
      (fun i => P.unitsField k (velocity (P.wPhys i t))) fun i hi => (hF i hi).1
    have heq : ∀ y ∈ ball (0 : ℂ) 4,
        (fun y => ∑ i ∈ Finset.Ico 1 k, P.unitsField k (velocity (P.wPhys i t)) y) y =
          P.unitsField k (velocity (P.omegaOut k t)) y := fun y hy =>
      (outer_sum_eq_ball P hP hN' hk hkn ht y hy).symm
    obtain ⟨hmem, hnorm⟩ := memCk_congr_of_eqOn isOpen_ball annN'_subset_ball heq hsum.1
    refine ⟨hmem, ?_⟩
    rw [hnorm]
    have hb : ∀ i ∈ Finset.Ico 1 k, 0 ≤ P.b i k * (eLpNorm (P.wR i t) 1 volume).toReal := by
      intro i hi
      have hμ : 0 < P.μ := by linarith [hP.datumParams.one_lt_μ]
      rw [Approx.b_def]
      exact mul_nonneg (mul_pos (zpow_pos hμ _) (div_pos (hP.r_pos k) (hP.r_pos i))).le
        ENNReal.toReal_nonneg
    have hm : 1 ≤ max 1 CL1 := le_max_left _ _
    have hS0 : 0 ≤ ∑ i ∈ Finset.Ico 1 k, P.b i k * (eLpNorm (P.wR i t) 1 volume).toReal :=
      Finset.sum_nonneg hb
    calc normCk Mh annN' (fun y => ∑ i ∈ Finset.Ico 1 k,
          P.unitsField k (velocity (P.wPhys i t)) y)
        ≤ ∑ i ∈ Finset.Ico 1 k, normCk Mh annN' (P.unitsField k (velocity (P.wPhys i t))) :=
          hsum.2
      _ ≤ ∑ i ∈ Finset.Ico 1 k, C4 Mh * P.b i k * (eLpNorm (P.wR i t) 1 volume).toReal :=
          Finset.sum_le_sum fun i hi => (hF i hi).2
      _ = C4 Mh * ∑ i ∈ Finset.Ico 1 k, P.b i k * (eLpNorm (P.wR i t) 1 volume).toReal := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ KO * max 1 CL1 *
            ∑ i ∈ Finset.Ico 1 k, P.b i k * (eLpNorm (P.wR i t) 1 volume).toReal := by
          refine mul_le_mul_of_nonneg_right ?_ hS0
          exact hC4.trans (le_mul_of_one_le_right hKO0 hm)

set_option linter.unusedVariables false in
/-- **`lem:transfer`(4), the identity** (`07_several_rings.tex:107-111`, proof `:229-236`). If
`S_i(t) ⊂ N_i` for every `1 ≤ i < k`, then on `N'_k`, in ring-`k` units, the velocity field of
`ω(t)1_{S_1(t)∪…∪S_{k-1}(t)}` is the sum over `i < k` of the velocity fields of
`A_iw_i(t,·/r_i)`. -/
theorem transfer_outer_sum_eq (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ P.n) {t : ℝ} (ht : 0 ≤ t)
    (hS : ∀ i ∈ Finset.Ico 1 k, P.PertDefined i t) :
    ∀ y ∈ annN', P.unitsField k (velocity (P.omegaOut k t)) y =
      ∑ i ∈ Finset.Ico 1 k, P.unitsField k (velocity (P.wPhys i t)) y := by
  intro y hy
  exact outer_sum_eq_ball P hP hN hk hkn ht y (annN'_subset_ball hy)

end Rings

end NonUniqueEuler
