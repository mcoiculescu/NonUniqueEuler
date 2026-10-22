import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec7.Transfer
import NonUniqueEuler.I.Sec7.InnerField
import NonUniqueEuler.I.Sec7.FieldUnits
import NonUniqueEuler.I.Sec6.FieldContinuity
import NonUniqueEuler.I.Infra.CkNorm.Basic
import NonUniqueEuler.H.Sec9.TransferStep.CkCongr
import NonUniqueEuler.H.Sec9.TransferStep.Decomp

/-!
# Proof: `lem:transfer-step` (`lem:transfer` in terms of the field majorants)

Proof of `I/Sec9/TransferStep.lean` (`09_relay.tex:167-225`).

(1) On `N'_i`, `ω_{≥i+1}(t) = A_{i+1}Φ(·/r_{i+1}) + A_{i+1}w_{i+1}(t,·/r_{i+1}) + ω_{≥i+2}(t)`; the
radial term has only a monopole there and the second term none, so `h^in_i(A_it)` (which is the
non-monopole field of `ω_{≥i+1}(t)` in ring-`i` units, `lem:inner-field`) is the field `T₁` of the
second term plus `T₂ = (E_g)_{[i]}`, `g = ω_{≥i+2}(t)`, on `N'` (`H/.../Decomp.lean`).
`lem:transfer`(2) bounds `T₁` by `C_Mε_i‖w_{i+1}(t)‖_{H^{s'}}`, `lem:transfer`(1) bounds `T₂` by
`C_Mε_i sup_{|y|=a/4}|(E_g)_{[i+1]}|`, and `(E_g)_{[i+1]} = h^in_{i+1}(A_{i+1}t)` on `N'`
(`lem:inner-field`; `E_g = 0` if `i + 1 = n`), so the supremum is `≤ η^in_{i+1}(A_{i+1}t)`.

(2) `h^out_k(A_kt)` is the field of `ω(t)1_{S_1(t)∪…∪S_{k-1}(t)}` in ring-`k` units (homogeneity of
`K_BS`), which on `N'` is the sum over `i < k` of the fields of `A_iw_i(t,·/r_i)`
(`transfer_outer_sum_eq`), each bounded by `C_Ob_{i,k}‖w_i(t)‖_{H^{s'}}` (`lem:transfer`(4)).

The identities hold on `N'` only; the `C^{M_h}(N')` norms of the two sides agree because both are
`C^{M_h}` near `N'` and `N' ⊂ closure (interior N')` (`H/.../CkCongr.lean`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace TransferStepAux

/-- `1 ≤ M_h`. -/
theorem one_le_Mh (S : Standing) : 1 ≤ S.Mh := by
  rw [Standing.Mh_def]
  omega

/-- The constants of `lem:transfer` at order `M_h` work. -/
theorem transferConst (S : Standing) (hS : S.Holds) :
    Rings.IsTransferConst S.P.χ S.Mh (Rings.CTM S.P.χ S.Mh) (Rings.CTO S.P.χ S.Mh) :=
  Rings.transferConsts_spec
    (Rings.transfer S.P.χ hS.valid.admissible hS.hN S.Mh (one_le_Mh S))

/-- `r_{i+1} ≤ (a/16) r_i`. -/
theorem r_succ_le (P : Approx) (hP : P.Valid) {i : ℕ} (hi : 1 ≤ i) :
    P.r (i + 1) ≤ a / 16 * P.r i := by
  have hdp := hP.datumParams
  have hr := hP.r_pos i
  have hsucc : P.r (i + 1) = P.s i * P.r i := radius_succ P.sbar P.μ hi
  have hs : P.s i ≤ P.sbar := by
    show P.sbar / (2 * P.μ) ^ i ≤ P.sbar
    exact div_le_self hdp.sbar_pos.le (one_le_pow₀ (by linarith [hdp.one_lt_μ]))
  rw [hsucc]
  exact mul_le_mul_of_nonneg_right (hs.trans hdp.sbar_le) hr.le

/-- `h^in_k(A_k t) ∈ C^M(N')` when `D_{k+1}(t) ⊂ B_{ar_k/8}` (`hIn_continuous` on `[t, t]`). -/
theorem memCk_hIn (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ P.n) {t : ℝ} (ht : 0 ≤ t) (hin : P.HInDefined k t) (M : ℕ) :
    MemCk M annN' (P.hIn k (P.A k * t)) :=
  (Approx.hIn_continuous P hP hN hk hkn ht
    (fun t' ht' => by
      obtain rfl : t' = t := le_antisymm ht'.2 ht'.1
      exact hin) M).1 _ ⟨le_rfl, le_rfl⟩

/-- `sup_{|y| = a/4} |(E_g)_{[i+1]}(y)| ≤ η^in_{i+1}(A_{i+1}t)` for `g = ω_{≥i+2}(t)`, pointwise on
`N'` (`09_relay.tex:212-216`). -/
theorem norm_unitsField_extField_le (S : Standing) (hS : S.Holds) {i : ℕ} (hi : 1 ≤ i)
    (hin : i < S.P.n) {t : ℝ} (ht : 0 ≤ t) (hdi1 : S.P.HDefined (i + 1) t) {y : ℂ}
    (hy : y ∈ annN') :
    ‖S.P.unitsField (i + 1) (BS.extField (S.P.omegaGe (i + 2) t)) y‖ ≤
      S.etaIn (i + 1) (S.P.A (i + 1) * t) := by
  have hP := hS.valid
  have hN := hS.hN
  rcases Nat.lt_or_ge (i + 1) S.P.n with h | h
  · have heq := Rings.inner_field_eq S.P hP hN (k := i + 1) (by omega) h ht hdi1.1 y hy
    rw [heq]
    exact norm_le_normCk (memCk_hIn S.P hP hN (by omega) h.le ht hdi1.1 S.Mh) hy
  · have hn : i + 2 = S.P.n + 1 := by omega
    have hz : BS.extField (S.P.omegaGe (i + 2) t) = 0 := by
      rw [hn, Approx.omegaGe_succ_n]
      funext x
      simp [BS.extField, BS.monopole, velocity]
    have hz' : S.P.unitsField (i + 1) (BS.extField (S.P.omegaGe (i + 2) t)) y = 0 := by
      rw [hz]
      simp [Approx.unitsField, scaleField]
    rw [hz', norm_zero]
    exact normCk_nonneg _ _ _

/-- The identity of `lem:transfer-step`(1) on `N'` (`09_relay.tex:198-206`):
`h^in_i(A_it) = T₁ + T₂`, `T₁` the field of `A_{i+1}w_{i+1}(t,·/r_{i+1})` and `T₂ = (E_g)_{[i]}`,
`g = ω_{≥i+2}(t)`, both in ring-`i` units. -/
theorem hIn_eq_add (S : Standing) (hS : S.Holds) {i : ℕ} (hi : 1 ≤ i) (hin : i < S.P.n)
    {t : ℝ} (ht : 0 ≤ t) (hS1 : S.P.PertDefined (i + 1) t) (hdi : S.P.HDefined i t) :
    EqOn (S.P.hIn i (S.P.A i * t))
      (S.P.unitsField i (velocity (S.P.wPhys (i + 1) t)) +
        S.P.unitsField i (BS.extField (S.P.omegaGe (i + 2) t))) annN' := by
  intro y hy
  have hP := hS.valid
  have hN := hS.hN
  have heq := Rings.inner_field_eq S.P hP hN hi hin ht hdi.1 y hy
  rw [← heq]
  have hri := hP.r_pos i
  have ha := zero_lt_a
  have hy1 : a / 4 ≤ ‖y‖ := hy.1
  have hx : 2 * S.P.r (i + 1) ≤ ‖((S.P.r i : ℝ) : ℂ) * y‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hri]
    have h1 := r_succ_le S.P hP hi
    nlinarith
  have hsplit := TransferStepAux.extField_omegaGe_split S.P hP hN hin ht hS1 hx
  simp only [Approx.unitsField, scaleField, Pi.add_apply]
  rw [hsplit, add_div]

end TransferStepAux

open TransferStepAux in
/-- **`lem:transfer-step`(1)** (`09_relay.tex:170-175`): for `1 ≤ i < n` and `t ≥ 0`, if
`S_{i+1}(t) ⊂ N_{i+1}` and `h_i`, `h_{i+1}` are defined at `t`, then for every integer `s' ≥ 0`,
`h^in_i(A_i t) ∈ C^{M_h}(N')` and
`η^in_i(A_i t) ≤ C_M ε_i (‖w_{i+1}(t)‖_{H^{s'}} + η^in_{i+1}(A_{i+1} t))`. -/
theorem transfer_step_one (S : Standing) (hS : S.Holds) {i : ℕ} (hi : 1 ≤ i) (hin : i < S.P.n)
    {t : ℝ} (ht : 0 ≤ t) (hS1 : S.P.PertDefined (i + 1) t) (hdi : S.P.HDefined i t)
    (hdi1 : S.P.HDefined (i + 1) t) (s' : ℕ) :
    MemCk S.Mh annN' (S.P.hIn i (S.P.A i * t)) ∧
      S.etaIn i (S.P.A i * t) ≤
        S.CM * S.P.eps i *
          (Sob.normH s' (S.P.w (i + 1) t) + S.etaIn (i + 1) (S.P.A (i + 1) * t)) := by
  have hP := hS.valid
  have hN := hS.hN
  have hT := transferConst S hS
  have hmem := memCk_hIn S.P hP hN hi hin.le ht hdi.1 S.Mh
  refine ⟨hmem, ?_⟩
  -- the field of `A_{i+1}w_{i+1}(t,·/r_{i+1})` (`lem:transfer`(2))
  obtain ⟨hT1mem, -, hT1bd⟩ := hT.next_ring S.P rfl hP i hi hin t ht hS1
  -- the non-monopole field of `g = ω_{≥i+2}(t)` (`lem:transfer`(1))
  obtain ⟨hg1, -, hgsym⟩ := omegaGe_facts S.P hP hN (k := i + 2) (by omega) (by omega) ht
  have hsym : IsMFoldSymmetric 3 (S.P.omegaGe (i + 2) t) :=
    Filter.Eventually.of_forall fun x => by
      simp only [Nat.cast_ofNat]
      exact hgsym x
  have hsupp : ∀ᵐ x ∂(volume : Measure ℂ), a * S.P.r (i + 1) / 8 < ‖x‖ →
      S.P.omegaGe (i + 2) t x = 0 :=
    Filter.Eventually.of_forall fun x hx => by
      refine Set.indicator_of_notMem (fun hxD => ?_) _
      have hb : x ∈ ball (0 : ℂ) (a * S.P.r (i + 1) / 8) := hdi1.1 hxD
      rw [mem_ball_zero_iff] at hb
      linarith
  obtain ⟨hT2mem, hT2bd⟩ := hT.inner_general S.P rfl hP i hi hin _ hg1 hsym hsupp
  -- the supremum on `{|y| = a/4}` is at most `η^in_{i+1}(A_{i+1}t)`
  have ha := zero_lt_a
  have ha1 := a_lt_one
  have hsph : (sphere (0 : ℂ) (a / 4)).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by positivity)
  have hsup : sSup ((fun y => ‖S.P.unitsField (i + 1) (BS.extField (S.P.omegaGe (i + 2) t)) y‖) ''
      sphere (0 : ℂ) (a / 4)) ≤ S.etaIn (i + 1) (S.P.A (i + 1) * t) := by
    refine csSup_le (hsph.image _) ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ annN' := by
      have : ‖y‖ = a / 4 := mem_sphere_zero_iff_norm.mp hy
      show a / 4 ≤ ‖y‖ ∧ ‖y‖ ≤ 3
      constructor <;> linarith
    exact norm_unitsField_extField_le S hS hi hin ht hdi1 hy'
  -- combine
  have hc : 0 ≤ Rings.CTM S.P.χ S.Mh * max 1 Rings.CL1 * S.P.eps i := by
    have h1 := hT.CTM_pos
    have h2 : (0 : ℝ) < max 1 Rings.CL1 := lt_of_lt_of_le one_pos (le_max_left _ _)
    have h3 : 0 < S.P.eps i := by
      have := hP.s_pos i
      have := hP.datumParams.one_lt_μ
      simp only [Approx.eps]
      positivity
    positivity
  have hadd := hT1mem.add hT2mem
  have hcongr := normCk_congr_of_eqOn_closure annN'_subset_closure_interior hmem.near hadd.1.near
    (hIn_eq_add S hS hi hin ht hS1 hdi)
  show normCk S.Mh annN' (S.P.hIn i (S.P.A i * t)) ≤ _
  rw [hcongr]
  have hb1 := hT1bd s'
  have hb2 := hT2bd.trans (mul_le_mul_of_nonneg_left hsup hc)
  calc normCk S.Mh annN' (S.P.unitsField i (velocity (S.P.wPhys (i + 1) t)) +
        S.P.unitsField i (BS.extField (S.P.omegaGe (i + 2) t)))
      ≤ normCk S.Mh annN' (S.P.unitsField i (velocity (S.P.wPhys (i + 1) t))) +
          normCk S.Mh annN' (S.P.unitsField i (BS.extField (S.P.omegaGe (i + 2) t))) := hadd.2
    _ ≤ Rings.CTM S.P.χ S.Mh * max 1 Rings.CL1 * S.P.eps i * Sob.normH s' (S.P.w (i + 1) t) +
          Rings.CTM S.P.χ S.Mh * max 1 Rings.CL1 * S.P.eps i *
            S.etaIn (i + 1) (S.P.A (i + 1) * t) := add_le_add hb1 hb2
    _ = S.CM * S.P.eps i *
          (Sob.normH s' (S.P.w (i + 1) t) + S.etaIn (i + 1) (S.P.A (i + 1) * t)) := by
        show _ = Rings.CTM S.P.χ S.Mh * max 1 Rings.CL1 * S.P.eps i * _
        ring

open TransferStepAux in
/-- **`lem:transfer-step`(2)** (`09_relay.tex:176-183`): for `1 ≤ k ≤ n` and `t ≥ 0`, if `h_k` is
defined at `t` and `S_i(t) ⊂ N_i` for every `i < k`, then for every integer `s' ≥ 0`,
`h^out_k(A_k t) ∈ C^{M_h}(N')` and `η^out_k(A_k t) ≤ C_O Σ_{i<k} b_{i,k} ‖w_i(t)‖_{H^{s'}}`. -/
theorem transfer_step_two (S : Standing) (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ S.P.n)
    {t : ℝ} (ht : 0 ≤ t) (hdef : S.P.HDefined k t)
    (hS' : ∀ i ∈ Finset.Ico 1 k, S.P.PertDefined i t) (s' : ℕ) :
    MemCk S.Mh annN' (S.P.hOut k (S.P.A k * t)) ∧
      S.etaOut k (S.P.A k * t) ≤
        S.CO * ∑ i ∈ Finset.Ico 1 k, S.P.b i k * Sob.normH s' (S.P.w i t) := by
  -- `hdef` (`h_k` defined at `t`) is not needed: `transfer_outer_sum_eq` and `lem:transfer`(4)
  -- use only `S_i(t) ⊂ N_i` for `i < k`.
  have hP := hS.valid
  have hN := hS.hN
  have hT := transferConst S hS
  have hA := hP.A_pos k
  have hr := hP.r_pos k
  -- `h^out_k(A_kt)` is the field of `ω(t)1_{S_1(t)∪…∪S_{k-1}(t)}` in ring-`k` units
  have hfun : S.P.hOut k (S.P.A k * t) = S.P.unitsField k (velocity (S.P.omegaOut k t)) := by
    funext y
    simp only [Approx.hOut, Approx.nuOut, Approx.unitsVort, Approx.unitsField]
    rw [mul_div_cancel_left₀ t hA.ne']
    exact (Rings.fields_scaleVort hA hr _).1 y
  obtain ⟨hmem, -⟩ := hT.outer_sum S.P rfl hP k hk hkn t ht hS'
  refine ⟨by rw [hfun]; exact hmem, ?_⟩
  -- the fields of the perturbations of the outer rings (`lem:transfer`(4))
  have hF : ∀ i ∈ Finset.Ico 1 k,
      MemCk S.Mh annN' (S.P.unitsField k (velocity (S.P.wPhys i t))) := fun i hi =>
    (hT.outer_ring S.P rfl hP i k (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2 hkn t ht
      (hS' i hi)).1
  obtain ⟨hsmem, hsbd⟩ := memCk_finsetSum annN'_nonempty (Finset.Ico 1 k)
    (fun i => S.P.unitsField k (velocity (S.P.wPhys i t))) hF
  have hcongr := normCk_congr_of_eqOn_closure annN'_subset_closure_interior hmem.near
    hsmem.near (Rings.transfer_outer_sum_eq S.P hP hN hk hkn ht hS')
  show normCk S.Mh annN' (S.P.hOut k (S.P.A k * t)) ≤ _
  rw [hfun, hcongr]
  refine hsbd.trans ?_
  show _ ≤ Rings.CTO S.P.χ S.Mh * max 1 Rings.CL1 * _
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hb := (hT.outer_ring S.P rfl hP i k (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2 hkn
    t ht (hS' i hi)).2.2 s'
  rw [← mul_assoc]
  exact hb

end Relay

end NonUniqueEuler
