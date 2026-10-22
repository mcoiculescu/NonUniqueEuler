import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec6.InnerCirc
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.H.Sec9.Oprime.Basic

/-!
# Helpers for `lem:Oprime`: the fields are defined on `[t♯_k, t]`

Helper file of `P/Sec9/Oprime.lean` (`09_relay.tex:638-650`, `:688-692`). Everything here is
proved. Under `S.OprimeHyp C₀ K₁ C_F k t`:

* `G_k ∈ [0, G₁]` and `P.GSmall` (`lem:inner-circ` with `C_Gμs̄² ≤ G₁`), `0 ≤ t♯_k`
  (`lem:clock`(1));
* `pertDefined`: `S_i(t') ⊂ N_i` for `i ≤ k` and `t' ∈ [0,t]` ((Loc)(1) and `t ≤ T_k < t♯_i < T_i`
  for `i < k`, `lem:clock`(1));
* `hDefined_k`: `h_k` is defined at `t' ∈ [t♯_k, t]` (`D_{k+1}(t') ⊂ B_{ar_k/8}` by hypothesis or
  trivially if `k = n`; the rings `i < k-1` lie outside `B_{6r_{k-1}} ⊃ B_{6r_k}` (`lem:O`), and
  ring `k-1` lies in `N_{k-1}`, which does not meet `B_{6r_k}`);
* `normH_w_le`: `‖w_i(t')‖_{H^{s_h}} ≤ C_Q maj_i(A_it')` for `i ≤ k-1`, `t' ∈ [0,t]`
  (`thm:quiet`(c) through `lem:O` if `t' > 0`; `w_i(0) = 0` if `t' = 0`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace OprimeH

open RingData Datum

/-! ### `‖0‖_{H^k} = 0` -/

theorem memH_zero_fun (k : ℕ) : Sob.MemH k (0 : ℂ → ℂ) :=
  ⟨MemLp.zero, fun _ _ => ⟨0, MemLp.zero, fun φ _ => by simp⟩⟩

theorem normH_zero_fun (k : ℕ) : Sob.normH k (0 : ℂ → ℂ) = 0 := by
  have h := ((memH_zero_fun k).const_smul (0 : ℂ)).2
  rw [zero_smul, norm_zero, zero_mul] at h
  exact h

/-! ### Inner circulation and the clock order -/

theorem G_mem (S : Standing) (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n) :
    S.P.G k ∈ Icc (0 : ℝ) Gbar :=
  ((S.P.inner_circ hS.valid hS.hN).2.2.2 hS.CG_le).1 k hk

theorem gSmall (S : Standing) (hS : S.Holds) : S.P.GSmall :=
  ((S.P.inner_circ hS.valid hS.hN).2.2.2 hS.CG_le).2

/-- `0 ≤ maj(τ)` for `τ ≥ 0` and `η ≥ 0`. -/
theorem maj_nonneg' {σ : ℝ} {η : ℝ → ℝ} (hη : ∀ v, 0 ≤ η v) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ OneRing.maj σ η τ := by
  unfold OneRing.maj
  exact intervalIntegral.integral_nonneg hτ fun v _ =>
    mul_nonneg (Real.exp_pos _).le (hη v)

theorem maj_nonneg (S : Standing) (i : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ S.maj i τ :=
  maj_nonneg' (fun v => S.eta_nonneg i v) hτ

theorem majIn_nonneg (S : Standing) (i : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ S.majIn i τ :=
  maj_nonneg' (fun v => S.etaIn_nonneg i v) hτ

variable {S : Standing} {C₀ K₁ CF : ℝ} {t : ℝ}

theorem tsh_nonneg (hS : S.Holds) {k : ℕ} (h : S.OprimeHyp C₀ K₁ CF k t) :
    0 ≤ S.P.tsh k :=
  (S.P.clock_order hS.valid hS.hN (gSmall S hS) h.one_le h.clock).2.2.2 k
    (Finset.mem_Icc.mpr ⟨le_rfl, h.le_n⟩)

theorem t_nonneg (hS : S.Holds) {k : ℕ} (h : S.OprimeHyp C₀ K₁ CF k t) : 0 ≤ t :=
  (tsh_nonneg hS h).trans h.mem_phase.1

/-- **`S_i(t') ⊂ N_i` for `i ≤ k`, `t' ∈ [0,t]`** ((Loc)(1); `t' ≤ t ≤ T_k < t♯_i < T_i` for
`i < k` by `lem:clock`(1)). -/
theorem pertDefined (hS : S.Holds) {k : ℕ} (h : S.OprimeHyp C₀ K₁ CF k t) {t' : ℝ}
    (ht' : t' ∈ Icc (0 : ℝ) t) {i : ℕ} (hi : i ∈ Finset.Icc 1 k) : S.P.PertDefined i t' := by
  have hi' := Finset.mem_Icc.mp hi
  refine (h.loc t' ht').1 i (Finset.mem_Icc.mpr ⟨hi'.1, hi'.2.trans h.le_n⟩) fun hc => ?_
  rcases eq_or_lt_of_le hi'.2 with hik | hlt
  · subst hik
    exact ht'.2.trans h.mem_phase.2
  · have hco := S.P.clock_order hS.valid hS.hN (gSmall S hS) hi'.1 hc
    have h3 := hco.2.2.1 i k le_rfl hlt h.le_n
    have h1 := hco.1 i (Finset.mem_Icc.mpr ⟨le_rfl, hlt.le.trans h.le_n⟩)
    linarith [ht'.2, h.mem_phase.2]

/-- `h^in_k` is defined at `t' ∈ [t♯_k, t]` (by hypothesis if `k < n`; `D_{n+1} = ∅`). -/
theorem hInDefined {k : ℕ} (h : S.OprimeHyp C₀ K₁ CF k t) {t' : ℝ}
    (ht' : t' ∈ Icc (S.P.tsh k) t) : S.P.HInDefined k t' := by
  rcases lt_or_eq_of_le h.le_n with hlt | hkn
  · exact (h.quiet hlt).2.2 t' ht'
  · intro x hx
    rw [hkn, S.P.D_succ_n] at hx
    exact hx.elim

/-- The hypotheses of `lem:O` for `j = k-1`, `τ = A_jt`, at `k = j+1`. -/
theorem oHyp {j : ℕ} (hj : 1 ≤ j) (h : S.OprimeHyp C₀ K₁ CF (j + 1) t) :
    S.OHyp j (S.P.A j * t) := by
  have := (h.outer (by omega)).1
  simpa only [Nat.add_sub_cancel] using this

/-- The conclusions of `lem:O` for `j = k-1`, `τ = A_jt`, at `k = j+1`. -/
theorem oConcl {j : ℕ} (hj : 1 ≤ j) (h : S.OprimeHyp C₀ K₁ CF (j + 1) t) :
    S.OConcl j (S.P.A j * t) := by
  have := (h.outer (by omega)).2.1
  simpa only [Nat.add_sub_cancel] using this

theorem theta_small {j : ℕ} (hj : 1 ≤ j) (h : S.OprimeHyp C₀ K₁ CF (j + 1) t) :
    S.theta j * (S.P.A j * t) ≤ 1 / 2 := by
  have := (h.outer (by omega)).2.2
  simpa only [Nat.add_sub_cancel] using this

theorem div_A (hS : S.Holds) (j : ℕ) (t : ℝ) : S.P.A j * t / S.P.A j = t :=
  mul_div_cancel_left₀ _ (hS.valid.A_pos j).ne'

/-- `h_j` is defined on `[0,t]` and `η_j ≤ 1` there (`lem:O`'s hypotheses). -/
theorem hDefined_j (hS : S.Holds) {j : ℕ} (hj : 1 ≤ j) (h : S.OprimeHyp C₀ K₁ CF (j + 1) t)
    {t' : ℝ} (ht' : t' ∈ Icc (0 : ℝ) t) : S.P.HDefined j t' := by
  have hg := (oHyp hj h).geom t' (by rw [div_A hS]; exact ht') j
    (Finset.mem_Icc.mpr ⟨hj, le_rfl⟩)
  exact ⟨hg.2.1, hg.1⟩

/-- `N_j ∩ B_{6r_{j+1}} = ∅`. -/
theorem Nk_inter_ball (hS : S.Holds) {j : ℕ} (hj : 1 ≤ j) :
    S.P.Nk j ∩ ball 0 (6 * S.P.r (j + 1)) = ∅ := by
  have hr := hS.valid.r_pos j
  have hrs : S.P.r (j + 1) = S.P.s j * S.P.r j := r_succ S.P hj
  have hs := s_le_a hS.valid hj
  have ha := Relay.zero_lt_a
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hxN : ((S.P.r j : ℝ) : ℂ)⁻¹ * x ∈ annN := hx.1
  have hxb : ‖x‖ < 6 * S.P.r (j + 1) := mem_ball_zero_iff.mp hx.2
  have h1 : a / 2 ≤ ‖((S.P.r j : ℝ) : ℂ)⁻¹ * x‖ := hxN.1
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le] at h1
  have h2 : a / 2 * S.P.r j ≤ ‖x‖ := by
    have := mul_le_mul_of_nonneg_left h1 hr.le
    rwa [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, mul_comm] at this
  rw [hrs] at hxb
  nlinarith

/-- **`h_k` is defined at `t' ∈ [t♯_k, t]`** (`09_relay.tex:638-642`), `k = j+1 ≥ 2`. -/
theorem hDefined_k (hS : S.Holds) {j : ℕ} (hj : 1 ≤ j) (h : S.OprimeHyp C₀ K₁ CF (j + 1) t)
    {t' : ℝ} (ht' : t' ∈ Icc (S.P.tsh (j + 1)) t) : S.P.HDefined (j + 1) t' := by
  have h0 : 0 ≤ t' := (tsh_nonneg hS h).trans ht'.1
  refine ⟨hInDefined h ht', fun i hi => ?_⟩
  have hi' := Finset.mem_Ico.mp hi
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi'.2) with hlt | hij
  · -- the rings `i < j` lie outside `B_{6r_j} ⊃ B_{6r_{j+1}}`
    have hout := (hDefined_j hS hj h ⟨h0, ht'.2⟩).2 i (Finset.mem_Ico.mpr ⟨hi'.1, hlt⟩)
    refine Set.eq_empty_of_subset_empty ?_
    rw [← hout]
    refine Set.inter_subset_inter_right _ (ball_subset_ball ?_)
    have hr := hS.valid.r_pos j
    have hrs : S.P.r (j + 1) = S.P.s j * S.P.r j := r_succ S.P hj
    have hs := s_le_a hS.valid hj
    have ha := Relay.a_lt_one
    rw [hrs]
    nlinarith
  · -- ring `j` lies in `N_j`
    subst hij
    have hP := pertDefined hS h ⟨h0, ht'.2⟩ (Finset.mem_Icc.mpr ⟨hj, by omega⟩)
    refine Set.eq_empty_of_subset_empty ?_
    rw [← Nk_inter_ball hS hj]
    exact Set.inter_subset_inter_left _ hP

/-- **`‖w_i(t')‖_{H^{s_h}} ≤ C_Q maj_i(A_i t')` for `1 ≤ i ≤ j`, `t' ∈ [0,t]`**
(`thm:quiet`(c) through `lem:O` if `t' > 0`; `w_i(0) = 0` if `t' = 0`, `09_relay.tex:643-650`). -/
theorem normH_w_le (hS : S.Holds) {j : ℕ} (hj : 1 ≤ j) (h : S.OprimeHyp C₀ K₁ CF (j + 1) t)
    {t' : ℝ} (ht' : t' ∈ Icc (0 : ℝ) t) {i : ℕ} (hi : i ∈ Finset.Icc 1 j) :
    Sob.normH S.sh (S.P.w i t') ≤ S.CQ * S.maj i (S.P.A i * t') := by
  have hi' := Finset.mem_Icc.mp hi
  rcases eq_or_lt_of_le ht'.1 with h0 | hpos
  · subst h0
    have hin : i < S.P.n := by have := h.le_n; omega
    rw [w_zero hS.valid hS.hN hi'.1 hin, normH_zero_fun, mul_zero, S.maj_zero, mul_zero]
  · have hq := ((oConcl hj h).quiet t' ⟨hpos, by rw [div_A hS]; exact ht'.2⟩ i hi).2
    have hb := hq.bound (S.P.A i * t') ⟨mul_nonneg (hS.valid.A_pos i).le ht'.1, le_rfl⟩
    rwa [div_A hS] at hb

end OprimeH

end Relay

end NonUniqueEuler
