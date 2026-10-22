import NonUniqueEuler.H.Sec9.O.Algebra
import NonUniqueEuler.I.Sec9.QuietRing

/-!
# Helpers for `P/Sec9/O`: applying `thm:quiet` to the rings `l ≤ j`

`09_relay.tex:310-322`: under the hypotheses of `lem:O`, if `maj_l ≤ maj_*` on `[0, A_l t]`,
then the hypotheses of `thm:quiet` hold for ring `l` on `[0, A_l t]` (`OProof.quietHyp_of`), and
its conclusions give `S_l(s) ⊂ 𝒩₋_l ⊂ N_l` and `eq:O-Q` for `s ∈ [0, t]`
(`OProof.pert_bound_of_quietConcl`). Also `maj_k ≥ 0` (`OProof.maj_nonneg`).
-/

noncomputable section

open Set MeasureTheory

namespace NonUniqueEuler.Relay.OProof

open RingData Datum

/-- `maj_k(τ) ≥ 0` for `τ ≥ 0` (`η_k ≥ 0`). -/
theorem maj_nonneg (S : Standing) (k : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ S.maj k τ := by
  show 0 ≤ ∫ v in (0 : ℝ)..τ, Real.exp (S.P.sigma k * (τ - v)) * S.P.eta S.Mh k v
  exact intervalIntegral.integral_nonneg hτ fun v _ =>
    mul_nonneg (Real.exp_pos _).le (S.P.eta_nonneg _ _ _)

/-- `𝒩₋ ⊂ N`. -/
theorem annNm_subset_annN : annNm ⊆ annN := by
  intro y hy
  rw [mem_annNm] at hy
  rw [mem_annN]
  have ha := zero_lt_a
  constructor <;> linarith [hy.1, hy.2]

/-- `𝒩₋_k = r_k𝒩₋ ⊂ r_kN = N_k`. -/
theorem Nmk_subset_Nk (P : Approx) (k : ℕ) : P.Nmk k ⊆ P.Nk k :=
  fun _ hx => annNm_subset_annN hx

/-- **The hypotheses of `thm:quiet` for ring `l ≤ j`** (`09_relay.tex:310-319`): under
`S.OHyp j τ`, for `t ∈ [0, τ/A_j]` and `1 ≤ l ≤ j`, if `maj_l(A_l s) ≤ maj_*` for `s ∈ [0,t]`, then
`S.QuietHyp l (A_l t)`. -/
theorem quietHyp_of (S : Standing) (hS : S.Holds) {j : ℕ} {τ : ℝ} (h : S.OHyp j τ) {t : ℝ}
    (ht : t ∈ Icc 0 (τ / S.P.A j)) {l : ℕ} (hl : l ∈ Finset.Icc 1 j)
    (hmaj : ∀ s ∈ Icc 0 t, S.maj l (S.P.A l * s) ≤ S.majst) : S.QuietHyp l (S.P.A l * t) := by
  have hl' := Finset.mem_Icc.mp hl
  have hA := hS.valid.A_pos l
  have hln : l ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.mpr ⟨hl'.1, by linarith [h.lt_n, hl'.2]⟩
  have hsub : ∀ τ'' ∈ Icc (0 : ℝ) (S.P.A l * t), τ'' / S.P.A l ∈ Icc (0 : ℝ) t := by
    intro τ'' hτ''
    refine ⟨div_nonneg hτ''.1 hA.le, ?_⟩
    rw [div_le_iff₀ hA]
    linarith [hτ''.2]
  have hT : ∀ s ∈ Icc (0 : ℝ) t, s ∈ Icc (0 : ℝ) (τ / S.P.A j) :=
    fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  refine ⟨hl'.1, by linarith [h.lt_n, hl'.2], ?_, ((standing_levels S hS).2.2.2 l hln).2.1, ?_, ?_⟩
  · intro t' ht'
    rw [mul_div_cancel_left₀ t hA.ne'] at ht'
    obtain ⟨hout, hin, -⟩ := h.geom t' (hT t' ht') l hl
    exact ⟨hin, hout⟩
  · intro τ'' hτ''
    have := (h.geom (τ'' / S.P.A l) (hT _ (hsub τ'' hτ'')) l hl).2.2
    rwa [mul_div_cancel₀ τ'' hA.ne'] at this
  · intro τ'' hτ''
    have := hmaj (τ'' / S.P.A l) (hsub τ'' hτ'')
    rwa [mul_div_cancel₀ τ'' hA.ne'] at this

/-- **`S_l(s) ⊂ N_l` and `eq:O-Q`** (`09_relay.tex:319-324`) from the conclusions of `thm:quiet`
for ring `l` on `[0, A_l t]`, for `s ∈ [0,t]`. -/
theorem pert_bound_of_quietConcl (S : Standing) (hS : S.Holds) {l : ℕ} {t : ℝ}
    (hc : S.QuietConcl l (S.P.A l * t)) {s : ℝ} (hs : s ∈ Icc 0 t) :
    S.P.PertDefined l s ∧ Sob.normH S.sh (S.P.w l s) ≤ S.CQ * S.maj l (S.P.A l * s) := by
  have hA := hS.valid.A_pos l
  have hmem : S.P.A l * s ∈ Icc (0 : ℝ) (S.P.A l * t) :=
    ⟨mul_nonneg hA.le hs.1, mul_le_mul_of_nonneg_left hs.2 hA.le⟩
  have h1 := hc.supp _ hmem
  have h2 := hc.bound _ hmem
  rw [mul_div_cancel_left₀ s hA.ne'] at h1 h2
  exact ⟨h1.trans (Nmk_subset_Nk S.P l), h2⟩

end NonUniqueEuler.Relay.OProof
