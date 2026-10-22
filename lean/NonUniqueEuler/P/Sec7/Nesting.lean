import NonUniqueEuler.Defs.Sec7.All
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec6.RingConfig
import NonUniqueEuler.I.Sec7.SkSmall

/-!
# Proof of `lem:nesting` (confinement of the inner material propagates outward)

Proof of the interface `NonUniqueEuler/I/Sec7/Nesting.lean` (`07_several_rings.tex:420-457`).

* (a) `D_{j+1}(t) = ⋃_{i>j} S_i(t)`: for `j < i ≤ k`, `S_i(t) ⊂ N_i ⊂ \bar B_{2r_i}` and
  `2r_i ≤ (a/16) r_j` (`eq:sk-small`, `Rings.sk_small`); for `i > k`, `S_i(t) ⊂ D_{k+1}(t) ⊂
  \bar B_{ar_k/8} ⊂ \bar B_{ar_j/8}`.
* (b) for `i < j`, `S_i(t) ⊂ N_i ⊂ {|x| ≥ (a/2)r_i}` and `(a/2) r_i ≥ 16 r_j`.
* `supp ω(t) ⊂ ⋃_i S_i(t)` (`regions_basic_two`), so `supp ω(t) ∖ S_j(t)` lies in
  `D_{j+1}(t) ∪ ⋃_{i<j} S_i(t)`.
* In ring-`j` units (`ringConfig_units`), the inner and outer parts of `P.ringConfig j` at time
  `A_j t` are `ν^in_j = A_j⁻¹ ω_{≥j+1}(t, r_j ·)` and `ν^out_j = A_j⁻¹ (ω(t)1_{⋃_{i<j}S_i(t)})(r_j ·)`,
  supported in `r_j⁻¹ D_{j+1}(t) ⊂ \bar B_{a/8}` and `r_j⁻¹ ⋃_{i<j} S_i(t) ⊂ ℝ² ∖ B_8`.

The ratio bound used is `r_k ≤ s_{k-1} r_i ≤ (a/32) r_i` for `1 ≤ i < k`, which follows from
`sk_small` and `s̄ ≤ 1` (here from the hypothesis `s̄^{m-2} ≤ 1/2`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Rings

open RingData Datum

namespace NestingAux

/-- For `1 ≤ i < k`: `r_k ≤ (a/32) r_i` and `r_k ≤ r_i` (from `eq:sk-small` and `s̄ ≤ 1/2`). -/
theorem r_lt_bounds (P : Approx) (hP : P.Valid) (hs : P.sbar ^ (3 - 2) ≤ 1 / 2) {i k : ℕ}
    (hi : 1 ≤ i) (hik : i < k) :
    P.r k ≤ a / 32 * P.r i ∧ P.r k ≤ P.r i := by
  obtain ⟨h1, h2, -, -⟩ := sk_small P hP
  have hri := hP.r_pos i
  have hk1 : 1 ≤ k - 1 := by omega
  obtain ⟨hs0, hs1, hs2⟩ := h1 (k - 1) hk1
  have hsbar : 0 < P.sbar := hP.datumParams.sbar_pos
  have hsb : P.sbar ≤ 1 / 2 := by simpa using hs
  have hpow : P.sbar ^ (k - i - 1) ≤ 1 := pow_le_one₀ hsbar.le (by linarith)
  have hq : P.r k / P.r i ≤ P.s (k - 1) := by
    calc P.r k / P.r i ≤ P.s (k - 1) * P.sbar ^ (k - i - 1) := h2 i k hi hik
      _ ≤ P.s (k - 1) * 1 := by gcongr
      _ = P.s (k - 1) := mul_one _
  rw [div_le_iff₀ hri] at hq
  constructor
  · calc P.r k ≤ P.s (k - 1) * P.r i := hq
      _ ≤ a / 32 * P.r i := by gcongr
  · calc P.r k ≤ P.s (k - 1) * P.r i := hq
      _ ≤ 1 * P.r i := by gcongr; linarith
      _ = P.r i := one_mul _

/-- `N_i = r_i N ⊂ {(a/2) r_i ≤ |x| ≤ 2 r_i}`. -/
theorem norm_of_mem_Nk (P : Approx) (hP : P.Valid) {i : ℕ} {x : ℂ} (hx : x ∈ P.Nk i) :
    a / 2 * P.r i ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * P.r i := by
  have hr := hP.r_pos i
  have hx' : ((P.r i : ℝ) : ℂ)⁻¹ * x ∈ annN := hx
  simp only [annN, Sect.closedAnnulus, mem_ofPred_eq] at hx'
  rw [norm_mul, norm_inv, Complex.norm_of_nonneg hr.le] at hx'
  obtain ⟨h1, h2⟩ := hx'
  rw [le_inv_mul_iff₀ hr] at h1
  rw [inv_mul_le_iff₀ hr] at h2
  constructor
  · linarith
  · linarith

/-- Membership in `D_k(t)`. -/
theorem mem_D {P : Approx} {k : ℕ} {t : ℝ} {x : ℂ} :
    x ∈ P.D k t ↔ ∃ i, (k ≤ i ∧ i ≤ P.n) ∧ x ∈ P.St i t := by
  simp only [Approx.D, mem_iUnion, Finset.mem_Icc, exists_prop]

end NestingAux

open NestingAux in
/-- **`lem:nesting`** (`07_several_rings.tex:420-433`). Assume (N1)–(N3), `s̄ ≤ a/16`,
`s̄^{m-2} ≤ 1/2`; let `1 ≤ k ≤ n`, `t ≥ 0`, `S_j(t) ⊂ N_j` for `1 ≤ j ≤ k`, and
`D_{k+1}(t) ⊂ \bar B_{a r_k/8}`. Then for every `1 ≤ j ≤ k`: (a) `D_{j+1}(t) ⊂ \bar B_{a r_j/8}`;
(b) `S_i(t) ∩ B_{8r_j} = ∅` for `i < j`; all vorticity outside `S_j(t)` lies in
`\bar B_{a r_j/8} ∪ (ℝ² ∖ B_{8r_j})`; and in ring-`j` units at the ring-`j` time `A_j t` the inner
part of the configuration of ring `j` is supported in `\bar B_{a/8}` and its outer part avoids
`B_6`. -/
theorem nesting (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    (hs : P.sbar ^ (3 - 2) ≤ 1 / 2) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ P.n) {t : ℝ} (ht : 0 ≤ t)
    (hS : ∀ j ∈ Finset.Icc 1 k, P.PertDefined j t)
    (hD : P.D (k + 1) t ⊆ closedBall 0 (a * P.r k / 8)) :
    ∀ j ∈ Finset.Icc 1 k,
      P.D (j + 1) t ⊆ closedBall 0 (a * P.r j / 8) ∧
      (∀ i ∈ Finset.Ico 1 j, P.St i t ⊆ (ball (0 : ℂ) (8 * P.r j))ᶜ) ∧
      tsupport (P.om t) \ P.St j t ⊆
        closedBall 0 (a * P.r j / 8) ∪ (ball (0 : ℂ) (8 * P.r j))ᶜ ∧
      tsupport ((P.ringConfig j).innerPart (P.A j * t)) ⊆ closedBall 0 (a / 8) ∧
      tsupport ((P.ringConfig j).outerPart (P.A j * t)) ∩ ball 0 6 = ∅ := by
  intro j hj
  obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hj
  have ha : 0 < a := Real.exp_pos _
  have hrj := hP.r_pos j
  have harj : 0 < a * P.r j := mul_pos ha hrj
  -- (a): `D_{j+1}(t) ⊂ \bar B_{a r_j/8}`
  have hA : P.D (j + 1) t ⊆ closedBall 0 (a * P.r j / 8) := by
    intro x hx
    obtain ⟨i, ⟨hi1, hin⟩, hxi⟩ := mem_D.mp hx
    rw [mem_closedBall_zero_iff]
    by_cases hik : i ≤ k
    · have hNi := norm_of_mem_Nk P hP (hS i (Finset.mem_Icc.mpr ⟨by omega, hik⟩) hxi)
      have hr := (r_lt_bounds P hP hs hj1 (by omega : j < i)).1
      linarith [hNi.2]
    · have hxD : x ∈ P.D (k + 1) t := mem_D.mpr ⟨i, ⟨by omega, hin⟩, hxi⟩
      have hxk := hD hxD
      rw [mem_closedBall_zero_iff] at hxk
      have hrkj : P.r k ≤ P.r j := by
        rcases eq_or_lt_of_le hjk with h | h
        · rw [h]
        · exact (r_lt_bounds P hP hs hj1 h).2
      calc ‖x‖ ≤ a * P.r k / 8 := hxk
        _ ≤ a * P.r j / 8 := by gcongr
  -- (b): `S_i(t) ⊂ ℝ² ∖ B_{8 r_j}` for `i < j`
  have hB : ∀ i ∈ Finset.Ico 1 j, P.St i t ⊆ (ball (0 : ℂ) (8 * P.r j))ᶜ := by
    intro i hi x hx
    obtain ⟨hi1, hij⟩ := Finset.mem_Ico.mp hi
    have hNi := norm_of_mem_Nk P hP (hS i (Finset.mem_Icc.mpr ⟨hi1, by omega⟩) hx)
    have hr := (r_lt_bounds P hP hs hi1 hij).1
    have hari : 0 < a * P.r i := mul_pos ha (hP.r_pos i)
    rw [mem_compl_iff, mem_ball_zero_iff, not_lt]
    linarith [hNi.1]
  -- the vorticity outside ring `j`
  have hC : tsupport (P.om t) \ P.St j t ⊆
      closedBall 0 (a * P.r j / 8) ∪ (ball (0 : ℂ) (8 * P.r j))ᶜ := by
    rintro x ⟨hx, hxj⟩
    have h2 := (P.regions_basic_two hP hN ht).2.2.2.2.1 hx
    simp only [mem_iUnion, Finset.mem_Icc, exists_prop] at h2
    obtain ⟨i, ⟨hi1, hin⟩, hxi⟩ := h2
    rcases lt_trichotomy i j with h | h | h
    · exact Or.inr (hB i (Finset.mem_Ico.mpr ⟨hi1, h⟩) hxi)
    · exact absurd (h ▸ hxi) hxj
    · exact Or.inl (hA (mem_D.mpr ⟨i, ⟨by omega, hin⟩, hxi⟩))
  -- ring-`j` units
  obtain ⟨-, -, -, -, hin, hout, -⟩ := P.ringConfig_units hP hN hj1 (hjk.trans hkn)
  have hτ : 0 ≤ P.A j * t := mul_nonneg (hP.A_pos j).le ht
  have hτt : P.A j * t / P.A j = t := mul_div_cancel_left₀ t (hP.A_pos j).ne'
  have hnorm : ∀ y : ℂ, ‖((P.r j : ℝ) : ℂ) * y‖ = P.r j * ‖y‖ := fun y => by
    rw [norm_mul, Complex.norm_of_nonneg hrj.le]
  -- the inner part: `supp ν^in_j ⊂ \bar B_{a/8}`
  have hI : tsupport (P.nuIn j t) ⊆ closedBall 0 (a / 8) := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    rw [Function.mem_support] at hy
    simp only [Approx.nuIn, Approx.unitsVort, scaleVort, Approx.omegaGe] at hy
    have hmem : ((P.r j : ℝ) : ℂ) * y ∈ P.D (j + 1) t := by
      by_contra hc
      exact hy (by rw [Set.indicator_of_notMem hc, mul_zero])
    have hy' := hA hmem
    rw [mem_closedBall_zero_iff, hnorm] at hy'
    rw [mem_closedBall_zero_iff]
    have h' : P.r j * ‖y‖ ≤ P.r j * (a / 8) := by linarith
    exact le_of_mul_le_mul_left h' hrj
  -- the outer part: `supp ν^out_j ⊂ ℝ² ∖ B_8`
  have hO : tsupport (P.nuOut j t) ⊆ (ball (0 : ℂ) 8)ᶜ := by
    refine closure_minimal (fun y hy => ?_) isOpen_ball.isClosed_compl
    rw [Function.mem_support] at hy
    simp only [Approx.nuOut, Approx.unitsVort, scaleVort, Approx.omegaOut] at hy
    have hmem : ((P.r j : ℝ) : ℂ) * y ∈ ⋃ i ∈ Finset.Ico 1 j, P.St i t := by
      by_contra hc
      exact hy (by rw [Set.indicator_of_notMem hc, mul_zero])
    simp only [mem_iUnion, exists_prop] at hmem
    obtain ⟨i, hi, hyi⟩ := hmem
    have hy' := hB i hi hyi
    rw [mem_compl_iff, mem_ball_zero_iff, not_lt, hnorm] at hy'
    rw [mem_compl_iff, mem_ball_zero_iff, not_lt]
    have h' : P.r j * 8 ≤ P.r j * ‖y‖ := by linarith
    exact le_of_mul_le_mul_left h' hrj
  refine ⟨hA, hB, hC, ?_, ?_⟩
  · rw [hin _ hτ, hτt]
    exact hI
  · rw [hout _ hτ, hτt, eq_empty_iff_forall_notMem]
    rintro y ⟨hy1, hy2⟩
    have hy8 := hO hy1
    rw [mem_compl_iff, mem_ball_zero_iff] at hy8
    rw [mem_ball_zero_iff] at hy2
    exact hy8 (by linarith)

end Rings

end NonUniqueEuler
