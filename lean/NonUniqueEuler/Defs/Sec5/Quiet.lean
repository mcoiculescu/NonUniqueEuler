import NonUniqueEuler.Defs.Sec5.Constants

/-!
# Section 5.2: a quiet ring — the constants of `thm:quiet` (definitions)

Manuscript `thm:quiet`
(`05_single_ring.tex:408-429`).

The constants `maj_*`, `C_Q`, `C_Δ` of `thm:quiet` are used by value in later definitions
(`09_relay.tex:39-40` (SA2), `:232` `K_O`, `:394` `C_Ξ`, `:609` `C_op`, `:943` `C_hand = K₁ C_Q`).
Following decision D11, the conclusion of the theorem is the Prop `IsQuietConst χ s_h N_Q maj_* C_Q C_Δ`
("these constants work"), and the constants are chosen from the existence statement
(`quietConsts`; the interface theorem `thm:quiet` proves `∃ maj_* C_Q C_Δ, IsQuietConst …` under
(N1)–(N3), `s_h ≥ 3`, `N_Q ≥ 2`, `N_Q σ_b ≥ Λ(s_h)`).

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- **The constants `maj_* ∈ (0,1]`, `C_Q`, `C_Δ` work in `thm:quiet`** for `s_h`, `N_Q`
(`05_single_ring.tex:408-429`): `C_Δ maj_* ≤ a/16`, and for every configuration of
`lem:reduction` on `[0,T]` with `ω_r(0) = Φ` and `G ∈ [0,G₁]`, every measurable `η` with
`‖h(t)‖_{C^{M_h}(N')} ≤ η(t) ≤ 1` on `[0,T]` whose Duhamel majorant satisfies `maj ≤ maj_*` on
`[0,T]`:
(a) `w = ω_r - Φ` solves `eq:ring` on `[0,T]` (`RingConfig.PertEq`), and for `t ∈ [0,T]` every
trajectory of `ω_r` moves radially by at most `C_Δ maj(t)` on `[0,t]` and `supp ω_r(t) ⊂ 𝒩₋`;
(b) `‖w(t) - wlin(t)‖_{H^{s_h}} ≤ C_Q maj(t)²`, with the linear response `wlin` (`OneRing.wlin`);
(c) `‖w(t)‖_{H^{s_h}} ≤ C_Q maj(t)`.
Here `maj = maj σ(G) η` (`def:majorant`). The manuscript says `C_Q, C_Δ < ∞`; they are also
nonnegative (`C_Δ ≥ 1` in the proof), which we include. The `C^{M_h}(N')` norm of `h(t)` is finite
under the hypotheses (`lem:reduction`(1)), so the bound by `η` is not a junk-value bound. -/
def IsQuietConst (χ : ℝ → ℝ) (sh NQ : ℕ) (majst CQ CΔ : ℝ) : Prop :=
  majst ∈ Ioc (0 : ℝ) 1 ∧ 0 ≤ CQ ∧ 0 ≤ CΔ ∧ CΔ * majst ≤ a / 16 ∧
    ∀ (c : RingConfig) (T : ℝ), c.Hyp T → c.ring0 = ringPhi χ → c.G ∈ Icc (0 : ℝ) Gbar →
      ∀ η : ℝ → ℝ, Measurable η →
        (∀ t ∈ Icc (0 : ℝ) T, normCk (Mh sh NQ) annN' (c.h t) ≤ η t ∧ η t ≤ 1) →
        (∀ t ∈ Icc (0 : ℝ) T, maj (Eig.sigma χ c.G) η t ≤ majst) →
        c.PertEq χ T ∧
          ∀ t ∈ Icc (0 : ℝ) T,
            c.MovesRadially t (CΔ * maj (Eig.sigma χ c.G) η t) ∧
              tsupport (c.ringPart t) ⊆ annNm ∧
              Sob.normH sh (c.w χ t - (wlin χ sh c.G c.h t).fn) ≤
                CQ * maj (Eig.sigma χ c.G) η t ^ 2 ∧
              Sob.normH sh (c.w χ t) ≤ CQ * maj (Eig.sigma χ c.G) η t

open Classical in
/-- The constants `(maj_*, C_Q, C_Δ)` of `thm:quiet` for `s_h`, `N_Q` (chosen; junk `(1, 0, 0)`
when none exist). -/
def quietConsts (χ : ℝ → ℝ) (sh NQ : ℕ) : ℝ × ℝ × ℝ :=
  if h : ∃ x : ℝ × ℝ × ℝ, IsQuietConst χ sh NQ x.1 x.2.1 x.2.2 then h.choose else (1, 0, 0)

/-- `maj_*` of `thm:quiet` (`05_single_ring.tex:411-413`). -/
def majst (χ : ℝ → ℝ) (sh NQ : ℕ) : ℝ := (quietConsts χ sh NQ).1

/-- `C_Q` of `thm:quiet` (`05_single_ring.tex:411-413`). -/
def CQ (χ : ℝ → ℝ) (sh NQ : ℕ) : ℝ := (quietConsts χ sh NQ).2.1

/-- `C_Δ` of `thm:quiet` (`05_single_ring.tex:411-413`). -/
def CDelta (χ : ℝ → ℝ) (sh NQ : ℕ) : ℝ := (quietConsts χ sh NQ).2.2

/-! ### Basic lemmas (fully proved) -/

/-- If constants for `thm:quiet` exist, the chosen ones work. -/
theorem quietConsts_spec {χ : ℝ → ℝ} {sh NQ : ℕ}
    (h : ∃ majst CQ CΔ : ℝ, IsQuietConst χ sh NQ majst CQ CΔ) :
    IsQuietConst χ sh NQ (majst χ sh NQ) (CQ χ sh NQ) (CDelta χ sh NQ) := by
  classical
  have h' : ∃ x : ℝ × ℝ × ℝ, IsQuietConst χ sh NQ x.1 x.2.1 x.2.2 := by
    obtain ⟨m, q, d, hq⟩ := h
    exact ⟨(m, q, d), hq⟩
  have hc : quietConsts χ sh NQ = h'.choose := by
    rw [quietConsts, dite_eq_left h']
  rw [majst, CQ, CDelta, hc]
  exact h'.choose_spec

theorem IsQuietConst.majst_mem {χ : ℝ → ℝ} {sh NQ : ℕ} {m q d : ℝ}
    (h : IsQuietConst χ sh NQ m q d) : m ∈ Ioc (0 : ℝ) 1 := h.1

theorem IsQuietConst.CQ_nonneg {χ : ℝ → ℝ} {sh NQ : ℕ} {m q d : ℝ}
    (h : IsQuietConst χ sh NQ m q d) : 0 ≤ q := h.2.1

theorem IsQuietConst.CDelta_nonneg {χ : ℝ → ℝ} {sh NQ : ℕ} {m q d : ℝ}
    (h : IsQuietConst χ sh NQ m q d) : 0 ≤ d := h.2.2.1

theorem IsQuietConst.CDelta_mul_le {χ : ℝ → ℝ} {sh NQ : ℕ} {m q d : ℝ}
    (h : IsQuietConst χ sh NQ m q d) : d * m ≤ a / 16 := h.2.2.2.1

end OneRing

end NonUniqueEuler
