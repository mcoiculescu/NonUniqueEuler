import NonUniqueEuler.Defs.Sec3.Paths

/-!
# Section 3: the setting and the conclusions of `prop:compact`

Manuscript source: `prop:compact` (`03_compactness.tex:251-271`), reused verbatim by
`prop:stable` ("In Proposition compact, assume in addition …", `03_compactness.tex:716-723`) and
by the proof of `thm:criterion` (`03_compactness.tex:969-1077`).

* `IsCompactSeq T M gs g ωs`: the hypotheses of `prop:compact`: `T > 0`; `gₙ, g ∈ L¹ ∩ L²`,
  `gₙ ⇀ g` weakly in `L²`; `ωₙ` weak solutions in `X₂(T)` with data `gₙ`, identified with their
  weakly continuous representatives on `[0, T]` (`IsWeakContL2On`, the convention of
  `03_compactness.tex:238-247`), and `sup_n sup_{t ∈ [0,T]} ‖ωₙ(t)‖_{L¹ ∩ L²} ≤ M`.
* `IsCompactLimit T g ωs ω`: the conclusions of `prop:compact` for the (already extracted)
  sequence `ωs` and the limit `ω`: `ω` is a weak solution in `X₂(T)` with datum `g`, weakly
  continuous on `[0, T]`, and (i) uniform weak convergence on `[0, T]`, (ii) lower
  semicontinuity of `‖·‖_{L^q}`, `q ∈ [1, 2]`, at every `t ∈ [0, T]`, (iii) `K ∗ ωₙ → K ∗ ω`
  in `L^s(0, T; L²(B_R))` for all `s ∈ [1, ∞)`, `R > 0`.

`prop:compact` then reads `IsCompactSeq T M gs g ωs → ∃ φ, StrictMono φ ∧ ∃ ω,
IsCompactLimit T g (fun n => ωs (φ n)) ω`, and `prop:stable` takes `IsCompactSeq` and
`IsCompactLimit` as hypotheses. Both predicates pass to subsequences (`IsCompactSeq.subseq`,
`IsCompactLimit.subseq`).

All lemmas in this file are fully proved.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact

open Weak

/-- The hypotheses of `prop:compact` (`03_compactness.tex:253-260`). -/
structure IsCompactSeq (T M : ℝ) (gs : ℕ → ℂ → ℝ) (g : ℂ → ℝ) (ωs : ℕ → ℝ → ℂ → ℝ) :
    Prop where
  T_pos : 0 < T
  memLp_one : MemLp g 1 volume
  memLp_two : MemLp g 2 volume
  memLp_one_seq : ∀ n, MemLp (gs n) 1 volume
  memLp_two_seq : ∀ n, MemLp (gs n) 2 volume
  /-- `gₙ ⇀ g` weakly in `L²`. -/
  weakTendsto : Prelim.WeakTendstoLp 2 gs g
  /-- `ωₙ` is a weak solution in `X₂(T)` with datum `gₙ`. -/
  weakSolution : ∀ n, IsWeakSolution 2 T (gs n) (ωs n)
  /-- `ωₙ` is its own weakly continuous representative on `[0, T]` (`03_compactness.tex:238-247`). -/
  weakCont : ∀ n, IsWeakContL2On (Icc 0 T) (ωs n)
  /-- `sup_n sup_{t ∈ [0,T]} ‖ωₙ(t)‖_{L¹ ∩ L²} ≤ M`. -/
  bound : ∀ n, ∀ t ∈ Icc 0 T, normL1LpE 2 (ωs n t) ≤ ENNReal.ofReal M

/-- The conclusions of `prop:compact` (`03_compactness.tex:260-271`) for the sequence `ωs` (the
extracted subsequence) and the limit `ω`. -/
structure IsCompactLimit (T : ℝ) (g : ℂ → ℝ) (ωs : ℕ → ℝ → ℂ → ℝ) (ω : ℝ → ℂ → ℝ) : Prop where
  /-- `ω` is a weak solution in `X₂(T)` with datum `g`. -/
  weakSolution : IsWeakSolution 2 T g ω
  /-- `ω` is weakly continuous into `L²` on `[0, T]` (`03_compactness.tex:288-289`, `:337-338`). -/
  weakCont : IsWeakContL2On (Icc 0 T) ω
  /-- (i) `sup_{t ∈ [0,T]} |∫ (ωₙ(t) - ω(t)) ψ| → 0` for every `ψ ∈ L²`. -/
  weakTendstoUnif : WeakTendstoUnifL2On ωs ω (Icc 0 T)
  /-- (ii) `‖ω(t)‖_{L^q} ≤ liminf_n ‖ωₙ(t)‖_{L^q}` for every `t ∈ [0, T]` and `q ∈ [1, 2]`. -/
  eLpNorm_le_liminf : ∀ t ∈ Icc 0 T, ∀ q : ℝ, 1 ≤ q → q ≤ 2 →
    eLpNorm (ω t) (ENNReal.ofReal q) volume ≤
      liminf (fun n => eLpNorm (ωs n t) (ENNReal.ofReal q) volume) atTop
  /-- (iii) `K ∗ ωₙ → K ∗ ω` in `L^s(0, T; L²(B_R))` for every `s ∈ [1, ∞)` and `R > 0`. -/
  velocity_tendsto : ∀ s : ℝ, 1 ≤ s → ∀ R : ℝ, 0 < R →
    Tendsto (fun n => bochnerNorm (ENNReal.ofReal s) 2 (Ioo 0 T) (ball (0 : ℂ) R)
      (fun t x => velocityField (ωs n) t x - velocityField ω t x)) atTop (𝓝 0)

/-! ### Subsequences (fully proved) -/

theorem _root_.NonUniqueEuler.Prelim.WeakTendstoLp.subseq {p : ℝ} {gs : ℕ → ℂ → ℝ}
    {g : ℂ → ℝ} (h : Prelim.WeakTendstoLp p gs g) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Prelim.WeakTendstoLp p (fun n => gs (φ n)) g :=
  ⟨fun n => h.1 (φ n), h.2.1, fun ψ hψ => (h.2.2 ψ hψ).comp hφ.tendsto_atTop⟩

theorem IsCompactSeq.subseq {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}
    (h : IsCompactSeq T M gs g ωs) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    IsCompactSeq T M (fun n => gs (φ n)) g (fun n => ωs (φ n)) where
  T_pos := h.T_pos
  memLp_one := h.memLp_one
  memLp_two := h.memLp_two
  memLp_one_seq n := h.memLp_one_seq (φ n)
  memLp_two_seq n := h.memLp_two_seq (φ n)
  weakTendsto := h.weakTendsto.subseq hφ
  weakSolution n := h.weakSolution (φ n)
  weakCont n := h.weakCont (φ n)
  bound n := h.bound (φ n)

theorem IsCompactLimit.subseq {T : ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsCompactLimit T g ωs ω) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    IsCompactLimit T g (fun n => ωs (φ n)) ω where
  weakSolution := h.weakSolution
  weakCont := h.weakCont
  weakTendstoUnif := h.weakTendstoUnif.subseq hφ
  eLpNorm_le_liminf t ht q hq1 hq2 :=
    (h.eLpNorm_le_liminf t ht q hq1 hq2).trans
      (hφ.tendsto_atTop.liminf_le_liminf_comp
        (u := fun n => eLpNorm (ωs n t) (ENNReal.ofReal q) volume))
  velocity_tendsto s hs R hR := (h.velocity_tendsto s hs R hR).comp hφ.tendsto_atTop

end NonUniqueEuler.Compact
