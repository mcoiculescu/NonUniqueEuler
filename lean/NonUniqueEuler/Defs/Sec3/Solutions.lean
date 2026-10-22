import NonUniqueEuler.Statement.WeakSolution
import Mathlib.Order.Filter.Basic

/-!
# Section 3: solutions on `[0, T₀)` and continuity into `L^p` on a time set

Manuscript sources: `02_prelim.tex:540-542` (a (renormalized) weak solution on `[0, T₀)`,
`T₀ ∈ (0, ∞]`: its restriction to `[0, T)` is a (renormalized) weak solution in `X_q(T)` for
every `T < T₀`), used in `def:adm` (`03_compactness.tex:878-886`), `lem:bounded-adm`,
`thm:criterion`, `prop:equiv`, `prop:defect`; `C([0, T); L^q)` in `lem:renorm-all-t` and
`C([0, T₀); L^q)` in `thm:criterion`(iii).

* The end time `T₀ ∈ (0, ∞]` is an extended nonnegative real `T₀ : ℝ≥0∞` (`⊤` is `∞`); a real
  time `T` satisfies `T < T₀` iff `ENNReal.ofReal T < T₀` (for `T > 0`).
* `timeInterval T₀ = [0, T₀) ⊆ ℝ`; `timeInterval ⊤ = Ici 0`,
  `timeInterval (ENNReal.ofReal T) = Ico 0 T`.
* `IsWeakSolutionUpTo q T₀ ωin ω`, `IsRenormalizedWeakSolutionUpTo q T₀ ωin ω`: (renormalized)
  weak solutions on `[0, T₀)`, **datum before solution** as in the statement layer. For
  `T₀ = ⊤` the renormalized notion is the statement layer's
  `IsRenormalizedWeakSolutionOnHalfLine` (`isRenormalizedWeakSolutionUpTo_top_iff`).
* `ContinuousIntoLpOn p s ω`: `ω(t) ∈ L^p` for `t ∈ s` and `t ↦ ω(t)` is continuous on `s` for the
  `L^p` distance; `ContinuousIntoLp p ω` (statement layer, `C([0,∞); L^p)`) is the case
  `s = Ici 0` (`continuousIntoLp_iff_continuousIntoLpOn`).

All lemmas in this file are fully proved.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Weak

/-- The time interval `[0, T₀)`, `T₀ ∈ (0, ∞]` (`02_prelim.tex:540`). -/
def timeInterval (T₀ : ℝ≥0∞) : Set ℝ :=
  {t | 0 ≤ t ∧ ENNReal.ofReal t < T₀}

theorem mem_timeInterval {T₀ : ℝ≥0∞} {t : ℝ} :
    t ∈ timeInterval T₀ ↔ 0 ≤ t ∧ ENNReal.ofReal t < T₀ :=
  Iff.rfl

@[simp] theorem timeInterval_top : timeInterval ⊤ = Ici 0 := by
  ext t
  simp [timeInterval, ENNReal.ofReal_lt_top]

theorem timeInterval_ofReal (T : ℝ) : timeInterval (ENNReal.ofReal T) = Ico 0 T := by
  ext t
  simp only [timeInterval, mem_ofPred_eq, mem_Ico]
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨h0, (ENNReal.ofReal_lt_ofReal_iff'.1 h).1⟩
  · rintro ⟨h0, h⟩
    exact ⟨h0, ENNReal.ofReal_lt_ofReal_iff'.2 ⟨h, h0.trans_lt h⟩⟩

theorem zero_mem_timeInterval {T₀ : ℝ≥0∞} (h : 0 < T₀) : (0 : ℝ) ∈ timeInterval T₀ :=
  ⟨le_rfl, by simpa using h⟩

theorem timeInterval_subset_Ici (T₀ : ℝ≥0∞) : timeInterval T₀ ⊆ Ici 0 :=
  fun _ ht => ht.1

/-- `[0, T] ⊆ [0, T₀)` for `T < T₀`. -/
theorem Icc_subset_timeInterval {T₀ : ℝ≥0∞} {T : ℝ} (hT : ENNReal.ofReal T < T₀) :
    Icc 0 T ⊆ timeInterval T₀ :=
  fun _ ht => ⟨ht.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) hT⟩

/-- A weak solution on `[0, T₀)` with exponent `q` (`def:weak`, `02_prelim.tex:540-542`): a weak
solution in `X_q(T)` with datum `ωin` for every `T ∈ (0, T₀)`. -/
def IsWeakSolutionUpTo (q : ℝ) (T₀ : ℝ≥0∞) (ωin : ℂ → ℝ) (ω : ℝ → ℂ → ℝ) : Prop :=
  ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ → IsWeakSolution q T ωin ω

/-- A renormalized weak solution on `[0, T₀)` with exponent `q` (`def:weak`,
`02_prelim.tex:540-542`): a renormalized weak solution in `X_q(T)` with datum `ωin` for every
`T ∈ (0, T₀)`. -/
def IsRenormalizedWeakSolutionUpTo (q : ℝ) (T₀ : ℝ≥0∞) (ωin : ℂ → ℝ) (ω : ℝ → ℂ → ℝ) :
    Prop :=
  ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ → IsRenormalizedWeakSolution q T ωin ω

theorem IsRenormalizedWeakSolutionUpTo.isWeakSolutionUpTo {q : ℝ} {T₀ : ℝ≥0∞}
    {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ} (h : IsRenormalizedWeakSolutionUpTo q T₀ ωin ω) :
    IsWeakSolutionUpTo q T₀ ωin ω :=
  fun T hT hTT₀ => (h T hT hTT₀).toIsWeakSolution

/-- For `T₀ = ∞` this is the statement layer's notion on `[0, ∞)`. -/
theorem isRenormalizedWeakSolutionUpTo_top_iff {q : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ} :
    IsRenormalizedWeakSolutionUpTo q ⊤ ωin ω ↔ IsRenormalizedWeakSolutionOnHalfLine q ωin ω :=
  ⟨fun h T hT => h T hT ENNReal.ofReal_lt_top, fun h T hT _ => h T hT⟩

/-- `ω ∈ C(s; L^p(ℝ²))`: `ω(t) ∈ L^p` for every `t ∈ s`, and `t ↦ ω(t)` is continuous on `s`
for the `L^p` distance (`03_compactness.tex:586`, `:952`). -/
def ContinuousIntoLpOn (p : ℝ≥0∞) (s : Set ℝ) (ω : ℝ → ℂ → ℝ) : Prop :=
  (∀ t ∈ s, MemLp (ω t) p volume) ∧
    ∀ t₀ ∈ s, Tendsto (fun t => eLpNorm (ω t - ω t₀) p volume) (𝓝[s] t₀) (𝓝 0)

theorem continuousIntoLp_iff_continuousIntoLpOn {p : ℝ≥0∞} {ω : ℝ → ℂ → ℝ} :
    ContinuousIntoLp p ω ↔ ContinuousIntoLpOn p (Ici 0) ω :=
  Iff.rfl

theorem ContinuousIntoLpOn.mono {p : ℝ≥0∞} {s s' : Set ℝ} {ω : ℝ → ℂ → ℝ}
    (h : ContinuousIntoLpOn p s ω) (hs : s' ⊆ s) : ContinuousIntoLpOn p s' ω :=
  ⟨fun t ht => h.1 t (hs ht), fun t ht => (h.2 t (hs ht)).mono_left (nhdsWithin_mono t hs)⟩

end NonUniqueEuler.Weak
