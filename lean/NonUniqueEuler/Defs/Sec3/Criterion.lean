import NonUniqueEuler.Defs.Sec3.Paths
import NonUniqueEuler.Defs.Sec3.Solutions
import NonUniqueEuler.Defs.Infra.Polar
import NonUniqueEuler.Statement.MainTheorem

/-!
# Part I Section 3: admissible sequences, the defect, and the non-uniqueness criterion

Current manuscript: Part I Definition 3.7 (`def:adm`), Theorem 3.8 (`thm:criterion`,
Equation (11), `eq:defect`) and Corollary 3.9 (`cor:defect`). The Lean auxiliary results
formerly called `lem:bounded-adm` and `prop:equiv` are retained legacy decompositions.

* `IsAdmissibleSeq q T₀ f fs ωs`: `(f⁽ⁿ⁾, ω⁽ⁿ⁾)` is a `q`-admissible sequence for `f` on
  `[0, T₀)`, generalizing current Part I Definition 3.7 (`def:adm`), which has
  `q = 2` and `T₀ = ∞`. Indexing: `n : ℕ` starts at `0` (the manuscript starts at `1`; Part II Definition 3.3 (`def:approx`)
  uses approximants of depth `n ≥ 2`).
  **Convention.** `thm:criterion`, legacy `prop:equiv`, Part I Corollary 3.9 (`cor:defect`; formerly `prop:defect`) evaluate `ω⁽ⁿ⁾(t)` at every time
  (`sup_t`, `ω⁽ⁿ⁾(T⁽ⁿ⁾)`), through the identification of a weak solution with its weakly
  continuous representative (Part I §3.2 (`sec:weak-rep`)). In Lean this is the separate
  hypothesis `∀ n, Weak.IsWeakContL2On (Weak.timeInterval T₀) (ωs n)`; `def:adm` itself does not
  contain it.
* `defectLp p T ωs f = limsup_n sup_{t ∈ [0,T]} ‖ω⁽ⁿ⁾(t) - f‖_{L^p} ∈ [0, ∞]`; eq:defect is
  `c = defectLp 1 T ωs f`, `0 < c`; legacy `prop:equiv`(b) uses `p = q ∈ (1, 2]`.
* `defectPairing T ωs f ψ = limsup_n sup_{t ∈ [0,T]} |∫ (ω⁽ⁿ⁾(t) - f) ψ| ∈ [0, ∞]`
  (legacy `prop:equiv`(d)).
* `TendstoUnifLqUpTo T₀ ωs ω`: `sup_{0 ≤ t ≤ T'} ‖ωₙ(t) - ω(t)‖_{L^q} → 0` for every `T' < T₀` and
  `q ∈ [1, 2]` (the Lean strengthening of Part I Theorem 3.8(iv), `thm:criterion`).
* `departureSet T₀ ω f = 𝒪 = {t ∈ [0, T₀) : ω(t) ≠ f}` and `departureTime T₀ ω f = inf 𝒪`
  (`thm:criterion`(v)); "`ω(t) ≠ f`" is inequality in `L¹ ∩ L²`, i.e. `¬ (ω t =ᵐ f)`.
* `IsSymmetricUnder Q ι g`: `g ∘ Q = ι g` a.e. for a linear isometry `Q` of `ℝ² = ℂ`
  (generalizing the three-fold symmetry in Part I Theorem 3.8(vi), `thm:criterion`); `isMFoldSymmetric_iff_isSymmetricUnder` relates it to the statement
  layer's `IsMFoldSymmetric` (`Q` = rotation by `2π/m`, `ι = 1`).
* `IsRadialTestProfile χ`: `χ ∈ C_c^∞((0, ∞))` real; `defectTest χ m x = χ(|x|) x̄^m`, the test
  function `Ψ` of Part I Corollary 3.9 (`cor:defect`; formerly `prop:defect`) (statement and proof, complex valued).

All lemmas in this file are fully proved.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact

open Weak

/-- A `q`-admissible sequence for `f` on `[0, T₀)` (the Lean generalization of Part I Definition 3.7, `def:adm`; the manuscript fixes `q = 2`, `T₀ = ∞`):
`4/3 < q < ∞` (`q` real), `T₀ ∈ (0, ∞]`, `f ∈ L¹ ∩ L^q`, `f⁽ⁿ⁾ ∈ L¹ ∩ L^q`, `f⁽ⁿ⁾ → f` in
`L¹ ∩ L^q`, and `ω⁽ⁿ⁾` is a renormalized weak solution on `[0, T₀)` with datum `f⁽ⁿ⁾`, exponent
`q`. -/
structure IsAdmissibleSeq (q : ℝ) (T₀ : ℝ≥0∞) (f : ℂ → ℝ) (fs : ℕ → ℂ → ℝ)
    (ωs : ℕ → ℝ → ℂ → ℝ) : Prop where
  q_gt : 4 / 3 < q
  T₀_pos : 0 < T₀
  memLp_one : MemLp f 1 volume
  memLp_q : MemLp f (ENNReal.ofReal q) volume
  memLp_one_seq : ∀ n, MemLp (fs n) 1 volume
  memLp_q_seq : ∀ n, MemLp (fs n) (ENNReal.ofReal q) volume
  /-- `f⁽ⁿ⁾ → f` in `L¹ ∩ L^q`. -/
  tendsto : Tendsto (fun n => normL1LpE (ENNReal.ofReal q) (fs n - f)) atTop (𝓝 0)
  /-- `ω⁽ⁿ⁾` is a renormalized weak solution on `[0, T₀)` with datum `f⁽ⁿ⁾`. -/
  renormalized : ∀ n, IsRenormalizedWeakSolutionUpTo q T₀ (fs n) (ωs n)

theorem IsAdmissibleSeq.subseq {q : ℝ} {T₀ : ℝ≥0∞} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ}
    {ωs : ℕ → ℝ → ℂ → ℝ} (h : IsAdmissibleSeq q T₀ f fs ωs) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    IsAdmissibleSeq q T₀ f (fun n => fs (φ n)) (fun n => ωs (φ n)) where
  q_gt := h.q_gt
  T₀_pos := h.T₀_pos
  memLp_one := h.memLp_one
  memLp_q := h.memLp_q
  memLp_one_seq n := h.memLp_one_seq (φ n)
  memLp_q_seq n := h.memLp_q_seq (φ n)
  tendsto := h.tendsto.comp hφ.tendsto_atTop
  renormalized n := h.renormalized (φ n)

/-- `limsup_n sup_{0 ≤ t ≤ T} ‖ω⁽ⁿ⁾(t) - f‖_{L^p}` (eq:defect with `p = 1`,
Part I Theorem 3.8 (`thm:criterion`) and its proof; legacy `prop:equiv`(a), (b)). -/
def defectLp (p : ℝ≥0∞) (T : ℝ) (ωs : ℕ → ℝ → ℂ → ℝ) (f : ℂ → ℝ) : ℝ≥0∞ :=
  limsup (fun n => supDist p (Icc 0 T) (ωs n) (stationary f)) atTop

/-- `limsup_n sup_{0 ≤ t ≤ T} |∫ (ω⁽ⁿ⁾(t) - f) ψ|` (legacy `prop:equiv`(d), legacy implication; current criterion and moment arguments cited above). -/
def defectPairing (T : ℝ) (ωs : ℕ → ℝ → ℂ → ℝ) (f : ℂ → ℝ) (ψ : ℂ → ℝ) : ℝ≥0∞ :=
  limsup (fun n => ⨆ t ∈ Icc 0 T, ‖∫ x, (ωs n t x - f x) * ψ x‖ₑ) atTop

/-- `sup_{0 ≤ t ≤ T'} ‖ωₙ(t) - ω(t)‖_{L^q} → 0` for every `T' < T₀` and every `q ∈ [1, 2]`
(the Lean strengthening of Part I Theorem 3.8(iv), `thm:criterion`; legacy `prop:equiv`(e)). -/
def TendstoUnifLqUpTo (T₀ : ℝ≥0∞) (ωs : ℕ → ℝ → ℂ → ℝ) (ω : ℝ → ℂ → ℝ) : Prop :=
  ∀ T' : ℝ, ENNReal.ofReal T' < T₀ → ∀ q : ℝ, 1 ≤ q → q ≤ 2 →
    Tendsto (fun n => supDist (ENNReal.ofReal q) (Icc 0 T') (ωs n) ω) atTop (𝓝 0)

/-- The set `𝒪 = {t ∈ [0, T₀) : ω(t) ≠ f}` of `thm:criterion`(v) (Part I Theorem 3.8 (`thm:criterion`) and its proof). -/
def departureSet (T₀ : ℝ≥0∞) (ω : ℝ → ℂ → ℝ) (f : ℂ → ℝ) : Set ℝ :=
  {t | t ∈ timeInterval T₀ ∧ ¬ (ω t =ᵐ[volume] f)}

/-- `t₀ = inf 𝒪` (`thm:criterion`(v), Part I Theorem 3.8 (`thm:criterion`) and its proof). (`sInf ∅ = 0` in `ℝ`; the
criterion proves `𝒪 ∩ (0, T] ≠ ∅`.) -/
def departureTime (T₀ : ℝ≥0∞) (ω : ℝ → ℂ → ℝ) (f : ℂ → ℝ) : ℝ :=
  sInf (departureSet T₀ ω f)

theorem departureSet_subset (T₀ : ℝ≥0∞) (ω : ℝ → ℂ → ℝ) (f : ℂ → ℝ) :
    departureSet T₀ ω f ⊆ timeInterval T₀ :=
  fun _ ht => ht.1

theorem departureTime_nonneg (T₀ : ℝ≥0∞) (ω : ℝ → ℂ → ℝ) (f : ℂ → ℝ) :
    0 ≤ departureTime T₀ ω f :=
  Real.sInf_nonneg fun _ ht => ht.1.1

theorem departureTime_le {T₀ : ℝ≥0∞} {ω : ℝ → ℂ → ℝ} {f : ℂ → ℝ} {t : ℝ}
    (ht : t ∈ departureSet T₀ ω f) : departureTime T₀ ω f ≤ t :=
  csInf_le ⟨0, fun _ hs => hs.1.1⟩ ht

/-- The stationary function `ω(t) = f`, `f ∈ L²`, is weakly continuous into `L²`
(`lem:radial-stationary`, Part I Lemma 3.6 (`lem:radial-stationary`)). -/
theorem isWeakContL2On_stationary {f : ℂ → ℝ} (hf : MemLp f 2 volume) (s : Set ℝ) :
    IsWeakContL2On s (stationary f) :=
  ⟨fun _ _ => hf, fun ψ _ => by
    show ContinuousOn (fun _ => ∫ x, f x * ψ x) s
    exact continuousOn_const⟩

/-- The distance of the stationary function to itself vanishes. -/
theorem supDist_stationary_self (p : ℝ≥0∞) (s : Set ℝ) (f : ℂ → ℝ) :
    supDist p s (stationary f) (stationary f) = 0 := by
  simp [supDist]

/-- `g ∘ Q = ι g` almost everywhere, for a linear isometry `Q` of `ℝ² = ℂ` and a sign `ι`
(`thm:criterion`(vi), Part I Theorem 3.8 (`thm:criterion`) and its proof). -/
def IsSymmetricUnder (Q : ℂ ≃ₗᵢ[ℝ] ℂ) (ι : ℝ) (g : ℂ → ℝ) : Prop :=
  (fun x => g (Q x)) =ᵐ[volume] fun x => ι * g x

/-- `m`-fold symmetry is symmetry under the rotation by `2π/m` with `ι = 1`
(Part I Corollary 3.9 (`cor:defect`) and its proof: `Q = O_{2π/3}`). -/
theorem isMFoldSymmetric_iff_isSymmetricUnder (m : ℕ) (g : ℂ → ℝ) :
    IsMFoldSymmetric m g ↔
      IsSymmetricUnder (rotation (Circle.exp (2 * Real.pi / m))) 1 g := by
  simp only [IsMFoldSymmetric, IsSymmetricUnder, one_mul, Polar.rot_eq_rotation]

/-- `χ ∈ C_c^∞((0, ∞))`, real valued (Part I Corollary 3.9 (`cor:defect`; formerly `prop:defect`), Part I Corollary 3.9 (`cor:defect`) and its proof). -/
structure IsRadialTestProfile (χ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ
  hasCompactSupport : HasCompactSupport χ
  tsupport_subset : tsupport χ ⊆ Ioi 0

/-- The test function `Ψ(x) = χ(|x|) x̄^m` of Part I Corollary 3.9 (`cor:defect`; formerly `prop:defect`) (statement and proof),
`x` written as a complex number. -/
def defectTest (χ : ℝ → ℝ) (m : ℕ) (x : ℂ) : ℂ :=
  (χ ‖x‖ : ℂ) * (starRingEnd ℂ x) ^ m

end NonUniqueEuler.Compact
