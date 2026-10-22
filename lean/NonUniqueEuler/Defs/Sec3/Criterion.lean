import NonUniqueEuler.Defs.Sec3.Paths
import NonUniqueEuler.Defs.Sec3.Solutions
import NonUniqueEuler.Defs.Infra.Polar
import NonUniqueEuler.Statement.MainTheorem

/-!
# Section 3: admissible sequences, the defect, and the non-uniqueness criterion

Manuscript sources: `def:adm` (`03_compactness.tex:878-886`), `lem:bounded-adm`
(`03_compactness.tex:888-904`), `thm:criterion` with eq:defect (`03_compactness.tex:933-968`),
`prop:equiv` (`03_compactness.tex:1079-1097`), `prop:defect` (`03_compactness.tex:1134-1153`).

* `IsAdmissibleSeq q T₀ f fs ωs`: `(f⁽ⁿ⁾, ω⁽ⁿ⁾)` is a `q`-admissible sequence for `f` on
  `[0, T₀)` (`def:adm`). Indexing: `n : ℕ` starts at `0` (the manuscript starts at `1`; Section 11
  starts at `2` and shifts, `06_datum.tex:89-91`).
  **Convention.** `thm:criterion`, `prop:equiv`, `prop:defect` evaluate `ω⁽ⁿ⁾(t)` at every time
  (`sup_t`, `ω⁽ⁿ⁾(T⁽ⁿ⁾)`), through the identification of a weak solution with its weakly
  continuous representative (`03_compactness.tex:238-247`). In Lean this is the separate
  hypothesis `∀ n, Weak.IsWeakContL2On (Weak.timeInterval T₀) (ωs n)`; `def:adm` itself does not
  contain it.
* `defectLp p T ωs f = limsup_n sup_{t ∈ [0,T]} ‖ω⁽ⁿ⁾(t) - f‖_{L^p} ∈ [0, ∞]`; eq:defect is
  `c = defectLp 1 T ωs f`, `0 < c`; `prop:equiv`(b) uses `p = q ∈ (1, 2]`.
* `defectPairing T ωs f ψ = limsup_n sup_{t ∈ [0,T]} |∫ (ω⁽ⁿ⁾(t) - f) ψ| ∈ [0, ∞]`
  (`prop:equiv`(d)).
* `TendstoUnifLqUpTo T₀ ωs ω`: `sup_{0 ≤ t ≤ T'} ‖ωₙ(t) - ω(t)‖_{L^q} → 0` for every `T' < T₀` and
  `q ∈ [1, 2]` (`thm:criterion`(iv)).
* `departureSet T₀ ω f = 𝒪 = {t ∈ [0, T₀) : ω(t) ≠ f}` and `departureTime T₀ ω f = inf 𝒪`
  (`thm:criterion`(v)); "`ω(t) ≠ f`" is inequality in `L¹ ∩ L²`, i.e. `¬ (ω t =ᵐ f)`.
* `IsSymmetricUnder Q ι g`: `g ∘ Q = ι g` a.e. for a linear isometry `Q` of `ℝ² = ℂ`
  (`thm:criterion`(vi)); `isMFoldSymmetric_iff_isSymmetricUnder` relates it to the statement
  layer's `IsMFoldSymmetric` (`Q` = rotation by `2π/m`, `ι = 1`).
* `IsRadialTestProfile χ`: `χ ∈ C_c^∞((0, ∞))` real; `defectTest χ m x = χ(|x|) x̄^m`, the test
  function `Ψ` of `prop:defect` (`03_compactness.tex:1137-1138`, complex valued).

All lemmas in this file are fully proved.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact

open Weak

/-- A `q`-admissible sequence for `f` on `[0, T₀)` (`def:adm`, `03_compactness.tex:878-886`):
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
`03_compactness.tex:937-941`; `prop:equiv`(a), (b)). -/
def defectLp (p : ℝ≥0∞) (T : ℝ) (ωs : ℕ → ℝ → ℂ → ℝ) (f : ℂ → ℝ) : ℝ≥0∞ :=
  limsup (fun n => supDist p (Icc 0 T) (ωs n) (stationary f)) atTop

/-- `limsup_n sup_{0 ≤ t ≤ T} |∫ (ω⁽ⁿ⁾(t) - f) ψ|` (`prop:equiv`(d), `03_compactness.tex:1090-1091`). -/
def defectPairing (T : ℝ) (ωs : ℕ → ℝ → ℂ → ℝ) (f : ℂ → ℝ) (ψ : ℂ → ℝ) : ℝ≥0∞ :=
  limsup (fun n => ⨆ t ∈ Icc 0 T, ‖∫ x, (ωs n t x - f x) * ψ x‖ₑ) atTop

/-- `sup_{0 ≤ t ≤ T'} ‖ωₙ(t) - ω(t)‖_{L^q} → 0` for every `T' < T₀` and every `q ∈ [1, 2]`
(`thm:criterion`(iv), `03_compactness.tex:954-955`; `prop:equiv`(e)). -/
def TendstoUnifLqUpTo (T₀ : ℝ≥0∞) (ωs : ℕ → ℝ → ℂ → ℝ) (ω : ℝ → ℂ → ℝ) : Prop :=
  ∀ T' : ℝ, ENNReal.ofReal T' < T₀ → ∀ q : ℝ, 1 ≤ q → q ≤ 2 →
    Tendsto (fun n => supDist (ENNReal.ofReal q) (Icc 0 T') (ωs n) ω) atTop (𝓝 0)

/-- The set `𝒪 = {t ∈ [0, T₀) : ω(t) ≠ f}` of `thm:criterion`(v) (`03_compactness.tex:956-957`). -/
def departureSet (T₀ : ℝ≥0∞) (ω : ℝ → ℂ → ℝ) (f : ℂ → ℝ) : Set ℝ :=
  {t | t ∈ timeInterval T₀ ∧ ¬ (ω t =ᵐ[volume] f)}

/-- `t₀ = inf 𝒪` (`thm:criterion`(v), `03_compactness.tex:958-959`). (`sInf ∅ = 0` in `ℝ`; the
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
(`lem:radial-stationary`, `03_compactness.tex:860-862`). -/
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
(`thm:criterion`(vi), `03_compactness.tex:963-966`). -/
def IsSymmetricUnder (Q : ℂ ≃ₗᵢ[ℝ] ℂ) (ι : ℝ) (g : ℂ → ℝ) : Prop :=
  (fun x => g (Q x)) =ᵐ[volume] fun x => ι * g x

/-- `m`-fold symmetry is symmetry under the rotation by `2π/m` with `ι = 1`
(`03_compactness.tex:1174-1176`: `Q = O_{2π/3}`). -/
theorem isMFoldSymmetric_iff_isSymmetricUnder (m : ℕ) (g : ℂ → ℝ) :
    IsMFoldSymmetric m g ↔
      IsSymmetricUnder (rotation (Circle.exp (2 * Real.pi / m))) 1 g := by
  simp only [IsMFoldSymmetric, IsSymmetricUnder, one_mul, Polar.rot_eq_rotation]

/-- `χ ∈ C_c^∞((0, ∞))`, real valued (`prop:defect`, `03_compactness.tex:1137`). -/
structure IsRadialTestProfile (χ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ
  hasCompactSupport : HasCompactSupport χ
  tsupport_subset : tsupport χ ⊆ Ioi 0

/-- The test function `Ψ(x) = χ(|x|) x̄^m` of `prop:defect` (`03_compactness.tex:1137-1138`),
`x` written as a complex number. -/
def defectTest (χ : ℝ → ℝ) (m : ℕ) (x : ℂ) : ℂ :=
  (χ ‖x‖ : ℂ) * (starRingEnd ℂ x) ^ m

end NonUniqueEuler.Compact
