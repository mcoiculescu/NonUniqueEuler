import NonUniqueEuler.Defs.Infra.WeakL2
import NonUniqueEuler.Defs.Infra.JointRep
import NonUniqueEuler.Defs.Sec2.Spaces
import NonUniqueEuler.Defs.Sec2.Conventions

/-!
# Section 3: weakly continuous representatives, norms of paths, distances

Manuscript sources: `lem:weak-cont` (`03_compactness.tex:120-145`) and the convention after it
(`03_compactness.tex:236-247`): "every weak solution is identified with its weakly continuous
representative, so that `ω(t)` is defined for every `t`"; `prop:compact`(i)–(iii)
(`03_compactness.tex:251-271`); `thm:criterion`(iv),(v), eq:defect (`03_compactness.tex:933-968`).

Representation (R5, D9). A space–time function stays a function `ω : ℝ → ℂ → ℝ` (as in the
statement layer); the manuscript's identification with the weakly continuous representative is
the *hypothesis* `IsWeakContL2On s ω`: every slice `ω t`, `t ∈ s`, is in `L²`, and
`t ↦ ∫ ω(t) ψ` is continuous on `s` for every `ψ ∈ L²` (exponent `b = 2` only, D9). Every
weak solution in `X₂(T)` has such a representative (`lem:weak-cont`), unique for every `t`
(two weakly continuous paths that agree for a.e. `t` agree for every `t`), so stating the
results of Section 3 for functions with this property is the manuscript's convention made
explicit. `isWeakContL2On_iff_toPath` is the bridge to the Hilbert-space form
`WeakL2.WeakContinuousOn` of the path of `L²` classes `JointRep.toPath ω`.

* `WeakTendstoUnifL2On ωs ω s`: `sup_{t ∈ s} |∫ (ωₙ(t) - ω(t)) ψ| → 0` for every `ψ ∈ L²`
  (`prop:compact`(i)).
* `normL1LpE p g = ‖g‖_{L¹} + ‖g‖_{L^p} ∈ [0, ∞]` (the norm of `L¹ ∩ L^p`, `02_prelim.tex:122-124`,
  in `ℝ≥0∞`, so with no junk value; the real version is `Prelim.normL1Lp`).
* `supDist p s ω₁ ω₂ = sup_{t ∈ s} ‖ω₁(t) - ω₂(t)‖_{L^p} ∈ [0, ∞]` (`thm:criterion`(iv),
  eq:defect with `ω₂ = stationary f`).
* `bochnerNorm s b I Ω u = ‖u‖_{L^s(I; L^b(Ω))} ∈ [0, ∞]` (`prop:compact`(iii)).

All lemmas in this file are fully proved.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace NonUniqueEuler.Weak

/-- `t ↦ ω(t)` is weakly continuous into `L²(ℝ²)` on `s` (`lem:weak-cont`(a) with `b = 2`,
`03_compactness.tex:130-131`, and the convention `03_compactness.tex:238-247`): `ω t ∈ L²` for
every `t ∈ s`, and `t ↦ ∫ ω(t) ψ` is continuous on `s` for every `ψ ∈ L²`. -/
structure IsWeakContL2On (s : Set ℝ) (ω : ℝ → ℂ → ℝ) : Prop where
  memLp : ∀ t ∈ s, MemLp (ω t) 2 volume
  continuousOn : ∀ ψ : ℂ → ℝ, MemLp ψ 2 volume → ContinuousOn (fun t => ∫ x, ω t x * ψ x) s

theorem IsWeakContL2On.mono {s s' : Set ℝ} {ω : ℝ → ℂ → ℝ} (h : IsWeakContL2On s ω)
    (hs : s' ⊆ s) : IsWeakContL2On s' ω :=
  ⟨fun t ht => h.memLp t (hs ht), fun ψ hψ => (h.continuousOn ψ hψ).mono hs⟩

/-- At times where the slice is in `L²`, the inner product of its class with the class of `ψ` is
`∫ ω(t) ψ`. -/
theorem inner_toPath_toLp {ω : ℝ → ℂ → ℝ} {t : ℝ} (ht : MemLp (ω t) 2 volume) {ψ : ℂ → ℝ}
    (hψ : MemLp ψ 2 volume) :
    ⟪(JointRep.toPath (μ := (volume : Measure ℂ)) ω t), hψ.toLp ψ⟫_ℝ = ∫ x, ω t x * ψ x := by
  rw [JointRep.toPath_of_memLp ht]
  exact WeakL2.inner_toLp_toLp ht hψ

/-- Bridge to the Hilbert-space form: `IsWeakContL2On s ω` iff the slices are in `L²` on `s` and
the path of their `L²` classes is weakly continuous on `s` (`WeakL2.WeakContinuousOn`). -/
theorem isWeakContL2On_iff_toPath {s : Set ℝ} {ω : ℝ → ℂ → ℝ} :
    IsWeakContL2On s ω ↔ (∀ t ∈ s, MemLp (ω t) 2 volume) ∧
      WeakL2.WeakContinuousOn (fun t => (JointRep.toPath (μ := (volume : Measure ℂ)) ω t)) s := by
  constructor
  · intro h
    refine ⟨h.memLp, fun y => ?_⟩
    have hy : MemLp (y : ℂ → ℝ) 2 volume := Lp.memLp y
    refine (h.continuousOn y hy).congr fun t ht => ?_
    have hyy : hy.toLp (y : ℂ → ℝ) = y := Lp.toLp_coeFn y hy
    simp only
    rw [← inner_toPath_toLp (h.memLp t ht) hy, hyy]
  · rintro ⟨hm, hc⟩
    refine ⟨hm, fun ψ hψ => ?_⟩
    refine (hc (hψ.toLp ψ)).congr fun t ht => ?_
    simp only
    rw [inner_toPath_toLp (hm t ht) hψ]

/-- Uniform weak convergence in `L²` on a time set `s` (`prop:compact`(i),
`03_compactness.tex:263-264`): for every `ψ ∈ L²`, `sup_{t ∈ s} |∫ (ωₙ(t) - ω(t)) ψ| → 0`. -/
def WeakTendstoUnifL2On (ωs : ℕ → ℝ → ℂ → ℝ) (ω : ℝ → ℂ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ψ : ℂ → ℝ, MemLp ψ 2 volume →
    TendstoUniformlyOn (fun n t => ∫ x, ωs n t x * ψ x) (fun t => ∫ x, ω t x * ψ x) atTop s

theorem WeakTendstoUnifL2On.mono {ωs : ℕ → ℝ → ℂ → ℝ} {ω : ℝ → ℂ → ℝ} {s s' : Set ℝ}
    (h : WeakTendstoUnifL2On ωs ω s) (hs : s' ⊆ s) : WeakTendstoUnifL2On ωs ω s' :=
  fun ψ hψ => (h ψ hψ).mono hs

theorem WeakTendstoUnifL2On.subseq {ωs : ℕ → ℝ → ℂ → ℝ} {ω : ℝ → ℂ → ℝ} {s : Set ℝ}
    (h : WeakTendstoUnifL2On ωs ω s) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    WeakTendstoUnifL2On (fun n => ωs (φ n)) ω s :=
  fun ψ hψ u hu => hφ.tendsto_atTop.eventually (h ψ hψ u hu)

/-- The norm `‖g‖_{L¹ ∩ L^p} = ‖g‖_{L¹} + ‖g‖_{L^p}` (`02_prelim.tex:122-124`) in `[0, ∞]`. -/
def normL1LpE (p : ℝ≥0∞) (g : ℂ → ℝ) : ℝ≥0∞ :=
  eLpNorm g 1 volume + eLpNorm g p volume

theorem eLpNorm_one_le_normL1LpE (p : ℝ≥0∞) (g : ℂ → ℝ) : eLpNorm g 1 volume ≤ normL1LpE p g :=
  le_self_add

theorem eLpNorm_le_normL1LpE (p : ℝ≥0∞) (g : ℂ → ℝ) : eLpNorm g p volume ≤ normL1LpE p g :=
  le_add_self

/-- The real norm `Prelim.normL1Lp` agrees with `normL1LpE` on `L¹ ∩ L^p`. -/
theorem normL1Lp_eq_toReal {p : ℝ≥0∞} {g : ℂ → ℝ} (h1 : MemLp g 1 volume)
    (hp : MemLp g p volume) : Prelim.normL1Lp p g = (normL1LpE p g).toReal := by
  rw [Prelim.normL1Lp, normL1LpE, ENNReal.toReal_add h1.eLpNorm_ne_top hp.eLpNorm_ne_top]

/-- `sup_{t ∈ s} ‖ω₁(t) - ω₂(t)‖_{L^p} ∈ [0, ∞]` (`thm:criterion`(iv), (v), eq:defect,
`03_compactness.tex:937-941`, `:954-957`). For the distance to a fixed function `f` use
`ω₂ = stationary f`. -/
def supDist (p : ℝ≥0∞) (s : Set ℝ) (ω₁ ω₂ : ℝ → ℂ → ℝ) : ℝ≥0∞ :=
  ⨆ t ∈ s, eLpNorm (ω₁ t - ω₂ t) p volume

theorem eLpNorm_le_supDist {p : ℝ≥0∞} {s : Set ℝ} {ω₁ ω₂ : ℝ → ℂ → ℝ} {t : ℝ} (ht : t ∈ s) :
    eLpNorm (ω₁ t - ω₂ t) p volume ≤ supDist p s ω₁ ω₂ :=
  le_iSup₂ (f := fun t (_ : t ∈ s) => eLpNorm (ω₁ t - ω₂ t) p volume) t ht

theorem supDist_le_iff {p : ℝ≥0∞} {s : Set ℝ} {ω₁ ω₂ : ℝ → ℂ → ℝ} {c : ℝ≥0∞} :
    supDist p s ω₁ ω₂ ≤ c ↔ ∀ t ∈ s, eLpNorm (ω₁ t - ω₂ t) p volume ≤ c :=
  iSup₂_le_iff

theorem supDist_mono_set {p : ℝ≥0∞} {s s' : Set ℝ} {ω₁ ω₂ : ℝ → ℂ → ℝ} (hs : s ⊆ s') :
    supDist p s ω₁ ω₂ ≤ supDist p s' ω₁ ω₂ :=
  biSup_mono hs

/-- The norm `‖u‖_{L^s(I; L^b(Ω))} = ‖t ↦ ‖u(t)‖_{L^b(Ω)}‖_{L^s(I)} ∈ [0, ∞]`
(`02_prelim.tex:101-120`; used in `prop:compact`(iii), `03_compactness.tex:268-269`). It is
computed slice-wise; for the a.e.-measurable functions of the applications it is the Bochner
norm. -/
def bochnerNorm {E : Type*} [NormedAddCommGroup E] (s b : ℝ≥0∞) (I : Set ℝ) (Ω : Set ℂ)
    (u : ℝ → ℂ → E) : ℝ≥0∞ :=
  eLpNorm (fun t => eLpNorm (u t) b (volume.restrict Ω)) s (volume.restrict I)

/-- Weak convergence in `L²` of functions (`Prelim.WeakTendstoLp` with `p = 2`) is tested
against `L²`. -/
theorem weakTendstoLp_two_iff {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} :
    Prelim.WeakTendstoLp 2 gs g ↔ (∀ n, MemLp (gs n) 2 volume) ∧ MemLp g 2 volume ∧
      ∀ φ : ℂ → ℝ, MemLp φ 2 volume →
        Tendsto (fun n => ∫ x, gs n x * φ x) atTop (𝓝 (∫ x, g x * φ x)) := by
  have h2 : (2 : ℝ).conjExponent = 2 := by norm_num [Real.conjExponent]
  simp only [Prelim.WeakTendstoLp, h2, ENNReal.ofReal_ofNat]

end NonUniqueEuler.Weak
