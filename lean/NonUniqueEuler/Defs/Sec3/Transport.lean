import NonUniqueEuler.Defs.Sec3.Auxiliary
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Section 3: the linear transport equation `(te)`

Manuscript source: `03_compactness.tex:42-66` (Equation `eq:te` and the standing integrability
assumptions). For `T > 0`, `t₀ ∈ [0, T)`, a real field `w`, a real function `u` on
`(t₀, T) × ℝ²` and a datum `u₀`, the requirement is
`∫_{t₀}^T ∫ u (∂_t φ + w · ∇φ) dx dt + ∫ u₀ φ(t₀, ·) dx = 0` for all `φ ∈ 𝒟_T`.

* `slabFrom t₀ T = (t₀, T) × ℝ²`; `slabFrom 0 T = slab T` (statement layer).
* `SolvesTE t₀ T u w u₀`: `u` satisfies `(te)` on `[t₀, T)` with field `w` and datum `u₀`. As in
  the statement layer's `SolvesTransport` (which is the case `t₀ = 0`, `solvesTE_zero_iff`), the
  absolute convergence of both integrals is part of the definition, so that Lean's junk value
  `∫ = 0` of a non-integrable integrand never enters. The manuscript derives the convergence from
  the standing assumptions (`03_compactness.tex:53-56`); with the conjuncts, the predicate is
  equivalent to the manuscript's requirement under those assumptions.
* `IsTEData t₀ T u w u₀`: the standing assumptions of `(te)` (`03_compactness.tex:52-56`): `u`, `w`
  and `u w` are integrable on `(t₀, T') × B_R` for all `T' < T`, `R > 0`, and `u₀ ∈ L¹_loc`.
  They are hypotheses of `lem:lip-renorm` ("let `w`, `u` and `u₀` be as in the definition of
  (te)").

The field `w : ℝ → ℂ → ℂ` is a real vector field written in `ℂ` (D1), `w · ∇φ` is
`fderiv ℝ φ(t, ·) x (w t x)` (`spaceDeriv`), and the integrand is the statement layer's
`transportIntegrand`. A renormalized function `Υ(u)` is written `fun t x => Υ (u t x)`, as in the
statement layer.

Fully proved API: `solvesTE_zero_iff`, `IsWeakSolution.solvesTE`,
`IsRenormalizedWeakSolution.solvesTE_renormalized`, and linearity (`SolvesTE.add`, `.sub`,
`.const_mul`, `.neg`), used e.g. in `prop:stable` (`z̄ - ū²` solves `(te)` with datum `0`,
`03_compactness.tex:776-779`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak

/-- The space–time slab `(t₀, T) × ℝ²`. -/
def slabFrom (t₀ T : ℝ) : Set (ℝ × ℂ) :=
  Ioo t₀ T ×ˢ (univ : Set ℂ)

@[simp] theorem slabFrom_zero (T : ℝ) : slabFrom 0 T = slab T :=
  rfl

/-- `u` satisfies Equation `(te)` on `[t₀, T)` with field `w` and datum `u₀`
(`eq:te`, `03_compactness.tex:46-58`): for every `φ ∈ 𝒟_T`, the integrand
`u (∂_t φ + w · ∇φ)` is integrable on `(t₀, T) × ℝ²`, `u₀ φ(t₀, ·)` is integrable, and
`∫_{t₀}^T ∫ u (∂_t φ + w · ∇φ) dx dt + ∫ u₀ φ(t₀, ·) dx = 0`. -/
structure SolvesTE (t₀ T : ℝ) (u : ℝ → ℂ → ℝ) (w : ℝ → ℂ → ℂ) (u₀ : ℂ → ℝ) : Prop where
  integrableOn : ∀ φ, IsTestFunction T φ → IntegrableOn (transportIntegrand u w φ) (slabFrom t₀ T)
  datum_integrable : ∀ φ, IsTestFunction T φ → Integrable (fun x : ℂ => u₀ x * φ (t₀, x))
  identity : ∀ φ, IsTestFunction T φ →
    (∫ t in Ioo t₀ T, ∫ x : ℂ, transportIntegrand u w φ (t, x)) + ∫ x : ℂ, u₀ x * φ (t₀, x) = 0

/-- The standing assumptions of Equation `(te)` (`03_compactness.tex:52-56`): `u`, `w` and `u w`
are integrable on `(t₀, T') × B_R` for all `T' < T` and `R > 0`, and `u₀ ∈ L¹_loc(ℝ²)`.
(Measurability of `u`, `w` on `(t₀, T) × ℝ²` follows: the slab is a countable union of such
sets.) -/
structure IsTEData (t₀ T : ℝ) (u : ℝ → ℂ → ℝ) (w : ℝ → ℂ → ℂ) (u₀ : ℂ → ℝ) : Prop where
  integrableOn_u : ∀ T' : ℝ, T' < T → ∀ R : ℝ, 0 < R →
    IntegrableOn (Function.uncurry u) (Ioo t₀ T' ×ˢ ball (0 : ℂ) R)
  integrableOn_w : ∀ T' : ℝ, T' < T → ∀ R : ℝ, 0 < R →
    IntegrableOn (Function.uncurry w) (Ioo t₀ T' ×ˢ ball (0 : ℂ) R)
  integrableOn_uw : ∀ T' : ℝ, T' < T → ∀ R : ℝ, 0 < R →
    IntegrableOn (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (Ioo t₀ T' ×ˢ ball (0 : ℂ) R)
  locallyIntegrable_datum : LocallyIntegrable u₀ volume

/-! ### Fully proved API -/

/-- `(te)` on `[0, T)` is the statement layer's `SolvesTransport`. -/
theorem solvesTE_zero_iff {T : ℝ} {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {u₀ : ℂ → ℝ} :
    SolvesTE 0 T u w u₀ ↔ SolvesTransport T u w u₀ :=
  ⟨fun h => ⟨h.integrableOn, h.datum_integrable, h.identity⟩,
    fun h => ⟨h.integrableOn, h.datum_integrable, h.identity⟩⟩

/-- A weak solution satisfies `(te)` on `[0, T)` with field `v = K ∗ ω` and its datum
(`03_compactness.tex:59-62`). -/
theorem _root_.NonUniqueEuler.IsWeakSolution.solvesTE {q T : ℝ} {ωin : ℂ → ℝ}
    {ω : ℝ → ℂ → ℝ} (h : IsWeakSolution q T ωin ω) : SolvesTE 0 T ω (velocityField ω) ωin :=
  solvesTE_zero_iff.2 h.weak

/-- A renormalized weak solution: `Υ(ω)` satisfies `(te)` on `[0, T)` with field `v = K ∗ ω` and
datum `Υ(ωin)` (`03_compactness.tex:62-65`). -/
theorem _root_.NonUniqueEuler.IsRenormalizedWeakSolution.solvesTE_renormalized {q T : ℝ}
    {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ} (h : IsRenormalizedWeakSolution q T ωin ω) {Υ : ℝ → ℝ}
    (hΥ : IsRenormalization Υ) :
    SolvesTE 0 T (fun t x => Υ (ω t x)) (velocityField ω) (fun x => Υ (ωin x)) :=
  solvesTE_zero_iff.2 (h.renormalized Υ hΥ)

/-- The iterated integral over the slab is the integral over the product (Fubini). -/
theorem integral_Ioo_integral_eq {t₀ T : ℝ} {F : ℝ × ℂ → ℝ}
    (hF : IntegrableOn F (slabFrom t₀ T)) :
    ∫ t in Ioo t₀ T, ∫ x : ℂ, F (t, x) = ∫ p in slabFrom t₀ T, F p := by
  have hF' : IntegrableOn F (Ioo t₀ T ×ˢ (univ : Set ℂ))
      ((volume : Measure ℝ).prod (volume : Measure ℂ)) := by
    rw [← Measure.volume_eq_prod]; exact hF
  have h := setIntegral_prod F hF'
  rw [← Measure.volume_eq_prod] at h
  rw [slabFrom, h]
  simp only [Measure.restrict_univ]

section Linearity

variable {t₀ T : ℝ} {u u' : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {u₀ u₀' : ℂ → ℝ}

theorem transportIntegrand_add (u u' : ℝ → ℂ → ℝ) (w : ℝ → ℂ → ℂ) (φ : ℝ × ℂ → ℝ) :
    transportIntegrand (fun t x => u t x + u' t x) w φ =
      fun p => transportIntegrand u w φ p + transportIntegrand u' w φ p := by
  funext p
  simp only [transportIntegrand, add_mul]

theorem transportIntegrand_const_mul (c : ℝ) (u : ℝ → ℂ → ℝ) (w : ℝ → ℂ → ℂ)
    (φ : ℝ × ℂ → ℝ) :
    transportIntegrand (fun t x => c * u t x) w φ = fun p => c * transportIntegrand u w φ p := by
  funext p
  simp only [transportIntegrand, mul_assoc]

/-- `(te)` is linear in `(u, u₀)`: sums. -/
theorem SolvesTE.add (h : SolvesTE t₀ T u w u₀) (h' : SolvesTE t₀ T u' w u₀') :
    SolvesTE t₀ T (fun t x => u t x + u' t x) w (fun x => u₀ x + u₀' x) where
  integrableOn φ hφ := by
    rw [transportIntegrand_add]
    exact (h.integrableOn φ hφ).add (h'.integrableOn φ hφ)
  datum_integrable φ hφ := by
    simp only [add_mul]
    exact (h.datum_integrable φ hφ).add (h'.datum_integrable φ hφ)
  identity φ hφ := by
    have h1 := h.identity φ hφ
    have h2 := h'.identity φ hφ
    have hi := h.integrableOn φ hφ
    have hi' := h'.integrableOn φ hφ
    have hs : IntegrableOn (fun p => transportIntegrand u w φ p + transportIntegrand u' w φ p)
        (slabFrom t₀ T) := hi.add hi'
    rw [transportIntegrand_add, integral_Ioo_integral_eq hs]
    rw [integral_Ioo_integral_eq hi] at h1
    rw [integral_Ioo_integral_eq hi'] at h2
    simp only [add_mul]
    rw [integral_add hi hi', integral_add (h.datum_integrable φ hφ) (h'.datum_integrable φ hφ)]
    linarith

/-- `(te)` is linear in `(u, u₀)`: constant multiples. -/
theorem SolvesTE.const_mul (h : SolvesTE t₀ T u w u₀) (c : ℝ) :
    SolvesTE t₀ T (fun t x => c * u t x) w (fun x => c * u₀ x) where
  integrableOn φ hφ := by
    rw [transportIntegrand_const_mul]
    exact (h.integrableOn φ hφ).const_mul c
  datum_integrable φ hφ := by
    simp only [mul_assoc]
    exact (h.datum_integrable φ hφ).const_mul c
  identity φ hφ := by
    have h1 := h.identity φ hφ
    have hi := h.integrableOn φ hφ
    have hs : IntegrableOn (fun p => c * transportIntegrand u w φ p) (slabFrom t₀ T) :=
      hi.const_mul c
    rw [transportIntegrand_const_mul, integral_Ioo_integral_eq hs]
    rw [integral_Ioo_integral_eq hi] at h1
    simp only [mul_assoc]
    rw [integral_const_mul, integral_const_mul, ← mul_add, h1, mul_zero]

theorem SolvesTE.neg (h : SolvesTE t₀ T u w u₀) :
    SolvesTE t₀ T (fun t x => -u t x) w (fun x => -u₀ x) := by
  simpa only [neg_one_mul] using h.const_mul (-1)

/-- `(te)` is linear in `(u, u₀)`: differences. -/
theorem SolvesTE.sub (h : SolvesTE t₀ T u w u₀) (h' : SolvesTE t₀ T u' w u₀') :
    SolvesTE t₀ T (fun t x => u t x - u' t x) w (fun x => u₀ x - u₀' x) := by
  simpa only [sub_eq_add_neg] using h.add h'.neg

end Linearity

end NonUniqueEuler.Weak
