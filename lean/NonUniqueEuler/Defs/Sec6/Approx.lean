import NonUniqueEuler.Defs.Sec6.Datum

/-!
# Section 6.2: the approximate solutions, ring-`k` units (definitions)

Manuscript `def:approx`
(`06_datum.tex:71-81`), the paragraph on ring-`k` units (`06_datum.tex:138-156`), the dilated
annuli of `def:regions` (`06_datum.tex:167`), the configuration of `lem:reduction` for ring `k`
(`06_datum.tex:323-330`), and the comparison class of `lem:clock` (`06_datum.tex:436-443`).

* `Approx`: the data fixed in Sections 6–11 ((SA3), `09_relay.tex:43-48`): the cutoff `χ`,
  `A₁`, `μ`, `s̄`, `κ_seed` (`κs`), the depth `n`, the clock parameters `δ₀`, `T_pin`
  (`def:clock`), and the vorticity `om` (`ω^{(n)}`). `Approx.Valid` says that the parameters are
  in their ranges and that `om` is the solution of `thm:smooth` with datum `f^{(n)}`. The
  vorticity is a field so that the causality statements of `lem:clock` can replace it
  (`Approx.withOm`); every derived object uses `P.om` and its flow `P.flow`.
* ring-`k` units: `scaleVort A r g = A⁻¹ g(r·)`, `scaleSol A r ω (τ, y) = A⁻¹ ω(τ/A, r y)`,
  `scaleField A r V = V(r·)/(A r)` (the manuscript's `V_{[k]}`), `scaleFlow`; `P.unitsVort k`,
  `P.unitsField k` with `(A, r) = (A_k, r_k)`;
* `scaleSet r U = r U`, and the dilated annuli `N_k, N'_k, N♭_k, 𝒩_k, 𝒩₋_k`;
* `P.ringConfig k`: the three parts of the datum in ring-`k` units, a `OneRing.RingConfig`.

Namespace `NonUniqueEuler.Datum`; the objects of an approximation `P` are in
`NonUniqueEuler.Datum.Approx` (dot notation `P.flow t`, `P.ringConfig k`, …).
All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Datum

open RingData

/-! ### Ring-`k` units (`06_datum.tex:138-156`) -/

/-- A vorticity in the units `(A, r)`: `y ↦ A⁻¹ g(r y)` (`06_datum.tex:138-140`). -/
def scaleVort (A r : ℝ) (g : ℂ → ℝ) (y : ℂ) : ℝ := A⁻¹ * g ((r : ℂ) * y)

/-- A space–time vorticity in the units `(A, r)`: `ω̃(τ, y) = A⁻¹ ω(τ/A, r y)`
(`06_datum.tex:138-140`). -/
def scaleSol (A r : ℝ) (om : ℝ → ℂ → ℝ) (τ : ℝ) (y : ℂ) : ℝ := A⁻¹ * om (τ / A) ((r : ℂ) * y)

/-- A velocity field in the units `(A, r)`: `V_{[k]}(y) = V(r y)/(A r)` (`06_datum.tex:150-154`,
with `(A, r) = (A_k, r_k)`). -/
def scaleField (A r : ℝ) (V : ℂ → ℂ) (y : ℂ) : ℂ := V ((r : ℂ) * y) / ((A * r : ℝ) : ℂ)

/-- A flow in the units `(A, r)`: `y ↦ r⁻¹ Φ_{τ/A}(r y)` (`06_datum.tex:141-142`). -/
def scaleFlow (A r : ℝ) (F : ℝ → ℂ → ℂ) (τ : ℝ) (y : ℂ) : ℂ := (r : ℂ)⁻¹ * F (τ / A) ((r : ℂ) * y)

/-- The dilated set `r U = {r y : y ∈ U}`, written as `{x : r⁻¹ x ∈ U}` (equal for `r ≠ 0`). -/
def scaleSet (r : ℝ) (U : Set ℂ) : Set ℂ := {x : ℂ | (r : ℂ)⁻¹ * x ∈ U}

theorem mem_scaleSet {r : ℝ} {U : Set ℂ} {x : ℂ} : x ∈ scaleSet r U ↔ (r : ℂ)⁻¹ * x ∈ U :=
  Iff.rfl

theorem mul_mem_scaleSet {r : ℝ} (hr : r ≠ 0) {U : Set ℂ} {y : ℂ} :
    (r : ℂ) * y ∈ scaleSet r U ↔ y ∈ U := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  simp [scaleSet, ← mul_assoc, inv_mul_cancel₀ hr']

theorem scaleVort_apply (A r : ℝ) (g : ℂ → ℝ) (y : ℂ) :
    scaleVort A r g y = A⁻¹ * g ((r : ℂ) * y) := rfl

theorem scaleField_apply (A r : ℝ) (V : ℂ → ℂ) (y : ℂ) :
    scaleField A r V y = V ((r : ℂ) * y) / ((A * r : ℝ) : ℂ) := rfl

/-! ### The approximation data -/

/-- **The data of Sections 6–11** (`def:approx`, `def:regions`, `def:clock`; (SA3),
`09_relay.tex:43-48`): the admissible cutoff `χ` (through `Φ = ringPhi χ`), `A₁`, `μ`, `s̄`,
`κ_seed` (`κs`), the depth `n`, the clock parameters `δ₀` and `T_pin`, and the space–time
vorticity `om`, which is `ω^{(n)}` (the solution of `thm:smooth` with datum `f^{(n)}`) under
`Approx.Valid`. Every derived object is defined for all data. -/
structure Approx where
  /-- the cutoff `χ` of `def:ring` -/
  χ : ℝ → ℝ
  /-- the amplitude `A₁` of the outermost ring -/
  A₁ : ℝ
  /-- the amplitude ratio `μ` -/
  μ : ℝ
  /-- the radius parameter `s̄` -/
  sbar : ℝ
  /-- the seed size `κ_seed` -/
  κs : ℝ
  /-- the depth `n` (number of rings) -/
  n : ℕ
  /-- the saturation level `δ₀` of `def:clock` -/
  δ₀ : ℝ
  /-- the pinning time `T_pin` of `def:clock` -/
  Tpin : ℝ
  /-- the vorticity `ω^{(n)}` -/
  om : ℝ → ℂ → ℝ

namespace Approx

variable (P : Approx)

/-- `A_k = A₁ μ^{k-1}` (`06_datum.tex:19`). -/
def A (k : ℕ) : ℝ := amp P.A₁ P.μ k

/-- `s_k = s̄ (2μ)^{-k}` (`06_datum.tex:19`). -/
def s (k : ℕ) : ℝ := ratio P.sbar P.μ k

/-- `r_k` (`r₁ = 1`, `r_{k+1} = s_k r_k`, `06_datum.tex:19`). -/
def r (k : ℕ) : ℝ := radius P.sbar P.μ k

/-- The `k`-th term `f^{(n)}_k` of `f^{(n)}` (`06_datum.tex:162-164`). -/
def term (k : ℕ) : ℂ → ℝ := approxTerm P.χ P.A₁ P.μ P.sbar P.κs P.n k

/-- The approximate datum `f^{(n)}` (`def:approx`, `06_datum.tex:76`). -/
def f : ℂ → ℝ := approxDatum P.χ P.A₁ P.μ P.sbar P.κs P.n

/-- The datum `f` of `def:datum` with the same parameters (`06_datum.tex:22-23`). -/
def datumF : ℂ → ℝ := datum P.χ P.A₁ P.μ P.sbar

/-- The velocity `v^{(n)} = K_BS * ω^{(n)}` (`def:approx`, `06_datum.tex:79`). -/
def vel (t : ℝ) (x : ℂ) : ℂ := velocityField P.om t x

/-- The flow `Φ_t` of `v^{(n)}` (`def:approx`, `06_datum.tex:80`): `Φ_t(y) = Φ_v(t, 0, y)`
(`Smooth.flowOf`; for a valid `P` this is `Smooth.flow f^{(n)} t`, `Valid.flow_eq`). -/
def flow (t : ℝ) (y : ℂ) : ℂ := Smooth.flowOf (velocityField P.om) t 0 y

/-- The inverse `Φ_t⁻¹ = Φ_v(0, t, ·)` of the flow map. -/
def flowInv (t : ℝ) (x : ℂ) : ℂ := Smooth.flowOf (velocityField P.om) 0 t x

/-- **The hypotheses of `def:approx`** (with those of `def:datum` and `def:clock`):
`χ` admissible, `A₁ > 0`, `μ ∈ (1, 2]`, `s̄ ∈ (0, a/16]` (`DatumParams`), `n ≥ 2`,
`κ_seed ∈ (0, κ_L]`, `δ₀ > 0`, `T_pin > 0`, and `om = ω^{(n)}` is the solution of `thm:smooth`
with datum `f^{(n)}`. Hypothesis (N1)–(N3) (`NumericalHypothesis P.χ`) is a separate hypothesis
of the statements, as everywhere. -/
structure Valid : Prop where
  admissible : IsAdmissibleCutoff P.χ
  datumParams : DatumParams P.A₁ P.μ P.sbar
  two_le_n : 2 ≤ P.n
  kseed_pos : 0 < P.κs
  kseed_le : P.κs ≤ OneRing.kL P.χ
  δ₀_pos : 0 < P.δ₀
  Tpin_pos : 0 < P.Tpin
  om_eq : P.om = Smooth.sol P.f

/-- The approximation with the given parameters and `om = ω^{(n)} = Smooth.sol f^{(n)}`. -/
def ofParams (χ : ℝ → ℝ) (A₁ μ sbar κs : ℝ) (n : ℕ) (δ₀ Tpin : ℝ) : Approx :=
  ⟨χ, A₁, μ, sbar, κs, n, δ₀, Tpin, Smooth.sol (approxDatum χ A₁ μ sbar κs n)⟩

/-- The same data with the vorticity replaced by `om'` (the comparison of `lem:clock`(2),(3),
`06_datum.tex:436-443`: `f^{(n)}`, the sets `S_k` and the parameters are kept; the flow becomes
the flow of `K_BS * om'`). -/
def withOm (om' : ℝ → ℂ → ℝ) : Approx := { P with om := om' }

/-- The dilated annulus `N_k = r_k N` (`06_datum.tex:167`). -/
def Nk (k : ℕ) : Set ℂ := scaleSet (P.r k) annN

/-- The dilated annulus `N'_k = r_k N'` (`06_datum.tex:167`). -/
def Npk (k : ℕ) : Set ℂ := scaleSet (P.r k) annN'

/-- The dilated annulus `N♭_k = r_k N♭` (`06_datum.tex:167`). -/
def Nflatk (k : ℕ) : Set ℂ := scaleSet (P.r k) annNflat

/-- The dilated annulus `𝒩_k = r_k 𝒩` (`06_datum.tex:167`). -/
def Nnk (k : ℕ) : Set ℂ := scaleSet (P.r k) annNn

/-- The dilated annulus `𝒩₋_k = r_k 𝒩₋` (`06_datum.tex:167`). -/
def Nmk (k : ℕ) : Set ℂ := scaleSet (P.r k) annNm

/-- A vorticity in ring-`k` units, `y ↦ A_k⁻¹ g(r_k y)` (`06_datum.tex:147-149`). -/
def unitsVort (k : ℕ) (g : ℂ → ℝ) : ℂ → ℝ := scaleVort (P.A k) (P.r k) g

/-- A velocity field in ring-`k` units, `V_{[k]}(y) = V(r_k y)/(A_k r_k)` (`06_datum.tex:150-154`).
"`V` is bounded on `N'_k` in `C^q`, in ring-`k` units, by `X`" (`07_several_rings.tex:36-39`) is
`normCk q annN' (P.unitsField k V) ≤ X` (with `MemCk`). -/
def unitsField (k : ℕ) (V : ℂ → ℂ) : ℂ → ℂ := scaleField (P.A k) (P.r k) V

/-- **The configuration of `lem:reduction` for ring `k`** (`06_datum.tex:323-330`,
`07_several_rings.tex:449-456`): the datum `A_k⁻¹ f^{(n)}(r_k ·)` in ring-`k` units split into the
ring part `A_k⁻¹ f^{(n)}_k(r_k ·)`, the inner part `A_k⁻¹ Σ_{i>k} f^{(n)}_i(r_k ·)` and the outer part
`A_k⁻¹ Σ_{i<k} f^{(n)}_i(r_k ·)`. Its solution is `ω^{(n)}` in ring-`k` units (scaling covariance
of `thm:smooth`), its `G` is `G_k`, and its field `h` is `h_k` on `N'` (interface statements). -/
def ringConfig (k : ℕ) : OneRing.RingConfig where
  ring0 := P.unitsVort k (P.term k)
  inner0 := P.unitsVort k fun x => ∑ i ∈ Finset.Ioc k P.n, P.term i x
  outer0 := P.unitsVort k fun x => ∑ i ∈ Finset.Ico 1 k, P.term i x

/-! ### Basic lemmas (fully proved) -/

theorem A_def (k : ℕ) : P.A k = amp P.A₁ P.μ k := rfl

theorem s_def (k : ℕ) : P.s k = ratio P.sbar P.μ k := rfl

theorem r_def (k : ℕ) : P.r k = radius P.sbar P.μ k := rfl

theorem f_def : P.f = approxDatum P.χ P.A₁ P.μ P.sbar P.κs P.n := rfl

theorem f_apply (x : ℂ) : P.f x = ∑ k ∈ Finset.Icc 1 P.n, P.term k x := rfl

theorem ofParams_om (χ : ℝ → ℝ) (A₁ μ sbar κs : ℝ) (n : ℕ) (δ₀ Tpin : ℝ) :
    (ofParams χ A₁ μ sbar κs n δ₀ Tpin).om = Smooth.sol (ofParams χ A₁ μ sbar κs n δ₀ Tpin).f :=
  rfl

/-- The approximation built from parameters in their ranges is valid. -/
theorem ofParams_valid {χ : ℝ → ℝ} {A₁ μ sbar κs : ℝ} {n : ℕ} {δ₀ Tpin : ℝ}
    (hχ : IsAdmissibleCutoff χ) (hp : DatumParams A₁ μ sbar) (hn : 2 ≤ n) (hκ : 0 < κs)
    (hκ' : κs ≤ OneRing.kL χ) (hδ : 0 < δ₀) (hT : 0 < Tpin) :
    (ofParams χ A₁ μ sbar κs n δ₀ Tpin).Valid :=
  ⟨hχ, hp, hn, hκ, hκ', hδ, hT, rfl⟩

@[simp] theorem withOm_om (om' : ℝ → ℂ → ℝ) : (P.withOm om').om = om' := rfl
@[simp] theorem withOm_χ (om' : ℝ → ℂ → ℝ) : (P.withOm om').χ = P.χ := rfl
@[simp] theorem withOm_A₁ (om' : ℝ → ℂ → ℝ) : (P.withOm om').A₁ = P.A₁ := rfl
@[simp] theorem withOm_μ (om' : ℝ → ℂ → ℝ) : (P.withOm om').μ = P.μ := rfl
@[simp] theorem withOm_sbar (om' : ℝ → ℂ → ℝ) : (P.withOm om').sbar = P.sbar := rfl
@[simp] theorem withOm_κs (om' : ℝ → ℂ → ℝ) : (P.withOm om').κs = P.κs := rfl
@[simp] theorem withOm_n (om' : ℝ → ℂ → ℝ) : (P.withOm om').n = P.n := rfl
@[simp] theorem withOm_δ₀ (om' : ℝ → ℂ → ℝ) : (P.withOm om').δ₀ = P.δ₀ := rfl
@[simp] theorem withOm_Tpin (om' : ℝ → ℂ → ℝ) : (P.withOm om').Tpin = P.Tpin := rfl

theorem withOm_f (om' : ℝ → ℂ → ℝ) : (P.withOm om').f = P.f := rfl

theorem withOm_term (om' : ℝ → ℂ → ℝ) (k : ℕ) : (P.withOm om').term k = P.term k := rfl

theorem withOm_self : P.withOm P.om = P := rfl

variable {P}

/-- For a valid `P`, the flow is the flow `Smooth.flow f^{(n)}` of `thm:smooth`(4). -/
theorem Valid.flow_eq (h : P.Valid) (t : ℝ) : P.flow t = Smooth.flow P.f t := by
  funext y
  simp only [flow, Smooth.flow, Smooth.vel, h.om_eq]

theorem Valid.flowInv_eq (h : P.Valid) (t : ℝ) : P.flowInv t = Smooth.flowInv P.f t := by
  funext x
  simp only [flowInv, Smooth.flowInv, Smooth.vel, h.om_eq]

theorem Valid.A_pos (h : P.Valid) (k : ℕ) : 0 < P.A k :=
  amp_pos h.datumParams.A₁_pos (by linarith [h.datumParams.one_lt_μ]) k

theorem Valid.s_pos (h : P.Valid) (k : ℕ) : 0 < P.s k :=
  ratio_pos h.datumParams.sbar_pos (by linarith [h.datumParams.one_lt_μ]) k

theorem Valid.r_pos (h : P.Valid) (k : ℕ) : 0 < P.r k :=
  radius_pos h.datumParams.sbar_pos (by linarith [h.datumParams.one_lt_μ]) k

theorem Valid.one_le_n (h : P.Valid) : 1 ≤ P.n := le_trans (by norm_num) h.two_le_n

variable (P)

/-- The datum of the configuration of ring `k` is `A_k⁻¹ f^{(n)}(r_k ·)` (`1 ≤ k ≤ n`). -/
theorem ringConfig_datum {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ P.n) :
    (P.ringConfig k).datum = P.unitsVort k P.f := by
  funext y
  simp only [OneRing.RingConfig.datum, ringConfig, unitsVort, scaleVort, f]
  rw [approxDatum_split P.χ P.A₁ P.μ P.sbar P.κs hk hkn]
  simp only [term]
  ring

variable {P}

/-- For `1 ≤ k < n` the ring part of the configuration of ring `k` is `Φ` (the hypothesis
`ω_r(0) = Φ` of `thm:quiet`, `OneRing.IsQuietConst`). -/
theorem Valid.ringConfig_ring0 (h : P.Valid) {k : ℕ} (hk : 1 ≤ k) (hkn : k < P.n) :
    (P.ringConfig k).ring0 = ringPhi P.χ := by
  funext y
  have hA : P.A k ≠ 0 := (h.A_pos k).ne'
  have hr : ((P.r k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (h.r_pos k).ne'
  simp only [ringConfig, unitsVort, scaleVort, term]
  rw [approxTerm_of_lt hk hkn]
  rw [← A_def, ← r_def, mul_div_cancel_left₀ y hr, ← mul_assoc, inv_mul_cancel₀ hA, one_mul]

/-- The ring part of the configuration of the innermost ring `n` is the seeded ring
`Φ^{κ_seed}` (`06_datum.tex:429-430`). -/
theorem Valid.ringConfig_ring0_n (h : P.Valid) :
    (P.ringConfig P.n).ring0 = OneRing.PhiSeed P.χ P.κs := by
  funext y
  have hA : P.A P.n ≠ 0 := (h.A_pos P.n).ne'
  have hr : ((P.r P.n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (h.r_pos P.n).ne'
  simp only [ringConfig, unitsVort, scaleVort, term]
  rw [approxTerm_self]
  rw [← A_def, ← r_def, mul_div_cancel_left₀ y hr, ← mul_assoc, inv_mul_cancel₀ hA, one_mul]

end Approx

end Datum

end NonUniqueEuler
