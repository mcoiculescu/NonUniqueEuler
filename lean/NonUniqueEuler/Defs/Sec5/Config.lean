import NonUniqueEuler.Defs.SmoothB.Solution
import NonUniqueEuler.Defs.Sec4.Eigendata
import NonUniqueEuler.Defs.Infra.CkNorm

/-!
# Section 5: one ring — the configuration of `lem:reduction` (definitions)

Manuscript
`05_single_ring.tex:28-40` (3-fold symmetric fields, radial motion of trajectories) and
`lem:reduction` (`05_single_ring.tex:86-128`).

Everything is in ring units (`04_ring.tex:46-52`), namespace `NonUniqueEuler.OneRing`.

* `RingConfig`: the data of `lem:reduction`, the three parts `ω_r(0), ω_i(0), ω_o(0)` of the datum
  (fields `ring0`, `inner0`, `outer0`; we avoid the letter `ω` in names, because
  `open scoped ContDiff` turns `ω` into a token);
* derived objects: the datum `ω(0) = ω_r(0) + ω_i(0) + ω_o(0)` (`datum`), the solution
  `ω = Smooth.sol ω(0)` of `thm:smooth` (`sol`), its flow `Φ_t` and inverse `Φ_t⁻¹` (`flow`,
  `flowInv`), the transported parts `ω_•(t) = ω_•(0) ∘ Φ_t⁻¹` (`ringPart`, `innerPart`,
  `outerPart`), the inner circulation `G = (2π)⁻¹ ∫ ω_i(0)` (`G`), the field
  `h(t) = K_BS * (ω_i(t) + ω_o(t)) - G x^⊥/|x|²` (`h`), and the perturbation `w = ω_r - Φ`
  (`w`, complexified; `pert0 = ω_r(0) - Φ`);
* `RingConfig.Hyp c T`: the hypotheses of `lem:reduction` on `[0, T]`;
* `RingConfig.MovesRadially c t δ`: "every trajectory of `ω_r` moves radially by at most `δ` on
  `[0,t]`" (`05_single_ring.tex:34-36`);
* `IsSymFieldOn U h`: the vector field `h` is `3`-fold symmetric on `U`, `h(O x) = O h(x)` with
  `O = O_{2π/3}` (`05_single_ring.tex:30-31`);
* `radComp h x = h·e_r`, `angComp h x = h·e_θ` (`lem:reduction`(1),(2));
* `annN1 = {a/4 < |y| < 3}`, the interior of `N'` (`05_single_ring.tex:221`);
* `CkPathOn k U I h`: `t ↦ h(t) ∈ C^k(U)` is continuous on `I` (`lem:reduction`(1),
  `lem:running`, `lem:linear-part`).

Conventions: smoothness is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)` (`C^∞`, decision D15); `supp` of a
continuous function is `tsupport`; vector fields are `ℂ`-valued (D1); `x^⊥ = I * x`.

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology ComplexConjugate

namespace NonUniqueEuler

namespace OneRing

open RingData

/-! ### Fields on the plane -/

/-- The vector field `h` is `3`-fold symmetric on `U`: `h(O x) = O h(x)` for `x ∈ U`, with
`O = O_{2π/3}` the rotation by `2π/3` (`05_single_ring.tex:30-31`). For `U = N'` (which is
rotation invariant) this is the manuscript's condition "on a neighborhood of `N'`" restricted to
`N'`, which is all that `C^k(N')` norms see. -/
def IsSymFieldOn (U : Set ℂ) (h : ℂ → ℂ) : Prop :=
  ∀ x ∈ U, h (rot (2 * Real.pi / 3) x) = rot (2 * Real.pi / 3) (h x)

/-- The radial component `h·e_r` of a vector field at `x ≠ 0`, `e_r = x/|x|`
(`lem:reduction`(1),(2), `05_single_ring.tex:107`, `:117`); the dot product of `u, v ∈ ℂ = ℝ²`
is `Re(u v̄)`. -/
def radComp (h : ℂ → ℂ) (x : ℂ) : ℝ :=
  (h x * conj (((‖x‖ : ℝ) : ℂ)⁻¹ * x)).re

/-- The angular component `h·e_θ` of a vector field at `x ≠ 0`, `e_θ = x^⊥/|x| = i x/|x|`
(`lem:reduction`(1), `05_single_ring.tex:107`). -/
def angComp (h : ℂ → ℂ) (x : ℂ) : ℝ :=
  (h x * conj (((‖x‖ : ℝ) : ℂ)⁻¹ * (Complex.I * x))).re

/-- `N₁ = {a/4 < |y| < 3}`, the interior of `N'` (`05_single_ring.tex:221`). -/
def annN1 : Set ℂ := {y : ℂ | a / 4 < ‖y‖ ∧ ‖y‖ < 3}

/-- `t ↦ h(t) ∈ C^k(U)` is continuous on `I`: every `h(t)`, `t ∈ I`, lies in `C^k(U)`, and
`‖h(t') - h(t)‖_{C^k(U)} → 0` as `t' → t` in `I` (`lem:reduction`(1),
`05_single_ring.tex:108-109`; `lem:running`, `:589-590`; `lem:linear-part`, `:624-625`). -/
def CkPathOn (k : ℕ) (U : Set ℂ) (I : Set ℝ) (h : ℝ → ℂ → ℂ) : Prop :=
  (∀ t ∈ I, MemCk k U (h t)) ∧
    ∀ t ∈ I, Tendsto (fun t' => normCk k U (h t' - h t)) (𝓝[I] t) (𝓝 0)

/-! ### The configuration of `lem:reduction` -/

/-- **The data of `lem:reduction`** (`05_single_ring.tex:88-95`): the three parts
`ω_r(0)` (`ring0`, the ring), `ω_i(0)` (`inner0`, the vorticity inside) and `ω_o(0)` (`outer0`,
the vorticity outside) of the datum `ω(0) = ω_r(0) + ω_i(0) + ω_o(0)`. The hypotheses are
`RingConfig.Hyp`; every derived object is defined for all data. -/
structure RingConfig where
  /-- `ω_r(0)`, the ring part of the datum. -/
  ring0 : ℂ → ℝ
  /-- `ω_i(0)`, the inner part of the datum. -/
  inner0 : ℂ → ℝ
  /-- `ω_o(0)`, the outer part of the datum. -/
  outer0 : ℂ → ℝ

namespace RingConfig

variable (c : RingConfig)

/-- The datum `ω(0) = ω_r(0) + ω_i(0) + ω_o(0)` (`05_single_ring.tex:90`). -/
def datum (x : ℂ) : ℝ := c.ring0 x + c.inner0 x + c.outer0 x

/-- The solution `ω` of `thm:smooth` with datum `ω(0)` (`05_single_ring.tex:88`). -/
def sol : ℝ → ℂ → ℝ := Smooth.sol c.datum

/-- The flow `Φ_t` of `ω` (`05_single_ring.tex:89`; `Smooth.flow`). -/
def flow (t : ℝ) (y : ℂ) : ℂ := Smooth.flow c.datum t y

/-- The inverse `Φ_t⁻¹` of the flow map (`Smooth.flowInv`). -/
def flowInv (t : ℝ) (x : ℂ) : ℂ := Smooth.flowInv c.datum t x

/-- `ω_r(t) = ω_r(0) ∘ Φ_t⁻¹` (`05_single_ring.tex:33`, `:93`). -/
def ringPart (t : ℝ) (x : ℂ) : ℝ := c.ring0 (c.flowInv t x)

/-- `ω_i(t) = ω_i(0) ∘ Φ_t⁻¹` (`05_single_ring.tex:93`). -/
def innerPart (t : ℝ) (x : ℂ) : ℝ := c.inner0 (c.flowInv t x)

/-- `ω_o(t) = ω_o(0) ∘ Φ_t⁻¹` (`05_single_ring.tex:93`). -/
def outerPart (t : ℝ) (x : ℂ) : ℝ := c.outer0 (c.flowInv t x)

/-- The inner circulation `G = (2π)⁻¹ ∫ ω_i(0)` (`05_single_ring.tex:95`). -/
def G : ℝ := (2 * Real.pi)⁻¹ * ∫ x, c.inner0 x

/-- The field `h(t) = K_BS * (ω_i(t) + ω_o(t)) - G x^⊥/|x|²` (`05_single_ring.tex:98-101`), with
`x^⊥ = i x`. The manuscript defines it on a neighborhood of `N'`; the formula is used everywhere
(only its values near `N'` enter the statements, through `C^k(N')` norms and the products
`h·∇w`, `h·∇Φ`, which vanish a.e. outside `N` whatever `h` is there; see `OneRing.hGrad`). -/
def h (t : ℝ) (x : ℂ) : ℂ :=
  velocity (fun y => c.innerPart t y + c.outerPart t y) x -
    (c.G : ℂ) * (Complex.I * x) / (((‖x‖ ^ 2 : ℝ)) : ℂ)

/-- The initial perturbation `w(0) = ω_r(0) - Φ`, complexified (`thm:active` (Init),
`05_single_ring.tex:886`; `lem:window`, `:690`; the running coefficient's `w₀ = w(0)`). -/
def pert0 (χ : ℝ → ℝ) (x : ℂ) : ℂ := ((c.ring0 x - ringPhi χ x : ℝ) : ℂ)

/-- The perturbation `w(t) = ω_r(t) - Φ`, complexified (`lem:reduction`(3),
`05_single_ring.tex:118-119`; real valued by construction). -/
def w (χ : ℝ → ℝ) (t : ℝ) (x : ℂ) : ℂ := ((c.ringPart t x - ringPhi χ x : ℝ) : ℂ)

/-- **The hypotheses of `lem:reduction` on `[0,T]`** (`05_single_ring.tex:88-97`): the datum
`ω(0)` is `C_c^∞` (so `ω` is the solution of `thm:smooth`), the three parts have pairwise disjoint
supports and are `3`-fold symmetric (then so is `ω(0)`), `T > 0`, and for every `t ∈ [0,T]`,
`supp ω_i(t) ⊂ \bar B_{a/8}` and `supp ω_o(t) ∩ B_6 = ∅`.
The parts themselves are not assumed smooth: the manuscript derives `ω_•(0) ∈ C_c^∞` from the
disjointness of the supports (`05_single_ring.tex:130-133`). -/
structure Hyp (T : ℝ) : Prop where
  datum_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c.datum
  datum_hasCompactSupport : HasCompactSupport c.datum
  disjoint_ring_inner : Disjoint (tsupport c.ring0) (tsupport c.inner0)
  disjoint_ring_outer : Disjoint (tsupport c.ring0) (tsupport c.outer0)
  disjoint_inner_outer : Disjoint (tsupport c.inner0) (tsupport c.outer0)
  sym_ring : IsMFoldSymmetric 3 c.ring0
  sym_inner : IsMFoldSymmetric 3 c.inner0
  sym_outer : IsMFoldSymmetric 3 c.outer0
  T_pos : 0 < T
  inner_tsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (c.innerPart t) ⊆ closedBall 0 (a / 8)
  outer_tsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (c.outerPart t) ∩ ball 0 6 = ∅

/-- **Every trajectory of `ω_r` moves radially by at most `δ` on `[0,t]`**
(`05_single_ring.tex:34-36`): `||Φ_τ(y)| - |y|| ≤ δ` for every `y ∈ supp ω_r(0)` and every
`τ ∈ [0,t]`. -/
def MovesRadially (t δ : ℝ) : Prop :=
  ∀ y ∈ tsupport c.ring0, ∀ τ ∈ Icc (0 : ℝ) t, |‖c.flow τ y‖ - ‖y‖| ≤ δ

/-- `supp ω_r(t) ⊂ K` for every `t ∈ [0,T]` (with `K = N` this is the hypothesis of
`lem:reduction`(3), `05_single_ring.tex:118`). -/
def RingSupportedIn (T : ℝ) (K : Set ℂ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, tsupport (c.ringPart t) ⊆ K

/-! ### Basic lemmas (fully proved) -/

theorem datum_apply (x : ℂ) : c.datum x = c.ring0 x + c.inner0 x + c.outer0 x := rfl

theorem sol_eq : c.sol = Smooth.sol c.datum := rfl

theorem ringPart_apply (t : ℝ) (x : ℂ) : c.ringPart t x = c.ring0 (c.flowInv t x) := rfl

theorem w_apply (χ : ℝ → ℝ) (t : ℝ) (x : ℂ) :
    c.w χ t x = ((c.ringPart t x - ringPhi χ x : ℝ) : ℂ) := rfl

/-- `w` is real valued. -/
theorem w_im (χ : ℝ → ℝ) (t : ℝ) (x : ℂ) : (c.w χ t x).im = 0 := by
  simp [w]

/-- `w(0) = ω_r(0) - Φ` once `Φ_0⁻¹ = id` (which is `thm:smooth`(4)). -/
theorem w_zero_of_flowInv_zero (χ : ℝ → ℝ) (h0 : ∀ x, c.flowInv 0 x = x) :
    c.w χ 0 = c.pert0 χ := by
  funext x
  simp [w, pert0, ringPart, h0 x]

theorem MovesRadially.mono {c : RingConfig} {t δ δ' : ℝ} (h : c.MovesRadially t δ)
    (hδ : δ ≤ δ') : c.MovesRadially t δ' :=
  fun y hy τ hτ => (h y hy τ hτ).trans hδ

theorem MovesRadially.mono_time {c : RingConfig} {t t' δ : ℝ} (h : c.MovesRadially t δ)
    (ht : t' ≤ t) : c.MovesRadially t' δ :=
  fun y hy τ hτ => h y hy τ ⟨hτ.1, hτ.2.trans ht⟩

theorem Hyp.mono {c : RingConfig} {T T' : ℝ} (h : c.Hyp T) (hT' : 0 < T') (hT : T' ≤ T) :
    c.Hyp T' where
  datum_contDiff := h.datum_contDiff
  datum_hasCompactSupport := h.datum_hasCompactSupport
  disjoint_ring_inner := h.disjoint_ring_inner
  disjoint_ring_outer := h.disjoint_ring_outer
  disjoint_inner_outer := h.disjoint_inner_outer
  sym_ring := h.sym_ring
  sym_inner := h.sym_inner
  sym_outer := h.sym_outer
  T_pos := hT'
  inner_tsupport := fun t ht => h.inner_tsupport t ⟨ht.1, ht.2.trans hT⟩
  outer_tsupport := fun t ht => h.outer_tsupport t ⟨ht.1, ht.2.trans hT⟩

/-- The zero configuration (all three parts `0`). -/
def zero : RingConfig := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- Non-vacuity: the zero configuration satisfies the hypotheses of `lem:reduction` on every
`[0,T]`, `T > 0`. -/
theorem hyp_zero {T : ℝ} (hT : 0 < T) : zero.Hyp T where
  datum_contDiff := by
    have : zero.datum = fun _ => (0 : ℝ) := by funext x; simp [zero, datum]
    rw [this]; exact contDiff_const
  datum_hasCompactSupport := by
    have : zero.datum = fun _ => (0 : ℝ) := by funext x; simp [zero, datum]
    rw [this]; exact HasCompactSupport.zero
  disjoint_ring_inner := by simp [zero]
  disjoint_ring_outer := by simp [zero]
  disjoint_inner_outer := by simp [zero]
  sym_ring := Filter.EventuallyEq.rfl
  sym_inner := Filter.EventuallyEq.rfl
  sym_outer := Filter.EventuallyEq.rfl
  T_pos := hT
  inner_tsupport := fun t _ => by
    have : zero.innerPart t = fun _ => (0 : ℝ) := rfl
    rw [this]; simp
  outer_tsupport := fun t _ => by
    have : zero.outerPart t = fun _ => (0 : ℝ) := rfl
    rw [this]; simp

end RingConfig

theorem annN1_subset_annN' : annN1 ⊆ annN' := fun _ hy => ⟨hy.1.le, hy.2.le⟩

theorem isOpen_annN1 : IsOpen annN1 :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem CkPathOn.mono_set {k : ℕ} {U : Set ℂ} {I I' : Set ℝ} {h : ℝ → ℂ → ℂ}
    (hh : CkPathOn k U I h) (hI : I' ⊆ I) : CkPathOn k U I' h :=
  ⟨fun t ht => hh.1 t (hI ht), fun t ht => (hh.2 t (hI ht)).mono_left (nhdsWithin_mono t hI)⟩

end OneRing

end NonUniqueEuler
