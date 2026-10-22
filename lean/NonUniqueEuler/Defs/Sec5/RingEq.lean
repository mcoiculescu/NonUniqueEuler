import NonUniqueEuler.Defs.Sec5.Config
import NonUniqueEuler.Defs.Sec2.BiotSavart
import NonUniqueEuler.Defs.Sec4.Extra2Eigendata

/-!
# Section 5: the perturbation equation, paths in `X^k`, the linear response and the running
coefficient (definitions)

Manuscript `05_single_ring.tex`:
`lem:duhamel` (`:50-57`), `lem:reduction`(3) and `eq:ring` (`:118-126`), `lem:energy`
(`:300-316`), `def:majorant` (`:383-388`), `thm:quiet`(b) (`:424-426`), `lem:running` and
`eq:running` (`:587-600`), `lem:linear-part` (`:616-633`), `thm:active`(b) (`:897-899`).

Namespace `NonUniqueEuler.OneRing` (ring units). Plane functions are `ℂ → ℂ` (the spaces
`X^k` consist of complex functions, `Lin.MemXFn`); the real vorticities are coerced.

* `PhiC χ`: the ring `Φ` as a complex function;
* `hGrad h g = h·∇g` (`05_single_ring.tex:125-126`; no indicator of `N'`, see its docstring;
  `hGrad h (PhiC χ) = Eig.hGradPhi χ h` by `rfl`);
* `bsGrad v g = (K_BS * v)·∇g` for a complex `v` (`K_BS * v = K_BS * Re v + i K_BS * Im v`);
* `Bfn v g = B(v,g) = -(K_BS * v)·∇g` (`eq:ring`); `bsNorm v x = |(K_BS * v)(x)|`;
* `ringRHS χ G h v = L(G)v + B(v,v) - h·∇v - h·∇Φ`, the right side of `eq:ring`;
* `PathC s T u`: `u ∈ C([0,T]; X^s)`; `PathC1 s T u u'`: `u ∈ C¹([0,T]; X^s)` with derivative
  `u'` (both through `Sect.toY s annN`, so the derivative is taken in the Banach space `Y^s(N)`);
* `RingConfig.PertEq c χ T`: the conclusion of `lem:reduction`(3): for every `k`,
  `w ∈ C¹([0,T]; X^k)` and `∂_t w` is the right side of `eq:ring`;
* `Rapp χ G h wapp wapp'`: the residual `R_app` of `lem:energy`;
* `forcing χ h τ = F(τ) = -h(τ)·∇Φ` (`thm:quiet`, `lem:running`);
* `wlin0 χ s G w₀ h u = e^{uL}w₀ + ∫₀ᵘ e^{(u-v)L} F(v) dv` (`lem:running`) and
  `wlin χ s G h t = wlin0 χ s G 0 h t`, the linear response of `thm:quiet`(b) — in `Y^s(N)`;
* `runCoef χ G w₀ h u = c(u) = ℓ_*(w₀) + ∫₀ᵘ e^{-λ_* v} ℓ_*(F(v)) dv` (`eq:running`);
* `modeFn χ G X = 2 Re(X φ_*(G))` (`lem:running`, `thm:active`(b), `lem:seed`);
* `maj σ η t = ∫₀ᵗ e^{σ(t-τ)} η(τ) dτ`, the Duhamel majorant (`def:majorant`, with
  `σ = σ(G) = Eig.sigma χ G`).

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-! ### The terms of `eq:ring` -/

/-- The ring `Φ` (ring units, `Statement/Ring.lean`) as a complex function. -/
def PhiC (χ : ℝ → ℝ) (y : ℂ) : ℂ := ((ringPhi χ y : ℝ) : ℂ)

/-- `h·∇g = h₁∂₁g + h₂∂₂g` with the weak derivatives of `g` (`Sob.dotGrad`; `lem:bilinear`(2),(3),
`eq:ring`). The manuscript takes "the functions equal to these products on `N'` and to `0`
elsewhere" (`05_single_ring.tex:125-126`), because `h` is only given near `N'`. For the `g` that
occur (`g = w ∈ X^k`, which vanishes a.e. outside `N`, and `g = Φ`, supported in `{a ≤ |y| ≤ 1}`)
the weak gradient of `g` vanishes a.e. on the open set `ℂ ∖ N`, so this product is `0` a.e.
outside `N ⊂ N'` whatever the values of `h` there: it is the manuscript's function up to a null
set, and every statement (norms, `Sect.toY`, `ℓ_*`) only sees the a.e. class. We do not insert the
indicator of `N'`, so that `hGrad h Φ` is definitionally `Eig.hGradPhi χ h` (`hGrad_PhiC`), the
form used by `lem:uniform` (`I/Sec4/Uniform.lean`). -/
def hGrad (h g : ℂ → ℂ) : ℂ → ℂ := Sob.dotGrad h g

/-- `(K_BS * v)·∇g` for a complex function `v`: the complex vector field `K_BS * v` has real part
`K_BS * Re v` and imaginary part `K_BS * Im v` (`BS.velocityRe`, `BS.velocityIm`), so
`(K_BS * v)·∇g = (K_BS * Re v)·∇g + i (K_BS * Im v)·∇g`. -/
def bsGrad (v g : ℂ → ℂ) (x : ℂ) : ℂ :=
  Sob.dotGrad (BS.velocityRe v) g x + Complex.I * Sob.dotGrad (BS.velocityIm v) g x

/-- The quadratic term `B(v,g) = -(K_BS * v)·∇g` of `eq:ring` (`05_single_ring.tex:123`,
`lem:bilinear`(1), `:238`). -/
def Bfn (v g : ℂ → ℂ) (x : ℂ) : ℂ := -bsGrad v g x

/-- The Euclidean norm `|(K_BS * v)(x)|` of the complex vector `(K_BS * v)(x) ∈ ℂ²` for a complex
function `v`: `(|K_BS * Re v|² + |K_BS * Im v|²)^{1/2}` (`lem:bilinear`(4),
`05_single_ring.tex:242`); for real `v` it is `‖velocity v x‖`. -/
def bsNorm (v : ℂ → ℂ) (x : ℂ) : ℝ :=
  Real.sqrt (‖BS.velocityRe v x‖ ^ 2 + ‖BS.velocityIm v x‖ ^ 2)

/-- The right side of `eq:ring`, `L(G)v + B(v,v) - h·∇v - h·∇Φ` (`05_single_ring.tex:123`),
for a perturbation `v` and a field `h` (`hGrad`). The linearization `L(G)` is `Lin.Lfn χ G` (`-Ω(·;G)∂_θ v - (K_BS * v)·∇Φ`, `04_ring.tex:161-164`). -/
def ringRHS (χ : ℝ → ℝ) (G : ℝ) (h v : ℂ → ℂ) (x : ℂ) : ℂ :=
  Lin.Lfn χ G v x + Bfn v v x - hGrad h v x - hGrad h (PhiC χ) x

/-! ### Paths in `X^s` -/

/-- `u ∈ C([0,T]; X^s)`: every `u(t)`, `t ∈ [0,T]`, lies in `X^s` (`Lin.MemXFn`: `3`-fold
symmetric, in `H^s`, supported in `N`), and `t ↦ u(t)` is continuous on `[0,T]` into
`Y^s(N)` (whose norm is the `H^s` norm) (`lem:duhamel`, `05_single_ring.tex:51-56`). -/
def PathC (s : ℕ) (T : ℝ) (u : ℝ → ℂ → ℂ) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) T, Lin.MemXFn s (u t)) ∧
    ContinuousOn (fun t => Sect.toY s annN (u t)) (Icc (0 : ℝ) T)

/-- `u ∈ C¹([0,T]; X^s)` with derivative `u'`: `u, u' ∈ C([0,T]; X^s)` and `u'(t)` is the
derivative of `t ↦ u(t)` in `Y^s(N)` within `[0,T]` (one-sided at the end points)
(`lem:duhamel`, `lem:reduction`(3), `lem:energy`). The manuscript's
`u ∈ C([0,T];X^k) ∩ C¹([0,T];X^{k-1})` with `∂_t u = u'` is `PathC k T u ∧ PathC1 (k-1) T u u'`. -/
def PathC1 (s : ℕ) (T : ℝ) (u u' : ℝ → ℂ → ℂ) : Prop :=
  PathC s T u ∧ PathC s T u' ∧
    ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun t => Sect.toY s annN (u t)) (Sect.toY s annN (u' t)) (Icc (0 : ℝ) T) t

/-- **The conclusion of `lem:reduction`(3)** (`05_single_ring.tex:118-126`): for every integer
`k ≥ 0`, `w = ω_r - Φ` lies in `C¹([0,T]; X^k)`, and its time derivative in `X^k` is the right
side of `eq:ring`, `∂_t w = L(G)w + B(w,w) - h·∇w - h·∇Φ`. (`w` is real valued by construction,
`RingConfig.w_im`.) For a smooth `w` the `X^k`-derivative and the pointwise one agree a.e., so this
is the manuscript's pointwise equation on `[0,T] × ℝ²`. -/
def RingConfig.PertEq (c : RingConfig) (χ : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ k : ℕ, PathC1 k T (c.w χ) (fun t => ringRHS χ c.G (c.h t) (c.w χ t))

/-- The residual `R_app = ∂_t w_app - (L(G)w_app + B(w_app,w_app) - h·∇w_app - h·∇Φ)` of
`lem:energy` (`05_single_ring.tex:308-310`), for an approximate solution `w_app` with time
derivative `w_app'` and a field `h(τ)`. -/
def Rapp (χ : ℝ → ℝ) (G : ℝ) (h : ℝ → ℂ → ℂ) (wapp wapp' : ℝ → ℂ → ℂ) (τ : ℝ) (x : ℂ) : ℂ :=
  wapp' τ x - ringRHS χ G (h τ) (wapp τ) x

/-! ### The linear response and the running coefficient -/

/-- The forcing `F(τ) = -h(τ)·∇Φ` (`hGrad`; `= -Eig.hGradPhi χ (h τ)`, `forcing_eq`) of the
linear response
(`thm:quiet`(b), `05_single_ring.tex:425`; `lem:running`, `:591`; `09_relay.tex`, `eq:running-k`). -/
def forcing (χ : ℝ → ℝ) (h : ℝ → ℂ → ℂ) (τ : ℝ) (x : ℂ) : ℂ :=
  -hGrad (h τ) (PhiC χ) x

/-- `wlin₀(u) = e^{uL(G)} w₀ + ∫₀ᵘ e^{(u-v)L(G)} F(v) dv` in `Y^s(N)` (`lem:running`,
`05_single_ring.tex:597`), with `F = forcing χ h`; the plane functions `w₀`, `F(v)` enter
through `Sect.toY s annN` (they lie in `X^s` in every application). -/
def wlin0 (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) (w₀ : ℂ → ℂ) (h : ℝ → ℂ → ℂ) (u : ℝ) : Sect.Y s annN :=
  Lin.duhamel χ s G (Sect.toY s annN w₀) (fun v => Sect.toY s annN (forcing χ h v)) u

/-- The **linear response** `wlin(t) = ∫₀ᵗ e^{(t-τ)L(G)}(-h(τ)·∇Φ) dτ` of `thm:quiet`(b)
(`05_single_ring.tex:424-426`), in `Y^s(N)`: `wlin0` with `w₀ = 0`. -/
def wlin (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) (h : ℝ → ℂ → ℂ) (t : ℝ) : Sect.Y s annN :=
  wlin0 χ s G 0 h t

/-- The **running coefficient** `c(u) = ℓ_*(w₀) + ∫₀ᵘ e^{-λ_* v} ℓ_*(F(v)) dv` (`eq:running`,
`05_single_ring.tex:592-595`), with `ℓ_* = ℓ_*(G)` on functions (`Eig.ellFn`),
`λ_* = λ_*(G)` (`Eig.lam`) and `F = forcing χ h`. -/
def runCoef (χ : ℝ → ℝ) (G : ℝ) (w₀ : ℂ → ℂ) (h : ℝ → ℂ → ℂ) (u : ℝ) : ℂ :=
  Eig.ellFn χ G w₀ +
    ∫ v in (0 : ℝ)..u, Complex.exp (-(Eig.lam χ G * v)) * Eig.ellFn χ G (forcing χ h v)

/-- The real function `2 Re(X φ_*(G))` (`lem:running`, `05_single_ring.tex:599`;
`thm:active`(b), `:897`; `lem:seed` with `X = κ`, `G = 0`). -/
def modeFn (χ : ℝ → ℝ) (G : ℝ) (X : ℂ) (x : ℂ) : ℂ :=
  ((2 * (X * Eig.phi χ G x).re : ℝ) : ℂ)

/-! ### The Duhamel majorant (`def:majorant`) -/

/-- The **Duhamel majorant** `maj(t) = ∫₀ᵗ e^{σ(t-τ)} η(τ) dτ` (`def:majorant`,
`05_single_ring.tex:383-388`), with `σ = σ(G)` (`Eig.sigma χ G`). The manuscript takes
`η : [0,T] → [0,∞)` integrable; carry these hypotheses (the interval integral is `0` for a
non-integrable `η`). -/
def maj (σ : ℝ) (η : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..t, Real.exp (σ * (t - τ)) * η τ

/-! ### Basic lemmas (fully proved) -/

theorem hGrad_eq (h g : ℂ → ℂ) : hGrad h g = Sob.dotGrad h g := rfl

/-- `h·∇Φ` is the field term `Eig.hGradPhi` of `lem:uniform` (`I/Sec4/Uniform.lean`). -/
theorem hGrad_PhiC (χ : ℝ → ℝ) (h : ℂ → ℂ) : hGrad h (PhiC χ) = Eig.hGradPhi χ h := rfl

theorem forcing_eq (χ : ℝ → ℝ) (h : ℝ → ℂ → ℂ) (τ : ℝ) :
    forcing χ h τ = fun x => -Eig.hGradPhi χ (h τ) x := rfl

theorem ringRHS_apply (χ : ℝ → ℝ) (G : ℝ) (h v : ℂ → ℂ) (x : ℂ) :
    ringRHS χ G h v x = Lin.Lfn χ G v x + Bfn v v x - hGrad h v x - hGrad h (PhiC χ) x := rfl

theorem PathC1.pathC {s : ℕ} {T : ℝ} {u u' : ℝ → ℂ → ℂ} (h : PathC1 s T u u') : PathC s T u :=
  h.1

theorem PathC1.pathC_deriv {s : ℕ} {T : ℝ} {u u' : ℝ → ℂ → ℂ} (h : PathC1 s T u u') :
    PathC s T u' :=
  h.2.1

theorem wlin_def (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) (h : ℝ → ℂ → ℂ) (t : ℝ) :
    wlin χ s G h t = wlin0 χ s G 0 h t := rfl

theorem wlin0_def (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) (w₀ : ℂ → ℂ) (h : ℝ → ℂ → ℂ) (u : ℝ) :
    wlin0 χ s G w₀ h u =
      Lin.S χ s G u (Sect.toY s annN w₀) +
        ∫ v in (0 : ℝ)..u, Lin.S χ s G (u - v) (Sect.toY s annN (forcing χ h v)) := rfl

theorem runCoef_zero (χ : ℝ → ℝ) (G : ℝ) (w₀ : ℂ → ℂ) (h : ℝ → ℂ → ℂ) :
    runCoef χ G w₀ h 0 = Eig.ellFn χ G w₀ := by
  simp [runCoef]

theorem modeFn_im (χ : ℝ → ℝ) (G : ℝ) (X : ℂ) (x : ℂ) : (modeFn χ G X x).im = 0 := by
  simp [modeFn]

theorem bsNorm_nonneg (v : ℂ → ℂ) (x : ℂ) : 0 ≤ bsNorm v x := Real.sqrt_nonneg _

theorem maj_zero (σ : ℝ) (η : ℝ → ℝ) : maj σ η 0 = 0 := by
  simp [maj]

end OneRing

end NonUniqueEuler
