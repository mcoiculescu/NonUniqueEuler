import NonUniqueEuler.Defs.Sec4.Linear
import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.Defs.Infra.Multipole

/-!
# Part I Section 4.6: the unstable eigenvalue, `(S_U)`, the eigendata and the uniform constants
(definitions)

Current references in Part I Section 4.6: Corollary 4.18 (`cor:sector-3`) for
`λ_*^c(G)`, Proposition 4.19 (`prop:SU`) for `λ_*(G) = λ_*^c(R_c²G)` and spectral separation,
Definition 4.20 (`def:eigendata`), Proposition 4.21 (`prop:U`), and Lemma 4.23 (`lem:uniform`).
The variable-gap predicate `(S_U)` remains a Lean definition. Namespace `NonUniqueEuler.Eig`.

Choices (decisions D10, D11, restructurings R2, R9):
* `lamC χ G` is the zero of (N1): the unique `λ` with `Re λ ≥ 9/200` and `E_3(λ;G) = 0`, for the
  statement layer's Evans function `evans χ 3` (chosen with `∃!`; junk `0` without uniqueness).
  `lam χ G = lamC χ (R_c² G)` is `λ_*(G)` of `prop:SU` (ring units).
* The eigendata are computed in the ring-units setting `ringPhiSetting χ` with `ℓ = 3`:
  `g_*`, `J`, `n_*`, `φ_*`, `ℓ_*(G)`, `β`, `pout_*`, as in `def:eigendata`.
* `R χ s G` is the Riesz projection of `prop:SU` (R2: the explicit rank-two operator
  `w ↦ ℓ_*(G)(w) φ_* + conj(ℓ_*(G)(conj w)) conj φ_*`, D10), on `Y^s(N)`; for real `w` it is
  `2 Re(ℓ_*(G)(w) φ_*)`.
* `sigb χ` is `inf_{G ∈ [0,G₁]} σ(G)`; that it is attained is `prop:U`(a) (R9).
* The constants of `lem:uniform` that later sections use by value (Part II Definition C.1 (`def:standing`))
  are defined: `cN`, `CN`, `cout`, `ellNorm` (`‖ℓ_*‖`), `phiNormMax`, `Cls`, `Cp`, `Cnab`.

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Real ComplexConjugate

namespace NonUniqueEuler

namespace Eig

open RingData Sect

/-! ### The unstable eigenvalue -/

open Classical in
/-- `λ_*^c(G)` (Part I Corollary 4.18 (`cor:sector-3`), reference units): the zero of
`E_3(·;G)` in `{Re λ ≥ 9/200}` given by (N1) (chosen; `0` if it is not unique). -/
def lamC (χ : ℝ → ℝ) (G : ℝ) : ℂ :=
  if h : ∃! z : ℂ, 9 / 200 ≤ z.re ∧ evans χ 3 z G = 0 then h.exists.choose else 0

/-- `λ_*(G) = λ_*^c(R_c² G)`, the unstable eigenvalue in ring units (`prop:SU`,
Part I Proposition 4.19 (`prop:SU`)). -/
def lam (χ : ℝ → ℝ) (G : ℝ) : ℂ := lamC χ (Rc ^ 2 * G)

/-- `σ(G) = Re λ_*(G)` (Part I Definition 4.20 (`def:eigendata`)). The manuscript's `σ` is `sigma χ 0`. -/
def sigma (χ : ℝ → ℝ) (G : ℝ) : ℝ := (lam χ G).re

/-- `ν(G) = -Im λ_*(G)` (the retained notation `ν(G) = -Im λ_*(G)` associated with Part I Definition 4.20 (`def:eigendata`)). -/
def nu (χ : ℝ → ℝ) (G : ℝ) : ℝ := -(lam χ G).im

/-- `z = λ_*(0)` (Part I Definition 4.20 (`def:eigendata`)). -/
def z (χ : ℝ → ℝ) : ℂ := lam χ 0

/-- `σ_b = min_{G ∈ [0,G₁]} σ(G)` (Part I Definition 4.20 (`def:eigendata`)), as an infimum (attained by `prop:U`(a)). -/
def sigb (χ : ℝ → ℝ) : ℝ := sInf (sigma χ '' Icc 0 Gbar)

/-! ### The retained spectral predicate `(S_U)` -/

/-- **Retained spectral predicate `(S_U)` with gap `σ₂`.** Its specialization at
`σ₂ = 9/200` is the mode-wise conclusion of Part I Proposition 4.19 (`prop:SU`).
The earlier manuscript imposed `σ₂ ≥ 0`: for every `G ∈ [0,G₁]` there is `λ_*` with `Re λ_* > σ₂` such that for every `s`,
the spectrum of `L_3(G)` on `X^s_3` in `{Re > σ₂}` is `{λ_*}`, `λ_*` is algebraically simple there
(R2 form, `Dunford.IsAlgSimpleEig`), the spectrum of `L_{-3}(G)` on `X^s_{-3}` in `{Re > σ₂}` is
`{conj λ_*}`, and that of `L_ℓ(G)` on `X^s_ℓ` is empty for `ℓ ∈ 3ℤ \ {3, -3}`. -/
def SU (χ : ℝ → ℝ) (σ₂ : ℝ) : Prop :=
  ∀ G ∈ Icc (0 : ℝ) Gbar, ∃ l : ℂ, σ₂ < l.re ∧ ∀ s : ℕ,
    spectrum ℂ (Lin.Lsec χ s 3 G) ∩ {w : ℂ | σ₂ < w.re} = {l} ∧
    Dunford.IsAlgSimpleEig (Lin.Lsec χ s 3 G) l ∧
    spectrum ℂ (Lin.Lsec χ s (-3) G) ∩ {w : ℂ | σ₂ < w.re} = {conj l} ∧
    ∀ ℓ : ℤ, (3 : ℤ) ∣ ℓ → ℓ ≠ 3 → ℓ ≠ -3 →
      spectrum ℂ (Lin.Lsec χ s ℓ G) ∩ {w : ℂ | σ₂ < w.re} = ∅

/-! ### Part I Definition 4.20 (`def:eigendata`) -/

/-- `ψ_*(G) = ψ_3(·;λ_*(G),G)` in ring units (normalized at `ξ₁ = ξL - ξR`). -/
def psistar (χ : ℝ → ℝ) (G : ℝ) : ℝ → ℂ := (ringPhiSetting χ).psi 3 (lam χ G) G

/-- The eigenprofile `g_*(G) = M_* k_3 ψ_*(log r)` in ring units (Part I Definition 4.20 (`def:eigendata`)). -/
def gstar (χ : ℝ → ℝ) (G : ℝ) : ℝ → ℂ := (ringPhiSetting χ).gStar 3 (lam χ G) G

/-- `J(G)` of `thm:evans-simple` in ring units (Part I Definition 4.20 (`def:eigendata`)). -/
def J (χ : ℝ → ℝ) (G : ℝ) : ℂ := (ringPhiSetting χ).J 3 (lam χ G) G

/-- `n_*(G) = ‖g_* e^{3iθ}‖_{L²(ℝ²)}` (Part I Definition 4.20 (`def:eigendata`)). -/
def nstar (χ : ℝ → ℝ) (G : ℝ) : ℝ := Sob.l2 (Ang.ofProfile 3 (gstar χ G))

/-- The normalized eigenfunction `φ_*(G) = n_*⁻¹ g_*(r) e^{3iθ}` (Part I Definition 4.20 (`def:eigendata`)). -/
def phi (χ : ℝ → ℝ) (G : ℝ) (x : ℂ) : ℂ :=
  ((nstar χ G : ℝ) : ℂ)⁻¹ * Ang.ofProfile 3 (gstar χ G) x

/-- `φ_*(G)` as an element of `Y^s(N)` (it lies in `X^s` for every `s`). -/
def phiY (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Y s annN := toY s annN (phi χ G)

/-- The functional `ℓ_*(G)(w) = n_*(G) ℓ_*(w_3)` on functions `w ∈ L²(N)` (Part I Definition 4.20 (`def:eigendata`)),
with `w_3` the sector-`3` profile and `ℓ_*` the functional of `thm:evans-simple`. -/
def ellFn (χ : ℝ → ℝ) (G : ℝ) (w : ℂ → ℂ) : ℂ :=
  ((nstar χ G : ℝ) : ℂ) * (ringPhiSetting χ).ellStar 3 (lam χ G) G (Polar.angularSector w 3)

open Classical in
/-- `ℓ_*(G)` as a continuous functional on `Y^s(N)` (chosen). On `Y^0(N) = L²(N)` its norm is
the manuscript's `‖ℓ_*(G)‖_{(X^0)^*}` (its representer lies in `X^0`, Part I Definition 4.20 (`def:eigendata`)). -/
def ell (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Y s annN →L[ℂ] ℂ :=
  if h : ∃ T : Y s annN →L[ℂ] ℂ, ∀ w : Y s annN, T w = ellFn χ G w.fn then h.choose else 0

/-- `b(r) = -(i/2) r⁻⁴ Φ'(r)` (Part I Definition 4.20 (`def:eigendata`); `bfun` with `ℓ = 3`). -/
def bprof (χ : ℝ → ℝ) : ℝ → ℂ := (ringPhiSetting χ).bfun 3

/-- `β(G) = ℓ_*(G)(b e^{3iθ})` (Part I Definition 4.20 (`def:eigendata`)). -/
def beta (χ : ℝ → ℝ) (G : ℝ) : ℂ := ellFn χ G (Ang.ofProfile 3 (bprof χ))

/-- `pout_*(G) = pout_3[φ_*(G)] = (2π)⁻¹ ∫ φ_*(y) ȳ³ dy` (Part I Definition 4.20 (`def:eigendata`), `def:multipole`,
Part I Definition 2.3 (`def:multipole`)). -/
def pout (χ : ℝ → ℝ) (G : ℝ) : ℂ := (2 * π : ℂ)⁻¹ * Multipole.conjMoment (phi χ G) 3

/-- Retained inner-moment quantity `pin_3[φ_*(G)] = (2π)⁻¹ ∫ φ_*(y) y⁻³ dy`.
It is auxiliary to the formulas in the proof of Part I Proposition 4.21(b) (`prop:U`),
with eigendata from Part I Definition 4.20 (`def:eigendata`). -/
def pinPhi (χ : ℝ → ℝ) (G : ℝ) : ℂ := (2 * π : ℂ)⁻¹ * Multipole.moment (phi χ G) (-3)

/-- The Riesz projection of `prop:SU` on functions (R2, D10):
`R(G)w = ℓ_*(G)(w) φ_* + conj(ℓ_*(G)(conj w)) conj φ_*`, which is `2 Re(ℓ_*(G)(w) φ_*)` for real
`w` (Part I Definition 4.20 (`def:eigendata`)). -/
def RFn (χ : ℝ → ℝ) (G : ℝ) (w : ℂ → ℂ) (x : ℂ) : ℂ :=
  ellFn χ G w * phi χ G x + conj (ellFn χ G fun y => conj (w y)) * conj (phi χ G x)

open Classical in
/-- The Riesz projection `R(G)` on `Y^s(N)` (chosen from `RFn`; `prop:SU`, `def:eigendata`). -/
def R (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Y s annN →L[ℂ] Y s annN :=
  if h : ∃ T : Y s annN →L[ℂ] Y s annN, ∀ w : Y s annN, (T w).fn =ᵐ[volume] RFn χ G w.fn
  then h.choose else 0

/-! ### The constants of Part I Lemma 4.23 (`lem:uniform`) -/

/-- `‖ℓ_*‖ = max_{G ∈ [0,G₁]} ‖ℓ_*(G)‖_{(X^0)^*}` (Part I Lemma 4.23 (`lem:uniform`)). -/
def ellNorm (χ : ℝ → ℝ) : ℝ := sSup ((fun G => ‖ell χ 0 G‖) '' Icc 0 Gbar)

/-- `max_{G ∈ [0,G₁]} ‖φ_*(G)‖_{H^k}` (Part I Lemma 4.23 (`lem:uniform`)). -/
def phiNormMax (χ : ℝ → ℝ) (k : ℕ) : ℝ := sSup ((fun G => Sob.normH k (phi χ G)) '' Icc 0 Gbar)

/-- `c_N = min|β| · min|pout_*|` over `[0,G₁]` (Part I Lemma 4.23 (`lem:uniform`)). -/
def cN (χ : ℝ → ℝ) : ℝ :=
  sInf ((fun G => ‖beta χ G‖) '' Icc 0 Gbar) * sInf ((fun G => ‖pout χ G‖) '' Icc 0 Gbar)

/-- `C_N = max|β| · max|pout_*|` over `[0,G₁]` (Part I Lemma 4.23 (`lem:uniform`)). -/
def CN (χ : ℝ → ℝ) : ℝ :=
  sSup ((fun G => ‖beta χ G‖) '' Icc 0 Gbar) * sSup ((fun G => ‖pout χ G‖) '' Icc 0 Gbar)

/-- `c_out = 2π min|pout_*|` over `[0,G₁]` (Part I Lemma 4.23 (`lem:uniform`)). -/
def cout (χ : ℝ → ℝ) : ℝ := 2 * π * sInf ((fun G => ‖pout χ G‖) '' Icc 0 Gbar)

/-- `‖∇Φ‖_{L²(ℝ²)}`, with `|∇Φ(y)| = ‖DΦ(y)‖`. -/
def gradPhiL2 (χ : ℝ → ℝ) : ℝ := Sob.l2 fun y => ((‖fderiv ℝ (ringPhi χ) y‖ : ℝ) : ℂ)

/-- `C_ls = ‖ℓ_*‖ ‖∇Φ‖_{L²}` (Part I Lemma 4.23 (`lem:uniform`)). -/
def Cls (χ : ℝ → ℝ) : ℝ := ellNorm χ * gradPhiL2 χ

/-- `C_p = 4/√π` (Part I Lemma 4.23 (`lem:uniform`)). -/
def Cp : ℝ := 4 / Real.sqrt π

/-- `C_∇(k) = 2^k ((k+1)(k+2)/2)^{1/2} ‖Φ‖_{H^{k+1}}` (Part I Lemma 4.23 (`lem:uniform`)). The bound
`‖h·∇Φ‖_{H^k} ≤ C_∇(k) ‖h‖_{C^k(N')}` holds with this constant also for the operator-norm
`C^k` norms of `normCk` (each `|∂^β h(x)|` is at most `‖D^{|β|} h(x)‖`). -/
def Cnab (χ : ℝ → ℝ) (k : ℕ) : ℝ :=
  2 ^ k * Real.sqrt (((k : ℝ) + 1) * ((k : ℝ) + 2) / 2) *
    Sob.normH (k + 1) fun y => ((ringPhi χ y : ℝ) : ℂ)

/-! ### Basic lemmas (fully proved) -/

theorem lamC_spec_of_existsUnique {χ : ℝ → ℝ} {G : ℝ}
    (h : ∃! z : ℂ, 9 / 200 ≤ z.re ∧ evans χ 3 z G = 0) :
    9 / 200 ≤ (lamC χ G).re ∧ evans χ 3 (lamC χ G) G = 0 := by
  classical
  rw [lamC, dite_eq_left h]
  exact h.exists.choose_spec

theorem lamC_eq_of_existsUnique {χ : ℝ → ℝ} {G : ℝ}
    (h : ∃! z : ℂ, 9 / 200 ≤ z.re ∧ evans χ 3 z G = 0) {z₀ : ℂ}
    (hz₀ : 9 / 200 ≤ z₀.re ∧ evans χ 3 z₀ G = 0) : lamC χ G = z₀ :=
  h.unique (lamC_spec_of_existsUnique h) hz₀

theorem ell_spec_of_exists {χ : ℝ → ℝ} {s : ℕ} {G : ℝ}
    (h : ∃ T : Y s annN →L[ℂ] ℂ, ∀ w : Y s annN, T w = ellFn χ G w.fn) (w : Y s annN) :
    ell χ s G w = ellFn χ G w.fn := by
  classical
  rw [ell, dite_eq_left h]
  exact h.choose_spec w

theorem R_spec_of_exists {χ : ℝ → ℝ} {s : ℕ} {G : ℝ}
    (h : ∃ T : Y s annN →L[ℂ] Y s annN, ∀ w : Y s annN, (T w).fn =ᵐ[volume] RFn χ G w.fn)
    (w : Y s annN) : (R χ s G w).fn =ᵐ[volume] RFn χ G w.fn := by
  classical
  rw [R, dite_eq_left h]
  exact h.choose_spec w

/-- For real `w`, `R(G)w = 2 Re(ℓ_*(G)(w) φ_*)` pointwise (Part I Definition 4.20 (`def:eigendata`)). -/
theorem RFn_of_real (χ : ℝ → ℝ) (G : ℝ) (w : ℂ → ℂ) (hw : ∀ y, conj (w y) = w y) (x : ℂ) :
    RFn χ G w x = ((2 * (ellFn χ G w * phi χ G x).re : ℝ) : ℂ) := by
  have hw' : (fun y => conj (w y)) = w := funext hw
  rw [RFn, hw', ← map_mul, Complex.add_conj]

theorem sigma_eq (χ : ℝ → ℝ) (G : ℝ) : sigma χ G = (lamC χ (Rc ^ 2 * G)).re := rfl

end Eig

end NonUniqueEuler
