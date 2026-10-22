import NonUniqueEuler.Defs.Sec4.Linear
import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.Defs.Infra.Multipole

/-!
# Section 4.5: the unstable eigenvalue, `(S_U)`, the eigendata and the uniform constants
(definitions)

Manuscript `04_ring.tex`:
`cor:sector-3` (`:1205-1216`: `λ_*^c(G)`), `def:SU` (`:1241-1251`), `prop:SU` (`:1253-1267`:
`λ_*(G) = λ_*^c(R_c² G)`), `def:eigendata` (`:1303-1338`), `prop:U` (`:1340-1354`),
`lem:uniform` (`:1502-1535`). Namespace `NonUniqueEuler.Eig`.

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
* The constants of `lem:uniform` that later sections use by value (`10_parameters.tex:35-44`)
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
/-- `λ_*^c(G)` (`cor:sector-3`, `04_ring.tex:1209-1210`, reference units): the zero of
`E_3(·;G)` in `{Re λ ≥ 9/200}` given by (N1) (chosen; `0` if it is not unique). -/
def lamC (χ : ℝ → ℝ) (G : ℝ) : ℂ :=
  if h : ∃! z : ℂ, 9 / 200 ≤ z.re ∧ evans χ 3 z G = 0 then h.exists.choose else 0

/-- `λ_*(G) = λ_*^c(R_c² G)`, the unstable eigenvalue in ring units (`prop:SU`,
`04_ring.tex:1256-1258`). -/
def lam (χ : ℝ → ℝ) (G : ℝ) : ℂ := lamC χ (Rc ^ 2 * G)

/-- `σ(G) = Re λ_*(G)` (`04_ring.tex:1311`). The manuscript's `σ` is `sigma χ 0`. -/
def sigma (χ : ℝ → ℝ) (G : ℝ) : ℝ := (lam χ G).re

/-- `ν(G) = -Im λ_*(G)` (`04_ring.tex:1312`). -/
def nu (χ : ℝ → ℝ) (G : ℝ) : ℝ := -(lam χ G).im

/-- `z = λ_*(0)` (`04_ring.tex:1323`). -/
def z (χ : ℝ → ℝ) : ℂ := lam χ 0

/-- `σ_b = min_{G ∈ [0,G₁]} σ(G)` (`04_ring.tex:1323`), as an infimum (attained by `prop:U`(a)). -/
def sigb (χ : ℝ → ℝ) : ℝ := sInf (sigma χ '' Icc 0 Gbar)

/-! ### `def:SU` (`04_ring.tex:1241-1251`) -/

/-- **`(S_U)` holds with gap `σ₂`** (`def:SU`, `04_ring.tex:1241-1251`; the manuscript assumes
`σ₂ ≥ 0`): for every `G ∈ [0,G₁]` there is `λ_*` with `Re λ_* > σ₂` such that for every `s`,
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

/-! ### `def:eigendata` (`04_ring.tex:1303-1338`) -/

/-- `ψ_*(G) = ψ_3(·;λ_*(G),G)` in ring units (normalized at `ξ₁ = ξL - ξR`). -/
def psistar (χ : ℝ → ℝ) (G : ℝ) : ℝ → ℂ := (ringPhiSetting χ).psi 3 (lam χ G) G

/-- The eigenprofile `g_*(G) = M_* k_3 ψ_*(log r)` in ring units (`04_ring.tex:1307`). -/
def gstar (χ : ℝ → ℝ) (G : ℝ) : ℝ → ℂ := (ringPhiSetting χ).gStar 3 (lam χ G) G

/-- `J(G)` of `thm:evans-simple` in ring units (`04_ring.tex:1307`). -/
def J (χ : ℝ → ℝ) (G : ℝ) : ℂ := (ringPhiSetting χ).J 3 (lam χ G) G

/-- `n_*(G) = ‖g_* e^{3iθ}‖_{L²(ℝ²)}` (`04_ring.tex:1308`). -/
def nstar (χ : ℝ → ℝ) (G : ℝ) : ℝ := Sob.l2 (Ang.ofProfile 3 (gstar χ G))

/-- The normalized eigenfunction `φ_*(G) = n_*⁻¹ g_*(r) e^{3iθ}` (`04_ring.tex:1310`). -/
def phi (χ : ℝ → ℝ) (G : ℝ) (x : ℂ) : ℂ :=
  ((nstar χ G : ℝ) : ℂ)⁻¹ * Ang.ofProfile 3 (gstar χ G) x

/-- `φ_*(G)` as an element of `Y^s(N)` (it lies in `X^s` for every `s`). -/
def phiY (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Y s annN := toY s annN (phi χ G)

/-- The functional `ℓ_*(G)(w) = n_*(G) ℓ_*(w_3)` on functions `w ∈ L²(N)` (`04_ring.tex:1313-1317`),
with `w_3` the sector-`3` profile and `ℓ_*` the functional of `thm:evans-simple`. -/
def ellFn (χ : ℝ → ℝ) (G : ℝ) (w : ℂ → ℂ) : ℂ :=
  ((nstar χ G : ℝ) : ℂ) * (ringPhiSetting χ).ellStar 3 (lam χ G) G (Polar.angularSector w 3)

open Classical in
/-- `ℓ_*(G)` as a continuous functional on `Y^s(N)` (chosen). On `Y^0(N) = L²(N)` its norm is
the manuscript's `‖ℓ_*(G)‖_{(X^0)^*}` (its representer lies in `X^0`, `04_ring.tex:1333-1338`). -/
def ell (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Y s annN →L[ℂ] ℂ :=
  if h : ∃ T : Y s annN →L[ℂ] ℂ, ∀ w : Y s annN, T w = ellFn χ G w.fn then h.choose else 0

/-- `b(r) = -(i/2) r⁻⁴ Φ'(r)` (`04_ring.tex:1318`; `bfun` with `ℓ = 3`). -/
def bprof (χ : ℝ → ℝ) : ℝ → ℂ := (ringPhiSetting χ).bfun 3

/-- `β(G) = ℓ_*(G)(b e^{3iθ})` (`04_ring.tex:1318`). -/
def beta (χ : ℝ → ℝ) (G : ℝ) : ℂ := ellFn χ G (Ang.ofProfile 3 (bprof χ))

/-- `pout_*(G) = pout_3[φ_*(G)] = (2π)⁻¹ ∫ φ_*(y) ȳ³ dy` (`04_ring.tex:1319`, `def:multipole`,
`02_prelim.tex:449-457`). -/
def pout (χ : ℝ → ℝ) (G : ℝ) : ℂ := (2 * π : ℂ)⁻¹ * Multipole.conjMoment (phi χ G) 3

/-- `pin_3[φ_*(G)] = (2π)⁻¹ ∫ φ_*(y) y⁻³ dy` (`04_ring.tex:1331-1333`, `prop:U`(b)). -/
def pinPhi (χ : ℝ → ℝ) (G : ℝ) : ℂ := (2 * π : ℂ)⁻¹ * Multipole.moment (phi χ G) (-3)

/-- The Riesz projection of `prop:SU` on functions (R2, D10):
`R(G)w = ℓ_*(G)(w) φ_* + conj(ℓ_*(G)(conj w)) conj φ_*`, which is `2 Re(ℓ_*(G)(w) φ_*)` for real
`w` (`04_ring.tex:1320-1321`, `:1327-1330`). -/
def RFn (χ : ℝ → ℝ) (G : ℝ) (w : ℂ → ℂ) (x : ℂ) : ℂ :=
  ellFn χ G w * phi χ G x + conj (ellFn χ G fun y => conj (w y)) * conj (phi χ G x)

open Classical in
/-- The Riesz projection `R(G)` on `Y^s(N)` (chosen from `RFn`; `prop:SU`, `def:eigendata`). -/
def R (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Y s annN →L[ℂ] Y s annN :=
  if h : ∃ T : Y s annN →L[ℂ] Y s annN, ∀ w : Y s annN, (T w).fn =ᵐ[volume] RFn χ G w.fn
  then h.choose else 0

/-! ### The constants of `lem:uniform` (`04_ring.tex:1502-1535`) -/

/-- `‖ℓ_*‖ = max_{G ∈ [0,G₁]} ‖ℓ_*(G)‖_{(X^0)^*}` (`04_ring.tex:1516`). -/
def ellNorm (χ : ℝ → ℝ) : ℝ := sSup ((fun G => ‖ell χ 0 G‖) '' Icc 0 Gbar)

/-- `max_{G ∈ [0,G₁]} ‖φ_*(G)‖_{H^k}` (`04_ring.tex:1517`). -/
def phiNormMax (χ : ℝ → ℝ) (k : ℕ) : ℝ := sSup ((fun G => Sob.normH k (phi χ G)) '' Icc 0 Gbar)

/-- `c_N = min|β| · min|pout_*|` over `[0,G₁]` (`04_ring.tex:1509`). -/
def cN (χ : ℝ → ℝ) : ℝ :=
  sInf ((fun G => ‖beta χ G‖) '' Icc 0 Gbar) * sInf ((fun G => ‖pout χ G‖) '' Icc 0 Gbar)

/-- `C_N = max|β| · max|pout_*|` over `[0,G₁]` (`04_ring.tex:1510`). -/
def CN (χ : ℝ → ℝ) : ℝ :=
  sSup ((fun G => ‖beta χ G‖) '' Icc 0 Gbar) * sSup ((fun G => ‖pout χ G‖) '' Icc 0 Gbar)

/-- `c_out = 2π min|pout_*|` over `[0,G₁]` (`04_ring.tex:1511`). -/
def cout (χ : ℝ → ℝ) : ℝ := 2 * π * sInf ((fun G => ‖pout χ G‖) '' Icc 0 Gbar)

/-- `‖∇Φ‖_{L²(ℝ²)}`, with `|∇Φ(y)| = ‖DΦ(y)‖`. -/
def gradPhiL2 (χ : ℝ → ℝ) : ℝ := Sob.l2 fun y => ((‖fderiv ℝ (ringPhi χ) y‖ : ℝ) : ℂ)

/-- `C_ls = ‖ℓ_*‖ ‖∇Φ‖_{L²}` (`04_ring.tex:1531`). -/
def Cls (χ : ℝ → ℝ) : ℝ := ellNorm χ * gradPhiL2 χ

/-- `C_p = 4/√π` (`04_ring.tex:1531`). -/
def Cp : ℝ := 4 / Real.sqrt π

/-- `C_∇(k) = 2^k ((k+1)(k+2)/2)^{1/2} ‖Φ‖_{H^{k+1}}` (`04_ring.tex:1532`). The bound
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

/-- For real `w`, `R(G)w = 2 Re(ℓ_*(G)(w) φ_*)` pointwise (`04_ring.tex:1320-1321`). -/
theorem RFn_of_real (χ : ℝ → ℝ) (G : ℝ) (w : ℂ → ℂ) (hw : ∀ y, conj (w y) = w y) (x : ℂ) :
    RFn χ G w x = ((2 * (ellFn χ G w * phi χ G x).re : ℝ) : ℂ) := by
  have hw' : (fun y => conj (w y)) = w := funext hw
  rw [RFn, hw', ← map_mul, Complex.add_conj]

theorem sigma_eq (χ : ℝ → ℝ) (G : ℝ) : sigma χ G = (lamC χ (Rc ^ 2 * G)).re := rfl

end Eig

end NonUniqueEuler
