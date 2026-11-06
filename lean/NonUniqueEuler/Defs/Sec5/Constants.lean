import NonUniqueEuler.Defs.Sec5.RingEq
import NonUniqueEuler.Defs.Sec2.HkCalculus
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Part II Section 2: the fixed auxiliary objects and the named constants (definitions)

Current manuscript: Part II Section 2 (`sec:single`), in
`manuscript/part2/sections/05_single_ring.tex`. The cutoffs are fixed before
Lemma 2.3 (`lem:bilinear`); the energy rate is specified in Lemma 2.4 (`lem:energy`)
and Equation (7) (`eq:Lambda`); Equation (15) (`eq:W-const`) fixes the window
orders, and Theorem 2.8 (`thm:quiet`) fixes `M_h`. The semigroup constant comes
from Part I Proposition 4.22 (`prop:semigroup`), and the linear-response constant
from Part II Lemma 2.10 (`lem:linear-part`).

This module retains the explicit constant choices of the Lean proof decomposition.
The current manuscript combines `C_B` and `C_h` into a constant `C_bil(k)` in
Lemma 2.3, and asks for a sufficiently large `Λ(s)` in Lemma 2.4. The formulas
for `n_s`, `C_HK`, `C_Ω`, `C_{N'}`, `A_s` and `Λ(s)` below are the retained
explicit choice, not formulas asserted by the current Equation (7), which only
requires `Λ(s) ≥ 2 max_G σ(G)`. Likewise, `Clin` gives a concrete constant for the
bound proved in Lemma 2.10.

Namespace `NonUniqueEuler.OneRing`. Decision D11: constants whose values later definitions use
are defined here (`Λ(s)`, `N_G`, `M`, `N_W`, `C_B`, `C_BS`, `C_h`, …); constants that the
manuscript obtains from a lemma are chosen by `Classical.choose` (here only through
`Sob.hkCalcConst`, `Sob.elConst` of `Defs/Sec2/HkCalculus.lean`); suprema and "least constants"
are `sSup`/`sInf` (junk `0` when unbounded or empty; their finiteness is part of the lemma that
introduces them).

* `chiB`: the cutoff `χ_B ∈ C_c^∞(B_4)`, `χ_B = 1` on `B_{7/2}` (a concrete `ContDiffBump` with
  radii `7/2`, `15/4`). The cutoff `χ_N` fixed before Part II Lemma 2.3 is not needed as a
  definition: `C_P(k)` (`Sob.hkCalcConst`) does not depend on it (any `χ_N` with
  `Sob.HkCalcSetting annN annN1 χN` witnesses its existence);
* `CP k = C_P(k)` (`Sob.hkCalcConst (max k 3) N N₁`), `Cel j = C^el_j` (`Sob.elConst j χ_B 4`);
* `CB k = C_B(k) = 2 C_P(k) C^el_{k-1}`, `CBS = C_BS = 2 C^el_1`, `Ch k = C_h(k)` (a supremum);
* `nIdx s = n_s`, `CHK s = C_HK = C_P(s)`, `omegaField χ G = Ω(|x|;G) x^⊥`, `COmega χ s = C_Ω`,
  `CNprime s = C_{N'}`, `As χ s = A_s`, `sigmaMax χ = max_{[0,G₁]} σ`, `Lam χ s = Λ(s)`;
* `pW = p = 3`, `NG χ s = N_G`, `Mact χ s = M = s + N_G + 2`, `NW χ s = N_W`, `Mh s_h N_Q = M_h`;
* `varsigma χ x = ς(x) = 1 + σ_b⁻¹ log(1/x)`;
* `IsSemigroupConst χ s σ' C`: `C` is a constant `C_S(s,σ')` of `prop:semigroup` (the three
  operator bounds); `Clin χ k σ' C_S = C_lin(k)` of `lem:linear-part` for that `C_S`.

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace OneRing

open RingData

/-! ### The cutoff `χ_B` and the constants of `lem:Hk-calculus` (Part II Lemma 2.3 (`lem:bilinear`)) -/

/-- The bump function behind `χ_B`: equal to `1` on `\bar B_{7/2}`, support `B_{15/4}`. -/
def chiBBump : ContDiffBump (0 : ℂ) where
  rIn := 7 / 2
  rOut := 15 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- **The cutoff `χ_B ∈ C_c^∞(B_4)` with `χ_B = 1` on `B_{7/2}`** (Part II Lemma 2.3 (`lem:bilinear`)),
fixed once and for all as a concrete smooth bump (any such function would do). -/
def chiB (x : ℂ) : ℝ := chiBBump x

/-- `C_P(k)`: the constant of `lem:Hk-calculus` for `max(k,3)`, the compact set `N`, the open set
`N₁` (and `χ_N`) (Part II Lemma 2.3 (`lem:bilinear`); `Sob.hkCalcConst`, chosen). It depends only on
`k` and `a`. -/
def CP (k : ℕ) : ℝ := Sob.hkCalcConst (max k 3) annN annN1

/-- `C^el_j`: the constant of `lem:Hk-calculus`(3) for `j`, `χ_B` and `ρ = 4`
(Part II Lemma 2.3 (`lem:bilinear`); `Sob.elConst`, chosen). It depends only on `j`. -/
def Cel (j : ℕ) : ℝ := Sob.elConst j chiB 4

/-- `C_B = C_B(k) = 2 C_P(k) C^el_{k-1}` (`lem:bilinear`, Part II Lemma 2.3). -/
def CB (k : ℕ) : ℝ := 2 * CP k * Cel (k - 1)

/-- `C_BS = 2 C^el_1` (`lem:bilinear`, Part II Lemma 2.3). -/
def CBS : ℝ := 2 * Cel 1

/-- `C_h = C_h(k)`: the supremum of `‖h·∇w‖_{H^k}` over all `w ∈ X^{k+1}` and
`h ∈ C^k(N';ℝ²)` with `‖w‖_{H^{k+1}} ≤ 1` and `‖h‖_{C^k(N')} ≤ 1` (`lem:bilinear`,
Part II Lemma 2.3); its finiteness is part of `lem:bilinear`. -/
def Ch (k : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ v hf : ℂ → ℂ, Lin.MemXFn (k + 1) v ∧ Sob.normH (k + 1) v ≤ 1 ∧
    MemCk k annN' hf ∧ normCk k annN' hf ≤ 1 ∧ x = Sob.normH k (hGrad hf v)}

/-! ### The retained explicit energy rate for Part II Lemma 2.4 (`lem:energy`) -/

/-- `n_s`, the number of multi-indices `α ∈ ℕ₀²` with `|α| ≤ s` (Part II Lemma 2.4 (`lem:energy`)). -/
def nIdx (s : ℕ) : ℕ := (Sob.multiIdx s).card

/-- `C_HK = C_P(s)` (Part II Lemma 2.4 (`lem:energy`)). -/
def CHK (s : ℕ) : ℝ := CP s

/-- The background field `Ω(|x|;G) x^⊥` of `(Φ, G)` (`x^⊥ = i x`; Part II Lemma 2.4 (`lem:energy`),
`lem:reduction`(2)). -/
def omegaField (χ : ℝ → ℝ) (G : ℝ) (x : ℂ) : ℂ :=
  ((Lin.Omega χ G ‖x‖ : ℝ) : ℂ) * (Complex.I * x)

/-- `C_Ω = sup_{G ∈ [0,G₁]} (‖Ω(|x|;G)x^⊥‖_{W^{1,∞}(N₁)} + ‖Ω(|x|;G)x^⊥‖_{H^s(N₁)})`
(Part II Lemma 2.4 (`lem:energy`)). -/
def COmega (χ : ℝ → ℝ) (s : ℕ) : ℝ :=
  sSup ((fun G => Sob.normW1infOn annN1 (omegaField χ G) +
      Sob.normHOn s annN1 (omegaField χ G)) ''
    Icc 0 Gbar)

/-- `C_{N'}`: the least constant with `‖h‖_{W^{1,∞}(N₁)} + ‖h‖_{H^s(N₁)} ≤ C_{N'} ‖h‖_{C^s(N')}`
for every `h ∈ C^s(N';ℝ²)` (Part II Lemma 2.4 (`lem:energy`)), as an infimum of the admissible
nonnegative constants. -/
def CNprime (s : ℕ) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ hf : ℂ → ℂ, MemCk s annN' hf →
    Sob.normW1infOn annN1 hf + Sob.normHOn s annN1 hf ≤ C * normCk s annN' hf}

/-- `A_s = C_Ω + C_{N'} + C^el_s + 6 C^el_2` (Part II Lemma 2.4 (`lem:energy`)). -/
def As (χ : ℝ → ℝ) (s : ℕ) : ℝ := COmega χ s + CNprime s + Cel s + 6 * Cel 2

/-- `σ_max = max_{G ∈ [0,G₁]} σ(G)` (Part II Lemma 2.4 (`lem:energy`), `thm:active`, Part II Theorem 2.12), as a
supremum (attained by `prop:U`(a)). -/
def sigmaMax (χ : ℝ → ℝ) : ℝ := sSup (Eig.sigma χ '' Icc 0 Gbar)

/-- **The retained explicit choice of `Λ(s)`** for Part II Lemma 2.4 (`lem:energy`),
subject to Equation (7) (`eq:Lambda`):
`Λ(s) = max(2 max_G σ(G), n_s C_HK A_s + 2 C_HK C^el_{s-1} (‖Φ‖_{H^{s+1}} + 1))`. -/
def Lam (χ : ℝ → ℝ) (s : ℕ) : ℝ :=
  max (2 * sigmaMax χ)
    (nIdx s * CHK s * As χ s + 2 * CHK s * Cel (s - 1) * (Sob.normH (s + 1) (PhiC χ) + 1))

/-! ### The numbers of Part II Equation (15) (`eq:W-const`) and `M_h` -/

/-- `p = 3` (`= m`) (`eq:W-const`, `thm:active`). -/
abbrev pW : ℕ := 3

/-- `N_G = min{n ∈ ℤ : n ≥ 2, n ≥ Λ(s)/σ_b + 1}` (`eq:W-const`, Part II Equation (15);
`thm:active`, Part II Theorem 2.12). -/
def NG (χ : ℝ → ℝ) (s : ℕ) : ℕ := max 2 ⌈Lam χ s / Eig.sigb χ + 1⌉₊

/-- `M = s + N_G + 2` (`eq:W-const`, `thm:active`, `lem:seed`). -/
def Mact (χ : ℝ → ℝ) (s : ℕ) : ℕ := s + NG χ s + 2

/-- `N_W = (p+2) N_G + 1` (`eq:W-const`, Part II Equation (15)). -/
def NW (χ : ℝ → ℝ) (s : ℕ) : ℕ := (pW + 2) * NG χ s + 1

/-- `M_h = s_h + N_Q + 1` (`thm:quiet`, Part II Theorem 2.8). -/
def Mh (sh NQ : ℕ) : ℕ := sh + NQ + 1

/-- `ς(x) = 1 + σ_b⁻¹ log(1/x)` for `x ∈ (0,1]`, defined before Part II
Equation (15) (`eq:W-const`). -/
def varsigma (χ : ℝ → ℝ) (x : ℝ) : ℝ := 1 + (Eig.sigb χ)⁻¹ * Real.log (1 / x)

/-! ### `C_S` of `prop:semigroup` and `C_lin(k)` of `lem:linear-part` -/

/-- `C` is a constant `C_S(s,σ')` of Part I Proposition 4.22 (`prop:semigroup`): for every
`G ∈ [0,G₁]`, `t ≥ 0` and `w ∈ X^s`,
`‖e^{tL(G)}(1 - R(G))w‖ ≤ C e^{σ't}‖w‖`, `‖R(G)w‖ ≤ C‖w‖`, `‖e^{tL(G)}w‖ ≤ C e^{σ(G)t}‖w‖`
(operator norms on `X^s`, the `H^s` norm being the norm of `Y^s(N)`). The two identities of
`prop:semigroup` do not involve `C` and are not part of this property. The body is exactly the
one of `Eig.propSemigroup_bounds` (`I/Sec4/PropSemigroup.lean`), so that theorem's conclusion is
definitionally `∃ C, 0 < C ∧ IsSemigroupConst χ s σ' C`. -/
def IsSemigroupConst (χ : ℝ → ℝ) (s : ℕ) (σ' C : ℝ) : Prop :=
  ∀ G ∈ Icc (0 : ℝ) Gbar, ∀ t : ℝ, 0 ≤ t →
    (∀ w : Sect.Y s annN, Lin.MemX w →
      ‖Lin.S χ s G t (w - Eig.R χ s G w)‖ ≤ C * Real.exp (σ' * t) * ‖w‖) ∧
      (∀ w : Sect.Y s annN, Lin.MemX w → ‖Eig.R χ s G w‖ ≤ C * ‖w‖) ∧
      (∀ w : Sect.Y s annN, Lin.MemX w →
        ‖Lin.S χ s G t w‖ ≤ C * Real.exp (Eig.sigma χ G * t) * ‖w‖)

/-- `C_lin(k) = C_S(k,σ')(1 + C_∇(k)/σ' + C_∇(k)/(σ_b - σ'))` (`lem:linear-part`,
Part II Lemma 2.10), for a given constant `C_S = C_S(k,σ')` of `prop:semigroup`. -/
def Clin (χ : ℝ → ℝ) (k : ℕ) (σ' CS : ℝ) : ℝ :=
  CS * (1 + Eig.Cnab χ k / σ' + Eig.Cnab χ k / (Eig.sigb χ - σ'))

/-! ### Basic lemmas (fully proved) -/

theorem chiB_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chiB :=
  chiBBump.contDiff

theorem tsupport_chiB : tsupport chiB = closedBall 0 (15 / 4) :=
  chiBBump.tsupport_eq

theorem tsupport_chiB_subset : tsupport chiB ⊆ ball 0 4 := by
  rw [tsupport_chiB]
  exact closedBall_subset_ball (by norm_num)

theorem chiB_hasCompactSupport : HasCompactSupport chiB :=
  chiBBump.hasCompactSupport

theorem chiB_eq_one {x : ℂ} (hx : ‖x‖ ≤ 7 / 2) : chiB x = 1 :=
  chiBBump.one_of_mem_closedBall (by simpa [chiBBump] using hx)

theorem chiB_nonneg (x : ℂ) : 0 ≤ chiB x := chiBBump.nonneg

theorem chiB_le_one (x : ℂ) : chiB x ≤ 1 := chiBBump.le_one

theorem CP_pos (k : ℕ) : 0 < CP k := Sob.hkCalcConst_pos _ _ _

theorem Cel_pos (j : ℕ) : 0 < Cel j := Sob.elConst_pos _ _ _

theorem CB_pos (k : ℕ) : 0 < CB k := by
  have := CP_pos k
  have := Cel_pos (k - 1)
  unfold CB
  positivity

theorem CBS_pos : 0 < CBS := by
  have := Cel_pos 1
  unfold CBS
  positivity

theorem CHK_eq (s : ℕ) : CHK s = CP s := rfl

theorem two_mul_sigmaMax_le_Lam (χ : ℝ → ℝ) (s : ℕ) : 2 * sigmaMax χ ≤ Lam χ s :=
  le_max_left _ _

theorem two_le_NG (χ : ℝ → ℝ) (s : ℕ) : 2 ≤ NG χ s := le_max_left _ _

theorem le_NG (χ : ℝ → ℝ) (s : ℕ) : Lam χ s / Eig.sigb χ + 1 ≤ NG χ s := by
  unfold NG
  calc Lam χ s / Eig.sigb χ + 1 ≤ (⌈Lam χ s / Eig.sigb χ + 1⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ ((max 2 ⌈Lam χ s / Eig.sigb χ + 1⌉₊ : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _

/-- `N_G` is the least integer `n` with `n ≥ 2` and `n ≥ Λ(s)/σ_b + 1`. -/
theorem NG_le {χ : ℝ → ℝ} {s n : ℕ} (hn : 2 ≤ n) (hn' : Lam χ s / Eig.sigb χ + 1 ≤ n) :
    NG χ s ≤ n :=
  max_le hn (Nat.ceil_le.2 hn')

theorem Mact_eq (χ : ℝ → ℝ) (s : ℕ) : Mact χ s = s + NG χ s + 2 := rfl

theorem add_four_le_Mact (χ : ℝ → ℝ) (s : ℕ) : s + 4 ≤ Mact χ s := by
  have := two_le_NG χ s
  unfold Mact
  omega

theorem Mh_eq (sh NQ : ℕ) : Mh sh NQ = sh + NQ + 1 := rfl

theorem IsSemigroupConst.mono {χ : ℝ → ℝ} {s : ℕ} {σ' C C' : ℝ} (h : IsSemigroupConst χ s σ' C)
    (hC : C ≤ C') : IsSemigroupConst χ s σ' C' := by
  intro G hG t ht
  obtain ⟨h1, h2, h3⟩ := h G hG t ht
  have he1 := (Real.exp_pos (σ' * t)).le
  have he2 := (Real.exp_pos (Eig.sigma χ G * t)).le
  refine ⟨fun w hw => (h1 w hw).trans ?_, fun w hw => (h2 w hw).trans ?_,
    fun w hw => (h3 w hw).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC he1) (norm_nonneg w)
  · exact mul_le_mul_of_nonneg_right hC (norm_nonneg w)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC he2) (norm_nonneg w)

end OneRing

end NonUniqueEuler
