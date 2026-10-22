import NonUniqueEuler.Defs.Sec6.Regions

/-!
# Section 6.4: the phase clock (definitions)

Manuscript `def:clock`
(`06_datum.tex:399-443`) and `lem:clock` (`06_datum.tex:445-461`).

The clock is defined recursively downward in `k` (`06_datum.tex:403-410`):
`t♯_n = 0`; `c_k(0) = ℓ_*(G_k)(w_k(t♯_k))`, `κ♯_k = |c_k(0)|`; `T̂_k = σ_k⁻¹ log(δ₀/κ♯_k)`,
`T_k = t♯_k + T̂_k/A_k`, `t♯_{k-1} = T_k + T_pin/A_k`. The manuscript defines each step only under
`S_k(t♯_k) ⊂ N_k` and `κ♯_k ∈ (0, δ₀)`. In Lean the recursion is carried out with the same formulas
without these conditions (total functions, `tshRev` by recursion on `n - k`), and
`P.ClockUpTo k` ("the clock is defined up to level `k`") records them for `i ∈ [k, n]`: under it,
`P.tsh i`, `P.ksh i`, `P.That i`, `P.T i` (`k ≤ i ≤ n`) and `P.tsh (k-1)` are the manuscript's numbers.
Following `06_datum.tex:413`, `T_{n+1} = 0`; `P.ClockUpTo (n+1)` holds (empty condition).

"Defined" conventions (`def:loc`, `07_several_rings.tex:466-468`; `11_bootstrap.tex:57-62`):
`T_j` is defined iff `P.ClockUpTo j`; `t♯_j` is defined iff `P.ClockUpTo (j+1)` (always for
`j = n`). `QuietAt`, `ActiveAt`, `DebrisAt` use them.

Also: the phase intervals `W_k`, `Ph_k = [t♯_k, T_k]`, `Pin_k`, the active time
`u = A_k(t - t♯_k)`, the running coefficient `c_k(u)` (`eq:running-k`), the kick time
`τ_K = A_{k+1}(t - T_{k+1})`, `τ₀ = -A_{k+1}T_{k+1}`, and the comparison class of `lem:clock`(2),(3)
(`IsComparisonVort`). All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Datum

open RingData

namespace Approx

variable (P : Approx)

/-! ### The recursion -/

/-- `|ℓ_*(G_k)(w_k(t))|`, the size of the unstable coefficient of ring `k` at time `t`
(`06_datum.tex:406`, evaluated at `t = t♯_k`). -/
def kshAt (k : ℕ) (t : ℝ) : ℝ := ‖Eig.ellFn P.χ (P.G k) (P.w k t)‖

/-- `σ_k⁻¹ log(δ₀/|ℓ_*(G_k)(w_k(t))|)` (`06_datum.tex:408`, at `t = t♯_k`). -/
def ThatAt (k : ℕ) (t : ℝ) : ℝ := (P.sigma k)⁻¹ * Real.log (P.δ₀ / P.kshAt k t)

/-- The recursion of `def:clock` indexed by `j = n - k`: `tshRev j = t♯_{n-j}`;
`t♯_n = 0` and `t♯_{k-1} = t♯_k + T̂_k/A_k + T_pin/A_k` with `k = n - j` (`06_datum.tex:404-409`). -/
def tshRev : ℕ → ℝ
  | 0 => 0
  | j + 1 => tshRev j + P.ThatAt (P.n - j) (tshRev j) / P.A (P.n - j) + P.Tpin / P.A (P.n - j)

/-- The activation time `t♯_k` (`def:clock`, `06_datum.tex:404`, `:409`). -/
def tsh (k : ℕ) : ℝ := P.tshRev (P.n - k)

/-- `c_k(0) = ℓ_*(G_k)(w_k(t♯_k))` (`06_datum.tex:405-406`). -/
def c0 (k : ℕ) : ℂ := Eig.ellFn P.χ (P.G k) (P.w k (P.tsh k))

/-- `κ♯_k = |c_k(0)|` (`06_datum.tex:406`). -/
def ksh (k : ℕ) : ℝ := ‖P.c0 k‖

/-- `T̂_k = σ_k⁻¹ log(δ₀/κ♯_k)`, the length of the active phase in active time
(`06_datum.tex:408`). -/
def That (k : ℕ) : ℝ := (P.sigma k)⁻¹ * Real.log (P.δ₀ / P.ksh k)

/-- The saturation time `T_k = t♯_k + T̂_k/A_k`, and `T_{n+1} = 0` (`06_datum.tex:408`, `:413`). -/
def T (k : ℕ) : ℝ := if k = P.n + 1 then 0 else P.tsh k + P.That k / P.A k

/-- `t̄♯_k = A_k t♯_k`, the activation time in ring-`k` time (`06_datum.tex:413`). -/
def tash (k : ℕ) : ℝ := P.A k * P.tsh k

/-- **The clock is defined up to level `k`** (`06_datum.tex:411-413`): `S_i(t♯_i) ⊂ N_i` and
`κ♯_i ∈ (0, δ₀)` for every `i ∈ [k, n]`. (For `k = n + 1` the condition is empty.) -/
def ClockUpTo (k : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc k P.n, P.St i (P.tsh i) ⊆ P.Nk i ∧ P.ksh i ∈ Ioo (0 : ℝ) P.δ₀

/-! ### Phases -/

/-- The window `W_k = [T_{k+1}, T_k]` (`06_datum.tex:413`). -/
def W (k : ℕ) : Set ℝ := Icc (P.T (k + 1)) (P.T k)

/-- The active phase `Ph_k = [t♯_k, T_k]` (`06_datum.tex:414`, `\Phase_k`). -/
def Phase (k : ℕ) : Set ℝ := Icc (P.tsh k) (P.T k)

/-- The pinning phase `Pin_k = [T_{k+1}, t♯_k]`, `k < n` (`06_datum.tex:415`). -/
def Pin (k : ℕ) : Set ℝ := Icc (P.T (k + 1)) (P.tsh k)

/-- Ring `j` is **quiet** at `t`: `t♯_j` is not defined or `t ≤ t♯_j` (`def:loc`,
`07_several_rings.tex:466-468`; `11_bootstrap.tex:57-58`; when the clock is defined this is the
`t ≤ t♯_j` of `def:clock`). -/
def QuietAt (j : ℕ) (t : ℝ) : Prop := ¬ P.ClockUpTo (j + 1) ∨ t ≤ P.tsh j

/-- Ring `j` is **active** at `t`: `T_j` is defined and `t♯_j ≤ t ≤ T_j`
(`06_datum.tex:416`, `11_bootstrap.tex:58-59`). -/
def ActiveAt (j : ℕ) (t : ℝ) : Prop := P.ClockUpTo j ∧ P.tsh j ≤ t ∧ t ≤ P.T j

/-- Ring `j` is **debris** at `t`: `T_j` is defined and `t > T_j` (`06_datum.tex:416`,
`11_bootstrap.tex:59-60`). -/
def DebrisAt (j : ℕ) (t : ℝ) : Prop := P.ClockUpTo j ∧ P.T j < t

/-- The active time `u = A_k(t - t♯_k)` of ring `k` (`06_datum.tex:417`). -/
def activeTime (k : ℕ) (t : ℝ) : ℝ := P.A k * (t - P.tsh k)

/-- The **running coefficient** of ring `k` (`eq:running-k`, `06_datum.tex:419-423`):
`c_k(u) = c_k(0) + ∫₀ᵘ e^{-λ_k v} ℓ_*(G_k)(F_k(v)) dv`, `F_k(v) = -h_k(t̄♯_k + v)·∇Φ`. This is
`OneRing.runCoef` with `G = G_k`, `w₀ = w_k(t♯_k)` and the field `v ↦ h_k(t̄♯_k + v)` (the indicator
of `N'` in `F_k` is omitted: `OneRing.hGrad`). -/
def runCoefK (k : ℕ) (u : ℝ) : ℂ :=
  OneRing.runCoef P.χ (P.G k) (P.w k (P.tsh k)) (fun v => P.hField k (P.tash k + v)) u

/-- The kick time `τ_K = A_{k+1}(t - T_{k+1})` of ring `k < n` (`06_datum.tex:424`). -/
def kickTime (k : ℕ) (t : ℝ) : ℝ := P.A (k + 1) * (t - P.T (k + 1))

/-- `τ₀ = -A_{k+1} T_{k+1}`, the kick time of `t = 0` (`06_datum.tex:425-426`). -/
def tau0 (k : ℕ) : ℝ := -(P.A (k + 1) * P.T (k + 1))

end Approx

/-! ### The comparison class of `lem:clock` -/

/-- **The comparison vorticities of `lem:clock`(2),(3)** (`06_datum.tex:436-443`): `ω̃` is smooth,
every `ω̃(t)`, `t ≥ 0`, has compact support, and `K_BS * ω̃` is smooth with every derivative bounded
on `[0, T] × ℝ²` for every `T`. "A quantity is determined by `ω^{(n)}` on `[0, t̄]`" means that it
is unchanged when `P` is replaced by `P.withOm ω̃` for such an `ω̃` with `ω̃ = ω^{(n)}` on
`[0, t̄] × ℝ²`. The manuscript asks `ω̃ ∈ C^∞([0, ∞) × ℝ²)`; we ask smoothness on `ℝ × ℝ²` (so that
the maximal flow `Smooth.flowOf` of `K_BS * ω̃` is the flow of a smooth field; a deviation from the
manuscript). -/
structure IsComparisonVort (om : ℝ → ℂ → ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry om)
  hasCompactSupport : ∀ t : ℝ, 0 ≤ t → HasCompactSupport (om t)
  velocity_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (velocityField om))
  velocity_bounded : ∀ T : ℝ, 0 < T → ∀ j : ℕ, ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : ℂ,
    ‖iteratedFDeriv ℝ j (Function.uncurry (velocityField om)) (t, x)‖ ≤ C

namespace Approx

variable (P : Approx)

/-! ### Basic lemmas (fully proved) -/

@[simp] theorem tshRev_zero : P.tshRev 0 = 0 := rfl

theorem tshRev_succ (j : ℕ) :
    P.tshRev (j + 1) =
      P.tshRev j + P.ThatAt (P.n - j) (P.tshRev j) / P.A (P.n - j) + P.Tpin / P.A (P.n - j) :=
  rfl

/-- `t♯_n = 0` (`06_datum.tex:404`). -/
theorem tsh_n : P.tsh P.n = 0 := by
  simp [tsh]

theorem T_succ_n : P.T (P.n + 1) = 0 := by
  simp [T]

theorem T_of_ne {k : ℕ} (hk : k ≠ P.n + 1) : P.T k = P.tsh k + P.That k / P.A k := by
  simp [T, hk]

theorem ksh_eq_kshAt (k : ℕ) : P.ksh k = P.kshAt k (P.tsh k) := rfl

theorem That_eq_ThatAt (k : ℕ) : P.That k = P.ThatAt k (P.tsh k) := rfl

/-- `t♯_k = T_{k+1} + T_pin/A_{k+1}` for `k < n` (`06_datum.tex:409`, with `k+1` in place of `k`). -/
theorem tsh_eq_T_add {k : ℕ} (hkn : k < P.n) :
    P.tsh k = P.T (k + 1) + P.Tpin / P.A (k + 1) := by
  have hne : k + 1 ≠ P.n + 1 := by omega
  have h1 : P.n - k = (P.n - (k + 1)) + 1 := by omega
  have h2 : P.n - (P.n - (k + 1)) = k + 1 := by omega
  rw [T_of_ne P hne, tsh, h1, tshRev_succ, h2, That_eq_ThatAt]
  rfl

theorem ksh_nonneg (k : ℕ) : 0 ≤ P.ksh k := norm_nonneg _

theorem tash_def (k : ℕ) : P.tash k = P.A k * P.tsh k := rfl

theorem clockUpTo_succ_n : P.ClockUpTo (P.n + 1) := by
  intro i hi
  simp only [Finset.mem_Icc] at hi
  omega

theorem ClockUpTo.mono {P : Approx} {k k' : ℕ} (h : P.ClockUpTo k) (hk : k ≤ k') :
    P.ClockUpTo k' := fun i hi =>
  h i (by simp only [Finset.mem_Icc] at hi ⊢; omega)

theorem ClockUpTo.pertDefined {P : Approx} {k i : ℕ} (h : P.ClockUpTo k) (hki : k ≤ i)
    (hin : i ≤ P.n) : P.PertDefined i (P.tsh i) :=
  (h i (by simp [Finset.mem_Icc, hki, hin])).1

theorem ClockUpTo.ksh_mem {P : Approx} {k i : ℕ} (h : P.ClockUpTo k) (hki : k ≤ i)
    (hin : i ≤ P.n) : P.ksh i ∈ Ioo (0 : ℝ) P.δ₀ :=
  (h i (by simp [Finset.mem_Icc, hki, hin])).2

theorem kickTime_zero (k : ℕ) : P.kickTime k 0 = P.tau0 k := by
  simp [kickTime, tau0]

theorem runCoefK_zero (k : ℕ) : P.runCoefK k 0 = P.c0 k := by
  simp [runCoefK, c0, OneRing.runCoef_zero]

theorem activeTime_tsh (k : ℕ) : P.activeTime k (P.tsh k) = 0 := by
  simp [activeTime]

end Approx

end Datum

end NonUniqueEuler
