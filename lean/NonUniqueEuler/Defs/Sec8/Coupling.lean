import NonUniqueEuler.Defs.Sec6.All
import NonUniqueEuler.Defs.Sec8.Kick

/-!
# Section 8: the coupling of ring `k` to its inner region (definitions)

Manuscript `lem:coupling`
(`08_kick.tex:21-64`) and the instance of the kick setting described before `lem:pinning`
(`08_kick.tex:168-171`, `:293-296`).

For an approximation `P` and a level `1 ≤ k < n` (ring-`k` time `τ = A_k t`, kick time
`τ_K = A_{k+1}(t - T_{k+1}) = μτ + τ₀`):
* `P.wlinIn s k τ = wlin_{in,k}(τ) = ∫₀^τ e^{(τ-v)L(G_k)}(-h^in_k(v)·∇Φ) dv ∈ Y^s(N)` and
  `P.wlinOut s k τ` (the same with `h^out_k`) (`OneRing.wlin`);
* `P.zeta0 k = ζ₀ = λ_k/μ`;
* `P.cin k τ_K = c^in(τ_K) = ℓ_*(G_k)(wlin_{in,k}(τ))`, `τ = (τ_K - τ₀)/μ`, as a function of kick time;
* `P.Ain k τ_K = A^in(τ_K) = e^{-ζ₀τ_K} c^in(τ_K)` (the kick amplitude);
* `P.cinK k = c^in_k = ℓ_*(G_k)(wlin_{in,k}(t̄♯_k))`;
* `P.qKick k τ_K = q_{k+1}` as a function of kick time.

The functional `ℓ_*(G_k)` is applied to plane functions (`Eig.ellFn`), and `wlin_{in,k}` is taken in
`Y^0(N) = L²(N)` (on which `ℓ_*(G_k)` is bounded, `lem:uniform`); the manuscript's
`wlin_{in,k}` in `X^s` has the same function for every `s`. All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Datum

namespace Approx

open RingData

variable (P : Approx)

/-- `wlin_{in,k}(τ) = ∫₀^τ e^{(τ-v)L(G_k)}(-h^in_k(v)·∇Φ) dv` in `Y^s(N)`
(`lem:coupling`(2), `08_kick.tex:38-42`). -/
def wlinIn (s k : ℕ) (τ : ℝ) : Sect.Y s annN := OneRing.wlin P.χ s (P.G k) (P.hIn k) τ

/-- `wlin_{out,k}(τ) = ∫₀^τ e^{(τ-v)L(G_k)}(-h^out_k(v)·∇Φ) dv` in `Y^s(N)`
(`lem:coupling`(3), `08_kick.tex:59`). -/
def wlinOut (s k : ℕ) (τ : ℝ) : Sect.Y s annN := OneRing.wlin P.χ s (P.G k) (P.hOut k) τ

/-- `ζ₀ = λ_k/μ`, the growth rate of ring `k` in the time of ring `k+1` (`eq:kick`, `08_kick.tex:48`). -/
def zeta0 (k : ℕ) : ℂ := P.lam k / P.μ

/-- `c^in(τ_K) = ℓ_*(G_k)(wlin_{in,k}(τ))`, `τ = (τ_K - τ₀)/μ`, as a function of the kick time
(`lem:coupling`(2), `08_kick.tex:43-44`, `:128-129`). -/
def cin (k : ℕ) (τK : ℝ) : ℂ :=
  Eig.ellFn P.χ (P.G k) (P.wlinIn 0 k ((τK - P.tau0 k) / P.μ)).fn

/-- The kick amplitude `A^in(τ_K) = e^{-ζ₀ τ_K} c^in(τ_K)` (`08_kick.tex:51`). -/
def Ain (k : ℕ) (τK : ℝ) : ℂ := Complex.exp (-(P.zeta0 k * τK)) * P.cin k τK

/-- `c^in_k = ℓ_*(G_k)(wlin_{in,k}(t̄♯_k))` (`08_kick.tex:52-53`). -/
def cinK (k : ℕ) : ℂ := Eig.ellFn P.χ (P.G k) (P.wlinIn 0 k (P.tash k)).fn

/-- `q_{k+1}` as a function of the kick time `τ_K` of ring `k`: `t = T_{k+1} + τ_K/A_{k+1}`
(`08_kick.tex:43-44`). -/
def qKick (k : ℕ) (τK : ℝ) : ℂ := P.q (k + 1) (P.T (k + 1) + τK / P.A (k + 1))

/-! ### Basic lemmas (fully proved) -/

theorem Ain_def (k : ℕ) (τK : ℝ) :
    P.Ain k τK = Complex.exp (-(P.zeta0 k * τK)) * P.cin k τK := rfl

theorem wlinIn_def (s k : ℕ) (τ : ℝ) :
    P.wlinIn s k τ = OneRing.wlin P.χ s (P.G k) (P.hIn k) τ := rfl

variable {P}

/-- For a valid `P`, `q_{k+1}(t)` is `qKick` at the kick time of `t`. -/
theorem Valid.qKick_kickTime (h : P.Valid) (k : ℕ) (t : ℝ) :
    P.qKick k (P.kickTime k t) = P.q (k + 1) t := by
  have hA : P.A (k + 1) ≠ 0 := (h.A_pos (k + 1)).ne'
  simp only [qKick, kickTime]
  congr 1
  field_simp
  ring

end Approx

end Datum

end NonUniqueEuler
