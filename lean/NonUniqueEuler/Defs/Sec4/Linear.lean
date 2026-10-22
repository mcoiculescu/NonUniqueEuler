import NonUniqueEuler.Defs.Sec4.RingSetting
import NonUniqueEuler.Defs.Sec4.Operators
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Section 4.5 and Section 5: the linearization at the ring in ring units (definitions)

Manuscript `04_ring.tex:1232-1239`
(the spaces `X^s`, `X^s_ℓ` and the operator `L(G)` in ring units) and `05_single_ring.tex:41-57`
(`e^{tL(G)}` on `X^k`, `lem:duhamel`).

Everything is the sector-setting object of `ringPhiSetting χ` (ring units, `N_* = N`), in the
namespace `NonUniqueEuler.Lin`:
* `Lin.Xsub s = Sect.YsymSub s N 3` and the predicate `Lin.MemX s w` on `w : Sect.Y s N`:
  the space `X^s` of `3`-fold symmetric `w ∈ H^s` supported in `N` (`04_ring.tex:1232-1234`;
  it equals `Y^s_{3ℤ}`, `Sect.YsymSub_eq_YZSub`). Decision D14: one ambient space `Y^s(N)`
  with a predicate; `Lin.MemXFn s f` is the same predicate for plane functions `f : ℂ → ℂ`;
* `Lin.Lsec χ s ℓ G`: the sector operator `L_ℓ(G)` on `X^s_ℓ = Y^s_ℓ(N)`;
* `Lin.S χ s G t`: the semigroup `e^{tL(G)}` on `Y^s(N)` (sector-wise exponential, D8/R1);
  it preserves `X^s` (`Sect.sectorExp_mem_YZSub`);
* `Lin.L χ s G : Y^{s+1}(N) → Y^s(N)` and `Lin.Lfn χ G w`: the operator `L(G)` (typed and on
  functions);
* `Lin.Sfn χ s G t f`: `e^{tL(G)}` applied to a plane function `f ∈ X^s` (via `Sect.toY`);
* `Lin.duhamel χ s G f₀ g t = e^{tL}f₀ + ∫₀ᵗ e^{(t-τ)L} g(τ) dτ` (`lem:duhamel`).

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Lin

open RingData Sect

/-- `X^s`: the `3`-fold symmetric `w ∈ H^s(ℝ²;ℂ)` with `supp w ⊆ N` (`04_ring.tex:1232-1234`),
as a closed submodule of the Sobolev tuple space. -/
def Xsub (s : ℕ) : Submodule ℂ (Sob.SobTuple s) := YsymSub s annN 3

/-- `w ∈ Y^s(N)` lies in `X^s`. -/
def MemX {s : ℕ} (w : Y s annN) : Prop := (w : Sob.SobTuple s) ∈ Xsub s

/-- A plane function `f` lies in `X^s`: `f ∈ H^s`, `f = 0` a.e. outside `N`, and `f` is `3`-fold
symmetric (`04_ring.tex:1232-1234`). -/
def MemXFn (s : ℕ) (f : ℂ → ℂ) : Prop :=
  Sob.MemH s f ∧ (∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → f x = 0) ∧ Ang.IsMFoldSymmetricC 3 f

/-- The angular velocity `Ω(r;G)` of `(Φ, G)` in ring units (`04_ring.tex:150`; it appears in the
velocity `v = Ω(|x|;G) x^⊥ + …` of `lem:reduction`(2), `05_single_ring.tex:110-115`). -/
def Omega (χ : ℝ → ℝ) (G r : ℝ) : ℝ := (ringPhiSetting χ).Omega G r

/-- The sector operator `L_ℓ(G)` on `X^s_ℓ = Y^s_ℓ(N)`, ring units (`04_ring.tex:1238-1239`). -/
def Lsec (χ : ℝ → ℝ) (s : ℕ) (ℓ : ℤ) (G : ℝ) : Ysec s annN ℓ →L[ℂ] Ysec s annN ℓ :=
  (ringPhiSetting χ).Lsec s ℓ G

/-- The semigroup `e^{tL(G)}` on `Y^s(N)` in ring units (`05_single_ring.tex:41-47`;
`lem:semigroup-construct`; defined sector-wise, D8/R1). -/
def S (χ : ℝ → ℝ) (s : ℕ) (G t : ℝ) : Y s annN →L[ℂ] Y s annN :=
  (ringPhiSetting χ).semigroup s G t

/-- The linearization `L(G) : Y^{s+1}(N) → Y^s(N)` at `(Φ, G)` (`04_ring.tex:1234-1238`). -/
def L (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Y (s + 1) annN →L[ℂ] Y s annN :=
  (ringPhiSetting χ).LinY s G

/-- The linearization `L(G)w = -Ω(·;G)∂_θ w - (K_BS * w)·∇Φ` at `(Φ, G)` on plane functions
(used pointwise in `eq:ring`, `05_single_ring.tex:118-124`). -/
def Lfn (χ : ℝ → ℝ) (G : ℝ) (w : ℂ → ℂ) : ℂ → ℂ :=
  (ringPhiSetting χ).linFn G w

/-- `e^{tL(G)} f` for a plane function `f ∈ X^s` (junk `0` if `f` is not the function of an
element of `Y^s(N)`). The value does not depend on `s` (a lemma for the interface files). -/
def Sfn (χ : ℝ → ℝ) (s : ℕ) (G t : ℝ) (f : ℂ → ℂ) : ℂ → ℂ :=
  (S χ s G t (toY s annN f)).fn

/-- The Duhamel integral `u(t) = e^{tL(G)} f₀ + ∫₀ᵗ e^{(t-τ)L(G)} g(τ) dτ` in `Y^s(N)`
(`lem:duhamel`, `05_single_ring.tex:52-56`). -/
def duhamel (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) (f₀ : Y s annN) (g : ℝ → Y s annN) (t : ℝ) :
    Y s annN :=
  S χ s G t f₀ + ∫ τ in (0 : ℝ)..t, S χ s G (t - τ) (g τ)

/-! ### Basic lemmas (fully proved) -/

theorem S_def (χ : ℝ → ℝ) (s : ℕ) (G t : ℝ) :
    S χ s G t = sectorExp s annN (fun ℓ => Lsec χ s ℓ G) t := rfl

theorem Lsec_def (χ : ℝ → ℝ) (s : ℕ) (ℓ : ℤ) (G : ℝ) :
    Lsec χ s ℓ G = (ringPhiSetting χ).transSec s ℓ G + (ringPhiSetting χ).Ksec s ℓ := rfl

theorem memX_iff {s : ℕ} (w : Y s annN) :
    MemX w ↔ (w : Sob.SobTuple s) ∈ YsymSub s annN 3 := Iff.rfl

end Lin

end NonUniqueEuler
