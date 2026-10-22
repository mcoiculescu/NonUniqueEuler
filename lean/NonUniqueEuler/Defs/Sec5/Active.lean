import NonUniqueEuler.Defs.Sec5.Constants
import NonUniqueEuler.Defs.Sec2.Multipole

/-!
# Section 5.3: an active ring — envelopes, the transient, and the constants of `thm:active`
(definitions)

Manuscript `lem:window`
(`05_single_ring.tex:678-704`), `thm:active` (`:863-912`) and `cor:active-moment`
(`:1104-1111`).

* explicit functions of the statements: `ahat κ σ u = κ e^{σu}` (`â`, `â₁`), `That σ δ₀ κ =
  σ⁻¹ log(δ₀/κ)` (`T̂`, `T̂₁`), `rhoOne σ σ' u = ⟨u⟩^p e^{-(σ-σ')u}` (`ρ₁` of `lem:window`),
  `tOneOf σ σ' C₀` (the least `t ≥ 0` with `2^{p/2} C₀ ⟨t'⟩^p e^{-(σ-σ')t'} ≤ 1` for all
  `t' ≥ t`), `tOne χ σ' C₀ G = t₁(C₀,G)`, `tOneBar χ σ' C₀ = t̄₁(C₀)`, the transient
  `rhoHatOf σ σ' C₀ u` (`ρ̂`, with `rhoHat χ σ' C₀ G`), `Cact χ σ' C₀ = C(C₀) =
  max(C₀, e^{σ_max t̄₁(C₀)})`, `etaMax = η_max = 1`;
* the hypotheses (Init), (Field), (Coef) of `thm:active` (`RingConfig.ActiveInit`,
  `ActiveField`, `ActiveCoef`) and its conclusions (a), (b) together with the bound of
  `cor:active-moment` (`RingConfig.ActiveConcl`);
* `IsActiveConst χ s σ' d_H C₂ C₃ κ₀`: "these constants work in `thm:active` and
  `cor:active-moment`" (D11: Sections 9–10 use `d_H, C₂, C₃, κ₀(·)` by value), and the chosen
  constants `activeConsts`, `dH`, `C2`, `C3`, `kappa0`.

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace OneRing

open RingData

/-! ### Envelopes and the transient -/

/-- `η_max = 1` (`thm:active`, `05_single_ring.tex:868`). -/
def etaMax : ℝ := 1

/-- The envelope `â(u) = κ e^{σu}` (`thm:active`, `05_single_ring.tex:873`; `â₁` of
`lem:window`, `:697`; `â_k` of `def:standing`). -/
def ahat (κ σ u : ℝ) : ℝ := κ * Real.exp (σ * u)

/-- The window end `T̂ = σ⁻¹ log(δ₀/κ)` (`thm:active`, `05_single_ring.tex:874`; `T̂₁` of
`lem:window`, `:686`). -/
def That (σ δ₀ κ : ℝ) : ℝ := σ⁻¹ * Real.log (δ₀ / κ)

/-- `ρ₁(u) = ⟨u⟩^p e^{-(σ-σ')u}` (`lem:window`, `05_single_ring.tex:697`). -/
def rhoOne (σ σ' u : ℝ) : ℝ := Prelim.jap u ^ pW * Real.exp (-((σ - σ') * u))

/-- The least `t ≥ 0` such that `2^{p/2} C₀ ⟨t'⟩^p e^{-(σ-σ')t'} ≤ 1` for all `t' ≥ t`
(`thm:active`, `05_single_ring.tex:874-875` with `σ = σ(G)`, and `:901-905` with `σ = σ_b`), as an
infimum (the set is a closed half-line when `σ > σ'`; junk `0` when it is empty). -/
def tOneOf (σ σ' C₀ : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∀ t' : ℝ, t ≤ t' →
    (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t' ^ pW * Real.exp (-((σ - σ') * t')) ≤ 1}

/-- `t₁ = t₁(C₀,G)` (`thm:active`, `05_single_ring.tex:874-875`). -/
def tOne (χ : ℝ → ℝ) (σ' C₀ G : ℝ) : ℝ := tOneOf (Eig.sigma χ G) σ' C₀

/-- `t̄₁(C₀)` (`thm:active`, `05_single_ring.tex:901-905`). -/
def tOneBar (χ : ℝ → ℝ) (σ' C₀ : ℝ) : ℝ := tOneOf (Eig.sigb χ) σ' C₀

/-- The **transient** `ρ̂(u) = C₀⟨u⟩^p e^{-(σ-σ')u}` for `0 ≤ u < t₁` and
`ρ̂(u) = ⟨u-t₁⟩^p e^{-(σ-σ')(u-t₁)}` for `u ≥ t₁`, with `t₁ = tOneOf σ σ' C₀`
(`thm:active`, `05_single_ring.tex:876-880`). -/
def rhoHatOf (σ σ' C₀ u : ℝ) : ℝ :=
  if u < tOneOf σ σ' C₀ then C₀ * Prelim.jap u ^ pW * Real.exp (-((σ - σ') * u))
  else Prelim.jap (u - tOneOf σ σ' C₀) ^ pW * Real.exp (-((σ - σ') * (u - tOneOf σ σ' C₀)))

/-- The transient `ρ̂` of `thm:active` for `G` (`σ = σ(G)`; `ρ̂_k` of `def:standing`). -/
def rhoHat (χ : ℝ → ℝ) (σ' C₀ G u : ℝ) : ℝ := rhoHatOf (Eig.sigma χ G) σ' C₀ u

/-- `C(C₀) = max(C₀, e^{σ_max t̄₁(C₀)})` (`thm:active`, `05_single_ring.tex:906-911`). -/
def Cact (χ : ℝ → ℝ) (σ' C₀ : ℝ) : ℝ := max C₀ (Real.exp (sigmaMax χ * tOneBar χ σ' C₀))

/-! ### The hypotheses and conclusions of `thm:active` -/

namespace RingConfig

variable (c : RingConfig)

/-- Hypothesis **(Init)** of `thm:active` (`05_single_ring.tex:886`):
`‖w(0)‖_{H^{M-1}} ≤ C₀κ` and `supp(Φ + w(0)) = supp ω_r(0) ⊂ 𝒩₋`. -/
def ActiveInit (χ : ℝ → ℝ) (s : ℕ) (C₀ κ : ℝ) : Prop :=
  Sob.normH (Mact χ s - 1) (c.pert0 χ) ≤ C₀ * κ ∧ tsupport c.ring0 ⊆ annNm

/-- Hypothesis **(Field)** of `thm:active` (`05_single_ring.tex:887-889`): `h = h₁ + h₂` on
`[0,ū]` (as fields on a neighborhood of `N'`, which is what the `C^M(N')` norms see), with
`‖h₁(u)‖_{C^M(N')} ≤ C₀κ⟨u⟩^p` and `‖h₂(u)‖_{C^M(N')} ≤ η_b â(u)`. The memberships `h_i(u) ∈
C^M(N')` are explicit: with a junk (infinite) norm the bounds would say nothing. -/
def ActiveField (χ : ℝ → ℝ) (s : ℕ) (ubar C₀ κ ηb : ℝ) : Prop :=
  ∃ h₁ h₂ : ℝ → ℂ → ℂ, ∀ u ∈ Icc (0 : ℝ) ubar,
    (∃ U : Set ℂ, IsOpen U ∧ annN' ⊆ U ∧ ∀ x ∈ U, c.h u x = h₁ u x + h₂ u x) ∧
      MemCk (Mact χ s) annN' (h₁ u) ∧
      normCk (Mact χ s) annN' (h₁ u) ≤ C₀ * κ * Prelim.jap u ^ pW ∧
      MemCk (Mact χ s) annN' (h₂ u) ∧
      normCk (Mact χ s) annN' (h₂ u) ≤ ηb * ahat κ (Eig.sigma χ c.G) u

/-- Hypothesis **(Coef)** of `thm:active` (`05_single_ring.tex:890`):
`|c(u)| ≤ κ(2 + C₀⟨u⟩^p e^{-σu})` on `[0,ū]`, for the running coefficient `c` with `w₀ = w(0)`. -/
def ActiveCoef (χ : ℝ → ℝ) (ubar C₀ κ : ℝ) : Prop :=
  ∀ u ∈ Icc (0 : ℝ) ubar,
    ‖runCoef χ c.G (c.pert0 χ) c.h u‖ ≤
      κ * (2 + C₀ * Prelim.jap u ^ pW * Real.exp (-(Eig.sigma χ c.G * u)))

/-- **The conclusions of `thm:active` at time `u`** (`05_single_ring.tex:893-899`), together with
that of `cor:active-moment` (`:1104-1111`), for `G = c.G`, `σ = σ(G)`, `λ = λ_*(G)`,
`â(u) = κe^{σu}`, the transient `ρ̂` and the running coefficient `c(u)` with `w₀ = w(0)`:
(a) every trajectory of `ω_r` moves radially by at most `C₂δ₀ + κ^{1/2}` on `[0,u]`, and
`supp(Φ + w(u)) = supp ω_r(u) ⊂ 𝒩`;
(b) `‖w(u) - 2Re(c(u)e^{λu}φ_*)‖_{H^s} ≤ C₂ â(u)[ρ̂(u) + â(u) + κ^{1/2} + η_b]` and
`‖w(u)‖_{H^s} ≤ C₂ â(u)(1 + ρ̂(u))`;
(`cor:active-moment`) with `q(u) = 2π pout_3[w(u)]`:
`|q(u) - 2π pout_*(G) c(u)e^{λu}| ≤ 2π C₃ â(u)[ρ̂(u) + â(u) + κ^{1/2} + η_b]`. -/
def ActiveConcl (χ : ℝ → ℝ) (s : ℕ) (σ' C₀ κ ηb δ₀ C₂ C₃ u : ℝ) : Prop :=
  c.MovesRadially u (C₂ * δ₀ + Real.sqrt κ) ∧ tsupport (c.ringPart u) ⊆ annNn ∧
    Sob.normH s (c.w χ u - modeFn χ c.G
        (runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u))) ≤
      C₂ * ahat κ (Eig.sigma χ c.G) u *
        (rhoHatOf (Eig.sigma χ c.G) σ' C₀ u + ahat κ (Eig.sigma χ c.G) u + Real.sqrt κ + ηb) ∧
    Sob.normH s (c.w χ u) ≤
      C₂ * ahat κ (Eig.sigma χ c.G) u * (1 + rhoHatOf (Eig.sigma χ c.G) σ' C₀ u) ∧
    ‖2 * Real.pi * BS.pout 3 (c.w χ u) -
        2 * Real.pi * Eig.pout χ c.G *
          (runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u))‖ ≤
      2 * Real.pi * C₃ * ahat κ (Eig.sigma χ c.G) u *
        (rhoHatOf (Eig.sigma χ c.G) σ' C₀ u + ahat κ (Eig.sigma χ c.G) u + Real.sqrt κ + ηb)

end RingConfig

/-- **The constants `d_H ∈ (0,1)`, `C₂ ≥ 1`, `C₃ > 0` and the function `κ₀(·) > 0` work in
`thm:active` and `cor:active-moment`** for `s` and `σ'` (`05_single_ring.tex:863-899`,
`:1104-1111`; `p = 3`, `M = Mact χ s`, `η_max = 1`): for every `C₀ ≥ 1`, every configuration of
`lem:reduction` on `[0,ū]` with `G ∈ [0,G₁]`, every `κ > 0`, `η_b ∈ [0,η_max]`,
`δ₀ ∈ (0,d_H]`, if (Init), (Field), (Coef) hold and (Small) `κ ≤ κ₀(C₀)`, then the conclusions
(a), (b) and that of `cor:active-moment` hold for every `u ∈ [0, min(ū, T̂)]`,
`T̂ = σ⁻¹ log(δ₀/κ)`. The last assertion of `thm:active` (`t₁ ≤ t̄₁`, `â ρ̂ ≤ C(C₀)κ⟨u⟩^pe^{σ'u}`)
does not involve these constants; it is a separate statement about `tOne`, `tOneBar`, `rhoHat`,
`Cact`. -/
def IsActiveConst (χ : ℝ → ℝ) (s : ℕ) (σ' dH C₂ C₃ : ℝ) (κ₀ : ℝ → ℝ) : Prop :=
  dH ∈ Ioo (0 : ℝ) 1 ∧ 1 ≤ C₂ ∧ 0 < C₃ ∧ (∀ C₀ : ℝ, 1 ≤ C₀ → 0 < κ₀ C₀) ∧
    ∀ C₀ : ℝ, 1 ≤ C₀ → ∀ (c : RingConfig) (ubar : ℝ), c.Hyp ubar → c.G ∈ Icc (0 : ℝ) Gbar →
      ∀ κ ηb δ₀ : ℝ, 0 < κ → ηb ∈ Icc (0 : ℝ) etaMax → δ₀ ∈ Ioc (0 : ℝ) dH →
        c.ActiveInit χ s C₀ κ → c.ActiveField χ s ubar C₀ κ ηb → c.ActiveCoef χ ubar C₀ κ →
        κ ≤ κ₀ C₀ →
        ∀ u ∈ Icc (0 : ℝ) (min ubar (That (Eig.sigma χ c.G) δ₀ κ)),
          c.ActiveConcl χ s σ' C₀ κ ηb δ₀ C₂ C₃ u

open Classical in
/-- The constants `(d_H, C₂, C₃, κ₀)` of `thm:active` for `s`, `σ'` (chosen; junk
`(1/2, 1, 1, 1)` when none exist). -/
def activeConsts (χ : ℝ → ℝ) (s : ℕ) (σ' : ℝ) : ℝ × ℝ × ℝ × (ℝ → ℝ) :=
  if h : ∃ x : ℝ × ℝ × ℝ × (ℝ → ℝ), IsActiveConst χ s σ' x.1 x.2.1 x.2.2.1 x.2.2.2 then
    h.choose
  else (1 / 2, 1, 1, fun _ => 1)

/-- `d_H` of `thm:active` (`05_single_ring.tex:868-869`). -/
def dH (χ : ℝ → ℝ) (s : ℕ) (σ' : ℝ) : ℝ := (activeConsts χ s σ').1

/-- `C₂` of `thm:active` (`05_single_ring.tex:868-869`). -/
def C2 (χ : ℝ → ℝ) (s : ℕ) (σ' : ℝ) : ℝ := (activeConsts χ s σ').2.1

/-- `C₃` of `thm:active` (`05_single_ring.tex:868-869`; used in `cor:active-moment`). -/
def C3 (χ : ℝ → ℝ) (s : ℕ) (σ' : ℝ) : ℝ := (activeConsts χ s σ').2.2.1

/-- The function `κ₀(·)` of `thm:active` (`05_single_ring.tex:869-870`). -/
def kappa0 (χ : ℝ → ℝ) (s : ℕ) (σ' : ℝ) : ℝ → ℝ := (activeConsts χ s σ').2.2.2

/-! ### Basic lemmas (fully proved) -/

/-- If constants for `thm:active` exist, the chosen ones work. -/
theorem activeConsts_spec {χ : ℝ → ℝ} {s : ℕ} {σ' : ℝ}
    (h : ∃ (dH C₂ C₃ : ℝ) (κ₀ : ℝ → ℝ), IsActiveConst χ s σ' dH C₂ C₃ κ₀) :
    IsActiveConst χ s σ' (dH χ s σ') (C2 χ s σ') (C3 χ s σ') (kappa0 χ s σ') := by
  classical
  have h' : ∃ x : ℝ × ℝ × ℝ × (ℝ → ℝ), IsActiveConst χ s σ' x.1 x.2.1 x.2.2.1 x.2.2.2 := by
    obtain ⟨d, c₂, c₃, k, hk⟩ := h
    exact ⟨(d, c₂, c₃, k), hk⟩
  have hc : activeConsts χ s σ' = h'.choose := by
    rw [activeConsts, dite_eq_left h']
  rw [dH, C2, C3, kappa0, hc]
  exact h'.choose_spec

theorem ahat_pos {κ : ℝ} (hκ : 0 < κ) (σ u : ℝ) : 0 < ahat κ σ u :=
  mul_pos hκ (Real.exp_pos _)

theorem ahat_zero (κ σ : ℝ) : ahat κ σ 0 = κ := by
  simp [ahat]

theorem rhoHatOf_of_lt {σ σ' C₀ u : ℝ} (hu : u < tOneOf σ σ' C₀) :
    rhoHatOf σ σ' C₀ u = C₀ * Prelim.jap u ^ pW * Real.exp (-((σ - σ') * u)) := by
  simp [rhoHatOf, hu]

theorem rhoHatOf_of_le {σ σ' C₀ u : ℝ} (hu : tOneOf σ σ' C₀ ≤ u) :
    rhoHatOf σ σ' C₀ u =
      Prelim.jap (u - tOneOf σ σ' C₀) ^ pW *
        Real.exp (-((σ - σ') * (u - tOneOf σ σ' C₀))) := by
  simp [rhoHatOf, not_lt.2 hu]

theorem le_Cact (χ : ℝ → ℝ) (σ' C₀ : ℝ) : C₀ ≤ Cact χ σ' C₀ := le_max_left _ _

end OneRing

end NonUniqueEuler
