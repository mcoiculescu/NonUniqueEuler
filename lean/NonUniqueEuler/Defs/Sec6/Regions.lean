import NonUniqueEuler.Defs.Sec6.Approx

/-!
# Section 6.3: regions, perturbations, inner circulation, moments and fields (definitions)

Manuscript `def:regions`
(`06_datum.tex:158-211`), the constants of `lem:inner-circ` and `lem:speed`
(`06_datum.tex:332-373`).

For an approximation `P : Approx` (`Defs/Sec6/Approx.lean`) and levels `1 ≤ k ≤ n`:
* `P.S k = supp f^{(n)}_k`, `P.St k t = S_k(t) = Φ_t(S_k)`, `P.D k t = D_k(t) = ⋃_{i=k}^n S_i(t)`
  (`D_{n+1}(t) = ∅`), `P.omegaGe k t = ω_{≥k}(t) = ω(t) 1_{D_k(t)}`, `P.omegaRing k t = ω(t) 1_{S_k(t)}`,
  `P.omegaOut k t = ω(t) 1_{S_1(t) ∪ … ∪ S_{k-1}(t)}`;
* the perturbation `w_k(t) = A_k⁻¹ ω(t, r_k ·) 1_{S_k(t)}(r_k ·) - Φ` in ring-`k` units (`wR`
  real, `w` complexified), and `wPhys k t = A_k w_k(t, ·/r_k)` in physical units;
* the inner circulation `G_k` (`2π G_k A_k r_k² = ∫ ω_{≥k+1}(0)`), `ε_k = μ s_k^{m+2}`,
  `σ_k = σ(G_k)`, `λ_k = λ_*(G_k)`, `x_k = σ_k/μ`, `β_k = β(G_k) s_k^{m+2}/(2π)`;
* the normalized moment `q_j(t) = conj(Q_m[ω_{≥j}(t)])/(A_j r_j^{m+2})` (the manuscript's
  `q_{k+1}` is `P.q (k+1)`);
* the inner and outer fields `h^in_k(τ)`, `h^out_k(τ)`, the external field `h_k = h^in_k + h^out_k`
  (ring-`k` time `τ = A_k t`), their `C^{M_h}(N')` norms `η^in_k`, `η^out_k`, `η_k`, and the
  Duhamel majorants `maj_k`, `maj^in_k`;
* the conditions under which these are the manuscript's objects: `PertDefined`
  (`S_k(t) ⊂ N_k`), `HInDefined` (`D_{k+1}(t) ⊂ B_{a r_k/8}`), `HOutDefined` (`S_i(t) ∩ B_{6 r_k} = ∅`
  for `i < k`), `HDefined`, and `GSmall` (`G_k ≤ G₁` for all levels);
* the constants `‖Φ‖_{L¹}` (`PhiL1`), `C_G`, `M_vort`, `C_*`.

Here `m = 3` (the symmetry order): `ε_k = μ s_k^5`, `Q_m = Q_3`. Partial objects of the manuscript
("while `S_k(t) ⊂ N_k`", "at a time with `D_{k+1}(t) ⊂ B_{a r_k/8}`", "if `G_k ≤ G₁`") are total
functions given by the same formulas; the conditions are hypotheses of the statements. All lemmas
here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate

namespace NonUniqueEuler

namespace Datum

open RingData

/-! ### Constants of Section 6 -/

/-- `‖Φ‖_{L¹}` (`Φ ≥ 0`, so this is `∫ Φ`; `06_datum.tex:234`). -/
def PhiL1 (χ : ℝ → ℝ) : ℝ := (eLpNorm (ringPhi χ) 1 volume).toReal

/-- `C_G = ‖Φ‖_{L¹}/π` (`lem:inner-circ`, `06_datum.tex:336`). -/
def CG (χ : ℝ → ℝ) : ℝ := PhiL1 χ / Real.pi

/-- `M_vort = 9π/2` (`lem:speed`, `06_datum.tex:364`). -/
def Mvort : ℝ := 9 * Real.pi / 2

/-- `C_* = (1 + c₄)/(2π) · M_vort^{1/2}`, with `c₄ = BS.cLpLinf 4` of `lem:LpLinf`
(`lem:speed`, `06_datum.tex:364-365`). -/
def Cstar : ℝ := (1 + BS.cLpLinf 4) / (2 * Real.pi) * Real.sqrt Mvort

theorem Mvort_pos : 0 < Mvort := by
  unfold Mvort; positivity

theorem PhiL1_nonneg (χ : ℝ → ℝ) : 0 ≤ PhiL1 χ := ENNReal.toReal_nonneg

theorem CG_nonneg (χ : ℝ → ℝ) : 0 ≤ CG χ := div_nonneg (PhiL1_nonneg χ) Real.pi_pos.le

namespace Approx

variable (P : Approx)

/-! ### Regions (`def:regions`, first item) -/

/-- `S_k = supp f^{(n)}_k` (`06_datum.tex:164`). -/
def S (k : ℕ) : Set ℂ := tsupport (P.term k)

/-- `S_k(t) = Φ_t(S_k)` (`06_datum.tex:165`). -/
def St (k : ℕ) (t : ℝ) : Set ℂ := P.flow t '' P.S k

/-- `D_k(t) = ⋃_{i=k}^{n} S_i(t)`; `D_{n+1}(t) = ∅` (`06_datum.tex:165`). -/
def D (k : ℕ) (t : ℝ) : Set ℂ := ⋃ i ∈ Finset.Icc k P.n, P.St i t

/-- `ω_{≥k}(t) = ω^{(n)}(t) 1_{D_k(t)}` (`06_datum.tex:166`). -/
def omegaGe (k : ℕ) (t : ℝ) : ℂ → ℝ := (P.D k t).indicator (P.om t)

/-- `ω^{(n)}(t) 1_{S_k(t)}`, the vorticity of ring `k` (`eq:omega-ge`, `06_datum.tex:230`). -/
def omegaRing (k : ℕ) (t : ℝ) : ℂ → ℝ := (P.St k t).indicator (P.om t)

/-- `ω^{(n)}(t) 1_{S_1(t) ∪ … ∪ S_{k-1}(t)}`, the vorticity of the rings outside ring `k`
(`06_datum.tex:194`; `lem:transfer`(4), `07_several_rings.tex:109`). -/
def omegaOut (k : ℕ) (t : ℝ) : ℂ → ℝ := (⋃ i ∈ Finset.Ico 1 k, P.St i t).indicator (P.om t)

/-! ### The perturbation (`def:regions`, third item) -/

/-- The perturbation of ring `k` at time `t` in ring-`k` units (`06_datum.tex:169-173`),
`w_k(t, y) = A_k⁻¹ ω^{(n)}(t, r_k y) 1_{S_k(t)}(r_k y) - Φ(y)` (real valued). The manuscript
defines it while `S_k(t) ⊂ N_k` (`PertDefined`); the formula is used for every `t`. -/
def wR (k : ℕ) (t : ℝ) (y : ℂ) : ℝ := P.unitsVort k (P.omegaRing k t) y - ringPhi P.χ y

/-- `w_k(t)` as a complex function (the form used with `Sob.normH`, `Lin.MemXFn`, `Eig.ellFn`,
and by `OneRing.RingConfig.w`). -/
def w (k : ℕ) (t : ℝ) (y : ℂ) : ℂ := ((P.wR k t y : ℝ) : ℂ)

/-- `A_k w_k(t, x/r_k)`, the perturbation of ring `k` in physical units (`lem:transfer`(2),(4),
`07_several_rings.tex:99`, `:106`). -/
def wPhys (k : ℕ) (t : ℝ) (x : ℂ) : ℝ := P.A k * P.wR k t ((P.r k : ℂ)⁻¹ * x)

/-- `S_k(t) ⊂ N_k`: the perturbation `w_k(t)` is defined (`06_datum.tex:169`). -/
def PertDefined (k : ℕ) (t : ℝ) : Prop := P.St k t ⊆ P.Nk k

/-! ### Inner circulation and rates (`def:regions`, fourth item) -/

/-- The inner circulation `G_k`: `2π G_k A_k r_k² = ∫ ω_{≥k+1}(0)` (`06_datum.tex:174-175`). -/
def G (k : ℕ) : ℝ := (2 * Real.pi * P.A k * P.r k ^ 2)⁻¹ * ∫ x, P.omegaGe (k + 1) 0 x

/-- `ε_k = μ s_k^{m+2}`, `m = 3` (`06_datum.tex:176`). -/
def eps (k : ℕ) : ℝ := P.μ * P.s k ^ (3 + 2)

/-- `σ_k = σ(G_k)` (`06_datum.tex:176-177`; meaningful if `G_k ≤ G₁`). -/
def sigma (k : ℕ) : ℝ := Eig.sigma P.χ (P.G k)

/-- `λ_k = λ_*(G_k)` (`06_datum.tex:177`). -/
def lam (k : ℕ) : ℂ := Eig.lam P.χ (P.G k)

/-- `x_k = σ_k/μ` (`06_datum.tex:177`). -/
def xk (k : ℕ) : ℝ := P.sigma k / P.μ

/-- `β_k = β(G_k) s_k^{m+2}/(2π)`, `m = 3` (`06_datum.tex:178`). -/
def betaK (k : ℕ) : ℂ := Eig.beta P.χ (P.G k) * ((P.s k : ℝ) : ℂ) ^ (3 + 2) / (2 * Real.pi)

/-- The assumption `G_k ≤ G₁` for `1 ≤ k ≤ n` of `def:clock` (`06_datum.tex:401-402`); it holds
if `C_G μ s̄² ≤ G₁` (`lem:inner-circ`). (`G_k ≥ 0` is part of `lem:inner-circ`.) -/
def GSmall : Prop := ∀ k ∈ Finset.Icc 1 P.n, P.G k ≤ Gbar

/-! ### The normalized moment (`def:regions`, fifth item) -/

/-- The normalized moment `q_j(t) = conj(Q_m[ω_{≥j}(t)]) / (A_j r_j^{m+2})`, `m = 3`
(`06_datum.tex:179-182`; the manuscript's `q_{k+1}(t)`, `k < n`, is `P.q (k + 1) t`). -/
def q (j : ℕ) (t : ℝ) : ℂ :=
  conj (BS.Qm 3 fun x => ((P.omegaGe j t x : ℝ) : ℂ)) / ((P.A j * P.r j ^ (3 + 2) : ℝ) : ℂ)

/-! ### The inner, outer and external fields (`def:regions`, sixth item) -/

/-- `ν^in_k(y) = A_k⁻¹ ω_{≥k+1}(t, r_k y)` at the time `t` (`06_datum.tex:188-189`). -/
def nuIn (k : ℕ) (t : ℝ) : ℂ → ℝ := P.unitsVort k (P.omegaGe (k + 1) t)

/-- `ν^out_k(y) = A_k⁻¹ ω^{(n)}(t, r_k y) 1_{S_1(t)∪…∪S_{k-1}(t)}(r_k y)` (`06_datum.tex:193-194`). -/
def nuOut (k : ℕ) (t : ℝ) : ℂ → ℝ := P.unitsVort k (P.omegaOut k t)

/-- The **inner field** of ring `k` at ring-`k` time `τ = A_k t` (`06_datum.tex:185-190`):
`h^in_k(τ) = K_BS * ν^in_k - G_k y^⊥/|y|²` (`y^⊥ = i y`), with `ν^in_k` at `t = τ/A_k`. The manuscript
defines it on `N'` at times with `D_{k+1}(t) ⊂ B_{a r_k/8}` (`HInDefined`); the formula is used on
all of `ℂ` and for all `τ`. -/
def hIn (k : ℕ) (τ : ℝ) (y : ℂ) : ℂ :=
  velocity (P.nuIn k (τ / P.A k)) y - (P.G k : ℂ) * (Complex.I * y) / ((‖y‖ ^ 2 : ℝ) : ℂ)

/-- The **outer field** `h^out_k(τ) = K_BS * ν^out_k` (`06_datum.tex:191-194`), defined by the
manuscript at times with `(S_1(t) ∪ … ∪ S_{k-1}(t)) ∩ B_{6 r_k} = ∅` (`HOutDefined`). -/
def hOut (k : ℕ) (τ : ℝ) (y : ℂ) : ℂ := velocity (P.nuOut k (τ / P.A k)) y

/-- The **external field** `h_k = h^in_k + h^out_k` of ring `k` (`06_datum.tex:195-196`). -/
def hField (k : ℕ) (τ : ℝ) (y : ℂ) : ℂ := P.hIn k τ y + P.hOut k τ y

/-- `D_{k+1}(t) ⊂ B_{a r_k/8}` (open disk): `h^in_k(A_k t)` is defined (`06_datum.tex:185`). -/
def HInDefined (k : ℕ) (t : ℝ) : Prop := P.D (k + 1) t ⊆ ball 0 (a * P.r k / 8)

/-- The rings `i < k` lie outside `B_{6 r_k}`: `h^out_k(A_k t)` is defined (`06_datum.tex:191-192`). -/
def HOutDefined (k : ℕ) (t : ℝ) : Prop := ∀ i ∈ Finset.Ico 1 k, P.St i t ∩ ball 0 (6 * P.r k) = ∅

/-- Both fields of ring `k` are defined at time `t` (`06_datum.tex:195`). -/
def HDefined (k : ℕ) (t : ℝ) : Prop := P.HInDefined k t ∧ P.HOutDefined k t

/-! ### Field norms and Duhamel majorants (`def:regions`, last two items) -/

/-- `η^in_k(τ) = ‖h^in_k(τ)‖_{C^{M_h}(N')}` (`06_datum.tex:197-201`); junk when the norm is
infinite (carry `MemCk`, or the definedness hypotheses under which it is finite). -/
def etaIn (Mh k : ℕ) (τ : ℝ) : ℝ := normCk Mh annN' (P.hIn k τ)

/-- `η^out_k(τ) = ‖h^out_k(τ)‖_{C^{M_h}(N')}` (`06_datum.tex:197-201`). -/
def etaOut (Mh k : ℕ) (τ : ℝ) : ℝ := normCk Mh annN' (P.hOut k τ)

/-- `η_k = η^in_k + η^out_k` (`06_datum.tex:200`). -/
def eta (Mh k : ℕ) (τ : ℝ) : ℝ := P.etaIn Mh k τ + P.etaOut Mh k τ

/-- The **Duhamel majorant** of ring `k`, `maj_k(τ) = ∫₀^τ e^{σ_k(τ-v)} η_k(v) dv`
(`06_datum.tex:202-207`; `OneRing.maj`), in ring-`k` time; meaningful if `G_k ≤ G₁` and `h_k` is
defined on `[0, τ/A_k]`. -/
def majK (Mh k : ℕ) (τ : ℝ) : ℝ := OneRing.maj (P.sigma k) (P.eta Mh k) τ

/-- `maj^in_k`, the majorant built from `η^in_k` (`06_datum.tex:209`). -/
def majIn (Mh k : ℕ) (τ : ℝ) : ℝ := OneRing.maj (P.sigma k) (P.etaIn Mh k) τ

/-! ### Basic lemmas (fully proved) -/

theorem D_succ_n (t : ℝ) : P.D (P.n + 1) t = ∅ := by
  simp [D]

theorem omegaGe_succ_n (t : ℝ) : P.omegaGe (P.n + 1) t = 0 := by
  funext x
  simp [omegaGe, D_succ_n]

/-- `G_n = 0` (`lem:inner-circ`; immediate from the definition: `D_{n+1}(0) = ∅`). -/
theorem G_n : P.G P.n = 0 := by
  simp [G, omegaGe_succ_n]

theorem w_apply (k : ℕ) (t : ℝ) (y : ℂ) :
    P.w k t y = ((P.unitsVort k (P.omegaRing k t) y - ringPhi P.χ y : ℝ) : ℂ) := rfl

theorem w_im (k : ℕ) (t : ℝ) (y : ℂ) : (P.w k t y).im = 0 := by
  simp [w]

theorem hField_apply (k : ℕ) (τ : ℝ) (y : ℂ) : P.hField k τ y = P.hIn k τ y + P.hOut k τ y := rfl

theorem eta_apply (Mh k : ℕ) (τ : ℝ) : P.eta Mh k τ = P.etaIn Mh k τ + P.etaOut Mh k τ := rfl

theorem etaIn_nonneg (Mh k : ℕ) (τ : ℝ) : 0 ≤ P.etaIn Mh k τ := normCk_nonneg _ _ _

theorem etaOut_nonneg (Mh k : ℕ) (τ : ℝ) : 0 ≤ P.etaOut Mh k τ := normCk_nonneg _ _ _

theorem eta_nonneg (Mh k : ℕ) (τ : ℝ) : 0 ≤ P.eta Mh k τ :=
  add_nonneg (P.etaIn_nonneg Mh k τ) (P.etaOut_nonneg Mh k τ)

theorem majK_zero (Mh k : ℕ) : P.majK Mh k 0 = 0 := OneRing.maj_zero _ _

theorem majIn_zero (Mh k : ℕ) : P.majIn Mh k 0 = 0 := OneRing.maj_zero _ _

theorem eps_def (k : ℕ) : P.eps k = P.μ * P.s k ^ 5 := rfl

variable {P}

theorem Valid.eps_pos (h : P.Valid) (k : ℕ) : 0 < P.eps k :=
  mul_pos (by linarith [h.datumParams.one_lt_μ]) (pow_pos (h.s_pos k) _)

/-- The sets `S_k` do not depend on the vorticity (they are supports of the terms of `f^{(n)}`). -/
theorem withOm_S (om' : ℝ → ℂ → ℝ) (k : ℕ) : (P.withOm om').S k = P.S k := rfl

end Approx

end Datum

end NonUniqueEuler
