import NonUniqueEuler.Defs.Sec10.Lists

/-!
# Section 10: the parameters of the construction as one record (definitions)

Manuscript `10_parameters.tex`:
the choices (P0)–(P6) (`def:P0-P4` `:20-71`, `def:P5` `:96-120`, `def:P6` `:132-168`), Table
`tab:param` (`:188-218`), and `lem:nonempty` (`:278-390`): "none of the choices depends on `n`,
`A₁` or `ω^{(n)}`", and "if (P0)–(P6) hold, then for every `n ≥ 2` and every `A₁ > 0` the standing
assumptions (SA) hold with these parameters, and (Det) holds".

* `Relay.Params`: the numbers chosen in Section 10, `χ, s, σ', δ₀, μ, T_pin, κ_seed, s̄` (the
  cutoff `χ` is fixed "once and for all", decision D12). They do not contain `n`, `A₁` or
  `ω^{(n)}`.
* `p.approx A₁ n`, `p.standing A₁ n`: the approximation `Approx.ofParams` and the standing datum of
  Section 9 at amplitude `A₁` and depth `n` (`ω^{(n)} = Smooth.sol f^{(n)}`); this is the setting of
  Section 11 ("fix `A₁ > 0` and `n ≥ 2`", `11_bootstrap.tex:12-18`).
* `p.ref = p.standing 1 2`: a reference standing datum. The lists (P0)–(P6) are the conditions
  `Standing.StructuralList`, `Standing.KappaList`, `Standing.SbarList` of `Defs/Sec10/Lists.lean`
  for `p.ref`: `p.Structural`, `p.KappaOK`, `p.SbarOK`, `p.Lists`. The choice `A₁ = 1`, `n = 2` is
  immaterial: `lists_iff` (and `structural_iff`, `kappaList_iff`, `sbarList_iff`) show that the
  conditions for `p.standing A₁ n` are the same for all `A₁`, `n` (none of them reads `A₁`, `n` or
  `ω^{(n)}`; each transfer is a re-packaging of definitionally equal fields).
* `Lists.holds`, `Lists.det`: (P0)–(P6) give (SA) and (Det) for `p.standing A₁ n`, every `A₁ > 0`,
  `n ≥ 2` (the last sentence of `lem:nonempty`; bookkeeping, fully proved).
* the `n`-independent numbers of Section 11: `p.Tstar A₁` (`T_*` of `lem:time`), `p.c0 A₁`
  (`c₀ = ½A₁c_outδ₀`), the datum `p.datum A₁` (`f` of `def:datum`) and `p.approxVort A₁ n`
  (`ω^{(n)}`); `standing_Tstar` etc. identify them with the standing-datum objects by `rfl`.

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- **The parameters of the construction** (`def:P0-P4`, `def:P5`, `def:P6`, Table `tab:param`,
`10_parameters.tex:20-218`): the cutoff `χ` of `def:ring` (fixed once and for all, D12), the
integer `s` and the rate `σ'` of (P0.2), the saturation level `δ₀` of (P1), the amplitude ratio
`μ` of (P2), the pinning time `T_pin` of (P3), the seed size `κ_seed` of (P5) and the scale ratio
`s̄` of (P6). Every other quantity of Section 10 is a function of these (the constants of (P0),
(P4) and the derived ones of Section 9). The depth `n`, the amplitude `A₁` and `ω^{(n)}` are not
parameters (`10_parameters.tex:13-15`). The conditions are `Params.Lists`. -/
structure Params where
  /-- the cutoff `χ` of `def:ring` (`Φ = ringPhi χ`) -/
  χ : ℝ → ℝ
  /-- the Sobolev index `s ≥ 3` of (P0.2) -/
  s : ℕ
  /-- the rate `σ'` of (P0.2) -/
  σ' : ℝ
  /-- the saturation level `δ₀` of (P1) -/
  δ₀ : ℝ
  /-- the amplitude ratio `μ` of (P2) -/
  μ : ℝ
  /-- the pinning time `T_pin` of (P3) -/
  Tpin : ℝ
  /-- the seed size `κ_seed` of (P5) -/
  κs : ℝ
  /-- the scale ratio `s̄` of (P6) -/
  sbar : ℝ

namespace Params

variable (p : Params)

/-- The objects of `def:datum`–`def:clock` with the parameters `p`, the amplitude `A₁` and the
depth `n` (`ω^{(n)} = Smooth.sol f^{(n)}`; (SA3), `09_relay.tex:43-48`). -/
def approx (A₁ : ℝ) (n : ℕ) : Approx := Approx.ofParams p.χ A₁ p.μ p.sbar p.κs n p.δ₀ p.Tpin

/-- The standing datum of Section 9 with the parameters `p`, the amplitude `A₁` and the depth `n`
(the setting of Section 11, `11_bootstrap.tex:12-18`). -/
def standing (A₁ : ℝ) (n : ℕ) : Standing := ⟨p.approx A₁ n, p.s, p.σ'⟩

/-- The reference standing datum `p.standing 1 2`, used to state the lists (P0)–(P6), which do not
depend on `A₁` and `n` (`lists_iff`). -/
def ref : Standing := p.standing 1 2

/-- **The structural list (P0)–(P4)** for `p` (`def:P0-P4`; `Standing.StructuralList`). -/
def Structural : Prop := p.ref.StructuralList

/-- **The κ-list (P5)** for `p` (`def:P5`): `κ_seed > 0` and (κ1)–(κ7) for every `κ ∈ (0, 2κ_seed]`
(`Standing.KappaList` with `κs = p.κs`). -/
def KappaOK : Prop := p.ref.KappaList p.κs

/-- **The s̄-list (P6)** for `p` (`def:P6`; `Standing.SbarList`). -/
def SbarOK : Prop := p.ref.SbarList

/-- **The parameter lists (P0)–(P6)** for `p` (`def:P0-P4`, `def:P5`, `def:P6`;
`Standing.ParamLists` of the reference datum; fields `structural`, `kappa`, `sbar`). -/
def Lists : Prop := p.ref.ParamLists

/-- The datum `f` of `def:datum` with the parameters `p` and the amplitude `A₁`
(`06_datum.tex:22-23`, the statement layer's `datum`). -/
def datum (A₁ : ℝ) : ℂ → ℝ := NonUniqueEuler.datum p.χ A₁ p.μ p.sbar

/-- The approximate solution `ω^{(n)} = Smooth.sol f^{(n)}` (`def:approx`, `06_datum.tex:76-80`). -/
def approxVort (A₁ : ℝ) (n : ℕ) : ℝ → ℂ → ℝ :=
  Smooth.sol (approxDatum p.χ A₁ p.μ p.sbar p.κs n)

/-- `T_*` of `lem:time` (`09_relay.tex:1468-1471`) for the parameters `p` and the amplitude `A₁`;
it does not depend on `n` (`standing_Tstar`). -/
def Tstar (A₁ : ℝ) : ℝ := (p.standing A₁ 2).Tstar

/-- `c₀ = ½A₁c_outδ₀` of `lem:readout` / `thm:Rsharp` (`09_relay.tex:1421`, `11_bootstrap.tex:627`)
for the parameters `p` and the amplitude `A₁`; it does not depend on `n` (`standing_c0`). -/
def c0 (A₁ : ℝ) : ℝ := (p.standing A₁ 2).c0

/-! ### Basic lemmas (fully proved) -/

@[simp] theorem standing_P (A₁ : ℝ) (n : ℕ) : (p.standing A₁ n).P = p.approx A₁ n := rfl
@[simp] theorem standing_s (A₁ : ℝ) (n : ℕ) : (p.standing A₁ n).s = p.s := rfl
@[simp] theorem standing_σ' (A₁ : ℝ) (n : ℕ) : (p.standing A₁ n).σ' = p.σ' := rfl
@[simp] theorem approx_χ (A₁ : ℝ) (n : ℕ) : (p.approx A₁ n).χ = p.χ := rfl
@[simp] theorem approx_A₁ (A₁ : ℝ) (n : ℕ) : (p.approx A₁ n).A₁ = A₁ := rfl
@[simp] theorem approx_μ (A₁ : ℝ) (n : ℕ) : (p.approx A₁ n).μ = p.μ := rfl
@[simp] theorem approx_sbar (A₁ : ℝ) (n : ℕ) : (p.approx A₁ n).sbar = p.sbar := rfl
@[simp] theorem approx_κs (A₁ : ℝ) (n : ℕ) : (p.approx A₁ n).κs = p.κs := rfl
@[simp] theorem approx_n (A₁ : ℝ) (n : ℕ) : (p.approx A₁ n).n = n := rfl
@[simp] theorem approx_δ₀ (A₁ : ℝ) (n : ℕ) : (p.approx A₁ n).δ₀ = p.δ₀ := rfl
@[simp] theorem approx_Tpin (A₁ : ℝ) (n : ℕ) : (p.approx A₁ n).Tpin = p.Tpin := rfl

theorem approx_om (A₁ : ℝ) (n : ℕ) : (p.approx A₁ n).om = p.approxVort A₁ n := rfl

theorem approx_f (A₁ : ℝ) (n : ℕ) :
    (p.approx A₁ n).f = approxDatum p.χ A₁ p.μ p.sbar p.κs n := rfl

theorem approx_datumF (A₁ : ℝ) (n : ℕ) : (p.approx A₁ n).datumF = p.datum A₁ := rfl

theorem approxVort_def (A₁ : ℝ) (n : ℕ) :
    p.approxVort A₁ n = Smooth.sol (approxDatum p.χ A₁ p.μ p.sbar p.κs n) := rfl

theorem datum_def (A₁ : ℝ) : p.datum A₁ = NonUniqueEuler.datum p.χ A₁ p.μ p.sbar := rfl

/-- `T_*` does not depend on the depth `n`. -/
theorem standing_Tstar (A₁ : ℝ) (n : ℕ) : (p.standing A₁ n).Tstar = p.Tstar A₁ := rfl

/-- `c₀` does not depend on the depth `n`. -/
theorem standing_c0 (A₁ : ℝ) (n : ℕ) : (p.standing A₁ n).c0 = p.c0 A₁ := rfl

theorem c0_def (A₁ : ℝ) : p.c0 A₁ = 1 / 2 * A₁ * Eig.cout p.χ * p.δ₀ := rfl

/-- The approximation of `p.standing A₁ n` is valid when the parameters are in their ranges. -/
theorem approx_valid {A₁ : ℝ} {n : ℕ} (hχ : IsAdmissibleCutoff p.χ)
    (hp : DatumParams A₁ p.μ p.sbar) (hn : 2 ≤ n) (hκ : 0 < p.κs)
    (hκ' : p.κs ≤ OneRing.kL p.χ) (hδ : 0 < p.δ₀) (hT : 0 < p.Tpin) :
    (p.approx A₁ n).Valid :=
  Approx.ofParams_valid hχ hp hn hκ hκ' hδ hT

/-! ### Independence of the lists of `A₁` and `n` -/

/-- (P0)–(P4) for `p.standing A₁ n` do not depend on `A₁`, `n`. -/
theorem structural_congr {A₁ A₁' : ℝ} {n n' : ℕ} (h : (p.standing A₁ n).StructuralList) :
    (p.standing A₁' n').StructuralList :=
  ⟨⟨h.p0.three_le_s, h.p0.σ'_gt, h.p0.σ'_lt_sigb, h.p0.σ'_lt_sigma⟩,
    ⟨h.p1.δ₀_pos, h.p1.δ₀_le_dH, h.p1.δ₀_le_kick, h.p1.δ₀_le_rd⟩,
    ⟨h.p2.one_lt_μ, h.p2.μ_le⟩, ⟨h.p3.Tpin_pos, h.p3.rT_le⟩⟩

/-- (κ1)–(κ7) at `κ` for `p.standing A₁ n` do not depend on `A₁`, `n`. -/
theorem condKappa_congr {A₁ A₁' : ℝ} {n n' : ℕ} {κ : ℝ} (h : (p.standing A₁ n).CondKappa κ) :
    (p.standing A₁' n').CondKappa κ :=
  ⟨h.k1, h.k2, h.k3, h.k4, h.k5, h.k6, h.k7⟩

/-- (P5) for `p.standing A₁ n` does not depend on `A₁`, `n`. -/
theorem kappaList_congr {A₁ A₁' : ℝ} {n n' : ℕ} {κs : ℝ} (h : (p.standing A₁ n).KappaList κs) :
    (p.standing A₁' n').KappaList κs :=
  ⟨h.1, fun κ hκ => p.condKappa_congr (h.2 κ hκ)⟩

/-- (P6) for `p.standing A₁ n` does not depend on `A₁`, `n`. -/
theorem sbarList_congr {A₁ A₁' : ℝ} {n n' : ℕ} (h : (p.standing A₁ n).SbarList) :
    (p.standing A₁' n').SbarList :=
  ⟨h.sbar_pos, h.b1_le, h.b1_pow, h.b2, h.b3, h.b4, h.b5, h.b6,
    ⟨⟨h.b7.small.KO_sbar, h.b7.small.CO_KO_sbar, h.b7.small.KO_mu_sbar⟩, h.b7.e22⟩,
    h.b8_etab, h.b8_level, h.b8_seed, h.b9_maj, h.b9_eta, h.b10, h.b11_handoff, h.b11_kick⟩

/-- (P0)–(P6) for `p.standing A₁ n` do not depend on `A₁`, `n`. -/
theorem paramLists_congr {A₁ A₁' : ℝ} {n n' : ℕ} (h : (p.standing A₁ n).ParamLists) :
    (p.standing A₁' n').ParamLists :=
  ⟨p.structural_congr h.structural, p.kappaList_congr h.kappa, p.sbarList_congr h.sbar⟩

theorem structural_iff (A₁ : ℝ) (n : ℕ) : (p.standing A₁ n).StructuralList ↔ p.Structural :=
  ⟨p.structural_congr, p.structural_congr⟩

theorem kappaList_iff (A₁ : ℝ) (n : ℕ) : (p.standing A₁ n).KappaList p.κs ↔ p.KappaOK :=
  ⟨p.kappaList_congr, p.kappaList_congr⟩

theorem sbarList_iff (A₁ : ℝ) (n : ℕ) : (p.standing A₁ n).SbarList ↔ p.SbarOK :=
  ⟨p.sbarList_congr, p.sbarList_congr⟩

/-- **The lists (P0)–(P6) do not depend on `A₁`, `n`, `ω^{(n)}`** (`lem:nonempty`,
`10_parameters.tex:286`, `:373-375`). -/
theorem lists_iff (A₁ : ℝ) (n : ℕ) : (p.standing A₁ n).ParamLists ↔ p.Lists :=
  ⟨p.paramLists_congr, p.paramLists_congr⟩

theorem lists_iff_and : p.Lists ↔ p.Structural ∧ p.KappaOK ∧ p.SbarOK :=
  ⟨fun h => ⟨h.structural, h.kappa, h.sbar⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- The structural list does not depend on `κ_seed` and `s̄` (Table `tab:param`: they are chosen
after (P0)–(P4)). -/
theorem structural_with {κs sbar : ℝ} (h : p.Structural) :
    ({ p with κs := κs, sbar := sbar } : Params).Structural :=
  ⟨⟨h.p0.three_le_s, h.p0.σ'_gt, h.p0.σ'_lt_sigb, h.p0.σ'_lt_sigma⟩,
    ⟨h.p1.δ₀_pos, h.p1.δ₀_le_dH, h.p1.δ₀_le_kick, h.p1.δ₀_le_rd⟩,
    ⟨h.p2.one_lt_μ, h.p2.μ_le⟩, ⟨h.p3.Tpin_pos, h.p3.rT_le⟩⟩

/-- (κ1)–(κ7) do not depend on `κ_seed` and `s̄` (Table `tab:param`: they involve only the
quantities of (P0)–(P4)). -/
theorem condKappa_with {κs sbar κ : ℝ} (h : p.ref.CondKappa κ) :
    ({ p with κs := κs, sbar := sbar } : Params).ref.CondKappa κ :=
  ⟨h.k1, h.k2, h.k3, h.k4, h.k5, h.k6, h.k7⟩

/-- The κ-list for a seed size `κ` with the other parameters of `p`: `κ` is admissible in (P5)
iff `p.ref.KappaList κ` (the set of admissible seed sizes of `lem:nonempty` is
`{κ | p.ref.KappaList κ}`). -/
theorem kappaOK_with_iff {κs sbar : ℝ} :
    ({ p with κs := κs, sbar := sbar } : Params).KappaOK ↔ p.ref.KappaList κs :=
  ⟨fun h => ⟨h.1, fun κ hκ =>
      have c := h.2 κ hκ
      ⟨c.k1, c.k2, c.k3, c.k4, c.k5, c.k6, c.k7⟩⟩,
    fun h => ⟨h.1, fun κ hκ => p.condKappa_with (h.2 κ hκ)⟩⟩

/-- **The lists can be satisfied** (the logical step from `lem:nonempty` to a choice of all the
parameters, `11_bootstrap.tex:724-725`): if (P0)–(P4) hold for some parameters `p` with cutoff `χ`
(the fields `κs`, `sbar` of `p` are irrelevant), the admissible seed sizes contain an interval
`(0, κ†]`, and for every admissible seed size the admissible `s̄` contain an interval `(0, s̄₀]`,
then some parameters with cutoff `χ` satisfy (P0)–(P6). The hypothesis is the shape recommended
for the interface `lem:nonempty`. -/
theorem exists_lists_of {χ : ℝ → ℝ}
    (h : ∃ p : Params, p.χ = χ ∧ p.Structural ∧
      (∃ κdag : ℝ, 0 < κdag ∧ ∀ κ ∈ Ioc (0 : ℝ) κdag, p.ref.KappaList κ) ∧
      ∀ κ : ℝ, p.ref.KappaList κ → ∃ sbar₀ : ℝ, 0 < sbar₀ ∧ ∀ sbar ∈ Ioc (0 : ℝ) sbar₀,
        ({ p with κs := κ, sbar := sbar } : Params).SbarOK) :
    ∃ p : Params, p.χ = χ ∧ p.Lists := by
  obtain ⟨p, hχ, hS, ⟨κd, hκd, hK⟩, hB⟩ := h
  have hKd : p.ref.KappaList κd := hK κd ⟨hκd, le_rfl⟩
  obtain ⟨s₀, hs₀, hsb⟩ := hB κd hKd
  refine ⟨{ p with κs := κd, sbar := s₀ }, hχ, ?_⟩
  exact ⟨p.structural_with hS, p.kappaOK_with_iff.2 hKd, hsb s₀ ⟨hs₀, le_rfl⟩⟩

/-! ### (SA) and (Det) from the lists (`lem:nonempty`, last sentence) -/

variable {p}

/-- **(P0)–(P6) give (SA)** for every `A₁ > 0` and `n ≥ 2` (`lem:nonempty`,
`10_parameters.tex:287-289`, `:377-389`), given (N) and an admissible cutoff. -/
theorem Lists.holds (hL : p.Lists) (hχ : IsAdmissibleCutoff p.χ)
    (hN : NumericalHypothesis p.χ) {A₁ : ℝ} (hA₁ : 0 < A₁) {n : ℕ} (hn : 2 ≤ n) :
    (p.standing A₁ n).Holds :=
  Standing.ParamLists.holds (p.paramLists_congr hL) hN hχ hA₁ hn rfl

/-- **(P0)–(P6) give (Det)** for every `A₁` and `n` (it is (B4), `10_parameters.tex:388-389`). -/
theorem Lists.det (hL : p.Lists) (A₁ : ℝ) (n : ℕ) : (p.standing A₁ n).Det :=
  Standing.ParamLists.det (p.paramLists_congr hL)

/-- The lists for `p.standing A₁ n`. -/
theorem Lists.standing (hL : p.Lists) (A₁ : ℝ) (n : ℕ) : (p.standing A₁ n).ParamLists :=
  p.paramLists_congr hL

theorem Lists.one_lt_μ (hL : p.Lists) : 1 < p.μ := hL.structural.p2.one_lt_μ

/-- `μ ≤ μ_max ≤ 17/16` (`11_bootstrap.tex:725`). -/
theorem Lists.μ_le (hL : p.Lists) : p.μ ≤ 17 / 16 := hL.structural.p2.mu_le_muMax_le

theorem Lists.sbar_pos (hL : p.Lists) : 0 < p.sbar := hL.sbar.sbar_pos

/-- `s̄ ≤ a/16` by (B1) (`11_bootstrap.tex:726`). -/
theorem Lists.sbar_le (hL : p.Lists) : p.sbar ≤ a / 16 := hL.sbar.b1_le

theorem Lists.kseed_pos (hL : p.Lists) : 0 < p.κs := hL.kappa.pos

theorem Lists.δ₀_pos (hL : p.Lists) : 0 < p.δ₀ := hL.structural.p1.δ₀_pos

theorem Lists.Tpin_pos (hL : p.Lists) : 0 < p.Tpin := hL.structural.p3.Tpin_pos

/-- `κ_seed ≤ κ_L` by (κ6) at `κ = 2κ_seed`. -/
theorem Lists.kseed_le (hL : p.Lists) : p.κs ≤ OneRing.kL p.χ := hL.kappa.le_kL

/-- `2κ_seed < δ₀` by (κ1) at `κ = 2κ_seed` (`11_bootstrap.tex:236`, `:687-688`). -/
theorem Lists.two_kseed_lt_δ₀ (hL : p.Lists) : 2 * p.κs < p.δ₀ :=
  hL.kappa.two_lt_δ₀ hL.δ₀_pos hL.one_lt_μ

/-- The parameter ranges of `def:datum` for every `A₁ > 0`. -/
theorem Lists.datumParams (hL : p.Lists) {A₁ : ℝ} (hA₁ : 0 < A₁) : DatumParams A₁ p.μ p.sbar :=
  ⟨hA₁, hL.one_lt_μ, by linarith [hL.μ_le], hL.sbar_pos, hL.sbar_le⟩

/-- The approximation `p.approx A₁ n` is valid for an admissible cutoff, `A₁ > 0`, `n ≥ 2`. -/
theorem Lists.approx_valid (hL : p.Lists) (hχ : IsAdmissibleCutoff p.χ) {A₁ : ℝ} (hA₁ : 0 < A₁)
    {n : ℕ} (hn : 2 ≤ n) : (p.approx A₁ n).Valid :=
  p.approx_valid hχ (hL.datumParams hA₁) hn hL.kseed_pos hL.kseed_le hL.δ₀_pos hL.Tpin_pos

end Params

end Relay

end NonUniqueEuler
