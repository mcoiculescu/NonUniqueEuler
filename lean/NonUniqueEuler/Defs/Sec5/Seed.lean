import NonUniqueEuler.Defs.Sec5.Constants

/-!
# Section 5.4: the seeded ring (`lem:seed`) (definitions)

Manuscript `lem:seed`
(`05_single_ring.tex:1131-1147`).

The seeded ring `Φ^κ = Φ ∘ Y_κ` enters the approximate data of Section 6 (`06_datum.tex:74-80`,
`f^{(n)} = … + A_n Φ^{κ_seed}(·/r_n)`), and `κ_L`, `C_seed` are used by value in Sections 9–10
((SA3), (P4) `C₀ = max{1, 2C_seed, …}`). Following decision D11, the properties of `lem:seed`
are Props and the objects are chosen:
* `PhiOf χ Y κ = Φ ∘ Y_κ` and `seedDiffOf χ Y κ = Φ ∘ Y_κ - Φ` (complexified) for any flow `Y`;
* `IsSeedFlow χ Y κ_L C'`: the flow `Y`, the number `κ_L` and the numbers `C'_k` have the
  properties of `lem:seed` that depend only on `Φ` (everything except the `C_seed` bound);
* `seedData χ` (chosen), `seedFlow χ = Y`, `kL χ = κ_L`, `Cprime χ = C'`, and the seeded ring
  `PhiSeed χ κ = Φ^κ`;
* `IsSeedConst χ s C`: `‖Φ^κ - Φ‖_{H^{M-1}} ≤ Cκ` for `κ ∈ (0,κ_L]` (`M = Mact χ s`), and
  `Cseed χ s` (chosen), which depends on `Φ`, `G₁` and `s`.

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- `Φ ∘ Y_κ` for a flow `Y` (`05_single_ring.tex:1139`). -/
def PhiOf (χ : ℝ → ℝ) (Y : ℝ → ℂ → ℂ) (κ : ℝ) (y : ℂ) : ℝ := ringPhi χ (Y κ y)

/-- `Φ ∘ Y_κ - Φ`, complexified (an element of `X^0`; `05_single_ring.tex:1143-1144`). -/
def seedDiffOf (χ : ℝ → ℝ) (Y : ℝ → ℂ → ℂ) (κ : ℝ) (y : ℂ) : ℂ :=
  ((PhiOf χ Y κ y - ringPhi χ y : ℝ) : ℂ)

/-- **The properties of `lem:seed` that depend only on `Φ`** (`05_single_ring.tex:1131-1147`):
`(Y_κ)_{κ∈ℝ}` is a smooth area-preserving flow on `ℝ²` (jointly `C^∞`, `Y_0 = id`,
`Y_{κ+κ'} = Y_κ ∘ Y_{κ'}`, each `Y_κ` measure preserving), the identity outside a compact subset
of `{a/2 < |y| < 2}`, commuting with `O = O_{2π/3}`; `κ_L > 0`; and for every `κ ∈ (0,κ_L]`,
`Φ^κ = Φ ∘ Y_κ` satisfies: `Φ^κ ∈ C_c^∞`, `Φ^κ ≥ 0`, `Φ^κ` is `3`-fold symmetric (pointwise,
which implies the a.e. form), equimeasurable with `Φ`, `supp Φ^κ ⊂ 𝒩₋`,
`|ℓ_*(0)(Φ^κ - Φ)| ∈ [κ/2, 2κ]`, and `‖Φ^κ - Φ - 2κ Re φ_*(0)‖_{H^k} ≤ C'_k κ²` for every `k`
(with the membership in `H^k` made explicit). The bound `‖Φ^κ - Φ‖_{H^{M-1}} ≤ C_seed κ` is
`IsSeedConst`. -/
structure IsSeedFlow (χ : ℝ → ℝ) (Y : ℝ → ℂ → ℂ) (κL : ℝ) (C' : ℕ → ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => Y p.1 p.2)
  zero : ∀ y, Y 0 y = y
  add : ∀ κ κ' y, Y (κ + κ') y = Y κ (Y κ' y)
  measurePreserving : ∀ κ, MeasurePreserving (Y κ) volume volume
  eq_self_off : ∃ K : Set ℂ, IsCompact K ∧ K ⊆ {y : ℂ | a / 2 < ‖y‖ ∧ ‖y‖ < 2} ∧
    ∀ κ : ℝ, ∀ y ∉ K, Y κ y = y
  rot_comm : ∀ κ y, Y κ (rot (2 * Real.pi / 3) y) = rot (2 * Real.pi / 3) (Y κ y)
  kL_pos : 0 < κL
  phi_contDiff : ∀ κ ∈ Ioc (0 : ℝ) κL, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (PhiOf χ Y κ)
  phi_hasCompactSupport : ∀ κ ∈ Ioc (0 : ℝ) κL, HasCompactSupport (PhiOf χ Y κ)
  phi_nonneg : ∀ κ ∈ Ioc (0 : ℝ) κL, ∀ y, 0 ≤ PhiOf χ Y κ y
  phi_sym : ∀ κ ∈ Ioc (0 : ℝ) κL, ∀ y, PhiOf χ Y κ (rot (2 * Real.pi / 3) y) = PhiOf χ Y κ y
  phi_equimeasurable : ∀ κ ∈ Ioc (0 : ℝ) κL, Equimeasurable (PhiOf χ Y κ) (ringPhi χ)
  phi_tsupport : ∀ κ ∈ Ioc (0 : ℝ) κL, tsupport (PhiOf χ Y κ) ⊆ annNm
  ell_mem : ∀ κ ∈ Ioc (0 : ℝ) κL, ‖Eig.ellFn χ 0 (seedDiffOf χ Y κ)‖ ∈ Icc (κ / 2) (2 * κ)
  expansion_memH : ∀ κ ∈ Ioc (0 : ℝ) κL, ∀ k : ℕ,
    Sob.MemH k (fun y => seedDiffOf χ Y κ y - modeFn χ 0 κ y)
  expansion : ∀ κ ∈ Ioc (0 : ℝ) κL, ∀ k : ℕ,
    Sob.normH k (fun y => seedDiffOf χ Y κ y - modeFn χ 0 κ y) ≤ C' k * κ ^ 2

open Classical in
/-- The data `(Y, κ_L, C')` of `lem:seed` (chosen; junk `(id, 1, 0)` when none exist). -/
def seedData (χ : ℝ → ℝ) : (ℝ → ℂ → ℂ) × ℝ × (ℕ → ℝ) :=
  if h : ∃ d : (ℝ → ℂ → ℂ) × ℝ × (ℕ → ℝ), IsSeedFlow χ d.1 d.2.1 d.2.2 then h.choose
  else (fun _ y => y, 1, fun _ => 0)

/-- The flow `(Y_κ)` of `lem:seed` (`05_single_ring.tex:1134-1136`). -/
def seedFlow (χ : ℝ → ℝ) : ℝ → ℂ → ℂ := (seedData χ).1

/-- `κ_L` of `lem:seed` (`05_single_ring.tex:1137`). -/
def kL (χ : ℝ → ℝ) : ℝ := (seedData χ).2.1

/-- The numbers `C'_k` of `lem:seed` (`05_single_ring.tex:1137`). -/
def Cprime (χ : ℝ → ℝ) : ℕ → ℝ := (seedData χ).2.2

/-- **The seeded ring** `Φ^κ = Φ ∘ Y_κ` (`05_single_ring.tex:1139`). -/
def PhiSeed (χ : ℝ → ℝ) (κ : ℝ) (y : ℂ) : ℝ := PhiOf χ (seedFlow χ) κ y

/-- `C` works as `C_seed` for `s` (`05_single_ring.tex:1143`): for `κ ∈ (0,κ_L]`,
`Φ^κ - Φ ∈ H^{M-1}` and `‖Φ^κ - Φ‖_{H^{M-1}} ≤ Cκ`, `M = Mact χ s = s + N_G + 2`. -/
def IsSeedConst (χ : ℝ → ℝ) (s : ℕ) (C : ℝ) : Prop :=
  ∀ κ ∈ Ioc (0 : ℝ) (kL χ),
    Sob.MemH (Mact χ s - 1) (seedDiffOf χ (seedFlow χ) κ) ∧
      Sob.normH (Mact χ s - 1) (seedDiffOf χ (seedFlow χ) κ) ≤ C * κ

open Classical in
/-- `C_seed` of `lem:seed` for `s` (chosen among the nonnegative constants with `IsSeedConst`;
junk `0`). -/
def Cseed (χ : ℝ → ℝ) (s : ℕ) : ℝ :=
  if h : ∃ C : ℝ, 0 ≤ C ∧ IsSeedConst χ s C then h.choose else 0

/-! ### Basic lemmas (fully proved) -/

/-- If data for `lem:seed` exist, the chosen ones have the properties. -/
theorem seedData_spec {χ : ℝ → ℝ}
    (h : ∃ (Y : ℝ → ℂ → ℂ) (κL : ℝ) (C' : ℕ → ℝ), IsSeedFlow χ Y κL C') :
    IsSeedFlow χ (seedFlow χ) (kL χ) (Cprime χ) := by
  classical
  have h' : ∃ d : (ℝ → ℂ → ℂ) × ℝ × (ℕ → ℝ), IsSeedFlow χ d.1 d.2.1 d.2.2 := by
    obtain ⟨Y, κL, C', hY⟩ := h
    exact ⟨(Y, κL, C'), hY⟩
  have hc : seedData χ = h'.choose := by
    rw [seedData, dite_eq_left h']
  rw [seedFlow, kL, Cprime, hc]
  exact h'.choose_spec

theorem Cseed_spec {χ : ℝ → ℝ} {s : ℕ} (h : ∃ C : ℝ, 0 ≤ C ∧ IsSeedConst χ s C) :
    0 ≤ Cseed χ s ∧ IsSeedConst χ s (Cseed χ s) := by
  classical
  rw [Cseed, dite_eq_left h]
  exact h.choose_spec

theorem Cseed_nonneg (χ : ℝ → ℝ) (s : ℕ) : 0 ≤ Cseed χ s := by
  classical
  rw [Cseed]
  split_ifs with h
  · exact h.choose_spec.1
  · exact le_rfl

theorem PhiSeed_apply (χ : ℝ → ℝ) (κ : ℝ) (y : ℂ) :
    PhiSeed χ κ y = ringPhi χ (seedFlow χ κ y) := rfl

end OneRing

end NonUniqueEuler
