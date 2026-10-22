import NonUniqueEuler.Defs.Sec2.BiotSavart

/-!
# Section 2: Sobolev calculus (`lem:Hk-calculus`), definitions and named constants

Definitions for Lemma `lem:Hk-calculus` (`02_prelim.tex:643-668`). Sobolev spaces are I-HK
(`Defs/Infra/Sobolev.lean`, namespace `Sob`): `MemH`, `normH`, `MemHOn`, `normHOn`, `MemW1infOn`,
`normW1infOn`, `weakPartial(On)`, and `dotGrad U w = U·∇w` for a real vector field `U : ℂ → ℂ`. The
embeddings `lem:embed` (E1)–(E3) are the I-HK interface theorems `Sob.L4_le`, `Sob.Linf_le_H2`,
`Sob.interp` (`I/Infra/Sobolev/Embed*.lean`, `Interp.lean`); they need no definitions.

* `hkComm N₁ α U w`: the commutator `[∂^α, U·∇]w = ∂^α(U·∇w) - U·∇∂^α w`, both terms extended by
  `0` outside `N₁` (`02_prelim.tex:667-668`);
* `weakDivOn V U`: the weak divergence `∂₁U₁ + ∂₂U₂` on `V` ("`div U = 0` on `N₁`");
* `HkCalcSetting N N₁ χN`: the standing assumptions of the lemma (`N` compact, `N₁ ⊇ N` open and
  bounded, `χ_N ∈ C_c^∞(N₁)` equal to `1` near `N`);
* the named constants. Section 5 fixes "a constant `C_P(k)` of `lem:Hk-calculus` for `max(k,3)`,
  `N`, `N₁`, `χ_N`" and "a constant `C^el_j` of `lem:Hk-calculus`(3) for `j`, `χ_B`, `ρ = 4`"
  (`05_single_ring.tex:222-227`) and builds later constants from them (`C_B`, `C_BS`, `C_HK`).
  Following decision D11 the defining properties are Props here (`IsHkCommConst`,
  `IsHkProdConst`, `IsHkCalcConst`, `IsHkBSConst`) and the constants are chosen
  (`hkCalcConst`, `elConst`); the existence statements `∃ C, 0 < C ∧ …` are proved in the
  interface layer (`I/Sec2/…`).

Deviation: in item (1) the manuscript allows complex vector fields `U`; here
`U : ℂ → ℂ` is a real vector field (D1), which covers every use (`lem:energy`,
`05_single_ring.tex:345-352`, applies (1) to the real field `U = Ω x^⊥ + h + K_BS ∗ w`). The
complex case follows by linearity from the real and imaginary parts. The cutoffs `χ_N`, `χ` are
real valued. Supports of Sobolev functions are a.e. statements (`∀ᵐ x, x ∉ N → w x = 0`), as in
I-HK; this weakens the hypotheses (and so strengthens the lemma) only on null sets, plus, in (3),
it allows the essential support of `w` to touch `∂B_ρ`; the proof by mollification still applies
(approximants supported in `B_{ρ+ε}` and `lem:BS-basic`(c) with radius `2ρ`).

All lemmas in this file are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

/-- The commutator `[∂^α, U·∇]w = ∂^α(U·∇w) - U·∇∂^α w` of `lem:Hk-calculus`(1), "with both terms
extended by `0` outside `N₁`" (`02_prelim.tex:667-668`). `∂^α(U·∇w)` is the weak derivative on
`N₁` (the field `U` is only given on `N₁`); `∂^α w` and `∇∂^α w` are weak derivatives on the
plane (`w ∈ H^{k+1}(ℝ²)`). -/
def hkComm (N₁ : Set ℂ) (α : ℕ × ℕ) (U w : ℂ → ℂ) : ℂ → ℂ :=
  N₁.indicator fun x => weakPartialOn N₁ α (dotGrad U w) x - dotGrad U (weakPartial α w) x

/-- The weak divergence `∂₁U₁ + ∂₂U₂` on `V` of a real vector field `U = U₁ + i U₂`. -/
def weakDivOn (V : Set ℂ) (U : ℂ → ℂ) (x : ℂ) : ℝ :=
  (weakPartialOn V (1, 0) U x).re + (weakPartialOn V (0, 1) U x).im

/-- The standing assumptions of `lem:Hk-calculus` (`02_prelim.tex:646-649`), apart from the
integer `k ≥ 3`: `N ⊆ ℝ²` compact, `N₁ ⊇ N` open and bounded, and `χ_N ∈ C_c^∞(N₁)` with
`χ_N = 1` on a neighborhood of `N`. -/
structure HkCalcSetting (N N₁ : Set ℂ) (χN : ℂ → ℝ) : Prop where
  isCompact : IsCompact N
  isOpen : IsOpen N₁
  isBounded : Bornology.IsBounded N₁
  subset : N ⊆ N₁
  contDiff : ContDiff ℝ ∞ χN
  hasCompactSupport : HasCompactSupport χN
  tsupport_subset : tsupport χN ⊆ N₁
  eq_one_near : ∃ V : Set ℂ, IsOpen V ∧ N ⊆ V ∧ ∀ x ∈ V, χN x = 1

/-- `C` is a constant for `lem:Hk-calculus`(1) (`02_prelim.tex:651-660`): for `w ∈ H^{k+1}`
vanishing outside `N`, a real vector field `U ∈ W^{1,∞}(N₁) ∩ H^k(N₁)` and `|α| ≤ k`, the weak
derivative `∂^α(U·∇w)` exists in `L²(N₁)`, the commutator lies in `L²` with
`‖[∂^α, U·∇]w‖_{L²} ≤ C (‖U‖_{W^{1,∞}(N₁)} + ‖U‖_{H^k(N₁)}) ‖w‖_{H^k}`, and if `div U = 0` on
`N₁`, then `|Re ⟨∂^α(U·∇w), ∂^α w⟩_{L²}| ≤ C (‖U‖_{W^{1,∞}(N₁)} + ‖U‖_{H^k(N₁)}) ‖w‖²_{H^k}`,
and the inner product is real when `w` is real. In the inner product `∂^α(U·∇w)` is extended by
`0` outside `N₁` (the chosen weak derivative is unspecified there; `∂^α w = 0` a.e. outside
`N ⊆ N₁` anyway). -/
def IsHkCommConst (k : ℕ) (N N₁ : Set ℂ) (C : ℝ) : Prop :=
  ∀ w U : ℂ → ℂ, MemH (k + 1) w → (∀ᵐ x, x ∉ N → w x = 0) → MemW1infOn N₁ U → MemHOn k N₁ U →
    ∀ α ∈ multiIdx k,
      (∃ G : ℂ → ℂ, MemLp G 2 (volume.restrict N₁) ∧
        HasWeakDerivOn N₁ (pdList α) (dotGrad U w) G) ∧
      MemLp (hkComm N₁ α U w) 2 volume ∧
      l2 (hkComm N₁ α U w) ≤ C * (normW1infOn N₁ U + normHOn k N₁ U) * normH k w ∧
      ((∀ᵐ x ∂(volume.restrict N₁), weakDivOn N₁ U x = 0) →
        |(Prelim.innerL2 (N₁.indicator (weakPartialOn N₁ α (dotGrad U w)))
            (weakPartial α w)).re| ≤
            C * (normW1infOn N₁ U + normHOn k N₁ U) * normH k w ^ 2 ∧
          ((∀ᵐ x, (w x).im = 0) →
            (Prelim.innerL2 (N₁.indicator (weakPartialOn N₁ α (dotGrad U w)))
              (weakPartial α w)).im = 0))

/-- `C` is a constant for `lem:Hk-calculus`(2) (`02_prelim.tex:661-662`):
`‖gh‖_{H^j} ≤ C ‖g‖_{H^j} ‖h‖_{H^j}` for every `2 ≤ j ≤ k` and `g, h ∈ H^j`. -/
def IsHkProdConst (k : ℕ) (C : ℝ) : Prop :=
  ∀ j : ℕ, 2 ≤ j → j ≤ k → ∀ g h : ℂ → ℂ, MemH j g → MemH j h →
    MemH j (g * h) ∧ normH j (g * h) ≤ C * normH j g * normH j h

/-- `C` is a constant of `lem:Hk-calculus` for `k`, `N`, `N₁` in the sense of
`05_single_ring.tex:226` (`C_P(k)`): it works in items (1) and (2). -/
def IsHkCalcConst (k : ℕ) (N N₁ : Set ℂ) (C : ℝ) : Prop :=
  IsHkCommConst k N N₁ C ∧ IsHkProdConst k C

/-- `C'` is a constant for `lem:Hk-calculus`(3) (`02_prelim.tex:663-666`) for `j`, `χ`, `ρ`:
for every `w ∈ H^j` vanishing outside `B_ρ`, `χ (K_BS ∗ w) ∈ H^{j+1}` and
`‖χ (K_BS ∗ w)‖_{H^{j+1}} ≤ C' ‖w‖_{H^j}`. For complex `w` the field `K_BS ∗ w` has real part
`BS.velocityRe w` and imaginary part `BS.velocityIm w`; the norm is summed over the entries
(`BS.normHC2`). -/
def IsHkBSConst (j : ℕ) (χ : ℂ → ℝ) (ρ C : ℝ) : Prop :=
  ∀ w : ℂ → ℂ, MemH j w → (∀ᵐ x, x ∉ ball (0 : ℂ) ρ → w x = 0) →
    MemH (j + 1) (fun x => (χ x : ℂ) * BS.velocityRe w x) ∧
    MemH (j + 1) (fun x => (χ x : ℂ) * BS.velocityIm w x) ∧
    BS.normHC2 (j + 1) (fun x => (χ x : ℂ) * BS.velocityRe w x)
      (fun x => (χ x : ℂ) * BS.velocityIm w x) ≤ C * normH j w

/-- The constant `C_P(k)` of `lem:Hk-calculus` for `k`, `N`, `N₁` (`05_single_ring.tex:226`):
a positive constant with `IsHkCalcConst`, chosen when one exists (proved in the interface layer
under `HkCalcSetting N N₁ χN` and `3 ≤ k`); junk value `1` otherwise. -/
@[irreducible] def hkCalcConst (k : ℕ) (N N₁ : Set ℂ) : ℝ :=
  open scoped Classical in
  if h : ∃ C : ℝ, 0 < C ∧ IsHkCalcConst k N N₁ C then h.choose else 1

/-- The constant `C^el_j` of `lem:Hk-calculus`(3) for `j`, `χ`, `ρ` (`05_single_ring.tex:224`):
a positive constant with `IsHkBSConst`, chosen when one exists; junk value `1` otherwise. -/
@[irreducible] def elConst (j : ℕ) (χ : ℂ → ℝ) (ρ : ℝ) : ℝ :=
  open scoped Classical in
  if h : ∃ C : ℝ, 0 < C ∧ IsHkBSConst j χ ρ C then h.choose else 1

/-! ### Basic lemmas (fully proved) -/

theorem hkComm_of_notMem {N₁ : Set ℂ} {α : ℕ × ℕ} {U w : ℂ → ℂ} {x : ℂ} (hx : x ∉ N₁) :
    hkComm N₁ α U w x = 0 :=
  indicator_of_notMem hx _

theorem hkCalcConst_pos (k : ℕ) (N N₁ : Set ℂ) : 0 < hkCalcConst k N N₁ := by
  classical
  rw [hkCalcConst]
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_pos

theorem hkCalcConst_spec {k : ℕ} {N N₁ : Set ℂ} (h : ∃ C : ℝ, 0 < C ∧ IsHkCalcConst k N N₁ C) :
    IsHkCalcConst k N N₁ (hkCalcConst k N N₁) := by
  classical
  rw [hkCalcConst, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec.2

theorem elConst_pos (j : ℕ) (χ : ℂ → ℝ) (ρ : ℝ) : 0 < elConst j χ ρ := by
  classical
  rw [elConst]
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_pos

theorem elConst_spec {j : ℕ} {χ : ℂ → ℝ} {ρ : ℝ} (h : ∃ C : ℝ, 0 < C ∧ IsHkBSConst j χ ρ C) :
    IsHkBSConst j χ ρ (elConst j χ ρ) := by
  classical
  rw [elConst, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec.2

/-- Larger constants work in (2). -/
theorem IsHkProdConst.mono {k : ℕ} {C C' : ℝ} (h : IsHkProdConst k C) (hC : C ≤ C') :
    IsHkProdConst k C' := by
  intro j hj hjk g f hg hf
  obtain ⟨hm, hb⟩ := h j hj hjk g f hg hf
  refine ⟨hm, hb.trans ?_⟩
  have h1 := normH_nonneg j g
  have h2 := normH_nonneg j f
  have := mul_nonneg h1 h2
  nlinarith

/-- Larger constants work in (3). -/
theorem IsHkBSConst.mono {j : ℕ} {χ : ℂ → ℝ} {ρ C C' : ℝ} (h : IsHkBSConst j χ ρ C)
    (hC : C ≤ C') : IsHkBSConst j χ ρ C' := by
  intro w hw hs
  obtain ⟨h1, h2, hb⟩ := h w hw hs
  exact ⟨h1, h2, hb.trans (mul_le_mul_of_nonneg_right hC (normH_nonneg j w))⟩

end NonUniqueEuler.Sob
