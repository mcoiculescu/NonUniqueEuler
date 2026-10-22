import NonUniqueEuler.Defs.Sec6.All

/-!
# Section 7.1: fields induced by one ring on another (definitions)

Manuscript `07_several_rings.tex:13-272`
(conventions for fields, `eq:complex-velocity`, `eq:derivative-norm`, `eq:Smi`, `lem:transfer`,
`lem:inner-field`).

* `Rings.complexForm V = V₁ - i V₂ = conj ∘ V`, the complex form of a vector field
  (`07_several_rings.tex:43-45`; for `V = K_BS * g` it is `BS.complexVelocity g`);
* `Rings.Smq m q = S_{m,q} = Σ_{p≥1} (pm+q)^q 2^{-(p-1)m}` (`eq:Smi`);
* `Rings.CL1 = |N|^{1/2}` (`lem:transfer`);
* `P.b i k = b_{i,k} = μ^{i-k} (r_k/r_i)^{m-2}` (`lem:transfer`(4));
* the constants of `lem:transfer` and `lem:inner-field`, which Sections 9–10 use by value
  ((SA2), `09_relay.tex:40-41`; `K_O`, `C_op`, `K₁`, `Ā`, …). Following decision D11, the content
  of each lemma is a Prop of its constants (`IsTransferConst χ M_h C^T_M C^T_O`,
  `IsInnerFieldConst χ M_h C_in`) and the constants are chosen (`CTM`, `CTO`, `Cin`);
  `C_M = C^T_M max(1, C_{L1})`, `C_O = C^T_O max(1, C_{L1})` (`CM`, `CO`). The interface theorems
  prove `∃ …, IsTransferConst …` (resp. `IsInnerFieldConst`) under (N1)–(N3); consumers use
  `transferConsts_spec`, `innerFieldConst_spec`.

Here `m = 3`. "`V` bounded on `N'_j` in `C^{M_h}`, in ring-`j` units, by `X`" is
`MemCk M_h annN' (P.unitsField j V) ∧ normCk M_h annN' (P.unitsField j V) ≤ X`. The non-monopole
field of `g` is `BS.extField g = K_BS * g - (∫ g) K_BS`. All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate

namespace NonUniqueEuler

namespace Rings

open RingData Datum

/-! ### Conventions for fields (`07_several_rings.tex:32-71`) -/

/-- The complex form `F = V₁ - i V₂` of a vector field `V = V₁ + i V₂` (`07_several_rings.tex:44-45`;
`eq:complex-velocity`, `eq:derivative-norm`). -/
def complexForm (V : ℂ → ℂ) (z : ℂ) : ℂ := conj (V z)

/-- `S_{m,q} = Σ_{p≥1} (pm + q)^q 2^{-(p-1)m}` (`eq:Smi`, `07_several_rings.tex:69-71`), summed
over `p = p' + 1`, `p' : ℕ`. -/
def Smq (m q : ℕ) : ℝ := ∑' p : ℕ, ((((p + 1) * m + q : ℕ) : ℝ)) ^ q * ((2 : ℝ)⁻¹) ^ (p * m)

/-- `C_{L1} = |N|^{1/2}`, `|N|` the area of `N = {a/2 ≤ |y| ≤ 2}` (`lem:transfer`,
`07_several_rings.tex:87-88`). -/
def CL1 : ℝ := Real.sqrt (volume annN).toReal

theorem CL1_nonneg : 0 ≤ CL1 := Real.sqrt_nonneg _

theorem complexForm_apply (V : ℂ → ℂ) (z : ℂ) : complexForm V z = conj (V z) := rfl

theorem complexForm_velocity (g : ℂ → ℝ) : complexForm (velocity g) = BS.complexVelocity g := rfl

end Rings

namespace Datum

namespace Approx

variable (P : Approx)

/-- `b_{i,k} = μ^{i-k} (r_k/r_i)^{m-2}`, `m = 3` (`lem:transfer`(4), `07_several_rings.tex:108`). -/
def b (i k : ℕ) : ℝ := P.μ ^ ((i : ℤ) - k) * (P.r k / P.r i) ^ (3 - 2)

theorem b_def (i k : ℕ) : P.b i k = P.μ ^ ((i : ℤ) - k) * (P.r k / P.r i) := by
  simp [b]

end Approx

end Datum

namespace Rings

open RingData Datum

/-! ### `lem:transfer` (`07_several_rings.tex:83-114`) -/

/-- **The constants `C^T_M`, `C^T_O` work in `lem:transfer` at order `M_h`**
(`07_several_rings.tex:83-114`), with `C_M = C^T_M max(1, C_{L1})`, `C_O = C^T_O max(1, C_{L1})`:
for every valid approximation `P` with cutoff `χ` (`s̄ ≤ a/16` is part of `Approx.Valid`), every
`t ≥ 0`:
1. (`inner_general`) for `1 ≤ j < n` and every real `g ∈ L¹`, `3`-fold symmetric, vanishing a.e.
   outside `\bar B_{a r_{j+1}/8}`, the non-monopole field `E_g` satisfies
   `‖(E_g)_{[j]}‖_{C^{M_h}(N')} ≤ C_M ε_j sup_{|y|=a/4} |(E_g)_{[j+1]}(y)|` (and `(E_g)_{[j]} ∈ C^{M_h}(N')`);
2. (`next_ring`) for `1 ≤ j < n`, if `S_{j+1}(t) ⊂ N_{j+1}`, the field of `A_{j+1} w_{j+1}(t, ·/r_{j+1})`
   is bounded on `N'_j` in `C^{M_h}`, in ring-`j` units, by `C_M ε_j ‖w_{j+1}(t)‖_{L¹}` and by
   `C_M ε_j ‖w_{j+1}(t)‖_{H^{s'}}` for every `s' ≥ 0`;
3. (`inner_region`) for `1 ≤ j < n`, if `D_{j+1}(t) ⊂ \bar B_R` with `0 < R ≤ a r_j/8`, the
   non-monopole field of `ω_{≥j+1}(t)` is bounded on `N'_j`, in ring-`j` units, by
   `C_M ε_j (R/r_{j+1})^m`;
4. (`outer_ring`) for `1 ≤ i < k ≤ n` with `S_i(t) ⊂ N_i`, the field of `A_i w_i(t, ·/r_i)` is
   bounded on `N'_k`, in ring-`k` units, by `C_O b_{i,k} ‖w_i(t)‖_{L¹}` and by
   `C_O b_{i,k} ‖w_i(t)‖_{H^{s'}}`; and (`outer_sum`) if `S_i(t) ⊂ N_i` for every `i < k`, the field
   of `ω(t) 1_{S_1(t)∪…∪S_{k-1}(t)}` is bounded on `N'_k`, in ring-`k` units, by
   `C_O Σ_{i<k} b_{i,k} ‖w_i(t)‖_{L¹}`.
The identity "the field of `ω(t)1_{S_1(t)∪…∪S_{k-1}(t)}` on `N'_k` is the sum over `i < k` of the
fields of `A_i w_i(t, ·/r_i)`" (item (4)) does not involve the constants and is a separate
interface statement. We add `0 < C^T_M`, `0 < C^T_O` and the `C^{M_h}(N')` memberships (junk-value
guard), and `0 < R` in (3). -/
structure IsTransferConst (χ : ℝ → ℝ) (Mh : ℕ) (CTM CTO : ℝ) : Prop where
  CTM_pos : 0 < CTM
  CTO_pos : 0 < CTO
  inner_general : ∀ P : Approx, P.χ = χ → P.Valid → ∀ j : ℕ, 1 ≤ j → j < P.n →
    ∀ g : ℂ → ℝ, MemLp g 1 volume → IsMFoldSymmetric 3 g →
      (∀ᵐ x ∂(volume : Measure ℂ), a * P.r (j + 1) / 8 < ‖x‖ → g x = 0) →
      MemCk Mh annN' (P.unitsField j (BS.extField g)) ∧
        normCk Mh annN' (P.unitsField j (BS.extField g)) ≤
          CTM * max 1 CL1 * P.eps j *
            sSup ((fun y => ‖P.unitsField (j + 1) (BS.extField g) y‖) '' sphere (0 : ℂ) (a / 4))
  next_ring : ∀ P : Approx, P.χ = χ → P.Valid → ∀ j : ℕ, 1 ≤ j → j < P.n →
    ∀ t : ℝ, 0 ≤ t → P.PertDefined (j + 1) t →
      MemCk Mh annN' (P.unitsField j (velocity (P.wPhys (j + 1) t))) ∧
        normCk Mh annN' (P.unitsField j (velocity (P.wPhys (j + 1) t))) ≤
          CTM * max 1 CL1 * P.eps j * (eLpNorm (P.wR (j + 1) t) 1 volume).toReal ∧
        ∀ s' : ℕ, normCk Mh annN' (P.unitsField j (velocity (P.wPhys (j + 1) t))) ≤
          CTM * max 1 CL1 * P.eps j * Sob.normH s' (P.w (j + 1) t)
  inner_region : ∀ P : Approx, P.χ = χ → P.Valid → ∀ j : ℕ, 1 ≤ j → j < P.n →
    ∀ t : ℝ, 0 ≤ t → ∀ R : ℝ, 0 < R → R ≤ a * P.r j / 8 → P.D (j + 1) t ⊆ closedBall 0 R →
      MemCk Mh annN' (P.unitsField j (BS.extField (P.omegaGe (j + 1) t))) ∧
        normCk Mh annN' (P.unitsField j (BS.extField (P.omegaGe (j + 1) t))) ≤
          CTM * max 1 CL1 * P.eps j * (R / P.r (j + 1)) ^ 3
  outer_ring : ∀ P : Approx, P.χ = χ → P.Valid → ∀ i k : ℕ, 1 ≤ i → i < k → k ≤ P.n →
    ∀ t : ℝ, 0 ≤ t → P.PertDefined i t →
      MemCk Mh annN' (P.unitsField k (velocity (P.wPhys i t))) ∧
        normCk Mh annN' (P.unitsField k (velocity (P.wPhys i t))) ≤
          CTO * max 1 CL1 * P.b i k * (eLpNorm (P.wR i t) 1 volume).toReal ∧
        ∀ s' : ℕ, normCk Mh annN' (P.unitsField k (velocity (P.wPhys i t))) ≤
          CTO * max 1 CL1 * P.b i k * Sob.normH s' (P.w i t)
  outer_sum : ∀ P : Approx, P.χ = χ → P.Valid → ∀ k : ℕ, 1 ≤ k → k ≤ P.n →
    ∀ t : ℝ, 0 ≤ t → (∀ i ∈ Finset.Ico 1 k, P.PertDefined i t) →
      MemCk Mh annN' (P.unitsField k (velocity (P.omegaOut k t))) ∧
        normCk Mh annN' (P.unitsField k (velocity (P.omegaOut k t))) ≤
          CTO * max 1 CL1 *
            ∑ i ∈ Finset.Ico 1 k, P.b i k * (eLpNorm (P.wR i t) 1 volume).toReal

open Classical in
/-- The constants `(C^T_M, C^T_O)` of `lem:transfer` at order `M_h` (chosen; junk `(1, 1)`). -/
def transferConsts (χ : ℝ → ℝ) (Mh : ℕ) : ℝ × ℝ :=
  if h : ∃ x : ℝ × ℝ, IsTransferConst χ Mh x.1 x.2 then h.choose else (1, 1)

/-- `C^T_M` of `lem:transfer` at order `M_h` (`07_several_rings.tex:86-87`). -/
def CTM (χ : ℝ → ℝ) (Mh : ℕ) : ℝ := (transferConsts χ Mh).1

/-- `C^T_O` of `lem:transfer` at order `M_h` (`07_several_rings.tex:86-87`). -/
def CTO (χ : ℝ → ℝ) (Mh : ℕ) : ℝ := (transferConsts χ Mh).2

/-- `C_M = C^T_M max(1, C_{L1})` (`07_several_rings.tex:89`). -/
def CM (χ : ℝ → ℝ) (Mh : ℕ) : ℝ := CTM χ Mh * max 1 CL1

/-- `C_O = C^T_O max(1, C_{L1})` (`07_several_rings.tex:89`). -/
def CO (χ : ℝ → ℝ) (Mh : ℕ) : ℝ := CTO χ Mh * max 1 CL1

/-! ### `lem:inner-field` (`07_several_rings.tex:243-252`) -/

/-- **The constant `C_in` works in `lem:inner-field` at order `M_h`** (`07_several_rings.tex:243-251`):
`C_in > 0` and for every valid approximation `P` with cutoff `χ`, `1 ≤ k < n`, `t ≥ 0`, `R` with
`0 < R ≤ a r_k/8`: if `ω_{≥k+1}(t)` is supported in `\bar B_R` and
`‖ω_{≥k+1}(t)‖_{L¹} ≤ M_vort A_{k+1} r_{k+1}²`, then the non-monopole field `E` of `ω_{≥k+1}(t)`
satisfies `E_{[k]} ∈ C^{M_h}(N')` and `‖E_{[k]}‖_{C^{M_h}(N')} ≤ C_in μ s_k² (R/r_k)^m`, `m = 3`.
The second assertion of the lemma (`E_{[k]} = h^in_k(A_k t)` on `N'` if `D_{k+1}(t) ⊂ B_{a r_k/8}`)
does not involve `C_in` and is a separate interface statement. -/
structure IsInnerFieldConst (χ : ℝ → ℝ) (Mh : ℕ) (C : ℝ) : Prop where
  pos : 0 < C
  bound : ∀ P : Approx, P.χ = χ → P.Valid → ∀ k : ℕ, 1 ≤ k → k < P.n →
    ∀ t : ℝ, 0 ≤ t → ∀ R : ℝ, 0 < R → R ≤ a * P.r k / 8 →
      tsupport (P.omegaGe (k + 1) t) ⊆ closedBall 0 R →
      eLpNorm (P.omegaGe (k + 1) t) 1 volume ≤
        ENNReal.ofReal (Mvort * P.A (k + 1) * P.r (k + 1) ^ 2) →
      MemCk Mh annN' (P.unitsField k (BS.extField (P.omegaGe (k + 1) t))) ∧
        normCk Mh annN' (P.unitsField k (BS.extField (P.omegaGe (k + 1) t))) ≤
          C * P.μ * P.s k ^ 2 * (R / P.r k) ^ 3

open Classical in
/-- `C_in` of `lem:inner-field` at order `M_h` (`07_several_rings.tex:245`; chosen, junk `1`). -/
def Cin (χ : ℝ → ℝ) (Mh : ℕ) : ℝ :=
  if h : ∃ C : ℝ, IsInnerFieldConst χ Mh C then h.choose else 1

/-! ### Basic lemmas (fully proved) -/

/-- If constants for `lem:transfer` exist, the chosen ones work. -/
theorem transferConsts_spec {χ : ℝ → ℝ} {Mh : ℕ} (h : ∃ CTM CTO : ℝ, IsTransferConst χ Mh CTM CTO) :
    IsTransferConst χ Mh (CTM χ Mh) (CTO χ Mh) := by
  classical
  have h' : ∃ x : ℝ × ℝ, IsTransferConst χ Mh x.1 x.2 := by
    obtain ⟨c₁, c₂, hc⟩ := h
    exact ⟨(c₁, c₂), hc⟩
  have hc : transferConsts χ Mh = h'.choose := by
    rw [transferConsts, dite_eq_left h']
  rw [CTM, CTO, hc]
  exact h'.choose_spec

theorem CM_def (χ : ℝ → ℝ) (Mh : ℕ) : CM χ Mh = CTM χ Mh * max 1 CL1 := rfl

theorem CO_def (χ : ℝ → ℝ) (Mh : ℕ) : CO χ Mh = CTO χ Mh * max 1 CL1 := rfl

theorem CTM_le_CM {χ : ℝ → ℝ} {Mh : ℕ} (h : 0 ≤ CTM χ Mh) : CTM χ Mh ≤ CM χ Mh :=
  le_mul_of_one_le_right h (le_max_left _ _)

theorem CTO_le_CO {χ : ℝ → ℝ} {Mh : ℕ} (h : 0 ≤ CTO χ Mh) : CTO χ Mh ≤ CO χ Mh :=
  le_mul_of_one_le_right h (le_max_left _ _)

/-- If a constant for `lem:inner-field` exists, the chosen one works. -/
theorem innerFieldConst_spec {χ : ℝ → ℝ} {Mh : ℕ} (h : ∃ C : ℝ, IsInnerFieldConst χ Mh C) :
    IsInnerFieldConst χ Mh (Cin χ Mh) := by
  classical
  rw [Cin, dite_eq_left h]
  exact h.choose_spec

end Rings

end NonUniqueEuler
