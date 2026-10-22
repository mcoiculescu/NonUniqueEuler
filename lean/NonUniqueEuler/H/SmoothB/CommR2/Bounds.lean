import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import NonUniqueEuler.H.SmoothB.CommR2.Norms
import NonUniqueEuler.H.SmoothB.CommR2.Formula
import NonUniqueEuler.I.Infra.Sobolev.EmbedL4
import NonUniqueEuler.Defs.SmoothB.Iteration
import NonUniqueEuler.Defs.Infra.Instances

/-!
# Helper for `lem:comm-R2`: the bound on each term of the commutator formula

Helper of `P/SmoothB/CommR2.lean`, steps 2-4 of the proof of `lem:comm-R2`
(`B_global_smooth.tex:165-175`). For `T = ∂^β u_l ∂^γ g` with `|β| ≥ 1`, `|γ| ≥ 1`,
`|β| + |γ| = s + 1` (`commTerm_bound`):
* `|β| = 1`: `‖T‖₂ ≤ |∇u|_max ‖∂^γ g‖₂ ≤ |∇u|_max ‖g‖_{H^s}`;
* `|β| = s`: `‖T‖₂ ≤ ‖∂^β u‖₂ ‖∂_m g‖_∞ ≤ ‖∇u‖_{H^{s-1}} ‖∇g‖_{L^∞}`;
* `2 ≤ |β| ≤ s - 1`: Hölder and (E1) (`Sob.L4_le_normH`):
  `‖T‖₂ ≤ ‖∂^β u‖_{H¹} ‖∂^γ g‖_{H¹} ≤ ‖∇u‖_{H^{s-1}} ‖g‖_{H^s}`;
so in all cases `‖T‖₂` is at most the bracket of `lem:comm-R2`. Also: `L²` sums of lists
(`listSum_bound`).

The Hölder instance `ENNReal.HolderTriple 4 4 2` comes from `Defs/Infra/Instances`; this file
declares no instance.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal

namespace NonUniqueEuler.Smooth.CommR2Aux

open Sob

/-! ### `L²` estimates -/

theorem l2_le_mul_of_le {f h : ℂ → ℂ} {c : ℝ} (hc : 0 ≤ c) (hh : MemLp h 2 volume)
    (hb : ∀ x, ‖f x‖ ≤ c * ‖h x‖) : l2 f ≤ c * l2 h := by
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume) (Eventually.of_forall hb) 2
  unfold l2
  calc (eLpNorm f 2 volume).toReal ≤ (ENNReal.ofReal c * eLpNorm h 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hh.eLpNorm_ne_top) h1
    _ = c * (eLpNorm h 2 volume).toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

/-- Hölder: `‖f h‖_{L²} ≤ ‖f‖_{L⁴} ‖h‖_{L⁴}`. -/
theorem l2_mul_le {f h : ℂ → ℂ} (hf : MemLp f 4 volume) (hh : MemLp h 4 volume) :
    l2 (fun x => f x * h x) ≤ (eLpNorm f 4 volume).toReal * (eLpNorm h 4 volume).toReal := by
  have h1 : eLpNorm (f • h) 2 volume ≤ eLpNorm f 4 volume * eLpNorm h 4 volume :=
    eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2) hh.1 hf.1
  unfold l2
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hh.eLpNorm_ne_top) h1

theorem l2_add_le {f h : ℂ → ℂ} (hf : MemLp f 2 volume) (hh : MemLp h 2 volume) :
    l2 (fun x => f x + h x) ≤ l2 f + l2 h := by
  have h1 : eLpNorm (f + h) 2 volume ≤ eLpNorm f 2 volume + eLpNorm h 2 volume :=
    eLpNorm_add_le hf.1 hh.1 (by norm_num)
  unfold l2
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hh.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hh.eLpNorm_ne_top⟩) h1

/-- `L²` bound of a finite (list) sum. -/
theorem listSum_bound {ι : Type*} (L : List ι) (F : ι → ℂ → ℂ) {B : ℝ}
    (hF : ∀ i ∈ L, MemLp (F i) 2 volume ∧ l2 (F i) ≤ B) :
    MemLp (fun x => (L.map (fun i => F i x)).sum) 2 volume ∧
      l2 (fun x => (L.map (fun i => F i x)).sum) ≤ L.length * B := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero, zero_mul]
    refine ⟨MemLp.zero' , ?_⟩
    simp [l2]
  | cons i L ih =>
    obtain ⟨h1, h2⟩ := ih fun j hj => hF j (by simp [hj])
    obtain ⟨h3, h4⟩ := hF i (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
    refine ⟨h3.add h1, ?_⟩
    have := l2_add_le h3 h1
    linarith

/-! ### The suprema `|∇u|_max` and `‖∇g‖_{L^∞}` -/

theorem le_gradEntryMax {u : ℂ → ℂ}
    (hbdd : ∃ M : ℝ, ∀ x : ℂ, ∀ i l : Fin 2, |Prelim.gradEntry u i l x| ≤ M) (x : ℂ)
    (i l : Fin 2) : |Prelim.gradEntry u i l x| ≤ gradEntryMax u := by
  obtain ⟨M, hM⟩ := hbdd
  have h1 : ∀ x i, BddAbove (range fun l => |Prelim.gradEntry u i l x|) :=
    fun _ _ => (Set.finite_range _).bddAbove
  have h2 : ∀ x, BddAbove (range fun i => ⨆ l, |Prelim.gradEntry u i l x|) :=
    fun _ => (Set.finite_range _).bddAbove
  have h3 : BddAbove (range fun x => ⨆ i, ⨆ l, |Prelim.gradEntry u i l x|) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact ciSup_le fun i => ciSup_le fun l => hM x i l
  calc |Prelim.gradEntry u i l x| ≤ ⨆ l, |Prelim.gradEntry u i l x| := le_ciSup (h1 x i) l
    _ ≤ ⨆ i, ⨆ l, |Prelim.gradEntry u i l x| :=
        le_ciSup (f := fun i => ⨆ l, |Prelim.gradEntry u i l x|) (h2 x) i
    _ ≤ gradEntryMax u := le_ciSup (f := fun x => ⨆ i, ⨆ l, |Prelim.gradEntry u i l x|) h3 x

theorem pd_eq_partialD (l : Fin 2) (h : ℂ → ℂ) (x : ℂ) :
    Prelim.pd l h x = partialD (unitIdx l) h x := by
  rw [partialD_unitIdx]
  rfl

theorem norm_pd_le_gradSupC {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (l : Fin 2) (x : ℂ) : ‖Prelim.pd l g x‖ ≤ gradSupC g := by
  have hT : IsTestFn univ g := ⟨hg, hgc, subset_univ _⟩
  have hb : ∀ m : Fin 2, ∃ C, ∀ x, ‖Prelim.pd m g x‖ ≤ C := by
    intro m
    have hm := hT.partialD (unitIdx m)
    obtain ⟨C, hC⟩ := hm.compact.exists_bound_of_continuous hm.continuous
    exact ⟨C, fun x => by rw [pd_eq_partialD]; exact hC x⟩
  have hle : ∀ m x, ‖Prelim.pd m g x‖ ≤ Prelim.gradAbs g x := by
    intro m x
    refine Real.le_sqrt_of_sq_le ?_
    fin_cases m
    · simp only [Fin.zero_eta]
      nlinarith [sq_nonneg ‖Prelim.pd 1 g x‖]
    · simp only [Fin.mk_one]
      nlinarith [sq_nonneg ‖Prelim.pd 0 g x‖]
  obtain ⟨C0, h0⟩ := hb 0
  obtain ⟨C1, h1⟩ := hb 1
  have hbdd : BddAbove (range (Prelim.gradAbs g)) := by
    refine ⟨C0 + C1, ?_⟩
    rintro _ ⟨y, rfl⟩
    have ha := norm_nonneg (Prelim.pd 0 g y)
    have hb' := norm_nonneg (Prelim.pd 1 g y)
    calc Prelim.gradAbs g y ≤ Real.sqrt ((‖Prelim.pd 0 g y‖ + ‖Prelim.pd 1 g y‖) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = ‖Prelim.pd 0 g y‖ + ‖Prelim.pd 1 g y‖ := Real.sqrt_sq (add_nonneg ha hb')
      _ ≤ C0 + C1 := add_le_add (h0 y) (h1 y)
  exact (hle l x).trans (le_ciSup hbdd x)

theorem gradEntryMax_nonneg {u : ℂ → ℂ}
    (hbdd : ∃ M : ℝ, ∀ x : ℂ, ∀ i l : Fin 2, |Prelim.gradEntry u i l x| ≤ M) :
    0 ≤ gradEntryMax u :=
  (abs_nonneg _).trans (le_gradEntryMax hbdd 0 0 0)

theorem gradSupC_nonneg {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    0 ≤ gradSupC g :=
  (norm_nonneg _).trans (norm_pd_le_gradSupC hg hgc 0 0)

/-! ### The bound on one term -/

/-- The bracket of `lem:comm-R2`. -/
def bracket (s : ℕ) (g u : ℂ → ℂ) : ℝ :=
  (gradEntryMax u + Prelim.gradNormH (s - 1) u) * normH s g +
    Prelim.gradNormH (s - 1) u * gradSupC g

/-- Each term `∂^β u_l ∂^γ g` (`|β|, |γ| ≥ 1`, `|β| + |γ| = s + 1`) of the commutator formula is
in `L²` with norm at most the bracket of `lem:comm-R2`. -/
theorem commTerm_bound {s : ℕ} (hs : 2 ≤ s) {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hbdd : ∃ M : ℝ, ∀ x : ℂ, ∀ i l : Fin 2, |Prelim.gradEntry u i l x| ≤ M)
    (hL2 : ∀ β : ℕ × ℕ, 1 ≤ β.1 + β.2 → β.1 + β.2 ≤ s → MemLp (partialD β u) 2 volume)
    {β γ : ℕ × ℕ} (hβ1 : 1 ≤ β.1 + β.2) (hγ1 : 1 ≤ γ.1 + γ.2)
    (hsum : (β.1 + β.2) + (γ.1 + γ.2) = s + 1) (l : Fin 2) :
    MemLp (fun x => compL l (partialD β u x) * partialD γ g x) 2 volume ∧
      l2 (fun x => compL l (partialD β u x) * partialD γ g x) ≤ bracket s g u := by
  have hT : IsTestFn univ g := ⟨hg, hgc, subset_univ _⟩
  have hTγ := hT.partialD γ
  have huβ : MemLp (partialD β u) 2 volume := hL2 β hβ1 (by omega)
  have hcβ : Continuous (partialD β u) := (contDiff_partialD hu β).continuous
  have hmeas : AEStronglyMeasurable (fun x => compL l (partialD β u x) * partialD γ g x) volume :=
    (((compL l).continuous.comp hcβ).mul hTγ.continuous).aestronglyMeasurable
  have hpt : ∀ x, ‖compL l (partialD β u x) * partialD γ g x‖ ≤
      ‖partialD β u x‖ * ‖partialD γ g x‖ := fun x => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_compL_le l _) (norm_nonneg _)
  -- membership in `L²`
  obtain ⟨C, hC⟩ := hTγ.compact.exists_bound_of_continuous hTγ.continuous
  have hmem : MemLp (fun x => compL l (partialD β u x) * partialD γ g x) 2 volume := by
    refine huβ.of_le_mul (c := C) hmeas (Eventually.of_forall fun x => ?_)
    refine (hpt x).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  refine ⟨hmem, ?_⟩
  -- nonnegativity of the pieces of the bracket
  have hE := gradEntryMax_nonneg hbdd
  have hG := gradNormH_nonneg (s - 1) u
  have hN := normH_nonneg s g
  have hS := gradSupC_nonneg hg hgc
  have hadd := add_mul (gradEntryMax u) (Prelim.gradNormH (s - 1) u) (normH s g)
  have hB1 : gradEntryMax u * normH s g ≤ bracket s g u := by
    unfold bracket
    linarith [mul_nonneg hG hN, mul_nonneg hG hS]
  have hB2 : Prelim.gradNormH (s - 1) u * gradSupC g ≤ bracket s g u := by
    unfold bracket
    linarith [mul_nonneg hE hN, mul_nonneg hG hN]
  have hB3 : Prelim.gradNormH (s - 1) u * normH s g ≤ bracket s g u := by
    unfold bracket
    linarith [mul_nonneg hE hN, mul_nonneg hG hS]
  by_cases hb1 : β.1 + β.2 = 1
  · -- `|β| = 1`: `∂^β u_l = ∂_m u_l` is bounded by `|∇u|_max`
    obtain ⟨m, β', hβ'⟩ := exists_eq_add_unitIdx hβ1
    have hm := unitIdx_size m
    have h0 : β' = 0 := by
      rw [hβ'] at hb1
      simp only [Prod.fst_add, Prod.snd_add] at hb1
      ext <;> simp <;> omega
    rw [h0, zero_add] at hβ'
    subst hβ'
    have hbd : ∀ x, ‖compL l (partialD (unitIdx m) u x) * partialD γ g x‖ ≤
        gradEntryMax u * ‖partialD γ g x‖ := by
      intro x
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [compL_apply, ← pd_eq_partialD, Complex.norm_real, Real.norm_eq_abs]
      exact le_gradEntryMax hbdd x l m
    calc l2 (fun x => compL l (partialD (unitIdx m) u x) * partialD γ g x)
        ≤ gradEntryMax u * l2 (partialD γ g) := l2_le_mul_of_le hE (hTγ.memLp 2 volume) hbd
      _ ≤ gradEntryMax u * normH s g :=
          mul_le_mul_of_nonneg_left (l2_partialD_le_normH hg (by omega)) hE
      _ ≤ bracket s g u := hB1
  by_cases hbs : β.1 + β.2 = s
  · -- `β = α`: `∂^γ g = ∂_m g` is bounded by `‖∇g‖_{L^∞}`
    obtain ⟨m, γ', hγ'⟩ := exists_eq_add_unitIdx hγ1
    have hm := unitIdx_size m
    have h0 : γ' = 0 := by
      have : γ.1 + γ.2 = 1 := by omega
      rw [hγ'] at this
      simp only [Prod.fst_add, Prod.snd_add] at this
      ext <;> simp <;> omega
    rw [h0, zero_add] at hγ'
    subst hγ'
    have hbd : ∀ x, ‖compL l (partialD β u x) * partialD (unitIdx m) g x‖ ≤
        gradSupC g * ‖partialD β u x‖ := by
      intro x
      refine (hpt x).trans ?_
      rw [mul_comm, ← pd_eq_partialD]
      exact mul_le_mul_of_nonneg_right (norm_pd_le_gradSupC hg hgc m x) (norm_nonneg _)
    calc l2 (fun x => compL l (partialD β u x) * partialD (unitIdx m) g x)
        ≤ gradSupC g * l2 (partialD β u) := l2_le_mul_of_le hS huβ hbd
      _ ≤ gradSupC g * Prelim.gradNormH (s - 1) u :=
          mul_le_mul_of_nonneg_left (l2_partialD_le_gradNormH hu hβ1 (by omega)) hS
      _ = Prelim.gradNormH (s - 1) u * gradSupC g := mul_comm _ _
      _ ≤ bracket s g u := hB2
  · -- `2 ≤ |β| ≤ s - 1`: Hölder and (E1)
    have hmu : MemH 1 (partialD β u) := by
      refine memH_of_smooth (contDiff_partialD hu β) fun δ hδ => ?_
      rw [mem_multiIdx] at hδ
      rw [partialD_partialD hu]
      exact hL2 (δ + β) (by simp only [Prod.fst_add, Prod.snd_add]; omega)
        (by simp only [Prod.fst_add, Prod.snd_add]; omega)
    have hmg : MemH 1 (partialD γ g) :=
      memH_of_smooth (contDiff_partialD hg γ) fun δ _ => (hTγ.partialD δ).memLp 2 volume
    obtain ⟨hu4, hu4b⟩ := L4_le_normH hmu
    obtain ⟨hg4, hg4b⟩ := L4_le_normH hmg
    have hc4 : MemLp (fun x => compL l (partialD β u x)) 4 volume :=
      hu4.of_le ((compL l).continuous.comp hcβ).aestronglyMeasurable
        (Eventually.of_forall fun x => norm_compL_le l _)
    have hc4b : (eLpNorm (fun x => compL l (partialD β u x)) 4 volume).toReal ≤
        (eLpNorm (partialD β u) 4 volume).toReal :=
      ENNReal.toReal_mono hu4.eLpNorm_ne_top (eLpNorm_mono fun x => norm_compL_le l _)
    calc l2 (fun x => compL l (partialD β u x) * partialD γ g x)
        ≤ (eLpNorm (fun x => compL l (partialD β u x)) 4 volume).toReal *
            (eLpNorm (partialD γ g) 4 volume).toReal := l2_mul_le hc4 hg4
      _ ≤ normH 1 (partialD β u) * normH 1 (partialD γ g) :=
          mul_le_mul (hc4b.trans hu4b) hg4b ENNReal.toReal_nonneg (normH_nonneg _ _)
      _ ≤ Prelim.gradNormH (s - 1) u * normH s g :=
          mul_le_mul (normH_one_partialD_le_gradNormH hu hβ1 (by omega))
            (normH_one_partialD_le hg (by omega)) (normH_nonneg _ _) hG
      _ ≤ bracket s g u := hB3

end NonUniqueEuler.Smooth.CommR2Aux
