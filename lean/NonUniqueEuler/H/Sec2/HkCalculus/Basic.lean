import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import NonUniqueEuler.Defs.Sec2.HkCalculus
import NonUniqueEuler.Defs.Infra.Instances
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.EmbedL4
import NonUniqueEuler.I.Infra.Sobolev.EmbedLinf

/-!
# Helper for `P/Sec2/HkCalculus`: `L²` estimates and multi-index bookkeeping

* Hölder estimates in `L²`: `l2_mul_le_of_top` (`L^∞ × L²`), `l2_mul_le_of_H2_left`
  (`lem:embed`(E2)), `l2_mul_le_of_H1` (`L⁴ × L⁴` and (E1));
* `L²` norms of sums, scalar multiples, indicators; Cauchy–Schwarz for `Prelim.innerL2`;
* multi-indices: `pdList_add_perm`, `weakPartial_weakPartial_ae_eq` (weak derivatives commute),
  `weakPartial_zero_ae_eq`, `sum_leIdx_choose` (`Σ_{β ≤ γ} C(γ,β) = 2^{|γ|}`),
  `card_multiIdx_le`, `sqrt_sum_sq_le`.

Note: a copy of these lemmas in another file (e.g. for `I/Sec2/HkCalculus/ProductLeibniz.lean`)
must use a namespace other than `HkCalcAux`, otherwise the full library declares the same
names twice.

Hölder instances: `ENNReal.HolderTriple 4 4 2` comes from
`Defs/Infra/Instances`, and `ENNReal.HolderTriple 2 2 1` from Mathlib
(`ENNReal.HolderConjugate.instTwoTwo`). This file declares no instance.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff ComplexConjugate

namespace NonUniqueEuler.Sob.HkCalcAux

/-! ### `L²` norms -/

theorem memLp_of_memH {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) : MemLp f 2 volume := by
  simpa using hf.memLp

theorem l2_congr_ae {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) : l2 f = l2 g := by
  unfold l2; rw [eLpNorm_congr_ae h]

theorem l2_const_mul (c : ℂ) (f : ℂ → ℂ) : l2 (fun x => c * f x) = ‖c‖ * l2 f := by
  unfold l2
  have : (fun x => c * f x) = c • f := rfl
  rw [this, eLpNorm_const_smul, ENNReal.toReal_mul]
  simp

theorem l2_indicator_le (s : Set ℂ) {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    l2 (s.indicator f) ≤ l2 f := by
  unfold l2
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_indicator_le f)

theorem l2_add_le {f h : ℂ → ℂ} (hf : MemLp f 2 volume) (hh : MemLp h 2 volume) :
    l2 (fun x => f x + h x) ≤ l2 f + l2 h := by
  have h1 : eLpNorm (f + h) 2 volume ≤ eLpNorm f 2 volume + eLpNorm h 2 volume :=
    eLpNorm_add_le hf.1 hh.1 (by norm_num)
  unfold l2
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hh.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hh.eLpNorm_ne_top⟩) h1

/-- `L²` bound of a finite sum. -/
theorem l2_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i ∈ s, MemLp (F i) 2 volume) :
    MemLp (fun x => ∑ i ∈ s, F i x) 2 volume ∧
      l2 (fun x => ∑ i ∈ s, F i x) ≤ ∑ i ∈ s, l2 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨MemLp.zero', by simp [l2]⟩
  | insert i s hi ih =>
    obtain ⟨h1, h2⟩ := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    have h3 := hF i (Finset.mem_insert_self i s)
    simp only [Finset.sum_insert hi]
    refine ⟨h3.add h1, ?_⟩
    have := l2_add_le h3 h1
    linarith

/-- `L^∞ × L²`: `‖f h‖_{L²} ≤ M ‖h‖_{L²}` when `‖f‖_{L^∞} ≤ M`. -/
theorem l2_mul_le_of_top {f h : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) {M : ℝ}
    (hM : 0 ≤ M) (hfM : eLpNorm f ⊤ volume ≤ ENNReal.ofReal M) (hh : MemLp h 2 volume) :
    MemLp (fun x => f x * h x) 2 volume ∧ l2 (fun x => f x * h x) ≤ M * l2 h := by
  have hfinf : MemLp f ⊤ volume := ⟨hf, lt_of_le_of_lt hfM ENNReal.ofReal_lt_top⟩
  have hb : eLpNorm (fun x => f x * h x) 2 volume ≤ eLpNorm f ⊤ volume * eLpNorm h 2 volume := by
    have := eLpNorm_le_eLpNorm_top_mul_eLpNorm (μ := volume) 2 f hh.1
      (fun a b : ℂ => a * b) 1 (Filter.Eventually.of_forall fun x => by simp [nnnorm_mul])
    simpa using this
  refine ⟨hh.mul' (r := 2) hfinf, ?_⟩
  unfold l2
  calc (eLpNorm (fun x => f x * h x) 2 volume).toReal
      ≤ (ENNReal.ofReal M * eLpNorm h 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hh.eLpNorm_ne_top)
          (hb.trans (mul_le_mul_left hfM _))
    _ = M * (eLpNorm h 2 volume).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM]

/-- `‖f h‖_{L²} ≤ ‖f‖_{H²} ‖h‖_{L²}` by `lem:embed`(E2). -/
theorem l2_mul_le_of_H2_left {f h : ℂ → ℂ} (hf : MemH 2 f) (hh : MemLp h 2 volume) :
    MemLp (fun x => f x * h x) 2 volume ∧ l2 (fun x => f x * h x) ≤ normH 2 f * l2 h :=
  l2_mul_le_of_top (memLp_of_memH hf).1 (normH_nonneg 2 f) (eLpNorm_top_le_normH_two hf) hh

/-- `‖h f‖_{L²} ≤ ‖h‖_{L²} ‖f‖_{H²}` by `lem:embed`(E2). -/
theorem l2_mul_le_of_H2_right {f h : ℂ → ℂ} (hh : MemLp h 2 volume) (hf : MemH 2 f) :
    MemLp (fun x => h x * f x) 2 volume ∧ l2 (fun x => h x * f x) ≤ l2 h * normH 2 f := by
  have e : (fun x => h x * f x) = fun x => f x * h x := by funext x; ring
  rw [e, mul_comm]
  exact l2_mul_le_of_H2_left hf hh

/-- `‖f h‖_{L²} ≤ ‖f‖_{L⁴} ‖h‖_{L⁴} ≤ ‖f‖_{H¹} ‖h‖_{H¹}` (Hölder and `lem:embed`(E1)). -/
theorem l2_mul_le_of_H1 {f h : ℂ → ℂ} (hf : MemH 1 f) (hh : MemH 1 h) :
    MemLp (fun x => f x * h x) 2 volume ∧ l2 (fun x => f x * h x) ≤ normH 1 f * normH 1 h := by
  obtain ⟨hf4, hf4'⟩ := L4_le_normH hf
  obtain ⟨hh4, hh4'⟩ := L4_le_normH hh
  have h1 : eLpNorm (f • h) 2 volume ≤ eLpNorm f 4 volume * eLpNorm h 4 volume :=
    eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2) hh4.1 hf4.1
  refine ⟨hh4.mul' (r := 2) hf4, ?_⟩
  unfold l2
  calc (eLpNorm (fun x => f x * h x) 2 volume).toReal
      ≤ (eLpNorm f 4 volume * eLpNorm h 4 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hf4.eLpNorm_ne_top hh4.eLpNorm_ne_top) h1
    _ = (eLpNorm f 4 volume).toReal * (eLpNorm h 4 volume).toReal := ENNReal.toReal_mul
    _ ≤ normH 1 f * normH 1 h := mul_le_mul hf4' hh4' ENNReal.toReal_nonneg (normH_nonneg 1 f)

/-! ### The `L²` pairing -/

theorem integrable_mul_conj {f g : ℂ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun x => f x * conj (g x)) volume := by
  have h2 : eLpNorm (fun x => conj (g x)) 2 volume = eLpNorm g 2 volume :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => by simp)
  have hg' : MemLp (fun x => conj (g x)) 2 volume := by
    refine ⟨hg.1.star, ?_⟩
    rw [h2]
    exact hg.2
  exact hf.integrable_mul (p := 2) (q := 2) hg'

/-- Cauchy–Schwarz: `|⟨f, g⟩| ≤ ‖f‖_{L²} ‖g‖_{L²}`. -/
theorem norm_innerL2_le {f g : ℂ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖Prelim.innerL2 f g‖ ≤ l2 f * l2 g := by
  have hint := integrable_mul_conj hf hg
  have h1 : eLpNorm (fun x => f x * conj (g x)) 1 volume ≤
      1 * eLpNorm f 2 volume * eLpNorm (fun x => conj (g x)) 2 volume :=
    eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 2) (q := 2) (r := 1) hf.1 hg.1.star
      (fun a b : ℂ => a * b) 1 (Filter.Eventually.of_forall fun x => by simp [nnnorm_mul])
  have h2 : eLpNorm (fun x => conj (g x)) 2 volume = eLpNorm g 2 volume :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => by simp)
  rw [h2, one_mul] at h1
  unfold Prelim.innerL2 l2
  calc ‖∫ x, f x * conj (g x)‖ ≤ ∫ x, ‖f x * conj (g x)‖ := norm_integral_le_integral_norm _
    _ = (eLpNorm (fun x => f x * conj (g x)) 1 volume).toReal := by
        rw [integral_norm_eq_lintegral_enorm hint.1, eLpNorm_one_eq_lintegral_enorm]
    _ ≤ (eLpNorm f 2 volume * eLpNorm g 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) h1
    _ = (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := ENNReal.toReal_mul

theorem innerL2_add_left {f₁ f₂ g : ℂ → ℂ} (h₁ : MemLp f₁ 2 volume) (h₂ : MemLp f₂ 2 volume)
    (hg : MemLp g 2 volume) :
    Prelim.innerL2 (fun x => f₁ x + f₂ x) g = Prelim.innerL2 f₁ g + Prelim.innerL2 f₂ g := by
  unfold Prelim.innerL2
  rw [← integral_add (integrable_mul_conj h₁ hg) (integrable_mul_conj h₂ hg)]
  congr 1
  funext x
  ring

theorem innerL2_congr_ae {f f' g g' : ℂ → ℂ} (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') :
    Prelim.innerL2 f g = Prelim.innerL2 f' g' := by
  unfold Prelim.innerL2
  refine integral_congr_ae ?_
  filter_upwards [hf, hg] with x h1 h2
  rw [h1, h2]

/-! ### Multi-indices -/

theorem mem_leIdx {γ β : ℕ × ℕ} : β ∈ leIdx γ ↔ β.1 ≤ γ.1 ∧ β.2 ≤ γ.2 := by
  simp only [leIdx, Finset.mem_product, Finset.mem_range]
  omega

theorem pdList_add_perm (α β : ℕ × ℕ) : (pdList α ++ pdList β).Perm (pdList (α + β)) := by
  simp only [pdList, Prod.fst_add, Prod.snd_add, List.replicate_add, List.append_assoc]
  exact List.Perm.append_left _ (List.perm_append_comm_assoc _ _ _)

theorem hasWeakDerivOn_nil_self (V : Set ℂ) (f : ℂ → ℂ) :
    HasWeakDerivOn V (pdList (0, 0)) f f := fun φ _ => by simp [pdList]

theorem weakPartial_zero_ae_eq {f : ℂ → ℂ} (hf : LocallyIntegrable f volume) :
    weakPartial (0, 0) f =ᵐ[volume] f := by
  have h := weakDerivOn_ae_eq isOpen_univ (hf.locallyIntegrableOn univ)
    (hasWeakDerivOn_nil_self univ f)
  filter_upwards [h] with x hx
  exact hx (mem_univ x)

/-- Weak derivatives commute: `∂^α ∂^β f = ∂^{α+β} f` a.e. for `f ∈ H^m`, `|α| + |β| ≤ m`. -/
theorem weakPartial_weakPartial_ae_eq {m : ℕ} {f : ℂ → ℂ} (hf : MemH m f) {α β : ℕ × ℕ}
    (h : α.1 + α.2 + (β.1 + β.2) ≤ m) :
    weakPartial α (weakPartial β f) =ᵐ[volume] weakPartial (α + β) f := by
  have hβ' : MemH (α.1 + α.2 + (β.1 + β.2)) f := hf.mono_order h
  obtain ⟨hβm, -⟩ := MemH.weakPartial (k := α.1 + α.2) (γ := β) hβ'
  obtain ⟨hL, hD⟩ := hβm.memLp_weakPartial (γ := α) (mem_multiIdx.2 le_rfl)
  have hβD := (hf.memLp_weakPartial (γ := β) (mem_multiIdx.2 (by omega))).2
  have hp := (hβD.trans hD).perm (pdList_add_perm α β)
  exact (hf.weakPartial_ae_eq (γ := α + β)
    (mem_multiIdx.2 (by simp only [Prod.fst_add, Prod.snd_add]; omega)) hL hp).symm

/-- `∂^δ ∂^e w ∈ H^a` with `‖∂^δ ∂^e w‖_{H^a} ≤ ‖w‖_{H^{a+|δ|+|e|}}`. -/
theorem memH_weakPartial_weakPartial {a : ℕ} {δ e : ℕ × ℕ} {w : ℂ → ℂ}
    (hw : MemH (a + (δ.1 + δ.2) + (e.1 + e.2)) w) :
    MemH a (weakPartial δ (weakPartial e w)) ∧
      normH a (weakPartial δ (weakPartial e w)) ≤ normH (a + (δ.1 + δ.2) + (e.1 + e.2)) w := by
  obtain ⟨h1, h2⟩ := MemH.weakPartial (k := a + (δ.1 + δ.2)) (γ := e) hw
  obtain ⟨h3, h4⟩ := MemH.weakPartial (k := a) (γ := δ) h1
  exact ⟨h3, h4.trans h2⟩

theorem sum_leIdx_choose (γ : ℕ × ℕ) :
    ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℝ) = 2 ^ (γ.1 + γ.2) := by
  rw [leIdx, Finset.sum_product]
  simp_rw [Nat.cast_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  have h1 : ∑ i ∈ Finset.range (γ.1 + 1), ((γ.1.choose i : ℕ) : ℝ) = 2 ^ γ.1 := by
    exact_mod_cast Nat.sum_range_choose γ.1
  have h2 : ∑ i ∈ Finset.range (γ.2 + 1), ((γ.2.choose i : ℕ) : ℝ) = 2 ^ γ.2 := by
    exact_mod_cast Nat.sum_range_choose γ.2
  rw [h1, h2, pow_add]

theorem card_multiIdx_le (k : ℕ) : (multiIdx k).card ≤ (k + 1) ^ 2 := by
  unfold multiIdx
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_product, sq]

theorem sqrt_sum_sq_le {s : Finset (ℕ × ℕ)} {a : ℕ × ℕ → ℝ} {B : ℝ} {n : ℕ}
    (hcard : s.card ≤ n ^ 2) (hB : 0 ≤ B) (ha : ∀ γ ∈ s, 0 ≤ a γ ∧ a γ ≤ B) :
    Real.sqrt (∑ γ ∈ s, a γ ^ 2) ≤ n * B := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc ∑ γ ∈ s, a γ ^ 2 ≤ ∑ _γ ∈ s, B ^ 2 :=
        Finset.sum_le_sum fun γ hγ => pow_le_pow_left₀ (ha γ hγ).1 (ha γ hγ).2 2
    _ = s.card * B ^ 2 := by simp
    _ ≤ (n ^ 2 : ℕ) * B ^ 2 := by gcongr
    _ = (n * B) ^ 2 := by push_cast; ring

end NonUniqueEuler.Sob.HkCalcAux
