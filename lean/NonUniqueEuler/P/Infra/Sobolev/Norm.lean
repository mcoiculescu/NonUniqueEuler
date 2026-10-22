import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import NonUniqueEuler.Defs.Infra.Sobolev
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Proof: algebra of `H^k` membership and norms (library I-HK)

Proof of `NonUniqueEuler/I/Infra/Sobolev/Norm.lean`: `H^k` is a vector space, `normH k` is a
seminorm on it, both are invariant under a.e. modification, and `‖f‖_{H^0} = ‖f‖_{L²}`.

The proof uses the weak-derivative interface `I/Infra/Sobolev/WeakDeriv.lean` (uniqueness
`weakDerivOn_ae_eq`, linearity `HasWeakDerivOn.add`/`const_mul`, `HasWeakDerivOn.congr_ae`),
`eLpNorm_add_le`/`eLpNorm_const_smul` for each multi-index, and Minkowski's inequality in
`ℓ²(multiIdx k)` from the Cauchy–Schwarz inequality `Real.sum_mul_le_sqrt_mul_sqrt`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

namespace NormAux

/-- Minkowski's inequality in `ℓ²` over a finite set. -/
theorem sqrt_sum_sq_add_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    Real.sqrt (∑ i ∈ s, (a i + b i) ^ 2) ≤
      Real.sqrt (∑ i ∈ s, a i ^ 2) + Real.sqrt (∑ i ∈ s, b i ^ 2) := by
  have hA : 0 ≤ ∑ i ∈ s, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB : 0 ≤ ∑ i ∈ s, b i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s a b
  have e : ∑ i ∈ s, (a i + b i) ^ 2 =
      ∑ i ∈ s, a i ^ 2 + 2 * ∑ i ∈ s, a i * b i + ∑ i ∈ s, b i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
  nlinarith [hcs]

/-- An `L²` function on the plane is locally integrable on `univ`. -/
theorem locInt_of_memLp {f : ℂ → ℂ} (hf : MemLp f 2 volume) : LocallyIntegrableOn f univ :=
  (hf.locallyIntegrable (by norm_num)).locallyIntegrableOn univ

/-- The chosen weak derivative agrees a.e. with any `L²` weak derivative. -/
theorem weakPartial_ae_eq_of {γ : ℕ × ℕ} {f g : ℂ → ℂ} (hg : MemLp g 2 volume)
    (h : HasWeakDerivOn univ (pdList γ) f g) : weakPartial γ f =ᵐ[volume] g := by
  have := weakDerivOn_ae_eq (V := univ) isOpen_univ (locInt_of_memLp hg) h
  filter_upwards [this] with x hx using hx (mem_univ x)

/-- For `f ∈ H^k` and `|γ| ≤ k`, the chosen weak derivative is an `L²` weak derivative. -/
theorem spec {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    MemLp (weakPartial γ f) 2 volume ∧ HasWeakDerivOn univ (pdList γ) f (weakPartial γ f) := by
  obtain ⟨g, hg, h⟩ := (memH_iff.1 hf).2 γ hγ
  refine ⟨hg.ae_eq (weakPartial_ae_eq_of hg h).symm, ?_⟩
  exact (weakDerivOn_spec (locInt_of_memLp hg) h).2

theorem l2_congr_ae {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) : l2 f = l2 g := by
  unfold l2
  rw [eLpNorm_congr_ae h]

theorem l2_add_le {f g : ℂ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    l2 (f + g) ≤ l2 f + l2 g := by
  unfold l2
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le hf.1 hg.1 (by norm_num))

theorem l2_const_smul (c : ℂ) (f : ℂ → ℂ) : l2 (c • f) = ‖c‖ * l2 f := by
  unfold l2
  rw [eLpNorm_const_smul, ENNReal.toReal_mul]
  simp

/-- Homogeneity of the `H^k` norm (stated before `MemH.sub`, which uses it). -/
theorem const_smul_aux {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) (c : ℂ) :
    MemH k (c • f) ∧ normH k (c • f) = ‖c‖ * normH k f := by
  have hd : ∀ γ ∈ multiIdx k, MemLp (c • weakPartial γ f) 2 volume ∧
      HasWeakDerivOn univ (pdList γ) (c • f) (c • weakPartial γ f) := by
    intro γ hγ
    obtain ⟨hf1, hf2⟩ := spec hf hγ
    exact ⟨hf1.const_smul c, hf2.const_mul c⟩
  have hmem : MemH k (c • f) :=
    memH_iff.2 ⟨(memH_iff.1 hf).1.const_smul c, fun γ hγ =>
      ⟨_, (hd γ hγ).1, (hd γ hγ).2⟩⟩
  refine ⟨hmem, ?_⟩
  rw [normH_eq, normH_eq]
  have e : ∀ γ ∈ multiIdx k, l2 (weakPartial γ (c • f)) ^ 2 =
      ‖c‖ ^ 2 * l2 (weakPartial γ f) ^ 2 := by
    intro γ hγ
    rw [l2_congr_ae (weakPartial_ae_eq_of (hd γ hγ).1 (hd γ hγ).2), l2_const_smul, mul_pow]
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

end NormAux

open NormAux

theorem MemH.add {k : ℕ} {f g : ℂ → ℂ} (hf : MemH k f) (hg : MemH k g) :
    MemH k (f + g) ∧ normH k (f + g) ≤ normH k f + normH k g := by
  have hd : ∀ γ ∈ multiIdx k, MemLp (weakPartial γ f + weakPartial γ g) 2 volume ∧
      HasWeakDerivOn univ (pdList γ) (f + g) (weakPartial γ f + weakPartial γ g) := by
    intro γ hγ
    obtain ⟨hf1, hf2⟩ := spec hf hγ
    obtain ⟨hg1, hg2⟩ := spec hg hγ
    refine ⟨hf1.add hg1, ?_⟩
    exact HasWeakDerivOn.add isOpen_univ (locInt_of_memLp (memH_iff.1 hf).1)
      (locInt_of_memLp (memH_iff.1 hg).1) (locInt_of_memLp hf1) (locInt_of_memLp hg1) hf2 hg2
  have hmem : MemH k (f + g) :=
    memH_iff.2 ⟨(memH_iff.1 hf).1.add (memH_iff.1 hg).1, fun γ hγ =>
      ⟨_, (hd γ hγ).1, (hd γ hγ).2⟩⟩
  refine ⟨hmem, ?_⟩
  rw [normH_eq, normH_eq, normH_eq]
  refine le_trans (Real.sqrt_le_sqrt ?_) (sqrt_sum_sq_add_le _ _ _)
  refine Finset.sum_le_sum fun γ hγ => ?_
  have hae := weakPartial_ae_eq_of (hd γ hγ).1 (hd γ hγ).2
  rw [l2_congr_ae hae]
  exact pow_le_pow_left₀ (l2_nonneg _)
    (l2_add_le (spec hf hγ).1 (spec hg hγ).1) 2

theorem MemH.sub {k : ℕ} {f g : ℂ → ℂ} (hf : MemH k f) (hg : MemH k g) :
    MemH k (f - g) ∧ normH k (f - g) ≤ normH k f + normH k g := by
  have e : f - g = f + (-1 : ℂ) • g := by
    rw [neg_one_smul, sub_eq_add_neg]
  obtain ⟨hg', hng⟩ := const_smul_aux hg (-1)
  obtain ⟨hmem, hle⟩ := hf.add hg'
  rw [e]
  refine ⟨hmem, hle.trans_eq ?_⟩
  rw [hng]
  simp

theorem MemH.const_smul {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) (c : ℂ) :
    MemH k (c • f) ∧ normH k (c • f) = ‖c‖ * normH k f :=
  const_smul_aux hf c

/-- `H^k` membership and the norm only depend on the a.e. class. -/
theorem MemH.congr_ae {k : ℕ} {f g : ℂ → ℂ} (hf : MemH k f) (hfg : f =ᵐ[volume] g) :
    MemH k g ∧ normH k g = normH k f := by
  have hfg' : ∀ᵐ x ∂volume, x ∈ univ → f x = g x := by
    filter_upwards [hfg] with x hx _ using hx
  have hd : ∀ γ ∈ multiIdx k, MemLp (weakPartial γ f) 2 volume ∧
      HasWeakDerivOn univ (pdList γ) g (weakPartial γ f) := by
    intro γ hγ
    obtain ⟨hf1, hf2⟩ := spec hf hγ
    exact ⟨hf1, hf2.congr_ae hfg' (ae_of_all _ fun _ _ => rfl)⟩
  have hmem : MemH k g :=
    memH_iff.2 ⟨(memH_iff.1 hf).1.ae_eq hfg, fun γ hγ => ⟨_, (hd γ hγ).1, (hd γ hγ).2⟩⟩
  refine ⟨hmem, ?_⟩
  rw [normH_eq, normH_eq]
  congr 1
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [l2_congr_ae (weakPartial_ae_eq_of (hd γ hγ).1 (hd γ hγ).2)]

/-- `‖f‖_{H^0} = ‖f‖_{L²}`. -/
theorem normH_zero {f : ℂ → ℂ} (hf : MemLp f 2 volume) : MemH 0 f ∧ normH 0 f = l2 f := by
  have h0 : HasWeakDerivOn univ (pdList (0, 0)) f f := fun φ _ => by simp [pdList]
  have hI : multiIdx 0 = {(0, 0)} := by
    ext γ
    rw [mem_multiIdx, Finset.mem_singleton]
    constructor
    · intro h
      exact Prod.ext (by omega) (by omega)
    · rintro rfl
      simp
  have hmem : MemH 0 f := by
    refine memH_iff.2 ⟨hf, fun γ hγ => ⟨f, hf, ?_⟩⟩
    rw [hI, Finset.mem_singleton] at hγ
    rw [hγ]
    exact h0
  refine ⟨hmem, ?_⟩
  rw [normH_eq, hI, Finset.sum_singleton, Real.sqrt_sq (l2_nonneg _),
    l2_congr_ae (weakPartial_ae_eq_of hf h0)]

end NonUniqueEuler.Sob
