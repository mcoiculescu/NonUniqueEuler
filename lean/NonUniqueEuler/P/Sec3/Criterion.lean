import NonUniqueEuler.Defs.Sec3.Extra2Criterion
import NonUniqueEuler.H.Sec3.Criterion.Props
import NonUniqueEuler.H.Sec3.Criterion.Departure
import NonUniqueEuler.H.Sec3.Criterion.Symmetry
import NonUniqueEuler.I.Sec3.Criterion.Limit
import NonUniqueEuler.I.Sec3.Criterion.Uniform
import NonUniqueEuler.I.Sec3.WeakContRep
import NonUniqueEuler.I.Sec3.RadialStationary

/-!
# Proof: `thm:criterion`, the non-uniqueness criterion (with eq:defect)

Proof of `I/Sec3/Criterion.lean` (manuscript `03_compactness.tex:933-1077`).

Structure (following the manuscript proof):
* pass to a subsequence along which `sup_{t ≤ T} ‖ω⁽ⁿ⁾(t) - f‖₁ → c`
  (`CriterionAux.exists_strictMono_tendsto_limsup`);
* step 1, construction of `ω_∞`, (i) and the uniform weak convergence: `criterion_limit`
  (`I/Sec3/Criterion/Limit.lean`);
* (ii), (iii): `H/Sec3/Criterion/Props.lean`;
* (iv): `criterion_tendstoUnif` (`I/Sec3/Criterion/Uniform.lean`);
* (v): `H/Sec3/Criterion/Departure.lean`, with `lem:weak-cont`(a) (`ω_∞(0) = f`) and
  `lem:radial-stationary`;
* (vi): `H/Sec3/Criterion/Symmetry.lean`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact

open Weak

/-- **`thm:criterion`** (`03_compactness.tex:933-968`): for radial `f`, a `2`-admissible sequence
`(f⁽ⁿ⁾, ω⁽ⁿ⁾)` for `f` on `[0, T₀)` (weakly continuous representatives) and `T ∈ (0, T₀)` with
eq:defect `limsup_n sup_{t ≤ T} ‖ω⁽ⁿ⁾(t) - f‖_{L¹} > 0`, there are a subsequence `φ` and a limit
`ω_∞` satisfying (i)–(vi) (`IsCriterionLimit`). -/
theorem criterion {T₀ : ℝ≥0∞} {T : ℝ} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}
    (hrad : IsRadial f) (hadm : IsAdmissibleSeq 2 T₀ f fs ωs)
    (hcont : ∀ n, IsWeakContL2On (timeInterval T₀) (ωs n))
    (hT : 0 < T) (hTT₀ : ENNReal.ofReal T < T₀) (hdefect : 0 < defectLp 1 T ωs f) :
    ∃ φ : ℕ → ℕ, ∃ ωinf : ℝ → ℂ → ℝ, IsCriterionLimit T₀ T f ωs φ ωinf := by
  -- the subsequence realizing the `limsup` of eq:defect
  obtain ⟨φ₁, hφ₁, hc⟩ := CriterionAux.exists_strictMono_tendsto_limsup
    (fun n => supDist 1 (Icc 0 T) (ωs n) (stationary f))
  have hadm₁ := hadm.subseq hφ₁
  -- step 1: the limit
  obtain ⟨φ₂, hφ₂, ω, hren, hwc, hunif⟩ :=
    criterion_limit hadm₁ (fun n => hcont (φ₁ n))
  have hadm₂ := hadm₁.subseq hφ₂
  have hf : AEStronglyMeasurable f volume := hadm.memLp_one.aestronglyMeasurable
  have hf2 : MemLp f 2 volume := by simpa using hadm.memLp_q
  -- (ii)
  have heq := CriterionAux.equimeasurable_of_renormalized hren hwc
  have hnorm := CriterionAux.eLpNorm_eq_of_equimeasurable heq
  -- (iii)
  have hc2 : ContinuousIntoLpOn 2 (timeInterval T₀) ω :=
    CriterionAux.continuousIntoLpOn_two hwc fun t ht => hnorm t ht 2 one_le_two
  have hLq : ∀ q : ℝ, 1 ≤ q → q ≤ 2 →
      ContinuousIntoLpOn (ENNReal.ofReal q) (timeInterval T₀) ω := by
    intro q hq1 hq2
    rcases lt_or_eq_of_le hq2 with h | h
    · exact CriterionAux.continuousIntoLpOn_lt_two hren hwc q hq1 h
    · subst h
      simpa using hc2
  have hc1 : ContinuousIntoLpOn 1 (timeInterval T₀) ω := by
    simpa using hLq 1 le_rfl one_le_two
  -- (iv)
  have htu : TendstoUnifLqUpTo T₀ (fun n => ωs (φ₁ (φ₂ n))) ω :=
    criterion_tendstoUnif hadm₂ (fun n => hcont (φ₁ (φ₂ n))) hren hwc hunif hnorm hLq
  -- (v)
  have hω0 : ω 0 =ᵐ[volume] f :=
    (hren T hT hTT₀).toIsWeakSolution.ae_eq_datum_of_isWeakContL2On
      (hwc.mono (Icc_subset_timeInterval hTT₀))
  have hsup : supDist 1 (Icc 0 T) ω (stationary f) = defectLp 1 T ωs f := by
    refine CriterionAux.supDist_eq_of_tendsto
      (ωs := fun n => ωs (φ₁ (φ₂ n)))
      (fun n t ht => ((hcont _).memLp t (Icc_subset_timeInterval hTT₀ ht)).aestronglyMeasurable)
      (fun t ht => (hwc.memLp t (Icc_subset_timeInterval hTT₀ ht)).aestronglyMeasurable) hf
      (hc.comp hφ₂.tendsto_atTop) ?_
    simpa using htu T hTT₀ 1 le_rfl one_le_two
  have hopen := CriterionAux.isOpen_departureSet_of hc1 hf hω0
  have hne : (departureSet T₀ ω f ∩ Ioc 0 T).Nonempty :=
    CriterionAux.departureSet_inter_nonempty_of hTT₀
      (fun t ht => (hwc.memLp t (Icc_subset_timeInterval hTT₀ ht)).aestronglyMeasurable) hf hω0
      (hsup ▸ hdefect)
  have hren_q := CriterionAux.renormalized_q_of_equimeasurable hren heq
  refine ⟨φ₁ ∘ φ₂, ω, ?_⟩
  exact
    { strictMono := hφ₁.comp hφ₂
      renormalized := hren
      weakCont := hwc
      equimeasurable := heq
      eLpNorm_eq := hnorm
      nonneg := CriterionAux.nonneg_of_equimeasurable heq
      renormalized_q := hren_q
      continuousIntoLp_le_two := hLq
      continuousIntoLp_gt_two := fun q r hq hqr hfr => by
        have hfq : MemLp f (ENNReal.ofReal q) volume :=
          LpInterp.memLp_of_memLp_of_memLp (p := 2) (by norm_num)
            (by rw [← ENNReal.ofReal_ofNat 2]; exact ENNReal.ofReal_le_ofReal hq.le)
            (ENNReal.ofReal_le_ofReal hqr.le) hf2 hfr
        exact CriterionAux.continuousIntoLpOn_of_interp hc2 hq hqr hfr
          (fun t ht => ((heq t ht).memLp_iff _).2 hfq)
          (fun t ht => (heq t ht).eLpNorm_eq _)
      tendstoUnif := htu
      supDist_eq := hsup
      isOpen_departureSet := hopen
      zero_not_mem_departureSet := CriterionAux.zero_not_mem_departureSet_of hω0
      departureSet_inter_nonempty := hne
      departureTime_lt := CriterionAux.departureTime_lt_of hopen hne
      distinct := fun T' hT' _ =>
        CriterionAux.distinctInX_of hopen (hne.mono inter_subset_left) hT'
      both_renormalized := fun T' hT' hT'T₀ q hq hfq => by
        have hT'0 : 0 < T' := (departureTime_nonneg T₀ ω f).trans_lt hT'
        exact ⟨radial_stationary hq hT'0 hadm.memLp_one hfq hrad,
          hren_q T' hT'0 hT'T₀ q hq hfq⟩
      symmetric := fun Q ι _ hsym t ht =>
        CriterionAux.isSymmetricUnder_of_weakTendsto (hwc.memLp t ht)
          (fun ψ hψ => (hunif t ht.2 ψ hψ).tendsto_at ⟨ht.1, le_rfl⟩) Q ι
          (fun n => hsym (φ₁ (φ₂ n)) t ht) }

end NonUniqueEuler.Compact
