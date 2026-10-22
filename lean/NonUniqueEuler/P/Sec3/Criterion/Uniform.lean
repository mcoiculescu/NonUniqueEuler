import NonUniqueEuler.Defs.Sec3.Criterion
import NonUniqueEuler.I.Sec3.BoundedAdm
import NonUniqueEuler.I.Sec3.RR
import NonUniqueEuler.I.Sec3.RenormAllT
import NonUniqueEuler.I.Infra.LpInterp.Interp
import NonUniqueEuler.H.Sec3.Criterion.Uniform.Claim

/-!
# Proof of `I/Sec3/Criterion/Uniform.lean`: `thm:criterion`(iv)

Manuscript: proof of `thm:criterion`, paragraphs "We now prove (iv)" and "We prove the claim",
`03_compactness.tex:1023-1056`.

Structure.
1. Choose `T_j ∈ (T', T₀)`, `T_j > 0` (`ENNReal.lt_iff_exists_real_btwn`), the bound
   `M = sup_n ‖f⁽ⁿ⁾‖_{L¹∩L²}` (`boundedAdm_iSup_eq`) and the constant `C_v`
   (`renormAllT_flux_bound`); eq:tail on `[0, T_j)` (`renormAllT_tail`) gives the uniform tail
   bound `∫_{|x|≥2R}|ω⁽ⁿ⁾(s)| ≤ ∫_{|x|≥R}|f⁽ⁿ⁾| + (‖∇ς‖_∞/R) C_v T_j M²`, `s ∈ [0, T']`.
2. The claim (`UniformAux.claim_two`, `UniformAux.claim_one`) and the continuity of `ω_∞` into
   `L¹`, `L²` give, by the triangle inequality (`UniformAux.tendsto_eLpNorm_sub_sub`), the
   sequential hypothesis of `UniformAux.tendsto_iSup_of_seq`, hence the uniform convergence for
   `q ∈ {1, 2}`.
3. For `q ∈ [1, 2]`: `‖g‖_q ≤ ‖g‖₁^{2/q-1} ‖g‖₂^{2-2/q}` (`LpInterp.eLpNorm_le_of_one_two`)
   bounds the supremum by `S₁^{2/q-1} S₂^{2-2/q} → 0` (`UniformAux.tendsto_rpow_mul_rpow_zero`).

Deviation (harmless): the weak convergence in the claim uses the uniform weak convergence on
`[0, T']` itself instead of `[0, T_j]`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact

open Weak

-- `hren` is part of the interface statement; the proof does not need it.
set_option linter.unusedVariables false in
/-- **`thm:criterion`(iv)** (`03_compactness.tex:1023-1056`): for a `2`-admissible sequence
(weakly continuous representatives) converging uniformly weakly in `L²` on every `[0, T']`,
`T' < T₀`, to a renormalized weak solution `ω_∞` on `[0, T₀)` with datum `f` that is weakly
continuous, conserves the `L^p` norms of `f` and is continuous into `L^q`, `q ∈ [1, 2]`, the
convergence is uniform in `L^q` on every `[0, T']`, `q ∈ [1, 2]`. -/
theorem criterion_tendstoUnif {T₀ : ℝ≥0∞} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ}
    {ωs : ℕ → ℝ → ℂ → ℝ} {ωinf : ℝ → ℂ → ℝ}
    (hadm : IsAdmissibleSeq 2 T₀ f fs ωs)
    (hcont : ∀ n, IsWeakContL2On (timeInterval T₀) (ωs n))
    (hren : IsRenormalizedWeakSolutionUpTo 2 T₀ f ωinf)
    (hwc : IsWeakContL2On (timeInterval T₀) ωinf)
    (hunif : ∀ T' : ℝ, ENNReal.ofReal T' < T₀ → WeakTendstoUnifL2On ωs ωinf (Icc 0 T'))
    (hnorm : ∀ t ∈ timeInterval T₀, ∀ p : ℝ≥0∞, 1 ≤ p →
      eLpNorm (ωinf t) p volume = eLpNorm f p volume)
    (hLq : ∀ q : ℝ, 1 ≤ q → q ≤ 2 →
      ContinuousIntoLpOn (ENNReal.ofReal q) (timeInterval T₀) ωinf) :
    TendstoUnifLqUpTo T₀ ωs ωinf := by
  intro T' hT' q hq1 hq2
  -- Step 1: `T_j ∈ (T', T₀)`, the bound `M`, the constant `C_v` and the tail bound.
  obtain ⟨Tj, -, hT'Tj, hTjT₀⟩ := ENNReal.lt_iff_exists_real_btwn.1 hT'
  have hTj : T' < Tj ∧ 0 < Tj := ENNReal.ofReal_lt_ofReal_iff'.1 hT'Tj
  have hK : Icc 0 T' ⊆ timeInterval T₀ := Icc_subset_timeInterval hT'
  have hKj : Icc 0 T' ⊆ Ico 0 Tj := fun s hs => ⟨hs.1, hs.2.trans_lt hTj.1⟩
  have hIj : Icc 0 Tj ⊆ timeInterval T₀ := Icc_subset_timeInterval hTjT₀
  obtain ⟨hsup, hfin⟩ := boundedAdm_iSup_eq hadm hcont
  set M : ℝ := (⨆ n, normL1LpE 2 (fs n)).toReal with hMdef
  have hM : ∀ n, ∀ s ∈ Icc 0 Tj, normL1LpE 2 (ωs n s) ≤ ENNReal.ofReal M := by
    intro n s hs
    rw [hMdef, ENNReal.ofReal_toReal hfin.ne, ← hsup]
    exact (le_iSup₂ (f := fun t (_ : t ∈ timeInterval T₀) => normL1LpE 2 (ωs n t)) s
      (hIj hs)).trans (le_iSup (fun n => ⨆ t ∈ timeInterval T₀, normL1LpE 2 (ωs n t)) n)
  obtain ⟨Cv, -, hflux⟩ := renormAllT_flux_bound
  have htail : ∀ R : ℝ, 0 < R → ∀ m, ∀ s ∈ Icc 0 T',
      ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖ωs m s x‖ₑ ≤
        (∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖fs m x‖ₑ) +
          ENNReal.ofReal (Smooth.gradSup sigmaCut / R) * ENNReal.ofReal (Cv * Tj * M ^ 2) := by
    intro R hR m s hs
    have hrm := hadm.renormalized m Tj hTj.2 hTjT₀
    have hcm := (hcont m).mono hIj
    refine (renormAllT_tail hrm hcm R hR s (hKj hs)).trans ?_
    exact add_le_add le_rfl
      (mul_le_mul_right (hflux Tj M (fs m) (ωs m) hrm.toIsWeakSolution hcm (hM m)) _)
  -- Measurability and the continuity of `ω_∞` along sequences.
  have hmeasK : ∀ m, ∀ s ∈ Icc 0 T', AEStronglyMeasurable (ωs m s) volume :=
    fun m s hs => ((hcont m).memLp s (hK hs)).1
  have hmeasinf : ∀ s ∈ Icc 0 T', AEStronglyMeasurable (ωinf s) volume :=
    fun s hs => (hwc.memLp s (hK hs)).1
  have hcontinf : ∀ p : ℝ, 1 ≤ p → p ≤ 2 → ∀ (t : ℕ → ℝ) (t₀ : ℝ), (∀ i, t i ∈ Icc 0 T') →
      t₀ ∈ Icc 0 T' → Tendsto t atTop (𝓝 t₀) →
      Tendsto (fun i => eLpNorm (ωinf (t i) - ωinf t₀) (ENNReal.ofReal p) volume) atTop
        (𝓝 0) :=
    fun p hp1 hp2 t t₀ ht ht₀ hlim => ((hLq p hp1 hp2).2 t₀ (hK ht₀)).comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun i => hK (ht i)⟩)
  have hnorm2 : ∀ t ∈ timeInterval T₀, eLpNorm (ωinf t) 2 volume = eLpNorm f 2 volume :=
    fun t ht => hnorm t ht 2 one_le_two
  -- Step 2: the uniform convergence for `q = 2` and `q = 1`.
  have hS2 : Tendsto (fun n => supDist 2 (Icc 0 T') (ωs n) ωinf) atTop (𝓝 0) := by
    refine UniformAux.tendsto_iSup_of_seq isCompact_Icc
      (fun n t => eLpNorm (ωs n t - ωinf t) 2 volume) ?_
    intro n t t₀ hn ht ht₀ hlim
    have h1 := UniformAux.claim_two hadm hcont hwc hnorm2 hK (hunif T' hT') hn ht ht₀ hlim
    have h2 := hcontinf 2 one_le_two le_rfl t t₀ ht ht₀ hlim
    rw [ENNReal.ofReal_ofNat] at h2
    exact UniformAux.tendsto_eLpNorm_sub_sub one_le_two (fun i => hmeasK _ _ (ht i))
      (fun i => hmeasinf _ (ht i)) (hmeasinf _ ht₀) h1 h2
  have hS1 : Tendsto (fun n => supDist 1 (Icc 0 T') (ωs n) ωinf) atTop (𝓝 0) := by
    refine UniformAux.tendsto_iSup_of_seq isCompact_Icc
      (fun n t => eLpNorm (ωs n t - ωinf t) 1 volume) ?_
    intro n t t₀ hn ht ht₀ hlim
    have h1 := UniformAux.claim_two hadm hcont hwc hnorm2 hK (hunif T' hT') hn ht ht₀ hlim
    have hg1 : eLpNorm (ωinf t₀) 1 volume ≠ ∞ := by
      rw [hnorm t₀ (hK ht₀) 1 le_rfl]
      exact hadm.memLp_one.eLpNorm_ne_top
    have h1' := UniformAux.claim_one hadm hmeasK (hmeasinf _ ht₀) hg1 htail hn ht h1
    have h2 := hcontinf 1 le_rfl one_le_two t t₀ ht ht₀ hlim
    rw [ENNReal.ofReal_one] at h2
    exact UniformAux.tendsto_eLpNorm_sub_sub le_rfl (fun i => hmeasK _ _ (ht i))
      (fun i => hmeasinf _ (ht i)) (hmeasinf _ ht₀) h1' h2
  -- Step 3: interpolation for `q ∈ [1, 2]`.
  have hq0 : 0 < q := by linarith
  have ha : 0 ≤ 2 / q - 1 := by
    rw [sub_nonneg, le_div_iff₀ hq0]
    linarith
  have hb : 0 ≤ 2 - 2 / q := by
    rw [sub_nonneg, div_le_iff₀ hq0]
    linarith
  have hlim := UniformAux.tendsto_rpow_mul_rpow_zero ha hb (by ring) hS1 hS2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) fun n => ?_
  rw [supDist_le_iff]
  intro s hs
  have hm := (hmeasK n s hs).sub (hmeasinf s hs)
  refine (LpInterp.eLpNorm_le_of_one_two hm hq1 hq2).trans ?_
  exact mul_le_mul' (ENNReal.rpow_le_rpow (eLpNorm_le_supDist hs) ha)
    (ENNReal.rpow_le_rpow (eLpNorm_le_supDist hs) hb)

end NonUniqueEuler.Compact
