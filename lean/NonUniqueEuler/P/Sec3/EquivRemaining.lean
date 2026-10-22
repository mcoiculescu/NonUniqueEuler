import NonUniqueEuler.Defs.Sec3.Extra2Criterion
import NonUniqueEuler.I.Sec3.Equiv
import NonUniqueEuler.I.Sec3.RR
import NonUniqueEuler.I.Sec3.BoundedAdm
import NonUniqueEuler.I.Infra.LpInterp.Interp
import NonUniqueEuler.H.Sec3.EquivRemaining.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Data.Real.ConjExponents
import Mathlib.Order.Filter.ENNReal
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE

/-!
# Proof of `I/Sec3/EquivRemaining.lean`: `prop:equiv`, the remaining implications

Manuscript: `prop:equiv`, `03_compactness.tex:1079-1097` (statement), proof
`03_compactness.tex:1099-1128`.

* (e) ⇒ (c) (`03_compactness.tex:1104-1108`): with `T' = T`, `ω^{(n_k)}(t) → ω_∞(t)` in `L¹`, so
  `∫ ω^{(n_k)}(t) ψ → ∫ ω_∞(t) ψ` for bounded `ψ` (Hölder `L¹`–`L^∞`). If `ω⁽ⁿ⁾(t) → f` in `𝒟'`,
  then `∫ (ω_∞(t) - f) ψ = 0` for every `ψ ∈ C_c^∞`, and `ω_∞(t) = f` a.e. by the fundamental
  lemma (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`; `ω_∞(t) - f ∈ L²` is locally
  integrable).
* (c) ⇒ (d) (`03_compactness.tex:1108-1110`): if `defectPairing = 0`, the suprema tend to `0`
  (`EquivRemaining.tendsto_zero_of_limsup_eq_zero`), and they dominate
  `|∫ ω⁽ⁿ⁾(t) ψ - ∫ f ψ|`.
* (d) ⇒ (b) (`03_compactness.tex:1111-1112`): Hölder `|∫ g ψ| ≤ ‖g‖_{L^q} ‖ψ‖_{L^{q'}}`
  (`EquivRemaining.enorm_integral_mul_le`, `q' = ENNReal.conjExponent q`), hence
  `defectPairing ≤ ‖ψ‖_{L^{q'}} · defectLp q`.
* (b) ⇒ (a) (`03_compactness.tex:1114-1127`): if `defectLp 1 = 0`, then
  `sup_t ‖ω⁽ⁿ⁾(t) - f‖_{L¹} → 0`. Along the filter `comap Prod.fst atTop` on `ℕ × [0, T]` (which
  encodes uniformity in `t`), `ω⁽ⁿ⁾(t) → f` in `L¹` with a uniform `L²` bound
  (`lem:bounded-adm`(ii), `boundedAdm_eLpNorm_eq`, `boundedAdm_iSup_eq`), hence weakly in `L²`
  (`EquivRemaining.tendsto_integral_mul_of_eLpNorm_one`), and `‖ω⁽ⁿ⁾(t)‖_{L²} = ‖f⁽ⁿ⁾‖_{L²} →
  ‖f‖_{L²}`; `lem:RR` (`radonRiesz_filter`) gives `sup_t ‖ω⁽ⁿ⁾(t) - f‖_{L²} → 0`. For `q ∈ (1, 2]`,
  `‖g‖_{L^q} ≤ ‖g‖_{L¹} + ‖g‖_{L²}` (`LpInterp.eLpNorm_le_eLpNorm_add_eLpNorm`) gives
  `defectLp q = 0`.
* TFAE: (a) ⇒ (e) ⇒ (c) ⇒ (d) ⇒ (a) (with `I/Sec3/Equiv.lean`), (d) ⇒ (b∀) ⇒ (b∃) ⇒ (a).

Deviations from the manuscript:
* (b) ⇒ (a): instead of choosing almost maximizing times `tₙ`, the Radon–Riesz lemma is applied
  along the filter `comap Prod.fst atTop` on `ℕ × [0, T]` (uniform convergence in `t`); and for
  `q ∈ (1, 2)` the bound `‖g‖_q ≤ ‖g‖_1 + ‖g‖_2` replaces the interpolation inequality (both
  `L¹` and `L²` suprema tend to `0` at this point, so either suffices).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact

open Weak

/-- `f ∈ L²` for a `2`-admissible sequence. -/
private theorem memLp_two_of_adm {T₀ : ℝ≥0∞} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ}
    {ωs : ℕ → ℝ → ℂ → ℝ} (hadm : IsAdmissibleSeq 2 T₀ f fs ωs) : MemLp f 2 volume := by
  have := hadm.memLp_q
  rwa [ENNReal.ofReal_ofNat] at this

/-- `g ψ ∈ L¹` for `g, ψ ∈ L²`, with the product written pointwise. -/
private theorem integrable_mul_two {g ψ : ℂ → ℝ} (hg : MemLp g 2 volume)
    (hψ : MemLp ψ 2 volume) : Integrable (fun x => g x * ψ x) volume :=
  hg.integrable_mul hψ

set_option linter.unusedVariables false in
/-- **`prop:equiv`, (e) ⇒ (c)** (`03_compactness.tex:1104-1108`). -/
theorem equiv_e_imp_c {T₀ : ℝ≥0∞} {T : ℝ} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ}
    {ωs : ℕ → ℝ → ℂ → ℝ} (hrad : IsRadial f) (hadm : IsAdmissibleSeq 2 T₀ f fs ωs)
    (hcont : ∀ n, IsWeakContL2On (timeInterval T₀) (ωs n))
    (hT : 0 < T) (hTT₀ : ENNReal.ofReal T < T₀) (he : HasNonstationaryLimit T₀ T ωs f) :
    NotDistribTendsto T ωs f := by
  obtain ⟨φ, hφ, ωinf, -, hwc, htend, t, ht, hne⟩ := he
  have hf2 : MemLp f 2 volume := memLp_two_of_adm hadm
  have htT : t ∈ Icc 0 T := Ioc_subset_Icc_self ht
  have htI : t ∈ timeInterval T₀ := Icc_subset_timeInterval hTT₀ htT
  have hinf2 : MemLp (ωinf t) 2 volume := hwc.memLp t htI
  refine ⟨t, ht, ?_⟩
  by_contra hall
  push Not at hall
  apply hne
  -- `ω^{(n_k)}(t) → ω_∞(t)` in `L¹` (`thm:criterion`(iv) with `T' = T`, `q = 1`)
  have hL1 : Tendsto (fun n => eLpNorm (ωs (φ n) t - ωinf t) 1 volume) atTop (𝓝 0) := by
    have h := htend T hTT₀ 1 le_rfl one_le_two
    rw [ENNReal.ofReal_one] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
      (fun n => eLpNorm_le_supDist (ω₁ := ωs (φ n)) (ω₂ := ωinf) htT)
  have key : ∀ ψ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, ψ x • (ωinf t x - f x) = 0 := by
    intro ψ hψ hψc
    have hψ2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
    have hψtop : MemLp ψ ⊤ volume := hψ.continuous.memLp_of_hasCompactSupport hψc
    have h1 : Tendsto (fun n => ∫ x, ωs (φ n) t x * ψ x) atTop
        (𝓝 (∫ x, ωinf t x * ψ x)) := by
      refine EquivRemaining.tendsto_of_enorm_sub_le
        (v := fun n => eLpNorm (ωs (φ n) t - ωinf t) 1 volume * eLpNorm ψ ⊤ volume) ?_
        (Eventually.of_forall fun n => ?_)
      · simpa using ENNReal.Tendsto.mul_const hL1 (Or.inr hψtop.eLpNorm_ne_top)
      · have hn2 : MemLp (ωs (φ n) t) 2 volume := (hcont (φ n)).memLp t htI
        rw [← integral_sub (integrable_mul_two hn2 hψ2) (integrable_mul_two hinf2 hψ2)]
        have heq : (fun x => ωs (φ n) t x * ψ x - ωinf t x * ψ x) =
            fun x => (ωs (φ n) t - ωinf t) x * ψ x := by
          funext x; simp [sub_mul]
        rw [heq]
        exact EquivRemaining.enorm_integral_mul_le (p := 1) (p' := ⊤) (hn2.1.sub hinf2.1)
          hψ2.1
    have h2 : Tendsto (fun n => ∫ x, ωs (φ n) t x * ψ x) atTop (𝓝 (∫ x, f x * ψ x)) :=
      (hall ψ hψ hψc).comp hφ.tendsto_atTop
    have hlim := tendsto_nhds_unique h1 h2
    have hsplit : ∫ x, ψ x • (ωinf t x - f x) = (∫ x, ωinf t x * ψ x) - ∫ x, f x * ψ x := by
      rw [← integral_sub (integrable_mul_two hinf2 hψ2) (integrable_mul_two hf2 hψ2)]
      congr 1; funext x; simp only [smul_eq_mul]; ring
    rw [hsplit, hlim, sub_self]
  have hloc : LocallyIntegrable (fun x => ωinf t x - f x) volume :=
    (hinf2.sub hf2).locallyIntegrable one_le_two
  filter_upwards [ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc key] with x hx
  exact sub_eq_zero.1 hx

set_option linter.unusedVariables false in
/-- **`prop:equiv`, (c) ⇒ (d)** (`03_compactness.tex:1108-1110`). -/
theorem equiv_c_imp_d {T₀ : ℝ≥0∞} {T : ℝ} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ}
    {ωs : ℕ → ℝ → ℂ → ℝ} (hrad : IsRadial f) (hadm : IsAdmissibleSeq 2 T₀ f fs ωs)
    (hcont : ∀ n, IsWeakContL2On (timeInterval T₀) (ωs n))
    (hT : 0 < T) (hTT₀ : ENNReal.ofReal T < T₀) (hc : NotDistribTendsto T ωs f) :
    HasPairingDefect T ωs f := by
  obtain ⟨t, ht, ψ, hψ, hψc, hnt⟩ := hc
  refine ⟨ψ, hψ, hψc, pos_iff_ne_zero.2 fun h0 => hnt ?_⟩
  have hf2 : MemLp f 2 volume := memLp_two_of_adm hadm
  have htT : t ∈ Icc 0 T := Ioc_subset_Icc_self ht
  have ht2 : ∀ n, MemLp (ωs n t) 2 volume := fun n =>
    (hcont n).memLp t (Icc_subset_timeInterval hTT₀ htT)
  have hψ2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  unfold defectPairing at h0
  have hsup := EquivRemaining.tendsto_zero_of_limsup_eq_zero h0
  refine EquivRemaining.tendsto_of_enorm_sub_le hsup (Eventually.of_forall fun n => ?_)
  rw [← integral_sub (integrable_mul_two (ht2 n) hψ2) (integrable_mul_two hf2 hψ2)]
  have heq : (fun x => ωs n t x * ψ x - f x * ψ x) = fun x => (ωs n t x - f x) * ψ x := by
    funext x; ring
  rw [heq]
  exact le_iSup₂ (f := fun s (_ : s ∈ Icc 0 T) => ‖∫ x, (ωs n s x - f x) * ψ x‖ₑ) t htT

set_option linter.unusedVariables false in
/-- **`prop:equiv`, (d) ⇒ (b) for every `q ∈ (1, 2]`** (`03_compactness.tex:1111-1112`). -/
theorem equiv_d_imp_b {T₀ : ℝ≥0∞} {T : ℝ} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ}
    {ωs : ℕ → ℝ → ℂ → ℝ} (hrad : IsRadial f) (hadm : IsAdmissibleSeq 2 T₀ f fs ωs)
    (hcont : ∀ n, IsWeakContL2On (timeInterval T₀) (ωs n))
    (hT : 0 < T) (hTT₀ : ENNReal.ofReal T < T₀) (hd : HasPairingDefect T ωs f) :
    ∀ q : ℝ, 1 < q → q ≤ 2 → 0 < defectLp (ENNReal.ofReal q) T ωs f := by
  intro q hq1 hq2
  obtain ⟨ψ, hψ, hψc, hpos⟩ := hd
  have hf2 : MemLp f 2 volume := memLp_two_of_adm hadm
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le
  have := ENNReal.HolderConjugate.conjExponent hq
  have hψq' : MemLp ψ (ENNReal.conjExponent (ENNReal.ofReal q)) volume :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  have hC : eLpNorm ψ (ENNReal.conjExponent (ENNReal.ofReal q)) volume ≠ ⊤ :=
    hψq'.eLpNorm_ne_top
  have hle : defectPairing T ωs f ψ ≤
      eLpNorm ψ (ENNReal.conjExponent (ENNReal.ofReal q)) volume *
        defectLp (ENNReal.ofReal q) T ωs f := by
    unfold defectPairing defectLp
    rw [← ENNReal.limsup_mul_const_of_ne_top hC]
    refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
    refine iSup₂_le fun t ht => ?_
    have ht2 : MemLp (ωs n t) 2 volume := (hcont n).memLp t (Icc_subset_timeInterval hTT₀ ht)
    calc ‖∫ x, (ωs n t x - f x) * ψ x‖ₑ
        ≤ eLpNorm (fun x => ωs n t x - f x) (ENNReal.ofReal q) volume *
            eLpNorm ψ (ENNReal.conjExponent (ENNReal.ofReal q)) volume :=
          EquivRemaining.enorm_integral_mul_le (ht2.1.sub hf2.1) hψq'.1
      _ ≤ supDist (ENNReal.ofReal q) (Icc 0 T) (ωs n) (stationary f) *
            eLpNorm ψ (ENNReal.conjExponent (ENNReal.ofReal q)) volume := by
          gcongr
          exact eLpNorm_le_supDist (ω₁ := ωs n) (ω₂ := stationary f) ht
  refine pos_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero] at hle
  exact (lt_of_lt_of_le hpos hle).false

set_option linter.unusedVariables false in
/-- **`prop:equiv`, (b) for some `q ∈ (1, 2]` ⇒ (a)** (`03_compactness.tex:1114-1127`). -/
theorem equiv_b_imp_a {T₀ : ℝ≥0∞} {T : ℝ} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ}
    {ωs : ℕ → ℝ → ℂ → ℝ} (hrad : IsRadial f) (hadm : IsAdmissibleSeq 2 T₀ f fs ωs)
    (hcont : ∀ n, IsWeakContL2On (timeInterval T₀) (ωs n))
    (hT : 0 < T) (hTT₀ : ENNReal.ofReal T < T₀)
    (hb : ∃ q : ℝ, 1 < q ∧ q ≤ 2 ∧ 0 < defectLp (ENNReal.ofReal q) T ωs f) :
    0 < defectLp 1 T ωs f := by
  obtain ⟨q, hq1, hq2, hpos⟩ := hb
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have hf2 : MemLp f 2 volume := memLp_two_of_adm hadm
  have hslice : ∀ n, ∀ t ∈ Icc 0 T, MemLp (ωs n t) 2 volume := fun n t ht =>
    (hcont n).memLp t (Icc_subset_timeInterval hTT₀ ht)
  -- (1) `sup_t ‖ω⁽ⁿ⁾(t) - f‖_{L¹} → 0`
  have h1 : Tendsto (fun n => supDist 1 (Icc 0 T) (ωs n) (stationary f)) atTop (𝓝 0) :=
    EquivRemaining.tendsto_zero_of_limsup_eq_zero h0
  -- the uniform `L²` bound (`lem:bounded-adm`(ii))
  obtain ⟨-, hfin⟩ := boundedAdm_iSup_eq hadm hcont
  have hnorm : ∀ n, ∀ t ∈ Icc 0 T, eLpNorm (ωs n t) 2 volume = eLpNorm (fs n) 2 volume := by
    intro n t ht
    have := boundedAdm_eLpNorm_eq hadm hcont n t (Icc_subset_timeInterval hTT₀ ht) 2
      one_le_two le_rfl
    rwa [ENNReal.ofReal_ofNat] at this
  have hfsB : ∀ n, eLpNorm (fs n) 2 volume ≤ ⨆ m, normL1LpE 2 (fs m) := fun n =>
    (eLpNorm_le_normL1LpE 2 (fs n)).trans (le_iSup (fun m => normL1LpE 2 (fs m)) n)
  -- (2) `sup_t ‖ω⁽ⁿ⁾(t) - f‖_{L²} → 0`, by `lem:RR` along `comap Prod.fst atTop` on `ℕ × [0, T]`
  have hgs : ∀ i : ℕ × Icc 0 T, MemLp (ωs i.1 i.2) 2 volume := fun i => hslice i.1 i.2 i.2.2
  have hL1l : Tendsto (fun i : ℕ × Icc 0 T => eLpNorm (ωs i.1 i.2 - f) 1 volume)
      (comap Prod.fst atTop) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h1.comp tendsto_comap) (fun _ => zero_le) (fun i => ?_)
    exact eLpNorm_le_supDist (ω₁ := ωs i.1) (ω₂ := stationary f) i.2.2
  have hbd : ∀ i : ℕ × Icc 0 T, eLpNorm (ωs i.1 i.2 - f) 2 volume ≤
      (⨆ m, normL1LpE 2 (fs m)) + eLpNorm f 2 volume := by
    intro i
    calc eLpNorm (ωs i.1 i.2 - f) 2 volume
        ≤ eLpNorm (ωs i.1 i.2) 2 volume + eLpNorm f 2 volume :=
          eLpNorm_sub_le (hgs i).1 hf2.1 one_le_two
      _ ≤ (⨆ m, normL1LpE 2 (fs m)) + eLpNorm f 2 volume := by
          rw [hnorm i.1 i.2 i.2.2]; gcongr; exact hfsB i.1
  have hM : (⨆ m, normL1LpE 2 (fs m)) + eLpNorm f 2 volume ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hfin.ne, hf2.eLpNorm_ne_top⟩
  have hw : ∀ ψ : ℂ → ℝ, MemLp ψ 2 volume →
      Tendsto (fun i : ℕ × Icc 0 T => ∫ x, ωs i.1 i.2 x * ψ x) (comap Prod.fst atTop)
        (𝓝 (∫ x, f x * ψ x)) := fun ψ hψ =>
    EquivRemaining.tendsto_integral_mul_of_eLpNorm_one hgs hf2 hL1l hM
      (Eventually.of_forall hbd) hψ
  have hfs2 : Tendsto (fun n => eLpNorm (fs n) 2 volume) atTop (𝓝 (eLpNorm f 2 volume)) := by
    refine EquivRemaining.tendsto_eLpNorm_of_tendsto_eLpNorm_sub one_le_two
      (fun n => (hadm.memLp_one_seq n).1) hf2 ?_
    have := hadm.tendsto
    rw [ENNReal.ofReal_ofNat] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => zero_le)
      (fun n => eLpNorm_le_normL1LpE 2 _)
  have hn : Tendsto (fun i : ℕ × Icc 0 T => eLpNorm (ωs i.1 i.2) 2 volume)
      (comap Prod.fst atTop) (𝓝 (eLpNorm f 2 volume)) := by
    have : (fun i : ℕ × Icc 0 T => eLpNorm (ωs i.1 i.2) 2 volume) =
        fun i => eLpNorm (fs i.1) 2 volume := by
      funext i; exact hnorm i.1 i.2 i.2.2
    rw [this]
    exact hfs2.comp tendsto_comap
  have hL2l := radonRiesz_filter hgs hf2 hw hn
  have h2 : Tendsto (fun n => supDist 2 (Icc 0 T) (ωs n) (stationary f)) atTop (𝓝 0) :=
    EquivRemaining.tendsto_iSup_of_tendsto_comap_fst
      (F := fun n t => eLpNorm (ωs n t - stationary f t) 2 volume) hL2l
  -- (3) `‖g‖_{L^q} ≤ ‖g‖_{L¹} + ‖g‖_{L²}` for `q ∈ (1, 2]`
  have hq1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le
  have hq2' : ENNReal.ofReal q ≤ 2 := by
    rw [← ENNReal.ofReal_ofNat]; exact ENNReal.ofReal_le_ofReal hq2
  have hqlim : Tendsto (fun n => supDist (ENNReal.ofReal q) (Icc 0 T) (ωs n) (stationary f))
      atTop (𝓝 0) := by
    have hsum : Tendsto (fun n => supDist 1 (Icc 0 T) (ωs n) (stationary f) +
        supDist 2 (Icc 0 T) (ωs n) (stationary f)) atTop (𝓝 0) := by
      simpa using h1.add h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
      (fun n => iSup₂_le fun t ht => ?_)
    calc eLpNorm (ωs n t - stationary f t) (ENNReal.ofReal q) volume
        ≤ eLpNorm (ωs n t - stationary f t) 1 volume +
            eLpNorm (ωs n t - stationary f t) 2 volume :=
          LpInterp.eLpNorm_le_eLpNorm_add_eLpNorm ((hslice n t ht).1.sub hf2.1) one_pos hq1' hq2'
      _ ≤ supDist 1 (Icc 0 T) (ωs n) (stationary f) +
            supDist 2 (Icc 0 T) (ωs n) (stationary f) :=
          add_le_add (eLpNorm_le_supDist ht) (eLpNorm_le_supDist ht)
  have hzero : defectLp (ENNReal.ofReal q) T ωs f = 0 := hqlim.limsup_eq
  rw [hzero] at hpos
  exact lt_irrefl _ hpos

/-- **`prop:equiv`** (`03_compactness.tex:1079-1097`): the conditions (a), (b) for some `q`,
(b) for every `q`, (c), (d), (e) are equivalent. -/
theorem equiv_tfae {T₀ : ℝ≥0∞} {T : ℝ} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ}
    {ωs : ℕ → ℝ → ℂ → ℝ} (hrad : IsRadial f) (hadm : IsAdmissibleSeq 2 T₀ f fs ωs)
    (hcont : ∀ n, IsWeakContL2On (timeInterval T₀) (ωs n))
    (hT : 0 < T) (hTT₀ : ENNReal.ofReal T < T₀) :
    List.TFAE [0 < defectLp 1 T ωs f,
      ∃ q : ℝ, 1 < q ∧ q ≤ 2 ∧ 0 < defectLp (ENNReal.ofReal q) T ωs f,
      ∀ q : ℝ, 1 < q → q ≤ 2 → 0 < defectLp (ENNReal.ofReal q) T ωs f,
      NotDistribTendsto T ωs f,
      HasPairingDefect T ωs f,
      HasNonstationaryLimit T₀ T ωs f] := by
  tfae_have 1 → 6 := equiv_a_imp_e hrad hadm hcont hT hTT₀
  tfae_have 6 → 4 := equiv_e_imp_c hrad hadm hcont hT hTT₀
  tfae_have 4 → 5 := equiv_c_imp_d hrad hadm hcont hT hTT₀
  tfae_have 5 → 1 := equiv_d_imp_a hrad hadm hcont hT hTT₀
  tfae_have 5 → 3 := equiv_d_imp_b hrad hadm hcont hT hTT₀
  tfae_have 3 → 2 := fun h => ⟨2, one_lt_two, le_rfl, h 2 one_lt_two le_rfl⟩
  tfae_have 2 → 1 := equiv_b_imp_a hrad hadm hcont hT hTT₀
  tfae_finish

end NonUniqueEuler.Compact
