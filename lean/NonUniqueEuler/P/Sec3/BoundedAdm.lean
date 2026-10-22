import NonUniqueEuler.Defs.Sec3.Criterion
import NonUniqueEuler.I.Sec3.L2Renorm
import NonUniqueEuler.I.Sec3.RenormAllT
import NonUniqueEuler.I.Infra.LpInterp.Interp

/-!
# Proof: `lem:bounded-adm`, bounded solutions are admissible; conservation of norms

Proof of `I/Sec3/BoundedAdm.lean` (same declarations, statements copied verbatim).

Manuscript: `lem:bounded-adm`, `03_compactness.tex:888-904` (statement), proof
`03_compactness.tex:906-931`.

Structure.
* (i) `BoundedAdmAux.memLinfLp_of_one_top`: `L^∞(I; L¹) ∩ L^∞(I; L^∞) ⊆ L^∞(I; L^p)` for
  `p ∈ [1, ∞]` (I-LPINT, `‖g‖_p ≤ ‖g‖₁ + ‖g‖_∞`). The Lean `MemX` asks for joint measurability on
  the slab, which `MemLinfLp` already provides, so the manuscript's Pettis/truncation argument for
  strong measurability into `L¹ ∩ L^q` is not needed. `BoundedAdmAux.isWeakSolution_of_exponent`:
  the fields `velocity_convergent` and `weak` of `IsWeakSolution` do not involve the exponent.
  Then `cor:L2-renorm` (`IsWeakSolution.isRenormalized_of_memLinfLp_two`).
* For the sequence: `f ∈ L¹ ∩ L^q` from `f = f⁽ᴺ⁾ - (f⁽ᴺ⁾ - f)` with `N` such that
  `‖f⁽ᴺ⁾ - f‖_{L¹∩L^q} < ∞`.
* (ii) For `t ∈ [0, T₀)` choose `T ∈ (t, T₀)` (`BoundedAdmAux.exists_gt_lt`) and apply
  `lem:renorm-all-t` (`Weak.renormAllT_eLpNorm_eq`) on `[0, T]`. Finiteness of the supremum:
  `‖f⁽ⁿ⁾‖ ≤ ‖f⁽ⁿ⁾ - f‖ + ‖f‖` is eventually `≤ ‖f‖ + 1`, and every term is finite
  (`BoundedAdmAux.iSup_lt_top_of_eventually_le`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact

open Weak

namespace BoundedAdmAux

/-- `L^∞(I; L¹) ∩ L^∞(I; L^∞) ⊆ L^∞(I; L^p)` for `1 ≤ p` (interpolation,
`03_compactness.tex:908-911`). -/
theorem memLinfLp_of_one_top {I : Set ℝ} {Ω : Set ℂ} {u : ℝ → ℂ → ℝ} {p : ℝ≥0∞}
    (h1 : Prelim.MemLinfLp I Ω 1 u) (hinf : Prelim.MemLinfLp I Ω ⊤ u) (hp : 1 ≤ p) :
    Prelim.MemLinfLp I Ω p u := by
  obtain ⟨M₁, hM₁⟩ := h1.essBounded
  obtain ⟨M₂, hM₂⟩ := hinf.essBounded
  refine ⟨h1.aestronglyMeasurable, M₁ + M₂, (hM₁.and hM₂).mono fun t ht => ?_⟩
  obtain ⟨⟨ht1, hb1⟩, ⟨ht2, hb2⟩⟩ := ht
  have hmem : MemLp (u t) p (volume.restrict Ω) :=
    LpInterp.memLp_of_memLp_of_memLp zero_lt_one hp le_top ht1 ht2
  refine ⟨hmem, ?_⟩
  have hle := LpInterp.eLpNorm_le_eLpNorm_add_eLpNorm ht1.1 zero_lt_one hp (le_top : p ≤ ⊤)
  calc (eLpNorm (u t) p (volume.restrict Ω)).toReal
      ≤ (eLpNorm (u t) 1 (volume.restrict Ω) + eLpNorm (u t) ⊤ (volume.restrict Ω)).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ht1.eLpNorm_ne_top, ht2.eLpNorm_ne_top⟩) hle
    _ = (eLpNorm (u t) 1 (volume.restrict Ω)).toReal +
          (eLpNorm (u t) ⊤ (volume.restrict Ω)).toReal :=
        ENNReal.toReal_add ht1.eLpNorm_ne_top ht2.eLpNorm_ne_top
    _ ≤ M₁ + M₂ := add_le_add hb1 hb2

/-- The weak formulation and the convergence of the Biot–Savart integral do not involve the
exponent (`03_compactness.tex:919-920`): a weak solution with exponent `q₀` that lies in
`X_q(T)`, with datum in `L^q`, is a weak solution with exponent `q`. -/
theorem isWeakSolution_of_exponent {q₀ q T : ℝ} {g : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsWeakSolution q₀ T g ω) (hq : 4 / 3 < q) (hgq : MemLp g (ENNReal.ofReal q) volume)
    (hX : MemX q T ω) : IsWeakSolution q T g ω where
  q_gt := hq
  T_pos := h.T_pos
  datum_memLp_one := h.datum_memLp_one
  datum_memLp_q := hgq
  memX := hX
  velocity_convergent := h.velocity_convergent
  weak := h.weak

/-- For `t ∈ [0, T₀)` there is a real `T` with `t < T < T₀`. -/
theorem exists_gt_lt {T₀ : ℝ≥0∞} {t : ℝ} (ht : t ∈ timeInterval T₀) :
    ∃ T : ℝ, t < T ∧ ENNReal.ofReal T < T₀ := by
  obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 ht.2
  exact ⟨r, (ENNReal.ofReal_lt_ofReal_iff'.1 hr1).1, hr2⟩

/-- A sequence in `[0, ∞)` (all terms finite) that is eventually bounded by a finite constant has
a finite supremum. -/
theorem iSup_lt_top_of_eventually_le {u : ℕ → ℝ≥0∞} (hu : ∀ n, u n < ⊤) {C : ℝ≥0∞}
    (hC : C < ⊤) (hev : ∀ᶠ n in atTop, u n ≤ C) : (⨆ n, u n) < ⊤ := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hle : (⨆ n, u n) ≤ (∑ n ∈ Finset.range N, u n) + C := by
    refine iSup_le fun n => ?_
    rcases lt_or_ge n N with h | h
    · exact le_add_right (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_range.2 h))
    · exact le_add_left (hN n h)
  exact lt_of_le_of_lt hle (ENNReal.add_lt_top.2 ⟨ENNReal.sum_lt_top.2 fun n _ => hu n, hC⟩)

/-- The triangle inequality for `‖·‖_{L¹ ∩ L^p}`, `1 ≤ p`, in the form
`‖g‖ ≤ ‖g - f‖ + ‖f‖`. -/
theorem normL1LpE_le_sub_add {p : ℝ≥0∞} (hp : 1 ≤ p) {g f : ℂ → ℝ}
    (hg : AEStronglyMeasurable g volume) (hf : AEStronglyMeasurable f volume) :
    normL1LpE p g ≤ normL1LpE p (g - f) + normL1LpE p f := by
  have hgf : AEStronglyMeasurable (g - f) volume := hg.sub hf
  have key : ∀ r : ℝ≥0∞, 1 ≤ r →
      eLpNorm g r volume ≤ eLpNorm (g - f) r volume + eLpNorm f r volume := by
    intro r hr
    calc eLpNorm g r volume = eLpNorm ((g - f) + f) r volume := by rw [sub_add_cancel]
      _ ≤ eLpNorm (g - f) r volume + eLpNorm f r volume := eLpNorm_add_le hgf hf hr
  unfold normL1LpE
  calc eLpNorm g 1 volume + eLpNorm g p volume
      ≤ (eLpNorm (g - f) 1 volume + eLpNorm f 1 volume) +
          (eLpNorm (g - f) p volume + eLpNorm f p volume) :=
        add_le_add (key 1 le_rfl) (key p hp)
    _ = (eLpNorm (g - f) 1 volume + eLpNorm (g - f) p volume) +
          (eLpNorm f 1 volume + eLpNorm f p volume) := add_add_add_comm _ _ _ _

end BoundedAdmAux

open BoundedAdmAux

set_option linter.unusedVariables false in
/-- **`lem:bounded-adm`(i)**, one solution (`03_compactness.tex:891-896`): a weak solution on
`[0, T₀)` (exponent `q₀ ∈ (4/3, ∞)`) with datum `g ∈ L¹ ∩ L^∞` that lies in
`L^∞(0, T; L¹ ∩ L^∞)` for every `T < T₀` is a renormalized weak solution in `X_q(T)` for every
`q ∈ (4/3, ∞)` and every `T < T₀`. -/
theorem boundedAdm_renormalized {T₀ : ℝ≥0∞} {q₀ : ℝ} {g : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (hT₀ : 0 < T₀) (hg1 : MemLp g 1 volume) (hginf : MemLp g ⊤ volume) (hq₀ : 4 / 3 < q₀)
    (hω : IsWeakSolutionUpTo q₀ T₀ g ω)
    (hbd : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ →
      Prelim.MemLinfLp (Ioo 0 T) univ 1 ω ∧ Prelim.MemLinfLp (Ioo 0 T) univ ⊤ ω) :
    ∀ q : ℝ, 4 / 3 < q → IsRenormalizedWeakSolutionUpTo q T₀ g ω := by
  intro q hq T hT hTT₀
  obtain ⟨h1, hinf⟩ := hbd T hT hTT₀
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 (by linarith)
  have hgq : MemLp g (ENNReal.ofReal q) volume :=
    LpInterp.memLp_of_memLp_of_memLp zero_lt_one hq1 le_top hg1 hginf
  have hX : MemX q T ω := Prelim.memX_iff.2 ⟨h1, memLinfLp_of_one_top h1 hinf hq1⟩
  have hw : IsWeakSolution q T g ω := isWeakSolution_of_exponent (hω T hT hTT₀) hq hgq hX
  have h2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 ω := memLinfLp_of_one_top h1 hinf one_le_two
  exact hw.isRenormalized_of_memLinfLp_two h2

/-- **`lem:bounded-adm`(i)**, the sequence (`03_compactness.tex:896-898`): under the hypotheses of
`boundedAdm_renormalized` for every `n`, if `q ∈ (4/3, ∞)` and `f⁽ⁿ⁾ → f` in `L¹ ∩ L^q`, then
`(f⁽ⁿ⁾, ω⁽ⁿ⁾)` is `q`-admissible for `f` on `[0, T₀)`. -/
theorem boundedAdm_admissible {T₀ : ℝ≥0∞} {q₀ q : ℝ} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ}
    {ωs : ℕ → ℝ → ℂ → ℝ} (hT₀ : 0 < T₀) (hfs1 : ∀ n, MemLp (fs n) 1 volume)
    (hfsinf : ∀ n, MemLp (fs n) ⊤ volume) (hq₀ : 4 / 3 < q₀)
    (hωs : ∀ n, IsWeakSolutionUpTo q₀ T₀ (fs n) (ωs n))
    (hbd : ∀ n, ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ →
      Prelim.MemLinfLp (Ioo 0 T) univ 1 (ωs n) ∧ Prelim.MemLinfLp (Ioo 0 T) univ ⊤ (ωs n))
    (hq : 4 / 3 < q) (hf : AEStronglyMeasurable f volume)
    (hconv : Tendsto (fun n => normL1LpE (ENNReal.ofReal q) (fs n - f)) atTop (𝓝 0)) :
    IsAdmissibleSeq q T₀ f fs ωs := by
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 (by linarith)
  have hfsq : ∀ n, MemLp (fs n) (ENNReal.ofReal q) volume := fun n =>
    LpInterp.memLp_of_memLp_of_memLp zero_lt_one hq1 le_top (hfs1 n) (hfsinf n)
  obtain ⟨N, hN⟩ := (hconv.eventually_lt_const ENNReal.zero_lt_top).exists
  have hm : AEStronglyMeasurable (fs N - f) volume := (hfs1 N).1.sub hf
  have hd1 : MemLp (fs N - f) 1 volume :=
    ⟨hm, lt_of_le_of_lt (eLpNorm_one_le_normL1LpE _ _) hN⟩
  have hdq : MemLp (fs N - f) (ENNReal.ofReal q) volume :=
    ⟨hm, lt_of_le_of_lt (eLpNorm_le_normL1LpE _ _) hN⟩
  have hf1 : MemLp f 1 volume := by
    have := (hfs1 N).sub hd1
    rwa [sub_sub_cancel] at this
  have hfq : MemLp f (ENNReal.ofReal q) volume := by
    have := (hfsq N).sub hdq
    rwa [sub_sub_cancel] at this
  exact
    { q_gt := hq
      T₀_pos := hT₀
      memLp_one := hf1
      memLp_q := hfq
      memLp_one_seq := hfs1
      memLp_q_seq := hfsq
      tendsto := hconv
      renormalized := fun n =>
        boundedAdm_renormalized hT₀ (hfs1 n) (hfsinf n) hq₀ (hωs n) (hbd n) q hq }

/-- **`lem:bounded-adm`(ii)**, conservation of norms (`03_compactness.tex:899-901`): for a
`2`-admissible sequence (identified with weakly continuous representatives on `[0, T₀)`),
`‖ω⁽ⁿ⁾(t)‖_{L^r} = ‖f⁽ⁿ⁾‖_{L^r}` for every `n`, `t ∈ [0, T₀)` and `r ∈ [1, 2]`. -/
theorem boundedAdm_eLpNorm_eq {T₀ : ℝ≥0∞} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}
    (hadm : IsAdmissibleSeq 2 T₀ f fs ωs)
    (hcont : ∀ n, IsWeakContL2On (timeInterval T₀) (ωs n)) :
    ∀ n, ∀ t ∈ timeInterval T₀, ∀ r : ℝ, 1 ≤ r → r ≤ 2 →
      eLpNorm (ωs n t) (ENNReal.ofReal r) volume = eLpNorm (fs n) (ENNReal.ofReal r) volume := by
  intro n t ht r hr1 hr2
  obtain ⟨T, htT, hT⟩ := exists_gt_lt ht
  have hT0 : 0 < T := lt_of_le_of_lt ht.1 htT
  have hren := hadm.renormalized n T hT0 hT
  have hc := (hcont n).mono (Icc_subset_timeInterval hT)
  exact renormAllT_eLpNorm_eq hren hc t ⟨ht.1, htT⟩ r hr1 hr2

/-- **`lem:bounded-adm`(ii)**, the uniform bound (`03_compactness.tex:901-903`): for a
`2`-admissible sequence, `sup_n sup_{t<T₀} ‖ω⁽ⁿ⁾(t)‖_{L¹∩L²} = sup_n ‖f⁽ⁿ⁾‖_{L¹∩L²} < ∞`. -/
theorem boundedAdm_iSup_eq {T₀ : ℝ≥0∞} {f : ℂ → ℝ} {fs : ℕ → ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}
    (hadm : IsAdmissibleSeq 2 T₀ f fs ωs)
    (hcont : ∀ n, IsWeakContL2On (timeInterval T₀) (ωs n)) :
    (⨆ n, ⨆ t ∈ timeInterval T₀, normL1LpE 2 (ωs n t)) = (⨆ n, normL1LpE 2 (fs n)) ∧
      (⨆ n, normL1LpE 2 (fs n)) < ⊤ := by
  have heq := boundedAdm_eLpNorm_eq hadm hcont
  have hpt : ∀ n, ∀ t ∈ timeInterval T₀, normL1LpE 2 (ωs n t) = normL1LpE 2 (fs n) := by
    intro n t ht
    have e1 := heq n t ht 1 le_rfl one_le_two
    have e2 := heq n t ht 2 one_le_two le_rfl
    rw [ENNReal.ofReal_one] at e1
    rw [ENNReal.ofReal_ofNat] at e2
    unfold normL1LpE
    rw [e1, e2]
  have hne : (timeInterval T₀).Nonempty := ⟨0, zero_mem_timeInterval hadm.T₀_pos⟩
  have hin : ∀ n, (⨆ t ∈ timeInterval T₀, normL1LpE 2 (ωs n t)) = normL1LpE 2 (fs n) := by
    intro n
    calc (⨆ t ∈ timeInterval T₀, normL1LpE 2 (ωs n t))
        = ⨆ t ∈ timeInterval T₀, normL1LpE 2 (fs n) :=
          iSup_congr fun t => iSup_congr fun ht => hpt n t ht
      _ = normL1LpE 2 (fs n) := biSup_const hne
  refine ⟨iSup_congr hin, ?_⟩
  -- finiteness: every term is finite and eventually `‖f⁽ⁿ⁾‖ ≤ ‖f⁽ⁿ⁾ - f‖ + ‖f‖ ≤ 1 + ‖f‖`
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := ENNReal.ofReal_ofNat 2
  have hf1 := hadm.memLp_one
  have hf2 : MemLp f 2 volume := by simpa [h2] using hadm.memLp_q
  have hfs2 : ∀ n, MemLp (fs n) 2 volume := fun n => by simpa [h2] using hadm.memLp_q_seq n
  have hconv : Tendsto (fun n => normL1LpE 2 (fs n - f)) atTop (𝓝 0) := by
    simpa [h2] using hadm.tendsto
  have hfin : ∀ n, normL1LpE 2 (fs n) < ⊤ := fun n =>
    ENNReal.add_lt_top.2 ⟨(hadm.memLp_one_seq n).eLpNorm_lt_top, (hfs2 n).eLpNorm_lt_top⟩
  have hfF : normL1LpE 2 f < ⊤ := ENNReal.add_lt_top.2 ⟨hf1.eLpNorm_lt_top, hf2.eLpNorm_lt_top⟩
  refine iSup_lt_top_of_eventually_le hfin (C := 1 + normL1LpE 2 f)
    (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hfF⟩) ?_
  filter_upwards [hconv.eventually_lt_const zero_lt_one] with n hn
  calc normL1LpE 2 (fs n) ≤ normL1LpE 2 (fs n - f) + normL1LpE 2 f :=
        normL1LpE_le_sub_add one_le_two (hadm.memLp_one_seq n).1 hf1.1
    _ ≤ 1 + normL1LpE 2 f := add_le_add_left hn.le _

end NonUniqueEuler.Compact
