import NonUniqueEuler.Defs.Sec3.Extra2Criterion
import NonUniqueEuler.I.Sec3.Criterion
import NonUniqueEuler.I.Sec3.Equiv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Proof of `prop:defect` (`I/Sec3/Defect.lean`)

Manuscript: `prop:defect`, `03_compactness.tex:1134-1153`, proof `03_compactness.tex:1155-1177`.

Structure of the proof.
1. `DefectAux.contDiff_defectTest`, `DefectAux.hasCompactSupport_defectTest`: `Ψ ∈ C_c^∞(ℝ²)`
   (`χ` vanishes near `0`, so `x ↦ χ(|x|)` is smooth also at `0`).
2. `DefectAux.integral_mul_defectTest_eq_zero`: `∫ f Ψ = 0` for radial `f` and `m ≥ 1`.
   **Deviation (harmless):** instead of polar coordinates we use the rotation invariance of
   Lebesgue measure: `Ψ(O_θ x) = e^{-imθ} Ψ(x)`, so with `θ = π/m` the change of variables
   `x ↦ O_θ x` and `f ∘ O_θ = f` a.e. give `∫ f Ψ = -∫ f Ψ`. This avoids the a.e. radial
   profile `f₀` of the manuscript.
3. `DefectAux.hasPairingDefect`: `prop:equiv`(d) with `T = T̄` for `ψ = Re Ψ` or `ψ = Im Ψ`.
   **Deviation (harmless):** instead of "one index occurs infinitely often" we use
   `|z| ≤ |Re z| + |Im z|`: if both limsups were `0`, eventually `aₙ + bₙ < c₀`.
4. `defect`: `equiv_d_imp_a` (`T₀ = ∞`) and `criterion` give `ω_∞`; the conclusions are read off
   `IsCriterionLimit` ((i), (ii), (iii) with R8 for `r = q + 1`, (v), (vi) with `Q = O_{2π/3}`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ComplexConjugate

namespace NonUniqueEuler.Compact

open Weak

namespace DefectAux

/-- `x ↦ χ(|x|)` is smooth on `ℂ` when `χ ∈ C_c^∞((0, ∞))`. -/
theorem contDiff_comp_norm {χ : ℝ → ℝ} (hχ : IsRadialTestProfile χ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℂ => χ ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have h0 : (0 : ℝ) ∉ tsupport χ := fun h => lt_irrefl (0 : ℝ) (hχ.tsupport_subset h)
    rw [notMem_tsupport_iff_eventuallyEq] at h0
    have ht : Tendsto (fun x : ℂ => ‖x‖) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0 : ℂ))
    have hev : (fun x : ℂ => χ ‖x‖) =ᶠ[𝓝 0] fun _ => (0 : ℝ) :=
      (ht.eventually h0).mono fun y hy => by simpa using hy
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact hχ.contDiff.contDiffAt.comp x (contDiffAt_norm ℝ hx)

/-- `x ↦ χ(|x|)` has compact support. -/
theorem hasCompactSupport_comp_norm {χ : ℝ → ℝ} (hχ : IsRadialTestProfile χ) :
    HasCompactSupport (fun x : ℂ => χ ‖x‖) := by
  obtain ⟨R, hR⟩ := hχ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) fun x hx => ?_
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have h' := hR h
  simp only [Metric.mem_closedBall, dist_zero_right, norm_norm] at h' hx
  exact hx h'

/-- `Ψ = defectTest χ m` is smooth. -/
theorem contDiff_defectTest {χ : ℝ → ℝ} (hχ : IsRadialTestProfile χ) (m : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (defectTest χ m) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℂ => ((χ ‖x‖ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_comp_norm hχ)
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℂ => (starRingEnd ℂ x) ^ m) :=
    Complex.conjCLE.contDiff.pow m
  exact h1.mul h2

/-- `Ψ = defectTest χ m` has compact support. -/
theorem hasCompactSupport_defectTest {χ : ℝ → ℝ} (hχ : IsRadialTestProfile χ) (m : ℕ) :
    HasCompactSupport (defectTest χ m) := by
  have h : HasCompactSupport (fun x : ℂ => ((χ ‖x‖ : ℝ) : ℂ)) :=
    (hasCompactSupport_comp_norm hχ).comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  exact h.mul_right

theorem continuous_defectTest {χ : ℝ → ℝ} (hχ : IsRadialTestProfile χ) (m : ℕ) :
    Continuous (defectTest χ m) :=
  (contDiff_defectTest hχ m).continuous

/-- `Ψ(O_θ x) = conj(e^{iθ})^m Ψ(x)`. -/
theorem defectTest_rot (χ : ℝ → ℝ) (m : ℕ) (θ : ℝ) (x : ℂ) :
    defectTest χ m (rot θ x) =
      (starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I))) ^ m * defectTest χ m x := by
  unfold defectTest
  rw [Polar.norm_rot, rot, map_mul, mul_pow]
  ring

/-- `conj(e^{iπ/m})^m = -1` for `m ≥ 1`. -/
theorem conj_exp_pow_eq_neg_one {m : ℕ} (hm : 1 ≤ m) :
    (starRingEnd ℂ (Complex.exp (((Real.pi / m : ℝ) : ℂ) * Complex.I))) ^ m = -1 := by
  rw [← map_pow, ← Complex.exp_nat_mul]
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have : (m : ℂ) * (((Real.pi / m : ℝ) : ℂ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [this, Complex.exp_pi_mul_I]
  simp

/-- `∫ f Ψ = 0` for radial `f` and `m ≥ 1` (`03_compactness.tex:1156-1159`), by rotation
invariance with `θ = π/m`. -/
theorem integral_mul_defectTest_eq_zero {f : ℂ → ℝ} (hrad : IsRadial f) (χ : ℝ → ℝ) {m : ℕ}
    (hm : 1 ≤ m) : ∫ x, (f x : ℂ) * defectTest χ m x = 0 := by
  have hmp := Polar.measurePreserving_rot (Real.pi / m)
  have hemb : MeasurableEmbedding (rot (Real.pi / m)) := by
    rw [Polar.rot_eq_rotation]
    exact (rotation (Circle.exp (Real.pi / m))).toHomeomorph.measurableEmbedding
  have h1 : ∫ x, (f (rot (Real.pi / m) x) : ℂ) * defectTest χ m (rot (Real.pi / m) x) =
      ∫ x, (f x : ℂ) * defectTest χ m x :=
    hmp.integral_comp hemb (fun x => (f x : ℂ) * defectTest χ m x)
  have h2 : ∫ x, (f (rot (Real.pi / m) x) : ℂ) * defectTest χ m (rot (Real.pi / m) x) =
      -∫ x, (f x : ℂ) * defectTest χ m x := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hrad (Real.pi / m)] with x hx
    rw [hx, defectTest_rot, conj_exp_pow_eq_neg_one hm]
    ring
  have h3 := h1.symm.trans h2
  linear_combination h3 / 2

/-- For locally integrable real `g`, `g Ψ` is integrable. -/
theorem integrable_mul_defectTest {g : ℂ → ℝ} (hg : LocallyIntegrable g volume) {χ : ℝ → ℝ}
    (hχ : IsRadialTestProfile χ) (m : ℕ) :
    Integrable (fun x => (g x : ℂ) * defectTest χ m x) := by
  have := hg.integrable_smul_right_of_hasCompactSupport (continuous_defectTest hχ m)
    (hasCompactSupport_defectTest hχ m)
  simpa only [Complex.real_smul] using this

/-- `Re ∫ g Ψ = ∫ g Re Ψ` for real `g`. -/
theorem re_integral_mul {g : ℂ → ℝ} {Ψ : ℂ → ℂ} (hG : Integrable (fun x => (g x : ℂ) * Ψ x)) :
    (∫ x, (g x : ℂ) * Ψ x).re = ∫ x, g x * (Ψ x).re := by
  have := integral_re hG
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at this
  exact this.symm

/-- `Im ∫ g Ψ = ∫ g Im Ψ` for real `g`. -/
theorem im_integral_mul {g : ℂ → ℝ} {Ψ : ℂ → ℂ} (hG : Integrable (fun x => (g x : ℂ) * Ψ x)) :
    (∫ x, (g x : ℂ) * Ψ x).im = ∫ x, g x * (Ψ x).im := by
  have := integral_im hG
  simp only [RCLike.im_to_complex, Complex.im_ofReal_mul] at this
  exact this.symm

/-- The pointwise estimate: for `g = ω⁽ⁿ⁾(t) - f` (locally integrable) and `‖∫ ω⁽ⁿ⁾(t) Ψ‖ ≥ c₀`,
`c₀ ≤ ‖∫ g Re Ψ‖ₑ + ‖∫ g Im Ψ‖ₑ`. -/
theorem ofReal_le_enorm_add_enorm {f w : ℂ → ℝ} (hrad : IsRadial f) {χ : ℝ → ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hχ : IsRadialTestProfile χ) (hf : LocallyIntegrable f volume)
    (hw : LocallyIntegrable w volume) {c₀ : ℝ}
    (hlow : c₀ ≤ ‖∫ x, (w x : ℂ) * defectTest χ m x‖) :
    ENNReal.ofReal c₀ ≤ ‖∫ x, (w x - f x) * (defectTest χ m x).re‖ₑ +
      ‖∫ x, (w x - f x) * (defectTest χ m x).im‖ₑ := by
  have hg : LocallyIntegrable (fun x => w x - f x) volume := hw.sub hf
  have hG := integrable_mul_defectTest hg hχ m
  have hW := integrable_mul_defectTest hw hχ m
  have hF := integrable_mul_defectTest hf hχ m
  have hsplit : ∫ x, (w x : ℂ) * defectTest χ m x =
      ∫ x, ((w x - f x : ℝ) : ℂ) * defectTest χ m x := by
    have : (fun x => ((w x - f x : ℝ) : ℂ) * defectTest χ m x) =
        fun x => (w x : ℂ) * defectTest χ m x - (f x : ℂ) * defectTest χ m x := by
      funext x
      push_cast
      ring
    rw [this, integral_sub hW hF, integral_mul_defectTest_eq_zero hrad χ hm, sub_zero]
  rw [hsplit] at hlow
  have hle := hlow.trans (Complex.norm_le_abs_re_add_abs_im _)
  rw [re_integral_mul hG, im_integral_mul hG] at hle
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hle

/-- `prop:equiv`(d) for `T = T̄`, with `ψ = Re Ψ` or `ψ = Im Ψ` (`03_compactness.tex:1159-1167`). -/
theorem hasPairingDefect {f : ℂ → ℝ} {m : ℕ} {χ : ℝ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}
    {c₀ Tbar : ℝ} {Tn : ℕ → ℝ} (hf1 : MemLp f 1 volume) (hrad : IsRadial f) (hm : 1 ≤ m)
    (hχ : IsRadialTestProfile χ) (hcont : ∀ n, IsWeakContL2On (Ici 0) (ωs n)) (hc₀ : 0 < c₀)
    (hlow : ∀ᶠ n in atTop, Tn n ∈ Icc 0 Tbar ∧
      c₀ ≤ ‖∫ x, (ωs n (Tn n) x : ℂ) * defectTest χ m x‖) :
    HasPairingDefect Tbar ωs f := by
  set a : ℕ → ℝ≥0∞ := fun n =>
    ⨆ t ∈ Icc 0 Tbar, ‖∫ x, (ωs n t x - f x) * (defectTest χ m x).re‖ₑ with ha_def
  set b : ℕ → ℝ≥0∞ := fun n =>
    ⨆ t ∈ Icc 0 Tbar, ‖∫ x, (ωs n t x - f x) * (defectTest χ m x).im‖ₑ with hb_def
  have hfl : LocallyIntegrable f volume := (memLp_one_iff_integrable.1 hf1).locallyIntegrable
  have hev : ∀ᶠ n in atTop, ENNReal.ofReal c₀ ≤ (a + b) n := by
    filter_upwards [hlow] with n hn
    obtain ⟨hTn, hlown⟩ := hn
    have hw : LocallyIntegrable (ωs n (Tn n)) volume :=
      ((hcont n).memLp (Tn n) hTn.1).locallyIntegrable (by norm_num)
    refine (ofReal_le_enorm_add_enorm hrad hm hχ hfl hw hlown).trans ?_
    refine add_le_add ?_ ?_
    · exact le_iSup₂ (f := fun t (_ : t ∈ Icc 0 Tbar) =>
        ‖∫ x, (ωs n t x - f x) * (defectTest χ m x).re‖ₑ) (Tn n) hTn
    · exact le_iSup₂ (f := fun t (_ : t ∈ Icc 0 Tbar) =>
        ‖∫ x, (ωs n t x - f x) * (defectTest χ m x).im‖ₑ) (Tn n) hTn
  have hc : 0 < ENNReal.ofReal c₀ := ENNReal.ofReal_pos.2 hc₀
  have hc2 : 0 < ENNReal.ofReal c₀ / 2 := ENNReal.half_pos hc.ne'
  have hΨ := contDiff_defectTest hχ m
  have hΨs := hasCompactSupport_defectTest hχ m
  by_cases ha : 0 < limsup a atTop
  · exact ⟨fun x => (defectTest χ m x).re, Complex.reCLM.contDiff.comp hΨ,
      hΨs.comp_left Complex.zero_re, ha⟩
  · refine ⟨fun x => (defectTest χ m x).im, Complex.imCLM.contDiff.comp hΨ,
      hΨs.comp_left Complex.zero_im, ?_⟩
    show 0 < limsup b atTop
    by_contra hb
    have ha0 : limsup a atTop < ENNReal.ofReal c₀ / 2 := (not_lt.1 ha).trans_lt hc2
    have hb0 : limsup b atTop < ENNReal.ofReal c₀ / 2 := (not_lt.1 hb).trans_lt hc2
    obtain ⟨n, han, hbn, hn⟩ :=
      ((eventually_lt_of_limsup_lt ha0).and ((eventually_lt_of_limsup_lt hb0).and hev)).exists
    have hlt : a n + b n < ENNReal.ofReal c₀ :=
      calc a n + b n < ENNReal.ofReal c₀ / 2 + ENNReal.ofReal c₀ / 2 := ENNReal.add_lt_add han hbn
        _ = ENNReal.ofReal c₀ := ENNReal.add_halves _
    exact absurd hn (not_le.2 hlt)

end DefectAux

/-- **`prop:defect`** (`03_compactness.tex:1134-1153`), with the extra conjunct "renormalized in
every `X_q(T)`" from `thm:criterion`(ii). -/
theorem defect {f : ℂ → ℝ} {m : ℕ} {χ : ℝ → ℝ} {fs : ℕ → ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}
    {c₀ Tbar : ℝ} {Tn : ℕ → ℝ}
    (hf : ∀ q : ℝ, 1 ≤ q → MemLp f (ENNReal.ofReal q) volume) (hrad : IsRadial f)
    (hm : 1 ≤ m) (hχ : IsRadialTestProfile χ)
    (hadm : IsAdmissibleSeq 2 ⊤ f fs ωs)
    (hcont : ∀ n, IsWeakContL2On (Ici 0) (ωs n))
    (hsym : ∀ n, ∀ t : ℝ, 0 ≤ t → IsMFoldSymmetric 3 (ωs n t))
    (hc₀ : 0 < c₀) (hTbar : 0 < Tbar)
    (hlow : ∀ᶠ n in atTop, Tn n ∈ Icc 0 Tbar ∧
      c₀ ≤ ‖∫ x, (ωs n (Tn n) x : ℂ) * defectTest χ m x‖) :
    ∃ ωinf : ℝ → ℂ → ℝ,
      IsRenormalizedWeakSolutionOnHalfLine 2 f ωinf ∧
      (∀ t : ℝ, 0 ≤ t → Equimeasurable (ωinf t) f ∧ IsMFoldSymmetric 3 (ωinf t)) ∧
      (∀ q : ℝ, 1 ≤ q → ContinuousIntoLp (ENNReal.ofReal q) ωinf) ∧
      (∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < Tbar ∧
        ∀ T' : ℝ, t₀ < T' → DistinctInX T' ωinf (stationary f)) ∧
      (∀ T : ℝ, 0 < T → ∀ q : ℝ, 4 / 3 < q → IsRenormalizedWeakSolution q T f ωinf) := by
  have hcont' : ∀ n, IsWeakContL2On (timeInterval ⊤) (ωs n) := by
    simpa only [timeInterval_top] using hcont
  have hTT : ENNReal.ofReal Tbar < ⊤ := ENNReal.ofReal_lt_top
  have hd : HasPairingDefect Tbar ωs f :=
    DefectAux.hasPairingDefect hadm.memLp_one hrad hm hχ hcont hc₀ hlow
  have ha := equiv_d_imp_a hrad hadm hcont' hTbar hTT hd
  obtain ⟨φ, ωinf, h⟩ := criterion hrad hadm hcont' hTbar hTT ha
  refine ⟨ωinf, ?_, ?_, ?_, ?_, ?_⟩
  · exact isRenormalizedWeakSolutionUpTo_top_iff.1 h.renormalized
  · intro t ht
    have ht' : t ∈ timeInterval ⊤ := by simpa using ht
    refine ⟨h.equimeasurable t ht', ?_⟩
    rw [isMFoldSymmetric_iff_isSymmetricUnder]
    exact h.symmetric _ 1 (Or.inl rfl)
      (fun n s hs => (isMFoldSymmetric_iff_isSymmetricUnder 3 _).1 (hsym n s hs.1)) t ht'
  · intro q hq
    rw [continuousIntoLp_iff_continuousIntoLpOn, ← timeInterval_top]
    rcases le_or_gt q 2 with hq2 | hq2
    · exact h.continuousIntoLp_le_two q hq hq2
    · exact h.continuousIntoLp_gt_two q (q + 1) hq2 (lt_add_one q) (hf (q + 1) (by linarith))
  · exact ⟨departureTime ⊤ ωinf f, departureTime_nonneg _ _ _, h.departureTime_lt,
      fun T' hT' => h.distinct T' hT' ENNReal.ofReal_lt_top⟩
  · intro T hT q hq
    exact h.renormalized_q T hT ENNReal.ofReal_lt_top q hq (hf q (by linarith))

end NonUniqueEuler.Compact
