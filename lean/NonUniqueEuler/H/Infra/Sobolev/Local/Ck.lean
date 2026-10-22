import NonUniqueEuler.H.Infra.Sobolev.Local.Basic
import NonUniqueEuler.I.Infra.Sobolev.Smooth

/-!
# Helper for `P/Infra/Sobolev/Local`: `C^k(U)` controls `H^k(V)` and `W^{1,∞}(V)`

For `V ⊆ U` open, `h ∈ C^s(U)`:
* `LocalAux.memCk_memHOn`: `‖h‖_{H^s(V)} ≤ (s+1) |V|^{1/2} ‖h‖_{C^s(U)}` when `|V| < ∞`;
* `LocalAux.memCk_memW1infOn`: `‖h‖_{W^{1,∞}(V)} ≤ 3 ‖h‖_{C^1(U)}`.

Proof: the classical derivatives are weak derivatives (`memHOn_of_contDiffOn`,
`hasWeakDerivOn_of_contDiffOn`), bounded by the `C^s(U)` norm (`norm_partialD_le_normCk`);
`‖g‖_{L²(V)} ≤ |V|^{1/2} sup_V |g|` (`eLpNorm_le_of_ae_bound`); `#multiIdx s ≤ (s+1)²`;
`|∇h| = (|∂₁h|² + |∂₂h|²)^{1/2} ≤ 2 ‖h‖_{C^1(U)}`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob.LocalAux

/-- Classical derivatives of a `C^n` function on an open set are `C^m` there, `m + |ws| ≤ n`.
(The same argument as `WeakDerivAux.contDiffOn_iterDirDeriv` in
`P/Infra/Sobolev/WeakDeriv.lean`.) -/
theorem contDiffOn_iterDirDeriv {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℂ} {n : ℕ}
    (hf : ContDiffOn ℝ n f V) (ws : List ℂ) :
    ∀ m : ℕ, m + ws.length ≤ n → ContDiffOn ℝ m (iterDirDeriv ws f) V := by
  induction ws with
  | nil =>
    intro m hm
    exact hf.of_le (by exact_mod_cast (by simpa using hm))
  | cons w ws ih =>
    intro m hm
    have h1 := ih (m + 1) (by simp only [List.length_cons] at hm; omega)
    have h2 := h1.fderiv_of_isOpen hV (m := m) (by push_cast; exact le_rfl)
    exact h2.clm_apply contDiffOn_const

theorem continuousOn_partialD {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℂ} {n : ℕ}
    (hf : ContDiffOn ℝ n f V) {γ : ℕ × ℕ} (hγ : γ.1 + γ.2 ≤ n) :
    ContinuousOn (partialD γ f) V :=
  (contDiffOn_iterDirDeriv hV hf (pdList γ) 0 (by simpa using hγ)).continuousOn

/-- `‖F‖_{L²(V)} ≤ |V|^{1/2} M` for `F` continuous on `V`, `|F| ≤ M` on `V`. -/
theorem l2On_le_of_bound {V : Set ℂ} (hV : MeasurableSet V) (hfin : volume V < ⊤) {F : ℂ → ℂ}
    (hF : ContinuousOn F V) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x ∈ V, ‖F x‖ ≤ M) :
    MemLp F 2 (volume.restrict V) ∧ l2On V F ≤ Real.sqrt (volume V).toReal * M := by
  have : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.2 hfin.ne
  have hae : ∀ᵐ x ∂(volume.restrict V), ‖F x‖ ≤ M := ae_restrict_of_forall_mem hV hb
  refine ⟨MemLp.of_bound (hF.aestronglyMeasurable hV) M hae, ?_⟩
  have h1 := eLpNorm_le_of_ae_bound (p := 2) hae
  rw [Measure.restrict_apply_univ] at h1
  have hfin' : volume V ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal M ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hfin.ne)
      ENNReal.ofReal_ne_top
  have h2 := ENNReal.toReal_mono hfin' h1
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hM] at h2
  unfold l2On
  refine h2.trans (le_of_eq ?_)
  rw [Real.sqrt_eq_rpow]
  norm_num

/-- `C^s(U)` controls `H^s(V)` for `V ⊆ U` open of finite measure. -/
theorem memCk_memHOn {s : ℕ} {U V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U)
    (hVfin : volume V < ⊤) {h : ℂ → ℂ} (hh : MemCk s U h) :
    MemHOn s V h ∧ normHOn s V h ≤ (s + 1) * Real.sqrt (volume V).toReal * normCk s U h := by
  obtain ⟨W, -, hUW, hcd⟩ := hh.near
  have hcdV : ContDiffOn ℝ s h V := hcd.mono (hVU.trans hUW)
  have hM : 0 ≤ normCk s U h := normCk_nonneg _ _ _
  have hbd : ∀ γ ∈ multiIdx s, MemLp (partialD γ h) 2 (volume.restrict V) ∧
      l2On V (partialD γ h) ≤ Real.sqrt (volume V).toReal * normCk s U h := by
    intro γ hγ
    have hγ' := mem_multiIdx.1 hγ
    exact l2On_le_of_bound hV.measurableSet hVfin (continuousOn_partialD hV hcdV hγ') hM
      (fun x hx => norm_partialD_le_normCk hh hγ' (hVU hx))
  obtain ⟨hmem, -⟩ := memHOn_of_contDiffOn hV hcdV (fun γ hγ => (hbd γ hγ).1)
  refine ⟨hmem, ?_⟩
  rw [normHOn_eq_of_contDiffOn hV hcdV (fun γ hγ => (hbd γ hγ).1)]
  set a := Real.sqrt (volume V).toReal * normCk s U h with ha_def
  have ha : 0 ≤ a := mul_nonneg (Real.sqrt_nonneg _) hM
  have hsum : ∑ γ ∈ multiIdx s, l2On V (partialD γ h) ^ 2 ≤ ((s + 1) * a) ^ 2 := by
    calc ∑ γ ∈ multiIdx s, l2On V (partialD γ h) ^ 2 ≤ ∑ γ ∈ multiIdx s, a ^ 2 :=
          Finset.sum_le_sum fun γ hγ => pow_le_pow_left₀ (l2On_nonneg _ _) (hbd γ hγ).2 2
      _ = (multiIdx s).card * a ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (s + 1) ^ 2 * a ^ 2 := by gcongr; exact card_multiIdx_le s
      _ = ((s + 1) * a) ^ 2 := by ring
  calc Real.sqrt (∑ γ ∈ multiIdx s, l2On V (partialD γ h) ^ 2)
      ≤ Real.sqrt (((s + 1) * a) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = (s + 1) * a := Real.sqrt_sq (by positivity)
    _ = (s + 1) * Real.sqrt (volume V).toReal * normCk s U h := by rw [ha_def]; ring

/-- `C^1(U)` controls `W^{1,∞}(V)` for `V ⊆ U` open. -/
theorem memCk_memW1infOn {U V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U) {h : ℂ → ℂ}
    (hh : MemCk 1 U h) : MemW1infOn V h ∧ normW1infOn V h ≤ 3 * normCk 1 U h := by
  obtain ⟨W, -, hUW, hcd⟩ := hh.near
  have hcdV : ContDiffOn ℝ 1 h V := hcd.mono (hVU.trans hUW)
  set M := normCk 1 U h with hM_def
  have hM : 0 ≤ M := normCk_nonneg _ _ _
  have hmeas := hV.measurableSet
  have hb0 : ∀ x ∈ V, ‖h x‖ ≤ M := fun x hx => norm_le_normCk hh (hVU hx)
  have h0 : MemLp h ⊤ (volume.restrict V) :=
    memLp_top_of_bound (hcdV.continuousOn.aestronglyMeasurable hmeas) M
      (ae_restrict_of_forall_mem hmeas hb0)
  have hd : ∀ γ : ℕ × ℕ, γ.1 + γ.2 ≤ 1 → ContinuousOn (partialD γ h) V ∧
      MemLp (partialD γ h) ⊤ (volume.restrict V) ∧
      HasWeakDerivOn V (pdList γ) h (partialD γ h) ∧ ∀ x ∈ V, ‖partialD γ h x‖ ≤ M := by
    intro γ hγ
    have hc := continuousOn_partialD hV hcdV (n := 1) hγ
    have hb : ∀ x ∈ V, ‖partialD γ h x‖ ≤ M := fun x hx => norm_partialD_le_normCk hh hγ (hVU hx)
    exact ⟨hc, memLp_top_of_bound (hc.aestronglyMeasurable hmeas) M
      (ae_restrict_of_forall_mem hmeas hb),
      hasWeakDerivOn_of_contDiffOn hV (n := 1) (by simpa using hγ) hcdV, hb⟩
  have hmem : MemW1infOn V h := by
    refine ⟨h0, fun γ hγ => ?_⟩
    have hγ1 : γ.1 + γ.2 ≤ 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
      rcases hγ with rfl | rfl <;> norm_num
    obtain ⟨hc, hm, hw, -⟩ := hd γ hγ1
    exact ⟨_, hm, hc.locallyIntegrableOn hmeas, hw⟩
  refine ⟨hmem, ?_⟩
  have e0 : (eLpNorm h ⊤ (volume.restrict V)).toReal ≤ M := by
    refine ENNReal.toReal_le_of_le_ofReal hM ?_
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound (ae_restrict_of_forall_mem hmeas hb0)
  have hae : ∀ γ : ℕ × ℕ, γ.1 + γ.2 ≤ 1 →
      ∀ᵐ x, x ∈ V → weakPartialOn V γ h x = partialD γ h x := fun γ hγ =>
    weakDerivOn_ae_eq hV ((hd γ hγ).1.locallyIntegrableOn hmeas) (hd γ hγ).2.2.1
  have e1 : (eLpNorm (gradNormOn V h) ⊤ (volume.restrict V)).toReal ≤ 2 * M := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    rw [eLpNorm_exponent_top]
    refine eLpNormEssSup_le_of_ae_bound ((ae_restrict_iff' hmeas).2 ?_)
    filter_upwards [hae (1, 0) (by norm_num), hae (0, 1) (by norm_num)] with x h1 h2 hx
    unfold gradNormOn
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), h1 hx, h2 hx]
    have b1 := (hd (1, 0) (by norm_num)).2.2.2 x hx
    have b2 := (hd (0, 1) (by norm_num)).2.2.2 x hx
    have c1 := pow_le_pow_left₀ (norm_nonneg _) b1 2
    have c2 := pow_le_pow_left₀ (norm_nonneg _) b2 2
    calc Real.sqrt (‖partialD (1, 0) h x‖ ^ 2 + ‖partialD (0, 1) h x‖ ^ 2)
        ≤ Real.sqrt ((2 * M) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * M := Real.sqrt_sq (by positivity)
  unfold normW1infOn
  linarith

end NonUniqueEuler.Sob.LocalAux
