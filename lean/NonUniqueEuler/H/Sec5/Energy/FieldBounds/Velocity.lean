import NonUniqueEuler.H.Sec5.Energy.FieldBounds.Local
import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.Bilinear
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Infra.Sobolev.EmbedLinf
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.Local
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Helper for `P/Sec5/Energy/FieldBounds`: the field `K_BS * Re w` on `N₁`

Step 3 of the proof of `lem:energy` (`05_single_ring.tex:338-344`). Let `W = K_BS * Re w`
(`BS.velocityRe w`) and `W_B = χ_B W`. Since `χ_B = 1` on `\bar B_{7/2} ⊇ N₁` (`chiB_eq_one`),
`W = W_B` on `N₁`, so the local weak derivatives and norms of `W` on `N₁` are those of `W_B`
(`FieldBoundsAux.weakDerivOn_congr_on`). Then:

* `‖W‖_{H^s(N₁)} ≤ ‖W_B‖_{H^s} ≤ ‖W_B‖_{H^{s+1}} ≤ C^el_s ‖w‖_{H^s} ≤ C^el_s`
  (`lem:Hk-calculus`(3), `Cel_isHkBSConst`; `MemH.memHOn`, `MemH.normH_mono`);
* `‖W‖_{W^{1,∞}(N₁)} ≤ 3 ‖W_B‖_{H^3} ≤ 3 C^el_2 ‖w‖_{H^2} ≤ 3 C^el_2` (`lem:embed`(E2),
  `eLpNorm_top_le_normH_two`, applied to `W_B`, `∂₁W_B`, `∂₂W_B`; `memW1infOn_of_memH_three`);
  the manuscript states `6C^el_2`, which is weaker;
* `div W = 0` on `N₁`: `div(K_BS * g) = 0` in `𝒟'(ℝ²)` for `g = Re w ∈ L¹`
  (`lem:BS-basic`(e), `BS.isWeaklyDivFree_velocity_of_L1`); testing against a real `ψ` supported
  in `N₁` and integrating by parts with the weak derivatives of `W_B` gives
  `∫ ψ (Re ∂₁W_B + Im ∂₂W_B) = 0`, hence `Re ∂₁W + Im ∂₂W = 0` a.e. on `N₁`
  (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`; `weakDivOn_eq_zero_of_isWeaklyDivFree`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob.FieldBoundsAux

/-! ### `H^3 ⊂ W^{1,∞}` -/

theorem ae_norm_le_of_eLpNorm_top_le {μ : Measure ℂ} {f : ℂ → ℂ} {C : ℝ}
    (h : eLpNorm f ⊤ μ ≤ ENNReal.ofReal C) (hC : 0 ≤ C) : ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
  have hne : eLpNorm f ⊤ μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  filter_upwards [ae_norm_le_toReal_eLpNorm_top hne] with x hx
  exact hx.trans (ENNReal.toReal_le_of_le_ofReal hC h)

theorem memLp_two_of_memH {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) : MemLp f 2 volume := by
  have := hf.memLp
  rwa [Measure.restrict_univ] at this

/-- The first derivatives of an `H^3` function: `L²`, weak derivatives on the plane, and
`‖∂_i f‖_{L^∞} ≤ ‖f‖_{H^3}` (`lem:embed`(E2) for `∂_i f ∈ H^2`). -/
theorem memH_three_deriv {f : ℂ → ℂ} (hf : MemH 3 f) {γ : ℕ × ℕ}
    (hγ : γ ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ))) :
    MemLp (weakPartial γ f) 2 volume ∧ HasWeakDerivOn univ (pdList γ) f (weakPartial γ f) ∧
      eLpNorm (weakPartial γ f) ⊤ volume ≤ ENNReal.ofReal (normH 3 f) := by
  have hγ1 : γ.1 + γ.2 = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
    rcases hγ with rfl | rfl <;> rfl
  have hγm : γ ∈ multiIdx 3 := mem_multiIdx.2 (by omega)
  obtain ⟨h1, h2⟩ := hf.memLp_weakPartial hγm
  have hf' : MemH (2 + (γ.1 + γ.2)) f := by rw [hγ1]; exact hf
  obtain ⟨h3, h4⟩ := MemH.weakPartial (k := 2) (γ := γ) hf'
  rw [hγ1] at h4
  exact ⟨h1, h2, (eLpNorm_top_le_normH_two h3).trans (ENNReal.ofReal_le_ofReal h4)⟩

/-- `H^3 ⊂ W^{1,∞}(V)` with `‖f‖_{W^{1,∞}(V)} ≤ 3 ‖f‖_{H^3}` (`lem:embed`(E2) applied to `f`,
`∂₁f`, `∂₂f`, and `|∇f| ≤ |∂₁f| + |∂₂f|`). -/
theorem memW1infOn_of_memH_three {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℂ} (hf : MemH 3 f) :
    MemW1infOn V f ∧ normW1infOn V f ≤ 3 * normH 3 f := by
  have hf2 : MemH 2 f := hf.mono_order (by norm_num)
  have hn23 : normH 2 f ≤ normH 3 f := hf.normH_mono (by norm_num)
  have hN := normH_nonneg 3 f
  have hfL2 := memLp_two_of_memH hf
  have hfμ : eLpNorm f ⊤ (volume.restrict V) ≤ ENNReal.ofReal (normH 3 f) :=
    (eLpNorm_mono_measure f Measure.restrict_le_self).trans
      ((eLpNorm_top_le_normH_two hf2).trans (ENNReal.ofReal_le_ofReal hn23))
  have hmem : MemW1infOn V f := by
    refine ⟨⟨hfL2.1.restrict, lt_of_le_of_lt hfμ ENNReal.ofReal_lt_top⟩, fun γ hγ => ?_⟩
    obtain ⟨h1, h2, h3⟩ := memH_three_deriv hf hγ
    exact ⟨weakPartial γ f, ⟨h1.1.restrict, lt_of_le_of_lt
      ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans h3) ENNReal.ofReal_lt_top⟩,
      (h1.locallyIntegrable one_le_two).locallyIntegrableOn V, h2.mono (subset_univ V)⟩
  refine ⟨hmem, ?_⟩
  -- the derivatives on `V` are the global ones
  have hd : ∀ γ ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ)),
      ∀ᵐ x ∂(volume.restrict V), ‖weakPartialOn V γ f x‖ ≤ normH 3 f := by
    intro γ hγ
    obtain ⟨h1, h2, h3⟩ := memH_three_deriv hf hγ
    have hae : ∀ᵐ x, x ∈ V → weakPartialOn V γ f x = weakPartial γ f x :=
      weakDerivOn_ae_eq hV ((h1.locallyIntegrable one_le_two).locallyIntegrableOn V)
        (h2.mono (subset_univ V))
    have hb := ae_restrict_of_ae (μ := volume) (s := V) (ae_norm_le_of_eLpNorm_top_le h3 hN)
    filter_upwards [(ae_restrict_iff' hV.measurableSet).2 hae, hb] with x hx1 hx2
    rw [hx1]
    exact hx2
  have hg : ∀ᵐ x ∂(volume.restrict V), ‖gradNormOn V f x‖ ≤ 2 * normH 3 f := by
    filter_upwards [hd _ mem_pair_left, hd _ mem_pair_right] with x h1 h2
    rw [Real.norm_of_nonneg (gradNormOn_nonneg _ _ _)]
    linarith [gradNormOn_le V f x]
  have hg' := (toReal_eLpNorm_top_le (by positivity) hg).2
  have hf' : (eLpNorm f ⊤ (volume.restrict V)).toReal ≤ normH 3 f :=
    ENNReal.toReal_le_of_le_ofReal hN hfμ
  unfold normW1infOn
  linarith

/-! ### The weak divergence of a weakly divergence-free field -/

/-- A locally integrable function on `V` times a test function supported in `V` is
integrable. -/
theorem integrable_mul_testFn {V : Set ℂ} {g φ : ℂ → ℂ} (hg : LocallyIntegrableOn g V)
    (hφ : IsTestFn V φ) : Integrable (fun x => g x * φ x) := by
  have hK : IsCompact (tsupport φ) := hφ.compact
  have h1 : IntegrableOn g (tsupport φ) := hg.integrableOn_compact_subset hφ.subset hK
  have h2 : IntegrableOn (fun x => g x * φ x) (tsupport φ) :=
    h1.mul_continuousOn hφ.continuous.continuousOn hK
  refine h2.integrable_of_forall_notMem_eq_zero (fun x hx => ?_)
  simp [image_eq_zero_of_notMem_tsupport hx]

/-- `Dψ(x) z = z₁ ∂₁ψ(x) + z₂ ∂₂ψ(x)`. -/
theorem fderiv_apply_eq (ψ : ℂ → ℝ) (x z : ℂ) :
    fderiv ℝ ψ x z = z.re * fderiv ℝ ψ x 1 + z.im * fderiv ℝ ψ x Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The key integration by parts: for `f ∈ H^1`, a real test function `ψ` with
`∫ Dψ(x)(f(x)) dx = 0` satisfies `∫ ψ (Re ∂₁f + Im ∂₂f) = 0`. -/
theorem integral_div_eq_zero {f : ℂ → ℂ} (hf : MemH 1 f) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (h0 : ∫ x, fderiv ℝ ψ x (f x) = 0) :
    ∫ x, ψ x • ((weakPartial (1, 0) f x).re + (weakPartial (0, 1) f x).im) = 0 := by
  set D₁ := weakPartial (1, 0) f with hD₁def
  set D₂ := weakPartial (0, 1) f with hD₂def
  have hm1 : ((1, 0) : ℕ × ℕ) ∈ multiIdx 1 := mem_multiIdx.2 (by norm_num)
  have hm2 : ((0, 1) : ℕ × ℕ) ∈ multiIdx 1 := mem_multiIdx.2 (by norm_num)
  obtain ⟨hD₁, hw₁⟩ := hf.memLp_weakPartial hm1
  obtain ⟨hD₂, hw₂⟩ := hf.memLp_weakPartial hm2
  have hfl : LocallyIntegrableOn f univ :=
    ((memLp_two_of_memH hf).locallyIntegrable one_le_two).locallyIntegrableOn univ
  have hl₁ : LocallyIntegrableOn D₁ univ := (hD₁.locallyIntegrable one_le_two).locallyIntegrableOn _
  have hl₂ : LocallyIntegrableOn D₂ univ := (hD₂.locallyIntegrable one_le_two).locallyIntegrableOn _
  -- the complex test function `Ψ = ψ`
  set Ψ : ℂ → ℂ := fun x => (ψ x : ℂ) with hΨdef
  have hΨ : IsTestFn univ Ψ :=
    ⟨Complex.ofRealCLM.contDiff.comp hψ, hψc.comp_left Complex.ofReal_zero, subset_univ _⟩
  have hdΨ : ∀ v : ℂ, iterDirDeriv [v] Ψ = fun x => ((fderiv ℝ ψ x v : ℝ) : ℂ) := by
    intro v
    funext x
    have hd : HasFDerivAt Ψ (Complex.ofRealCLM.comp (fderiv ℝ ψ x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x ((hψ.differentiable (by simp)) x).hasFDerivAt
    show fderiv ℝ Ψ x v = _
    rw [hd.fderiv]
    rfl
  -- the two integrations by parts
  have e₁ := hw₁ Ψ hΨ
  have e₂ := hw₂ Ψ hΨ
  rw [show pdList (1, 0) = [(1 : ℂ)] from rfl, hdΨ] at e₁
  rw [show pdList (0, 1) = [Complex.I] from rfl, hdΨ] at e₂
  simp only [List.length_singleton, pow_one] at e₁ e₂
  -- integrability
  have I₁ : Integrable (fun x => f x * ((fderiv ℝ ψ x 1 : ℝ) : ℂ)) := by
    have := integrable_mul_testFn hfl (hΨ.iterDirDeriv [1])
    rwa [hdΨ] at this
  have I₂ : Integrable (fun x => f x * ((fderiv ℝ ψ x Complex.I : ℝ) : ℂ)) := by
    have := integrable_mul_testFn hfl (hΨ.iterDirDeriv [Complex.I])
    rwa [hdΨ] at this
  have J₁ : Integrable (fun x => D₁ x * Ψ x) := integrable_mul_testFn hl₁ hΨ
  have J₂ : Integrable (fun x => D₂ x * Ψ x) := integrable_mul_testFn hl₂ hΨ
  -- real and imaginary parts
  have r₁ : ∫ x, (f x).re * fderiv ℝ ψ x 1 = -∫ x, (D₁ x).re * ψ x := by
    have a1 := integral_re I₁
    have a2 := integral_re J₁
    simp only [RCLike.re_to_complex, Complex.re_mul_ofReal, hΨdef] at a1 a2
    rw [a1, e₁, a2, neg_one_mul, Complex.neg_re]
  have r₂ : ∫ x, (f x).im * fderiv ℝ ψ x Complex.I = -∫ x, (D₂ x).im * ψ x := by
    have a1 := integral_im I₂
    have a2 := integral_im J₂
    simp only [RCLike.im_to_complex, Complex.im_mul_ofReal, hΨdef] at a1 a2
    rw [a1, e₂, a2, neg_one_mul, Complex.neg_im]
  have K₁ : Integrable (fun x => (f x).re * fderiv ℝ ψ x 1) := by
    have := I₁.re
    simpa only [RCLike.re_to_complex, Complex.re_mul_ofReal] using this
  have K₂ : Integrable (fun x => (f x).im * fderiv ℝ ψ x Complex.I) := by
    have := I₂.im
    simpa only [RCLike.im_to_complex, Complex.im_mul_ofReal] using this
  have L₁ : Integrable (fun x => (D₁ x).re * ψ x) := by
    have := J₁.re
    simpa only [RCLike.re_to_complex, Complex.re_mul_ofReal, hΨdef] using this
  have L₂ : Integrable (fun x => (D₂ x).im * ψ x) := by
    have := J₂.im
    simpa only [RCLike.im_to_complex, Complex.im_mul_ofReal, hΨdef] using this
  have hsplit : ∫ x, fderiv ℝ ψ x (f x) =
      (∫ x, (f x).re * fderiv ℝ ψ x 1) + ∫ x, (f x).im * fderiv ℝ ψ x Complex.I := by
    calc ∫ x, fderiv ℝ ψ x (f x) =
        ∫ x, ((f x).re * fderiv ℝ ψ x 1 + (f x).im * fderiv ℝ ψ x Complex.I) :=
          integral_congr_ae (Eventually.of_forall fun x => fderiv_apply_eq ψ x (f x))
      _ = _ := integral_add K₁ K₂
  have hsum : ∫ x, ψ x • ((D₁ x).re + (D₂ x).im) =
      (∫ x, (D₁ x).re * ψ x) + ∫ x, (D₂ x).im * ψ x := by
    calc ∫ x, ψ x • ((D₁ x).re + (D₂ x).im) = ∫ x, ((D₁ x).re * ψ x + (D₂ x).im * ψ x) :=
          integral_congr_ae (Eventually.of_forall fun x => by simp only [smul_eq_mul]; ring)
      _ = _ := integral_add L₁ L₂
  rw [hsum]
  rw [hsplit, r₁, r₂] at h0
  linarith

/-- If `f ∈ H^1` agrees on the open set `V` with a field `u` that is divergence free in
`𝒟'(ℝ²)`, then the weak divergence of `u` on `V` vanishes a.e. on `V`. -/
theorem weakDivOn_eq_zero_of_isWeaklyDivFree {V : Set ℂ} (hV : IsOpen V) {u f : ℂ → ℂ}
    (hf : MemH 1 f) (hfu : ∀ x ∈ V, f x = u x) (hu : Prelim.IsWeaklyDivFree u) :
    ∀ᵐ x ∂(volume.restrict V), weakDivOn V u x = 0 := by
  set D₁ := weakPartial (1, 0) f with hD₁def
  set D₂ := weakPartial (0, 1) f with hD₂def
  have hm1 : ((1, 0) : ℕ × ℕ) ∈ multiIdx 1 := mem_multiIdx.2 (by norm_num)
  have hm2 : ((0, 1) : ℕ × ℕ) ∈ multiIdx 1 := mem_multiIdx.2 (by norm_num)
  obtain ⟨hD₁, hw₁⟩ := hf.memLp_weakPartial hm1
  obtain ⟨hD₂, hw₂⟩ := hf.memLp_weakPartial hm2
  have hl₁ : LocallyIntegrableOn D₁ V := (hD₁.locallyIntegrable one_le_two).locallyIntegrableOn V
  have hl₂ : LocallyIntegrableOn D₂ V := (hD₂.locallyIntegrable one_le_two).locallyIntegrableOn V
  -- the local weak derivatives of `u` on `V`
  have he₁ : ∀ᵐ x, x ∈ V → weakPartialOn V (1, 0) u x = D₁ x :=
    weakDerivOn_ae_eq hV hl₁ ((hasWeakDerivOn_congr_on hfu).1 (hw₁.mono (subset_univ V)))
  have he₂ : ∀ᵐ x, x ∈ V → weakPartialOn V (0, 1) u x = D₂ x :=
    weakDerivOn_ae_eq hV hl₂ ((hasWeakDerivOn_congr_on hfu).1 (hw₂.mono (subset_univ V)))
  -- `Re ∂₁f + Im ∂₂f = 0` a.e. on `V`
  have hFl : LocallyIntegrableOn (fun x => (D₁ x).re + (D₂ x).im) V := by
    have h1 : MemLp (fun x => (D₁ x).re + (D₂ x).im) 2 volume := by
      exact hD₁.re.add hD₂.im
    exact (h1.locallyIntegrable one_le_two).locallyIntegrableOn V
  have hF : ∀ᵐ x, x ∈ V → (D₁ x).re + (D₂ x).im = 0 := by
    refine hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero hFl ?_
    intro ψ hψ hψc hψV
    refine integral_div_eq_zero hf hψ hψc ?_
    have hdiv := (hu ψ hψ hψc).2
    rw [← hdiv]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ V
    · simp only [hfu x hx]
    · have hx' : x ∉ tsupport (fderiv ℝ ψ) := fun h => hx (hψV (tsupport_fderiv_subset ℝ h))
      simp only [image_eq_zero_of_notMem_tsupport hx', zero_apply]
  refine (ae_restrict_iff' hV.measurableSet).2 ?_
  filter_upwards [he₁, he₂, hF] with x h1 h2 h3 hxV
  unfold weakDivOn
  rw [h1 hxV, h2 hxV]
  exact h3 hxV

end NonUniqueEuler.Sob.FieldBoundsAux

namespace NonUniqueEuler.OneRing.FieldBoundsAux

open RingData Sob Sob.FieldBoundsAux

/-! ### The Biot–Savart field on `N₁` -/

theorem annN_subset_ball : annN ⊆ ball (0 : ℂ) 4 := by
  intro x hx
  have : ‖x‖ ≤ 2 := hx.2
  rw [mem_ball_zero_iff]
  linarith

/-- `χ_B (K_BS * Re w) = K_BS * Re w` on `N₁`. -/
theorem chiB_velocityRe_eq (w : ℂ → ℂ) :
    ∀ x ∈ annN1, (fun y => (chiB y : ℂ) * BS.velocityRe w y) x = BS.velocityRe w x := by
  intro x hx
  have : ‖x‖ < 3 := hx.2
  simp only [chiB_eq_one (by linarith : ‖x‖ ≤ 7 / 2), Complex.ofReal_one, one_mul]

/-- `lem:Hk-calculus`(3) for `χ_B` and `ρ = 4`: `‖χ_B K_BS * Re w‖_{H^{j+1}} ≤ C^el_j` for
`j ≤ s`, `‖w‖_{H^s} ≤ 1`. -/
theorem chiB_velocityRe_memH {s j : ℕ} (hj : j ≤ s) {w : ℂ → ℂ} (hw : MemH s w)
    (hwN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → w x = 0) (hw1 : normH s w ≤ 1) :
    MemH (j + 1) (fun y => (chiB y : ℂ) * BS.velocityRe w y) ∧
      normH (j + 1) (fun y => (chiB y : ℂ) * BS.velocityRe w y) ≤ Cel j := by
  have hwj : MemH j w := hw.mono_order hj
  have hsupp : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ ball (0 : ℂ) 4 → w x = 0 :=
    hwN.mono fun x hx hxB => hx fun hxN => hxB (annN_subset_ball hxN)
  obtain ⟨h1, -, hb⟩ := Cel_isHkBSConst j w hwj hsupp
  refine ⟨h1, ?_⟩
  have hle : normH (j + 1) (fun y => (chiB y : ℂ) * BS.velocityRe w y) ≤
      BS.normHC2 (j + 1) (fun y => (chiB y : ℂ) * BS.velocityRe w y)
        (fun y => (chiB y : ℂ) * BS.velocityIm w y) := by
    unfold BS.normHC2
    exact (le_abs_self _).trans (Real.abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg _)))
  have hwj1 : normH j w ≤ 1 := (hw.normH_mono hj).trans hw1
  have hC := Cel_pos j
  calc _ ≤ _ := hle
    _ ≤ Cel j * normH j w := hb
    _ ≤ Cel j * 1 := mul_le_mul_of_nonneg_left hwj1 hC.le
    _ = Cel j := mul_one _

/-- `K_BS * Re w ∈ H^s(N₁)` with `‖K_BS * Re w‖_{H^s(N₁)} ≤ C^el_s`. -/
theorem velocityRe_memHOn {s : ℕ} {w : ℂ → ℂ} (hw : MemH s w)
    (hwN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → w x = 0) (hw1 : normH s w ≤ 1) :
    MemHOn s annN1 (BS.velocityRe w) ∧ normHOn s annN1 (BS.velocityRe w) ≤ Cel s := by
  obtain ⟨h1, h2⟩ := chiB_velocityRe_memH le_rfl hw hwN hw1
  obtain ⟨h3, h4⟩ := MemH.memHOn (h1.mono_order (Nat.le_succ s)) isOpen_annN1
  have h5 := h1.normH_mono (Nat.le_succ s)
  refine ⟨memHOn_congr_on isOpen_annN1.measurableSet (chiB_velocityRe_eq w) h3, ?_⟩
  rw [← normHOn_congr_on s (chiB_velocityRe_eq w)]
  linarith

/-- `K_BS * Re w ∈ W^{1,∞}(N₁)` with `‖K_BS * Re w‖_{W^{1,∞}(N₁)} ≤ 3 C^el_2`. -/
theorem velocityRe_memW1infOn {s : ℕ} (hs : 2 ≤ s) {w : ℂ → ℂ} (hw : MemH s w)
    (hwN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → w x = 0) (hw1 : normH s w ≤ 1) :
    MemW1infOn annN1 (BS.velocityRe w) ∧ normW1infOn annN1 (BS.velocityRe w) ≤ 3 * Cel 2 := by
  obtain ⟨h1, h2⟩ := chiB_velocityRe_memH hs hw hwN hw1
  obtain ⟨h3, h4⟩ := memW1infOn_of_memH_three isOpen_annN1 h1
  refine ⟨memW1infOn_congr_on isOpen_annN1.measurableSet (chiB_velocityRe_eq w) h3, ?_⟩
  rw [← normW1infOn_congr_on isOpen_annN1.measurableSet (chiB_velocityRe_eq w)]
  linarith

/-- `Re w ∈ L¹` (`w ∈ L²` vanishes outside the bounded set `N`). -/
theorem re_memLp_one {s : ℕ} {w : ℂ → ℂ} (hw : MemH s w)
    (hwN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → w x = 0) :
    MemLp (fun y => (w y).re) 1 volume := by
  have h2 : MemLp w 2 volume := memLp_two_of_memH hw
  have hm : MeasurableSet annN := isCompact_annN.isClosed.measurableSet
  have hi : MemLp (annN.indicator w) 2 volume := h2.indicator hm
  have hi1 : MemLp (annN.indicator w) 1 volume :=
    hi.mono_exponent_of_measure_support_ne_top (s := annN)
      (fun x hx => indicator_of_notMem hx _) isCompact_annN.measure_lt_top.ne (by norm_num)
  have hae : annN.indicator w =ᵐ[volume] w := by
    filter_upwards [hwN] with x hx
    by_cases hxN : x ∈ annN
    · simp [hxN]
    · simp [hxN, hx hxN]
  have := (hi1.ae_eq hae).re
  simpa only [RCLike.re_to_complex] using this

/-- `div(K_BS * Re w) = 0` weakly, a.e. on `N₁`. -/
theorem weakDivOn_velocityRe {s : ℕ} {w : ℂ → ℂ} (hw : MemH s w)
    (hwN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → w x = 0) (hw1 : normH s w ≤ 1) :
    ∀ᵐ x ∂(volume.restrict annN1), weakDivOn annN1 (BS.velocityRe w) x = 0 := by
  obtain ⟨h1, -⟩ := chiB_velocityRe_memH (Nat.zero_le s) hw hwN hw1
  exact weakDivOn_eq_zero_of_isWeaklyDivFree isOpen_annN1 h1 (chiB_velocityRe_eq w)
    (BS.isWeaklyDivFree_velocity_of_L1 (re_memLp_one hw hwN))

end NonUniqueEuler.OneRing.FieldBoundsAux
