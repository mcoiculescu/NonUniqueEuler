import NonUniqueEuler.H.Infra.Sobolev.Local.Leibniz

/-!
# Helper for `P/Infra/Sobolev/Local`: extension of `W^{1,∞}(V)` by a cutoff

`LocalAux.memW1infOn_mul_testFn`: for `χ` a test function supported in the open set `V`,
`‖χ U‖_{W^{1,∞}(ℝ²)} ≤ C ‖U‖_{W^{1,∞}(V)}` with `C = 3 sup|χ| + sup|∂₁χ| + sup|∂₂χ|`.

Proof: `∂_v(χU) = (∂_vχ) U + χ ∂_vU` weakly on `V` (`hasWeakDerivOn_mul_single`); this
vanishes outside `tsupport χ`, so by the support lemma (`hasWeakDerivOn_univ_of_cutoff`) it is
the weak derivative on the plane; then pointwise bounds, a.e.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob.LocalAux

/-- `‖f x‖ ≤ ‖f‖_{L^∞}` a.e., when the essential supremum is finite. -/
theorem ae_norm_le_toReal_eLpNorm_top {μ : Measure ℂ} {f : ℂ → ℂ}
    (hf : eLpNorm f ⊤ μ ≠ ⊤) : ∀ᵐ x ∂μ, ‖f x‖ ≤ (eLpNorm f ⊤ μ).toReal := by
  rw [eLpNorm_exponent_top] at hf ⊢
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  have := ENNReal.toReal_mono hf hx
  rwa [toReal_enorm] at this

theorem ae_real_le_toReal_eLpNorm_top {μ : Measure ℂ} {f : ℂ → ℝ}
    (hf : eLpNorm f ⊤ μ ≠ ⊤) : ∀ᵐ x ∂μ, ‖f x‖ ≤ (eLpNorm f ⊤ μ).toReal := by
  rw [eLpNorm_exponent_top] at hf ⊢
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  have := ENNReal.toReal_mono hf hx
  rwa [toReal_enorm] at this

/-- `‖χ g‖_{L^p(μ)} ≤ B ‖g‖_{L^p(μ)}` for `|χ| ≤ B` (real-valued form). -/
theorem toReal_eLpNorm_mul_le {μ : Measure ℂ} {p : ℝ≥0∞} {χ g : ℂ → ℂ} {B : ℝ}
    (hB : ∀ x, ‖χ x‖ ≤ B) (hg : eLpNorm g p μ ≠ ⊤) :
    (eLpNorm (fun x => χ x * g x) p μ).toReal ≤ B * (eLpNorm g p μ).toReal := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := μ) (f := fun x => χ x * g x)
    (g := g) (c := B) (Eventually.of_forall fun x => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)) p
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg) h1
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0] at h2

theorem sqrt_sq_add_sq_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ a + b := by
  calc Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt ((a + b) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg ha hb])
    _ = a + b := Real.sqrt_sq (add_nonneg ha hb)

/-- One direction of the extension: `∂_v(χU) = (∂_vχ) U + χ G` weakly on the plane. -/
theorem dir_aux {V K W : Set ℂ} (hV : IsOpen V) {χ ζ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hζ : IsTestFn V ζ) (hW : IsOpen W) (hKW : K ⊆ W) (hζW : ∀ x ∈ W, ζ x = 1) (hKV : K ⊆ V)
    (hχK : ∀ x, x ∉ K → χ x = 0) {v : ℂ} (hχvK : ∀ x, x ∉ K → dirDeriv v χ x = 0)
    {B₀ B : ℝ} (hB₀ : ∀ x, ‖χ x‖ ≤ B₀) (hB : ∀ x, ‖dirDeriv v χ x‖ ≤ B)
    {U G : ℂ → ℂ} (hU : MemLp U ⊤ (volume.restrict V)) (hG : MemLp G ⊤ (volume.restrict V))
    (hGl : LocallyIntegrableOn G V) (hUG : HasWeakDerivOn V [v] U G) :
    MemLp (fun x => dirDeriv v χ x * U x + χ x * G x) ⊤ volume ∧
      HasWeakDerivOn univ [v] (fun x => χ x * U x)
        (fun x => dirDeriv v χ x * U x + χ x * G x) ∧
      (∀ x, x ∉ V → dirDeriv v χ x * U x + χ x * G x = 0) ∧
      (∀ x, ‖dirDeriv v χ x * U x + χ x * G x‖ ≤ B * ‖U x‖ + B₀ * ‖G x‖) := by
  have hUl : LocallyIntegrableOn U V := locInt_of_memLp le_top hU
  have hprod := hasWeakDerivOn_mul_single hχ hUl hGl hUG
  have hfK : ∀ᵐ x, x ∉ K → χ x * U x = 0 :=
    Eventually.of_forall fun x hx => by rw [hχK x hx, zero_mul]
  have hS := hasWeakDerivOn_univ_of_cutoff hζ hW hKW hζW hfK hprod
  have hzero : ∀ x, x ∉ K → dirDeriv v χ x * U x + χ x * G x = 0 := fun x hx => by
    rw [hχvK x hx, hχK x hx, zero_mul, zero_mul, add_zero]
  have hζH : (fun x => ζ x * (dirDeriv v χ x * U x + χ x * G x)) =
      fun x => dirDeriv v χ x * U x + χ x * G x := by
    funext x
    by_cases hx : x ∈ K
    · rw [hζW x (hKW hx), one_mul]
    · rw [hzero x hx, mul_zero]
  rw [hζH] at hS
  have hzV : ∀ x, x ∉ V → dirDeriv v χ x * U x + χ x * G x = 0 :=
    fun x hx => hzero x (fun h => hx (hKV h))
  refine ⟨?_, hS, hzV, fun x => ?_⟩
  · refine memLp_of_restrict_of_ae_zero hV.measurableSet (Eventually.of_forall hzV) ?_
    exact (memLp_mul_of_bound (contDiff_dirDeriv hχ v).continuous hB hU).add
      (memLp_mul_of_bound hχ.continuous hB₀ hG)
  · refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (hB₀ x) (norm_nonneg _))

theorem norm_weakPartialOn_le_gradNormOn (V : Set ℂ) (U : ℂ → ℂ) (x : ℂ) :
    ‖weakPartialOn V (1, 0) U x‖ ≤ gradNormOn V U x ∧
      ‖weakPartialOn V (0, 1) U x‖ ≤ gradNormOn V U x := by
  unfold gradNormOn
  constructor
  · exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖weakPartialOn V (0, 1) U x‖])
  · exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖weakPartialOn V (1, 0) U x‖])

/-- Extension of `W^{1,∞}(V)` by a cutoff supported in `V`. -/
theorem memW1infOn_mul_testFn {V : Set ℂ} (hV : IsOpen V) {χ : ℂ → ℂ} (hχ : IsTestFn V χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℂ → ℂ, MemW1infOn V U →
      MemW1infOn univ (fun x => χ x * U x) ∧
        normW1infOn univ (fun x => χ x * U x) ≤ C * normW1infOn V U := by
  have hmeas := hV.measurableSet
  have hK : IsCompact (tsupport χ) := hχ.compact
  have hKV : tsupport χ ⊆ V := hχ.subset
  obtain ⟨ζ, hζ, -, W, hW, hKW, hζW⟩ := exists_cutoff hK hV hKV
  have hχK' : IsTestFn (tsupport χ) χ := ⟨hχ.smooth, hχ.compact, subset_rfl⟩
  have hχ1 := hχ.dirDeriv 1
  have hχI := hχ.dirDeriv Complex.I
  obtain ⟨B₀, hB₀⟩ := hχ.continuous.bounded_above_of_compact_support hχ.compact
  obtain ⟨B₁, hB₁⟩ := hχ1.continuous.bounded_above_of_compact_support hχ1.compact
  obtain ⟨B₂, hB₂⟩ := hχI.continuous.bounded_above_of_compact_support hχI.compact
  have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ 0)
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ 0)
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ 0)
  have hχK : ∀ x, x ∉ tsupport χ → χ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hχvK : ∀ v x, x ∉ tsupport χ → dirDeriv v χ x = 0 := fun v x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx ((hχK'.dirDeriv v).subset h))
  refine ⟨3 * B₀ + B₁ + B₂, by positivity, fun U hU => ?_⟩
  obtain ⟨G₁, hG₁, hG₁l, hUG₁⟩ := hU.deriv (1, 0) (by simp)
  obtain ⟨G₂, hG₂, hG₂l, hUG₂⟩ := hU.deriv (0, 1) (by simp)
  obtain ⟨m₁, w₁, z₁, b₁⟩ := dir_aux hV hχ.smooth hζ hW hKW hζW hKV hχK (hχvK 1) hB₀ hB₁
    hU.memLp hG₁ hG₁l hUG₁
  obtain ⟨m₂, w₂, z₂, b₂⟩ := dir_aux hV hχ.smooth hζ hW hKW hζW hKV hχK (hχvK Complex.I) hB₀ hB₂
    hU.memLp hG₂ hG₂l hUG₂
  have hzχU : ∀ x, x ∉ V → χ x * U x = 0 := fun x hx => by
    rw [hχK x (fun h => hx (hKV h)), zero_mul]
  have hχU : MemLp (fun x => χ x * U x) ⊤ volume :=
    memLp_of_restrict_of_ae_zero hmeas (Eventually.of_forall hzχU)
      (memLp_mul_of_bound hχ.continuous hB₀ hU.memLp)
  have hmem : MemW1infOn univ (fun x => χ x * U x) := by
    refine ⟨by rwa [Measure.restrict_univ], fun γ hγ => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
    rcases hγ with rfl | rfl
    · exact ⟨_, by rwa [Measure.restrict_univ],
        (m₁.locallyIntegrable le_top).locallyIntegrableOn univ, w₁⟩
    · exact ⟨_, by rwa [Measure.restrict_univ],
        (m₂.locallyIntegrable le_top).locallyIntegrableOn univ, w₂⟩
  refine ⟨hmem, ?_⟩
  set N₀ := (eLpNorm U ⊤ (volume.restrict V)).toReal with hN₀
  set N₁ := (eLpNorm (gradNormOn V U) ⊤ (volume.restrict V)).toReal with hN₁
  have hN₀0 : 0 ≤ N₀ := ENNReal.toReal_nonneg
  have hN₁0 : 0 ≤ N₁ := ENNReal.toReal_nonneg
  -- the `L^∞` part
  have e0 : (eLpNorm (fun x => χ x * U x) ⊤ (volume.restrict univ)).toReal ≤ B₀ * N₀ := by
    rw [Measure.restrict_univ, eLpNorm_eq_restrict_of_ae_zero hmeas (Eventually.of_forall hzχU)]
    exact toReal_eLpNorm_mul_le hB₀ hU.memLp.eLpNorm_ne_top
  -- a.e. identifications of the weak derivatives
  have a1 : ∀ᵐ x, x ∈ V → weakPartialOn V (1, 0) U x = G₁ x := weakDerivOn_ae_eq hV hG₁l hUG₁
  have a2 : ∀ᵐ x, x ∈ V → weakPartialOn V (0, 1) U x = G₂ x := weakDerivOn_ae_eq hV hG₂l hUG₂
  have aU := (ae_restrict_iff' hmeas).1 (ae_norm_le_toReal_eLpNorm_top hU.memLp.eLpNorm_ne_top)
  -- finiteness of the gradient norm
  have aG₁ := (ae_restrict_iff' hmeas).1 (ae_norm_le_toReal_eLpNorm_top hG₁.eLpNorm_ne_top)
  have aG₂ := (ae_restrict_iff' hmeas).1 (ae_norm_le_toReal_eLpNorm_top hG₂.eLpNorm_ne_top)
  have hgfin : eLpNorm (gradNormOn V U) ⊤ (volume.restrict V) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (?_ : _ ≤ ENNReal.ofReal
      ((eLpNorm G₁ ⊤ (volume.restrict V)).toReal + (eLpNorm G₂ ⊤ (volume.restrict V)).toReal))
    rw [eLpNorm_exponent_top]
    refine eLpNormEssSup_le_of_ae_bound ((ae_restrict_iff' hmeas).2 ?_)
    filter_upwards [a1, a2, aG₁, aG₂] with x h1 h2 g1 g2 hx
    unfold gradNormOn
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), h1 hx, h2 hx]
    exact (sqrt_sq_add_sq_le _ _ (norm_nonneg _) (norm_nonneg _)).trans
      (add_le_add (g1 hx) (g2 hx))
  have aD := (ae_restrict_iff' hmeas).1 (ae_real_le_toReal_eLpNorm_top hgfin)
  -- the weak derivatives of `χ U` on the plane
  have u1 : ∀ᵐ x, x ∈ univ → weakPartialOn univ (1, 0) (fun x => χ x * U x) x =
      dirDeriv 1 χ x * U x + χ x * G₁ x :=
    weakDerivOn_ae_eq isOpen_univ ((m₁.locallyIntegrable le_top).locallyIntegrableOn univ) w₁
  have u2 : ∀ᵐ x, x ∈ univ → weakPartialOn univ (0, 1) (fun x => χ x * U x) x =
      dirDeriv Complex.I χ x * U x + χ x * G₂ x :=
    weakDerivOn_ae_eq isOpen_univ ((m₂.locallyIntegrable le_top).locallyIntegrableOn univ) w₂
  have e1 : (eLpNorm (gradNormOn univ (fun x => χ x * U x)) ⊤ (volume.restrict univ)).toReal ≤
      (B₁ + B₂) * N₀ + 2 * B₀ * N₁ := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    rw [Measure.restrict_univ, eLpNorm_exponent_top]
    refine eLpNormEssSup_le_of_ae_bound ?_
    filter_upwards [a1, a2, aU, aD, u1, u2] with x h1 h2 hUx hDx k1 k2
    unfold gradNormOn
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), k1 (mem_univ x), k2 (mem_univ x)]
    refine (sqrt_sq_add_sq_le _ _ (norm_nonneg _) (norm_nonneg _)).trans ?_
    by_cases hx : x ∈ V
    · have hg := norm_weakPartialOn_le_gradNormOn V U x
      have hD : gradNormOn V U x ≤ N₁ := by
        have := hDx hx
        have hnn : 0 ≤ gradNormOn V U x := Real.sqrt_nonneg _
        rwa [Real.norm_eq_abs, abs_of_nonneg hnn] at this
      have c1 : ‖G₁ x‖ ≤ N₁ := by rw [← h1 hx]; exact hg.1.trans hD
      have c2 : ‖G₂ x‖ ≤ N₁ := by rw [← h2 hx]; exact hg.2.trans hD
      have d1 := b₁ x
      have d2 := b₂ x
      have hUx' := hUx hx
      have f1 : B₁ * ‖U x‖ ≤ B₁ * N₀ := mul_le_mul_of_nonneg_left hUx' hB₁0
      have f2 : B₂ * ‖U x‖ ≤ B₂ * N₀ := mul_le_mul_of_nonneg_left hUx' hB₂0
      have f3 : B₀ * ‖G₁ x‖ ≤ B₀ * N₁ := mul_le_mul_of_nonneg_left c1 hB₀0
      have f4 : B₀ * ‖G₂ x‖ ≤ B₀ * N₁ := mul_le_mul_of_nonneg_left c2 hB₀0
      linarith
    · rw [z₁ x hx, z₂ x hx, norm_zero, add_zero]
      positivity
  unfold normW1infOn
  have : B₀ * N₀ + ((B₁ + B₂) * N₀ + 2 * B₀ * N₁) ≤ (3 * B₀ + B₁ + B₂) * (N₀ + N₁) := by
    nlinarith [mul_nonneg hB₀0 hN₀0, mul_nonneg hB₀0 hN₁0, mul_nonneg hB₁0 hN₁0,
      mul_nonneg hB₂0 hN₁0]
  linarith

end NonUniqueEuler.Sob.LocalAux
