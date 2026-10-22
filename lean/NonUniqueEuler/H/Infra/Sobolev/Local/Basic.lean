import NonUniqueEuler.H.Infra.Sobolev.Local.Cutoff
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helper for `P/Infra/Sobolev/Local`: restriction and the support lemma

* `LocalAux.memHOn_spec`: for `f ∈ H^k(V)`, `V` open, the chosen weak derivatives
  `weakPartialOn V γ f` lie in `L²(V)` and are weak derivatives on `V`;
* `LocalAux.memHOn_mono_set`: restriction to a smaller open set, with the norm inequality
  (uniqueness of weak derivatives on the smaller set, `weakDerivOn_ae_eq`);
* `LocalAux.hasWeakDerivOn_univ_of_cutoff`: the support lemma. If `f = 0` a.e. outside `K`,
  `g = ∂_{vs} f` weakly on `V`, and `ζ` is a test function supported in `V` equal to `1` on an
  open `W ⊇ K`, then `ζ g = ∂_{vs} f` weakly on the plane. For a test function `φ`,
  `∂_{vs} φ = ∂_{vs}(ζ φ)` on `W` and `f = 0` a.e. off `K`, so
  `∫ f ∂_{vs} φ = ∫ f ∂_{vs}(ζφ) = (-1)^{|vs|} ∫ g ζ φ` (`02_prelim.tex`, proof of the local
  norms; the manuscript writes `φ = ζφ + (1-ζ)φ`);
* `LocalAux.memH_of_memHOn_of_support`, `LocalAux.normHOn_eq_normH_of_support`.

Uses `weakDerivOn_ae_eq` (`I/Infra/Sobolev/WeakDeriv.lean`) as a black box.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob.LocalAux

/-! ### `L^p` on subsets -/

/-- An `L^p(V)` function, `p ≥ 1`, is locally integrable on `V`. -/
theorem locInt_of_memLp {V : Set ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p) {g : ℂ → ℂ}
    (hg : MemLp g p (volume.restrict V)) : LocallyIntegrableOn g V :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hg.locallyIntegrable hp)

theorem testFn_eq_zero {V : Set ℂ} {φ : ℂ → ℂ} (hφ : IsTestFn V φ) {x : ℂ} (hx : x ∉ V) :
    φ x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.subset h))

theorem l2On_congr_ae {V : Set ℂ} (hV : MeasurableSet V) {f g : ℂ → ℂ}
    (h : ∀ᵐ x, x ∈ V → f x = g x) : l2On V f = l2On V g := by
  unfold l2On
  rw [eLpNorm_congr_ae ((ae_restrict_iff' hV).2 h)]

theorem l2On_mono_set {V V' : Set ℂ} (hVV' : V' ⊆ V) {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict V)) : l2On V' f ≤ l2On V f :=
  ENNReal.toReal_mono hf.eLpNorm_ne_top
    (eLpNorm_mono_measure f (Measure.restrict_mono hVV' le_rfl))

theorem indicator_ae_eq_of_ae_zero {V : Set ℂ} {f : ℂ → ℂ} (h : ∀ᵐ x, x ∉ V → f x = 0) :
    V.indicator f =ᵐ[volume] f := by
  filter_upwards [h] with x hx
  by_cases hxV : x ∈ V
  · simp [hxV]
  · simp [hxV, hx hxV]

theorem eLpNorm_eq_restrict_of_ae_zero {V : Set ℂ} (hV : MeasurableSet V) {f : ℂ → ℂ}
    {p : ℝ≥0∞} (h : ∀ᵐ x, x ∉ V → f x = 0) :
    eLpNorm f p volume = eLpNorm f p (volume.restrict V) := by
  rw [← eLpNorm_congr_ae (indicator_ae_eq_of_ae_zero h),
    eLpNorm_indicator_eq_eLpNorm_restrict hV]

theorem memLp_of_restrict_of_ae_zero {V : Set ℂ} (hV : MeasurableSet V) {f : ℂ → ℂ}
    {p : ℝ≥0∞} (h : ∀ᵐ x, x ∉ V → f x = 0) (hf : MemLp f p (volume.restrict V)) :
    MemLp f p volume :=
  ((memLp_indicator_iff_restrict hV).2 hf).ae_eq (indicator_ae_eq_of_ae_zero h)

/-- A bounded continuous multiplier keeps `L^p(V)`. -/
theorem memLp_mul_of_bound {V : Set ℂ} {p : ℝ≥0∞} {χ g : ℂ → ℂ} (hχ : Continuous χ) {B : ℝ}
    (hB : ∀ x, ‖χ x‖ ≤ B) (hg : MemLp g p (volume.restrict V)) :
    MemLp (fun x => χ x * g x) p (volume.restrict V) := by
  refine hg.of_le_mul (c := B) (hχ.aestronglyMeasurable.mul hg.1) (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

/-! ### Weak derivatives on subsets -/

/-- For `f ∈ H^k(V)`, `V` open, the chosen weak derivatives are `L²(V)` weak derivatives. -/
theorem memHOn_spec {k : ℕ} {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℂ} (hf : MemHOn k V f)
    {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    MemLp (weakPartialOn V γ f) 2 (volume.restrict V) ∧
      HasWeakDerivOn V (pdList γ) f (weakPartialOn V γ f) := by
  obtain ⟨g, hg, hfg⟩ := hf.deriv γ hγ
  have hgl := locInt_of_memLp one_le_two hg
  have hae := weakDerivOn_ae_eq hV hgl hfg
  refine ⟨hg.ae_eq ((ae_restrict_iff' hV.measurableSet).2 ?_), (weakDerivOn_spec hgl hfg).2⟩
  exact hae.mono fun x hx hxV => (hx hxV).symm

/-- The chosen weak derivative on a smaller open set agrees with a weak derivative on the
larger one. -/
theorem weakDerivOn_ae_eq_of_subset {V V' : Set ℂ} (hV' : IsOpen V') (hVV' : V' ⊆ V)
    {vs : List ℂ} {f g : ℂ → ℂ} (hg : LocallyIntegrableOn g V) (h : HasWeakDerivOn V vs f g) :
    ∀ᵐ x, x ∈ V' → weakDerivOn V' vs f x = g x :=
  weakDerivOn_ae_eq hV' (hg.mono_set hVV') (h.mono hVV')

/-- Restriction `H^k(V) → H^k(V')` for open `V' ⊆ V`. -/
theorem memHOn_mono_set {k : ℕ} {f : ℂ → ℂ} {V V' : Set ℂ} (hV : IsOpen V) (hV' : IsOpen V')
    (hVV' : V' ⊆ V) (hf : MemHOn k V f) : MemHOn k V' f ∧ normHOn k V' f ≤ normHOn k V f := by
  have hμ : volume.restrict V' ≤ volume.restrict V := Measure.restrict_mono hVV' le_rfl
  refine ⟨⟨hf.memLp.mono_measure hμ, fun γ hγ => ?_⟩, ?_⟩
  · obtain ⟨g, hg, hfg⟩ := hf.deriv γ hγ
    exact ⟨g, hg.mono_measure hμ, hfg.mono hVV'⟩
  · unfold normHOn
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun γ hγ => ?_)
    obtain ⟨h2, hd⟩ := memHOn_spec hV hf hγ
    have hae := weakDerivOn_ae_eq_of_subset hV' hVV' (locInt_of_memLp one_le_two h2) hd
    have e : l2On V' (weakPartialOn V' γ f) = l2On V' (weakPartialOn V γ f) :=
      l2On_congr_ae hV'.measurableSet hae
    rw [e]
    exact pow_le_pow_left₀ (l2On_nonneg _ _) (l2On_mono_set hVV' h2) 2

/-! ### The support lemma -/

/-- If `f = 0` a.e. outside `K`, `g = ∂_{vs} f` weakly on `V`, and `ζ` is a test function
supported in `V` with `ζ = 1` on an open `W ⊇ K`, then `ζ g = ∂_{vs} f` weakly on the plane. -/
theorem hasWeakDerivOn_univ_of_cutoff {V K W : Set ℂ} {ζ : ℂ → ℂ} (hζ : IsTestFn V ζ)
    (hW : IsOpen W) (hKW : K ⊆ W) (hζW : ∀ x ∈ W, ζ x = 1) {vs : List ℂ} {f g : ℂ → ℂ}
    (hfK : ∀ᵐ x, x ∉ K → f x = 0) (h : HasWeakDerivOn V vs f g) :
    HasWeakDerivOn univ vs f (fun x => ζ x * g x) := by
  intro φ hφ
  have hζφ : IsTestFn V (fun x => ζ x * φ x) :=
    ⟨hζ.smooth.mul hφ.smooth, hζ.compact.mul_right, tsupport_mul_subset_left.trans hζ.subset⟩
  have hloc : EqOn (fun x => ζ x * φ x) φ W := fun x hx => by simp [hζW x hx]
  have hder := iterDirDeriv_eqOn hW hloc vs
  calc ∫ x, f x * iterDirDeriv vs φ x
      = ∫ x, f x * iterDirDeriv vs (fun x => ζ x * φ x) x := by
        refine integral_congr_ae ?_
        filter_upwards [hfK] with x hx
        by_cases hxK : x ∈ K
        · rw [hder (hKW hxK)]
        · simp [hx hxK]
    _ = (-1) ^ vs.length * ∫ x, g x * (ζ x * φ x) := h _ hζφ
    _ = (-1) ^ vs.length * ∫ x, ζ x * g x * φ x := by
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun x => by ring)

/-- `ζ g ∈ L²` for `g ∈ L²(V)` and a cutoff `ζ` supported in `V` with `‖ζ‖ ≤ 1`. -/
theorem memLp_cutoff_mul {V : Set ℂ} (hV : IsOpen V) {ζ g : ℂ → ℂ} {p : ℝ≥0∞}
    (hζ : IsTestFn V ζ) (hζ1 : ∀ x, ‖ζ x‖ ≤ 1) (hg : MemLp g p (volume.restrict V)) :
    MemLp (fun x => ζ x * g x) p volume :=
  memLp_of_restrict_of_ae_zero hV.measurableSet
    (Eventually.of_forall fun x hx => by simp [testFn_eq_zero hζ hx])
    (memLp_mul_of_bound hζ.continuous hζ1 hg)

/-- For `f = 0` a.e. outside a compact `K ⊆ V`: `f ∈ H^k(V)` implies `f ∈ H^k`. -/
theorem memH_of_memHOn_of_support {k : ℕ} {f : ℂ → ℂ} {K V : Set ℂ} (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) (hfK : ∀ᵐ x, x ∉ K → f x = 0) (hf : MemHOn k V f) :
    MemH k f := by
  obtain ⟨ζ, hζ, hζ1, W, hW, hKW, hζW⟩ := exists_cutoff hK hV hKV
  have hfV : ∀ᵐ x, x ∉ V → f x = 0 := hfK.mono fun x hx hxV => hx (fun h => hxV (hKV h))
  refine memH_iff.2 ⟨memLp_of_restrict_of_ae_zero hV.measurableSet hfV hf.memLp, fun γ hγ => ?_⟩
  obtain ⟨g, hg, hfg⟩ := hf.deriv γ hγ
  exact ⟨_, memLp_cutoff_mul hV hζ hζ1 hg, hasWeakDerivOn_univ_of_cutoff hζ hW hKW hζW hfK hfg⟩

/-- For `f ∈ H^k` with `f = 0` a.e. outside a compact `K ⊆ V`: `‖f‖_{H^k(V)} = ‖f‖_{H^k}`. -/
theorem normHOn_eq_normH_of_support {k : ℕ} {f : ℂ → ℂ} {K V : Set ℂ} (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) (hfK : ∀ᵐ x, x ∉ K → f x = 0) (hf : MemH k f) :
    normHOn k V f = normH k f := by
  obtain ⟨ζ, hζ, hζ1, W, hW, hKW, hζW⟩ := exists_cutoff hK hV hKV
  have hfV' : MemHOn k V f := (memHOn_mono_set isOpen_univ hV (subset_univ V) hf).1
  unfold normH normHOn
  congr 1
  refine Finset.sum_congr rfl fun γ hγ => ?_
  obtain ⟨g, hg, hfg⟩ := hfV'.deriv γ hγ
  have hg' := memLp_cutoff_mul hV hζ hζ1 hg
  have hS := hasWeakDerivOn_univ_of_cutoff hζ hW hKW hζW hfK hfg
  have hae1 := weakDerivOn_ae_eq isOpen_univ
    ((hg'.locallyIntegrable one_le_two).locallyIntegrableOn univ) hS
  obtain ⟨h2, hd⟩ := memHOn_spec isOpen_univ hf hγ
  have hae2 := weakDerivOn_ae_eq_of_subset hV (subset_univ V) (locInt_of_memLp one_le_two h2) hd
  have e1 : l2On V (weakPartialOn V γ f) = l2On V (weakPartialOn univ γ f) :=
    l2On_congr_ae hV.measurableSet hae2
  have e2 : l2On univ (weakPartialOn univ γ f) = l2On V (weakPartialOn univ γ f) := by
    unfold l2On
    rw [Measure.restrict_univ, eLpNorm_eq_restrict_of_ae_zero hV.measurableSet]
    filter_upwards [hae1] with x hx hxV
    have hx' : weakPartialOn univ γ f x = ζ x * g x := hx (mem_univ x)
    rw [hx', testFn_eq_zero hζ hxV, zero_mul]
  rw [e1, e2]

/-! ### Crude norm bounds -/

theorem card_multiIdx_le (k : ℕ) : ((multiIdx k).card : ℝ) ≤ (k + 1) ^ 2 := by
  have : (multiIdx k).card ≤ (k + 1) ^ 2 := by
    unfold multiIdx
    calc _ ≤ (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).card := Finset.card_filter_le _ _
      _ = (k + 1) ^ 2 := by simp [Finset.card_product, sq]
  exact_mod_cast this

/-- If every term `‖∂^γ f‖_{L²(V)}`, `|γ| ≤ k`, is at most `S`, then
`‖f‖_{H^k(V)} ≤ (k+1) S` (as `#multiIdx k ≤ (k+1)²`). -/
theorem normHOn_le_of_forall {k : ℕ} {V : Set ℂ} {f : ℂ → ℂ} {S : ℝ} (hS : 0 ≤ S)
    (h : ∀ γ ∈ multiIdx k, l2On V (weakPartialOn V γ f) ≤ S) : normHOn k V f ≤ (k + 1) * S := by
  unfold normHOn
  have hsum : ∑ γ ∈ multiIdx k, l2On V (weakPartialOn V γ f) ^ 2 ≤ ((k + 1) * S) ^ 2 := by
    calc _ ≤ ∑ γ ∈ multiIdx k, S ^ 2 :=
          Finset.sum_le_sum fun γ hγ => pow_le_pow_left₀ (l2On_nonneg _ _) (h γ hγ) 2
      _ = (multiIdx k).card * S ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k + 1) ^ 2 * S ^ 2 := by gcongr; exact card_multiIdx_le k
      _ = ((k + 1) * S) ^ 2 := by ring
  calc Real.sqrt _ ≤ Real.sqrt (((k + 1) * S) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = (k + 1) * S := Real.sqrt_sq (by positivity)

theorem l2On_weakPartialOn_le_normHOn {k : ℕ} {V : Set ℂ} {f : ℂ → ℂ} {γ : ℕ × ℕ}
    (hγ : γ ∈ multiIdx k) : l2On V (weakPartialOn V γ f) ≤ normHOn k V f := by
  unfold normHOn
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun β => l2On V (weakPartialOn V β f) ^ 2)
    (fun β _ => sq_nonneg _) hγ

theorem normHOn_mono_order {k k' : ℕ} (hk : k ≤ k') (V : Set ℂ) (f : ℂ → ℂ) :
    normHOn k V f ≤ normHOn k' V f := by
  unfold normHOn
  refine Real.sqrt_le_sqrt ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (multiIdx_mono hk) fun _ _ _ => sq_nonneg _

theorem hasWeakDerivOn_zero (V : Set ℂ) (f : ℂ → ℂ) : HasWeakDerivOn V (pdList (0, 0)) f f := by
  intro φ _
  simp [pdList]

/-- `‖f‖_{L²(V)} ≤ ‖f‖_{H^k(V)}`. -/
theorem l2On_le_normHOn {k : ℕ} {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict V)) : l2On V f ≤ normHOn k V f := by
  have hae := weakDerivOn_ae_eq hV (locInt_of_memLp one_le_two hf) (hasWeakDerivOn_zero V f)
  have e : l2On V (weakPartialOn V (0, 0) f) = l2On V f := l2On_congr_ae hV.measurableSet hae
  rw [← e]
  exact l2On_weakPartialOn_le_normHOn (zero_mem_multiIdx k)

/-- `‖χ g‖_{L²(V)} ≤ B ‖g‖_{L²(V)}` for `|χ| ≤ B`. -/
theorem l2On_mul_le {V : Set ℂ} {χ g : ℂ → ℂ} {B : ℝ} (hB : ∀ x, ‖χ x‖ ≤ B)
    (hg : MemLp g 2 (volume.restrict V)) : l2On V (fun x => χ x * g x) ≤ B * l2On V g := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume.restrict V) (f := fun x => χ x * g x)
    (g := g) (c := B) (Eventually.of_forall fun x => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)) 2
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_ne_top) h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0] at h2
  exact h2

/-- Triangle inequality in `L²(V)`. -/
theorem l2On_add_le {V : Set ℂ} {a b : ℂ → ℂ} (ha : MemLp a 2 (volume.restrict V))
    (hb : MemLp b 2 (volume.restrict V)) : l2On V (fun x => a x + b x) ≤ l2On V a + l2On V b := by
  unfold l2On
  rw [← ENNReal.toReal_add ha.eLpNorm_ne_top hb.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ha.eLpNorm_ne_top, hb.eLpNorm_ne_top⟩)
    (eLpNorm_add_le ha.1 hb.1 one_le_two)

end NonUniqueEuler.Sob.LocalAux
