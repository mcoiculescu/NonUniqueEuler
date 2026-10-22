import NonUniqueEuler.Defs.Sec2.HkCalculus
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helper for `P/Sec5/Energy/FieldBounds`: local Sobolev bookkeeping on an open set

Generic facts about `H^k(V)`, `W^{1,∞}(V)` and the weak divergence on an open set `V ⊆ ℂ`, used
in step 4 of the proof of `lem:energy` (`05_single_ring.tex:333-346`: the norms of
`U = Ω x^⊥ + h + K_BS*w` on `N₁`).

* `FieldBoundsAux.weakDerivOn_congr_on` and its consequences: the local weak derivatives, the
  local norms and the weak divergence on `V` only see the values of the function on `V`;
* `FieldBoundsAux.memHOn_add`, `memW1infOn_add`: Minkowski's inequality for `‖·‖_{H^k(V)}` and
  `‖·‖_{W^{1,∞}(V)}`, with `sqrt_sum_sq_le` (Minkowski in `ℓ²` of a finite set);
* `FieldBoundsAux.weakDivOn_add`: the weak divergence is additive (a.e. on `V`);
* `FieldBoundsAux.weakDivOn_eq_divergence`: for a `C¹` field the weak divergence is the classical
  one (a.e. on `V`).

Uses `HasWeakDerivOn.add`, `weakDerivOn_ae_eq`, `hasWeakDerivOn_of_contDiffOn`
(`I/Infra/Sobolev/WeakDeriv.lean`) as black boxes.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob.FieldBoundsAux

/-! ### Generalities -/

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

/-- Triangle inequality in `L²(V)`. -/
theorem l2On_add_le {V : Set ℂ} {a b : ℂ → ℂ} (ha : MemLp a 2 (volume.restrict V))
    (hb : MemLp b 2 (volume.restrict V)) : l2On V (a + b) ≤ l2On V a + l2On V b := by
  unfold l2On
  rw [← ENNReal.toReal_add ha.eLpNorm_ne_top hb.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ha.eLpNorm_ne_top, hb.eLpNorm_ne_top⟩)
    (eLpNorm_add_le ha.1 hb.1 one_le_two)

/-- `‖f x‖ ≤ ‖f‖_{L^∞}` a.e., when the essential supremum is finite. -/
theorem ae_norm_le_toReal_eLpNorm_top {μ : Measure ℂ} {f : ℂ → ℂ}
    (hf : eLpNorm f ⊤ μ ≠ ⊤) : ∀ᵐ x ∂μ, ‖f x‖ ≤ (eLpNorm f ⊤ μ).toReal := by
  rw [eLpNorm_exponent_top] at hf ⊢
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  have := ENNReal.toReal_mono hf hx
  rwa [toReal_enorm] at this

/-- An a.e. bound `‖f‖ ≤ C` gives `‖f‖_{L^∞} ≤ C` (real form). -/
theorem toReal_eLpNorm_top_le {μ : Measure ℂ} {F : Type*} [NormedAddCommGroup F] {f : ℂ → F}
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    eLpNorm f ⊤ μ ≠ ⊤ ∧ (eLpNorm f ⊤ μ).toReal ≤ C := by
  have h1 : eLpNorm f ⊤ μ ≤ ENNReal.ofReal C := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound h
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1, ?_⟩
  calc (eLpNorm f ⊤ μ).toReal ≤ (ENNReal.ofReal C).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    _ = C := ENNReal.toReal_ofReal hC

/-! ### Minkowski in `ℓ²` of a finite set -/

/-- If `0 ≤ c ≤ a + b` termwise, then `(∑ c²)^{1/2} ≤ (∑ a²)^{1/2} + (∑ b²)^{1/2}`. -/
theorem sqrt_sum_sq_le {ι : Type*} (S : Finset ι) {a b c : ι → ℝ} (hc : ∀ i ∈ S, 0 ≤ c i)
    (h : ∀ i ∈ S, c i ≤ a i + b i) :
    Real.sqrt (∑ i ∈ S, c i ^ 2) ≤
      Real.sqrt (∑ i ∈ S, a i ^ 2) + Real.sqrt (∑ i ∈ S, b i ^ 2) := by
  set A := ∑ i ∈ S, a i ^ 2 with hAdef
  set B := ∑ i ∈ S, b i ^ 2 with hBdef
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : ∑ i ∈ S, c i ^ 2 ≤ ∑ i ∈ S, (a i + b i) ^ 2 :=
    Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (hc i hi) (h i hi) 2
  have h2 : ∑ i ∈ S, (a i + b i) ^ 2 = A + 2 * ∑ i ∈ S, a i * b i + B := by
    rw [hAdef, hBdef, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 := Real.sum_mul_le_sqrt_mul_sqrt S a b
  have h4 : (Real.sqrt A + Real.sqrt B) ^ 2 = A + 2 * (Real.sqrt A * Real.sqrt B) + B := by
    rw [add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
    ring
  calc Real.sqrt (∑ i ∈ S, c i ^ 2) ≤ Real.sqrt ((Real.sqrt A + Real.sqrt B) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [h4]
        linarith
    _ = Real.sqrt A + Real.sqrt B := Real.sqrt_sq (by positivity)

/-- The two-term case: `|(c₁,c₂)| ≤ |(a₁,a₂)| + |(b₁,b₂)|` for `0 ≤ cᵢ ≤ aᵢ + bᵢ`. -/
theorem sqrt_two_le {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (h₁0 : 0 ≤ c₁) (h₂0 : 0 ≤ c₂) (h₁ : c₁ ≤ a₁ + b₁)
    (h₂ : c₂ ≤ a₂ + b₂) :
    Real.sqrt (c₁ ^ 2 + c₂ ^ 2) ≤ Real.sqrt (a₁ ^ 2 + a₂ ^ 2) + Real.sqrt (b₁ ^ 2 + b₂ ^ 2) := by
  have := sqrt_sum_sq_le (Finset.univ : Finset (Fin 2)) (a := ![a₁, a₂]) (b := ![b₁, b₂])
    (c := ![c₁, c₂]) (fun i _ => by fin_cases i <;> simpa) (fun i _ => by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using this

theorem sqrt_sq_add_sq_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ a + b := by
  calc Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt ((a + b) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg ha hb])
    _ = a + b := Real.sqrt_sq (add_nonneg ha hb)

/-! ### Only the values on `V` matter -/

section Congr

variable {V : Set ℂ} {f f' : ℂ → ℂ}

theorem hasWeakDerivOn_congr_on {vs : List ℂ} {g : ℂ → ℂ} (hff' : ∀ x ∈ V, f x = f' x) :
    HasWeakDerivOn V vs f g ↔ HasWeakDerivOn V vs f' g := by
  have key : ∀ φ : ℂ → ℂ, IsTestFn V φ →
      ∫ x, f x * iterDirDeriv vs φ x = ∫ x, f' x * iterDirDeriv vs φ x := by
    intro φ hφ
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ V
    · simp only [hff' x hx]
    · simp only [testFn_eq_zero (hφ.iterDirDeriv vs) hx, mul_zero]
  exact ⟨fun h φ hφ => (key φ hφ).symm.trans (h φ hφ),
    fun h φ hφ => (key φ hφ).trans (h φ hφ)⟩

theorem weakDerivOn_congr_on {vs : List ℂ} (hff' : ∀ x ∈ V, f x = f' x) :
    weakDerivOn V vs f = weakDerivOn V vs f' := by
  have h : HasWeakDerivOn V vs f = HasWeakDerivOn V vs f' :=
    funext fun _ => propext (hasWeakDerivOn_congr_on hff')
  unfold weakDerivOn
  rw [h]

theorem weakPartialOn_congr_on (hff' : ∀ x ∈ V, f x = f' x) (γ : ℕ × ℕ) :
    weakPartialOn V γ f = weakPartialOn V γ f' :=
  weakDerivOn_congr_on hff'

theorem normHOn_congr_on (k : ℕ) (hff' : ∀ x ∈ V, f x = f' x) :
    normHOn k V f = normHOn k V f' := by
  unfold normHOn
  simp only [weakPartialOn_congr_on hff']

theorem memHOn_congr_on {k : ℕ} (hV : MeasurableSet V) (hff' : ∀ x ∈ V, f x = f' x)
    (hf : MemHOn k V f) : MemHOn k V f' := by
  refine ⟨hf.memLp.ae_eq ((ae_restrict_iff' hV).2 (Eventually.of_forall hff')), fun γ hγ => ?_⟩
  obtain ⟨g, hg, hfg⟩ := hf.deriv γ hγ
  exact ⟨g, hg, (hasWeakDerivOn_congr_on hff').1 hfg⟩

theorem gradNormOn_congr_on (hff' : ∀ x ∈ V, f x = f' x) : gradNormOn V f = gradNormOn V f' := by
  funext x
  unfold gradNormOn
  rw [weakPartialOn_congr_on hff', weakPartialOn_congr_on hff']

theorem memW1infOn_congr_on (hV : MeasurableSet V) (hff' : ∀ x ∈ V, f x = f' x)
    (hf : MemW1infOn V f) : MemW1infOn V f' := by
  refine ⟨hf.memLp.ae_eq ((ae_restrict_iff' hV).2 (Eventually.of_forall hff')), fun γ hγ => ?_⟩
  obtain ⟨g, hg, hgl, hfg⟩ := hf.deriv γ hγ
  exact ⟨g, hg, hgl, (hasWeakDerivOn_congr_on hff').1 hfg⟩

theorem normW1infOn_congr_on (hV : MeasurableSet V) (hff' : ∀ x ∈ V, f x = f' x) :
    normW1infOn V f = normW1infOn V f' := by
  unfold normW1infOn
  rw [gradNormOn_congr_on hff',
    eLpNorm_congr_ae ((ae_restrict_iff' hV).2 (Eventually.of_forall hff'))]

theorem weakDivOn_congr_on (hff' : ∀ x ∈ V, f x = f' x) : weakDivOn V f = weakDivOn V f' := by
  funext x
  unfold weakDivOn
  rw [weakPartialOn_congr_on hff', weakPartialOn_congr_on hff']

end Congr

/-! ### The chosen weak derivatives -/

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

/-- For `f ∈ W^{1,∞}(V)`, `V` open, the chosen first weak derivatives are `L^∞(V)`, locally
integrable, weak derivatives. -/
theorem memW1infOn_spec {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℂ} (hf : MemW1infOn V f)
    {γ : ℕ × ℕ} (hγ : γ ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ))) :
    MemLp (weakPartialOn V γ f) ⊤ (volume.restrict V) ∧
      LocallyIntegrableOn (weakPartialOn V γ f) V ∧
      HasWeakDerivOn V (pdList γ) f (weakPartialOn V γ f) := by
  obtain ⟨g, hg, hgl, hfg⟩ := hf.deriv γ hγ
  have hae := weakDerivOn_ae_eq hV hgl hfg
  obtain ⟨h1, h2⟩ := weakDerivOn_spec hgl hfg
  exact ⟨hg.ae_eq ((ae_restrict_iff' hV.measurableSet).2 (hae.mono fun x hx hxV => (hx hxV).symm)),
    h1, h2⟩

theorem mem_pair_left : ((1, 0) : ℕ × ℕ) ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ)) := by simp

theorem mem_pair_right : ((0, 1) : ℕ × ℕ) ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ)) := by simp

/-- `|∇f| ≤ |∂₁f| + |∂₂f|` pointwise. -/
theorem gradNormOn_le (V : Set ℂ) (f : ℂ → ℂ) (x : ℂ) :
    gradNormOn V f x ≤ ‖weakPartialOn V (1, 0) f x‖ + ‖weakPartialOn V (0, 1) f x‖ :=
  sqrt_sq_add_sq_le _ _ (norm_nonneg _) (norm_nonneg _)

theorem gradNormOn_nonneg (V : Set ℂ) (f : ℂ → ℂ) (x : ℂ) : 0 ≤ gradNormOn V f x :=
  Real.sqrt_nonneg _

/-- The gradient part of the `W^{1,∞}(V)` norm is finite. -/
theorem eLpNorm_gradNormOn_ne_top {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℂ}
    (hf : MemW1infOn V f) : eLpNorm (gradNormOn V f) ⊤ (volume.restrict V) ≠ ⊤ := by
  obtain ⟨a, -, -⟩ := memW1infOn_spec hV hf mem_pair_left
  obtain ⟨b, -, -⟩ := memW1infOn_spec hV hf mem_pair_right
  have ha := ae_norm_le_toReal_eLpNorm_top a.eLpNorm_ne_top
  have hb := ae_norm_le_toReal_eLpNorm_top b.eLpNorm_ne_top
  refine (toReal_eLpNorm_top_le
    (C := (eLpNorm (weakPartialOn V (1, 0) f) ⊤ (volume.restrict V)).toReal +
      (eLpNorm (weakPartialOn V (0, 1) f) ⊤ (volume.restrict V)).toReal)
    (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) ?_).1
  filter_upwards [ha, hb] with x hxa hxb
  rw [Real.norm_of_nonneg (gradNormOn_nonneg _ _ _)]
  exact (gradNormOn_le V f x).trans (add_le_add hxa hxb)

/-! ### Sums -/

/-- Minkowski for `H^k(V)`. -/
theorem memHOn_add {k : ℕ} {V : Set ℂ} (hV : IsOpen V) {F G : ℂ → ℂ} (hF : MemHOn k V F)
    (hG : MemHOn k V G) :
    MemHOn k V (F + G) ∧ normHOn k V (F + G) ≤ normHOn k V F + normHOn k V G := by
  have hd : ∀ γ ∈ multiIdx k,
      MemLp (weakPartialOn V γ F + weakPartialOn V γ G) 2 (volume.restrict V) ∧
      HasWeakDerivOn V (pdList γ) (F + G) (weakPartialOn V γ F + weakPartialOn V γ G) := by
    intro γ hγ
    obtain ⟨a2, ad⟩ := memHOn_spec hV hF hγ
    obtain ⟨b2, bd⟩ := memHOn_spec hV hG hγ
    exact ⟨a2.add b2, HasWeakDerivOn.add hV (locInt_of_memLp one_le_two hF.memLp)
      (locInt_of_memLp one_le_two hG.memLp) (locInt_of_memLp one_le_two a2)
      (locInt_of_memLp one_le_two b2) ad bd⟩
  refine ⟨⟨hF.memLp.add hG.memLp, fun γ hγ => ⟨_, hd γ hγ⟩⟩, ?_⟩
  unfold normHOn
  refine sqrt_sum_sq_le _ (fun γ _ => l2On_nonneg _ _) fun γ hγ => ?_
  have hae := weakDerivOn_ae_eq hV (locInt_of_memLp one_le_two (hd γ hγ).1) (hd γ hγ).2
  have e : l2On V (weakPartialOn V γ (F + G)) =
      l2On V (weakPartialOn V γ F + weakPartialOn V γ G) :=
    l2On_congr_ae hV.measurableSet hae
  obtain ⟨a2, -⟩ := memHOn_spec hV hF hγ
  obtain ⟨b2, -⟩ := memHOn_spec hV hG hγ
  rw [e]
  exact l2On_add_le a2 b2

/-- The first weak derivatives of a sum of `W^{1,∞}(V)` fields: membership, and the chosen
derivative of the sum is the sum of the chosen derivatives (a.e. on `V`). -/
theorem memW1infOn_add_deriv {V : Set ℂ} (hV : IsOpen V) {F G : ℂ → ℂ} (hF : MemW1infOn V F)
    (hG : MemW1infOn V G) {γ : ℕ × ℕ} (hγ : γ ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ))) :
    MemLp (weakPartialOn V γ F + weakPartialOn V γ G) ⊤ (volume.restrict V) ∧
      LocallyIntegrableOn (weakPartialOn V γ F + weakPartialOn V γ G) V ∧
      HasWeakDerivOn V (pdList γ) (F + G) (weakPartialOn V γ F + weakPartialOn V γ G) ∧
      ∀ᵐ x, x ∈ V → weakPartialOn V γ (F + G) x =
        weakPartialOn V γ F x + weakPartialOn V γ G x := by
  obtain ⟨a, al, ad⟩ := memW1infOn_spec hV hF hγ
  obtain ⟨b, bl, bd⟩ := memW1infOn_spec hV hG hγ
  have hl : LocallyIntegrableOn (weakPartialOn V γ F + weakPartialOn V γ G) V := al.add bl
  have hd := HasWeakDerivOn.add hV (locInt_of_memLp le_top hF.memLp)
    (locInt_of_memLp le_top hG.memLp) al bl ad bd
  exact ⟨a.add b, hl, hd, weakDerivOn_ae_eq hV hl hd⟩

/-- Minkowski for `W^{1,∞}(V)`. -/
theorem memW1infOn_add {V : Set ℂ} (hV : IsOpen V) {F G : ℂ → ℂ} (hF : MemW1infOn V F)
    (hG : MemW1infOn V G) :
    MemW1infOn V (F + G) ∧ normW1infOn V (F + G) ≤ normW1infOn V F + normW1infOn V G := by
  have hmem : MemW1infOn V (F + G) := by
    refine ⟨hF.memLp.add hG.memLp, fun γ hγ => ?_⟩
    obtain ⟨h1, h2, h3, -⟩ := memW1infOn_add_deriv hV hF hG hγ
    exact ⟨_, h1, h2, h3⟩
  refine ⟨hmem, ?_⟩
  set μ := volume.restrict V
  -- the `L^∞` part
  have hFt := hF.memLp.eLpNorm_ne_top
  have hGt := hG.memLp.eLpNorm_ne_top
  have h0 : (eLpNorm (F + G) ⊤ μ).toReal ≤ (eLpNorm F ⊤ μ).toReal + (eLpNorm G ⊤ μ).toReal := by
    rw [← ENNReal.toReal_add hFt hGt]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hFt, hGt⟩)
      (eLpNorm_add_le hF.memLp.1 hG.memLp.1 le_top)
  -- the gradient part
  obtain ⟨-, -, -, e1⟩ := memW1infOn_add_deriv hV hF hG mem_pair_left
  obtain ⟨-, -, -, e2⟩ := memW1infOn_add_deriv hV hF hG mem_pair_right
  have hpt : ∀ᵐ x ∂μ, ‖gradNormOn V (F + G) x‖ ≤ (gradNormOn V F + gradNormOn V G) x := by
    have e : ∀ᵐ x ∂μ, weakPartialOn V (1, 0) (F + G) x =
          weakPartialOn V (1, 0) F x + weakPartialOn V (1, 0) G x ∧
        weakPartialOn V (0, 1) (F + G) x =
          weakPartialOn V (0, 1) F x + weakPartialOn V (0, 1) G x := by
      refine (ae_restrict_iff' hV.measurableSet).2 ?_
      filter_upwards [e1, e2] with x hx1 hx2 hxV
      exact ⟨hx1 hxV, hx2 hxV⟩
    filter_upwards [e] with x ⟨hx1, hx2⟩
    rw [Real.norm_of_nonneg (gradNormOn_nonneg _ _ _), Pi.add_apply]
    unfold gradNormOn
    rw [hx1, hx2]
    exact sqrt_two_le (norm_nonneg _) (norm_nonneg _) (norm_add_le _ _) (norm_add_le _ _)
  have hFg := eLpNorm_gradNormOn_ne_top hV hF
  have hGg := eLpNorm_gradNormOn_ne_top hV hG
  have h1 : eLpNorm (gradNormOn V (F + G)) ⊤ μ ≤
      eLpNorm (gradNormOn V F) ⊤ μ + eLpNorm (gradNormOn V G) ⊤ μ := by
    refine (eLpNorm_mono_ae_real hpt).trans ?_
    simp only [eLpNorm_exponent_top]
    exact eLpNormEssSup_add_le
  have h1' : (eLpNorm (gradNormOn V (F + G)) ⊤ μ).toReal ≤
      (eLpNorm (gradNormOn V F) ⊤ μ).toReal + (eLpNorm (gradNormOn V G) ⊤ μ).toReal := by
    rw [← ENNReal.toReal_add hFg hGg]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hFg, hGg⟩) h1
  unfold normW1infOn
  linarith

/-- The weak divergence is additive (a.e. on `V`). -/
theorem weakDivOn_add {V : Set ℂ} (hV : IsOpen V) {F G : ℂ → ℂ} (hF : MemW1infOn V F)
    (hG : MemW1infOn V G) :
    ∀ᵐ x ∂(volume.restrict V), weakDivOn V (F + G) x = weakDivOn V F x + weakDivOn V G x := by
  obtain ⟨-, -, -, e1⟩ := memW1infOn_add_deriv hV hF hG mem_pair_left
  obtain ⟨-, -, -, e2⟩ := memW1infOn_add_deriv hV hF hG mem_pair_right
  refine (ae_restrict_iff' hV.measurableSet).2 ?_
  filter_upwards [e1, e2] with x hx1 hx2 hxV
  unfold weakDivOn
  rw [hx1 hxV, hx2 hxV, Complex.add_re, Complex.add_im]
  ring

/-! ### Classical fields -/

theorem pdList_one_zero' : pdList (1, 0) = [(1 : ℂ)] := rfl

theorem pdList_zero_one' : pdList (0, 1) = [Complex.I] := rfl

/-- For a `C¹` field on the open set `V`, the chosen first weak derivative in the direction `v`
is the classical one, a.e. on `V`. -/
theorem weakDerivOn_single_ae_eq {V : Set ℂ} (hV : IsOpen V) {U : ℂ → ℂ}
    (hU : ContDiffOn ℝ 1 U V) (v : ℂ) :
    ∀ᵐ x, x ∈ V → weakDerivOn V [v] U x = fderiv ℝ U x v := by
  have hw : HasWeakDerivOn V [v] U (iterDirDeriv [v] U) :=
    hasWeakDerivOn_of_contDiffOn hV (n := 1) (by simp) hU
  have hc : ContinuousOn (iterDirDeriv [v] U) V := by
    have : ContinuousOn (fun x => fderiv ℝ U x v) V :=
      (hU.continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const
    exact this
  exact weakDerivOn_ae_eq hV (hc.locallyIntegrableOn hV.measurableSet) hw

/-- For a `C¹` field on the open set `V`, the weak divergence is the classical one, a.e. on
`V`. -/
theorem weakDivOn_eq_divergence {V : Set ℂ} (hV : IsOpen V) {U : ℂ → ℂ}
    (hU : ContDiffOn ℝ 1 U V) :
    ∀ᵐ x ∂(volume.restrict V), weakDivOn V U x = Prelim.divergence U x := by
  have h1 := weakDerivOn_single_ae_eq hV hU 1
  have h2 := weakDerivOn_single_ae_eq hV hU Complex.I
  refine (ae_restrict_iff' hV.measurableSet).2 ?_
  filter_upwards [h1, h2] with x hx1 hx2 hxV
  unfold weakDivOn weakPartialOn
  rw [pdList_one_zero', pdList_zero_one', hx1 hxV, hx2 hxV, Prelim.divergence_eq]

end NonUniqueEuler.Sob.FieldBoundsAux
