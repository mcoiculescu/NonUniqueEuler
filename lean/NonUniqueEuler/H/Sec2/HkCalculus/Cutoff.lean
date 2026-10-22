import NonUniqueEuler.H.Sec2.HkCalculus.Basic
import NonUniqueEuler.H.Sec2.HkCalculus.ReIm
import NonUniqueEuler.I.Infra.Sobolev.Leibniz

/-!
# Helper for `P/Sec2/HkCalculus`: the cut-off field `Ũ = χ_N U` (proof of `lem:Hk-calculus`(1))

`02_prelim.tex:690-696, 735-745`. Generic facts used for `Ũ = χ_N U`:
* `eLpNorm_weakPartial_re_le`, `eLpNorm_weakPartial_im_le`: for `Ũ ∈ W^{1,∞}(ℝ²)`, the first weak
  derivatives of `Re Ũ`, `Im Ũ` are bounded in `L^∞` by `‖Ũ‖_{W^{1,∞}}`;
* `dotGrad_ae_eq_of_eqOn`, `indicator_dotGrad_ae_eq_of_eqOn`: `U·∇f = Ũ·∇f` a.e. when `Ũ = U` on a
  neighborhood `V` of `N` and `∇f = 0` a.e. outside `N` ("the commutator is unchanged");
* `weakDivOn_univ_ae_eq_zero`: `div Ũ = 0` a.e. on `N` when `div U = 0` on `N₁` and `Ũ = U` on
  `V ⊇ N`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Sob.HkCalcAux

theorem mem_firstIdx {β : ℕ × ℕ} (h : β.1 + β.2 = 1) :
    β ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ)) := by
  rcases β with ⟨a, b⟩
  simp only at h
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp only [zero_add] at h; subst h; simp
  · have hb : b = 0 := by omega
    have ha' : a = 1 := by omega
    subst hb; subst ha'; simp

/-- The chosen first weak derivatives of a `W^{1,∞}(V)` field are weak derivatives, locally
integrable on `V`, and essentially bounded (a.e. equal to the given bounded ones). -/
theorem w1inf_deriv_spec {V : Set ℂ} (hV : IsOpen V) {U : ℂ → ℂ} (hU : MemW1infOn V U)
    {e : ℕ × ℕ} (he : e ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ))) :
    LocallyIntegrableOn (weakPartialOn V e U) V ∧
      HasWeakDerivOn V (pdList e) U (weakPartialOn V e U) ∧
      eLpNorm (weakPartialOn V e U) ⊤ (volume.restrict V) < ⊤ := by
  obtain ⟨G, hGinf, hGloc, hGD⟩ := hU.deriv e he
  obtain ⟨h1, h2⟩ := weakDerivOn_spec hGloc hGD
  refine ⟨h1, h2, ?_⟩
  have h3 := weakDerivOn_ae_eq hV hGloc hGD
  have h4 : weakPartialOn V e U =ᵐ[volume.restrict V] G :=
    (ae_restrict_iff' hV.measurableSet).2 h3
  rw [eLpNorm_congr_ae h4]
  exact hGinf.2

theorem gradNormOn_ge {V : Set ℂ} {U : ℂ → ℂ} {e : ℕ × ℕ}
    (he : e ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ))) (x : ℂ) :
    ‖weakPartialOn V e U x‖ ≤ gradNormOn V U x := by
  unfold gradNormOn
  refine Real.le_sqrt_of_sq_le ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · nlinarith [sq_nonneg ‖weakPartialOn V (0, 1) U x‖]
  · nlinarith [sq_nonneg ‖weakPartialOn V (1, 0) U x‖]

/-- `ess sup |∇Ũ| < ∞` for `Ũ ∈ W^{1,∞}(ℝ²)`. -/
theorem w1inf_gradNorm_lt_top {U : ℂ → ℂ} (hU : MemW1infOn univ U) :
    eLpNorm (gradNormOn univ U) ⊤ volume < ⊤ := by
  have hd1 := w1inf_deriv_spec isOpen_univ hU (e := (1, 0)) (by simp)
  have hd2 := w1inf_deriv_spec isOpen_univ hU (e := (0, 1)) (by simp)
  rw [Measure.restrict_univ] at hd1 hd2
  have hm1 : AEStronglyMeasurable (weakPartialOn univ (1, 0) U) volume :=
    ((locallyIntegrableOn_univ.1 hd1.1).aestronglyMeasurable)
  have hm2 : AEStronglyMeasurable (weakPartialOn univ (0, 1) U) volume :=
    ((locallyIntegrableOn_univ.1 hd2.1).aestronglyMeasurable)
  have hle : ∀ x, ‖gradNormOn univ U x‖ ≤
      ‖weakPartialOn univ (1, 0) U x‖ + ‖weakPartialOn univ (0, 1) U x‖ := by
    intro x
    unfold gradNormOn
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_left]
    · nlinarith [norm_nonneg (weakPartialOn univ (1, 0) U x),
        norm_nonneg (weakPartialOn univ (0, 1) U x)]
    · positivity
  calc eLpNorm (gradNormOn univ U) ⊤ volume ≤
        eLpNorm (fun x => ‖weakPartialOn univ (1, 0) U x‖ + ‖weakPartialOn univ (0, 1) U x‖)
          ⊤ volume := eLpNorm_mono_real hle
    _ ≤ eLpNorm (fun x => ‖weakPartialOn univ (1, 0) U x‖) ⊤ volume +
          eLpNorm (fun x => ‖weakPartialOn univ (0, 1) U x‖) ⊤ volume :=
        eLpNorm_add_le hm1.norm hm2.norm le_top
    _ < ⊤ := by
        rw [eLpNorm_norm, eLpNorm_norm]
        exact ENNReal.add_lt_top.2 ⟨hd1.2.2, hd2.2.2⟩

theorem locallyIntegrableOn_univ_of_W1inf {U : ℂ → ℂ} (hU : MemW1infOn univ U) :
    LocallyIntegrableOn U univ := by
  have h := hU.memLp
  rw [Measure.restrict_univ] at h
  exact (h.locallyIntegrable le_top).locallyIntegrableOn univ

/-- The common step: the first weak derivatives of `L Ũ` (`L = Re` or `Im`) are bounded by
`‖Ũ‖_{W^{1,∞}}` in `L^∞`. -/
theorem eLpNorm_weakPartial_reim_le {U : ℂ → ℂ} (hU : MemW1infOn univ U)
    (L : ℂ → ℂ) (hL : ∀ z, ‖L z‖ ≤ ‖z‖)
    (hLD : ∀ e ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ)),
      weakPartial e (fun x => L (U x)) =ᵐ[volume] fun x => L (weakPartialOn univ e U x))
    {β : ℕ × ℕ} (hβ : β.1 + β.2 = 1) :
    eLpNorm (weakPartial β (fun x => L (U x))) ⊤ volume ≤
      ENNReal.ofReal (normW1infOn univ U) := by
  have he := mem_firstIdx hβ
  rw [eLpNorm_congr_ae (hLD β he)]
  have h1 : eLpNorm (fun x => L (weakPartialOn univ β U x)) ⊤ volume ≤
      eLpNorm (gradNormOn univ U) ⊤ volume := by
    refine eLpNorm_mono_real fun x => ?_
    exact (hL _).trans (gradNormOn_ge he x)
  refine h1.trans ?_
  rw [← ENNReal.ofReal_toReal (w1inf_gradNorm_lt_top hU).ne]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold normW1infOn
  rw [Measure.restrict_univ]
  linarith [ENNReal.toReal_nonneg (a := eLpNorm U ⊤ volume)]

theorem weakPartial_re_ae_eq {U : ℂ → ℂ} (hU : MemW1infOn univ U) {e : ℕ × ℕ}
    (he : e ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ))) :
    weakPartial e (fun x => ((U x).re : ℂ)) =ᵐ[volume]
      fun x => ((weakPartialOn univ e U x).re : ℂ) := by
  obtain ⟨h1, h2, -⟩ := w1inf_deriv_spec isOpen_univ hU he
  have h3 := hasWeakDerivOn_re isOpen_univ (locallyIntegrableOn_univ_of_W1inf hU) h1 h2
  have h4 := weakDerivOn_ae_eq isOpen_univ (locInt_re h1) h3
  filter_upwards [h4] with x hx
  exact hx (mem_univ x)

theorem weakPartial_im_ae_eq {U : ℂ → ℂ} (hU : MemW1infOn univ U) {e : ℕ × ℕ}
    (he : e ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ))) :
    weakPartial e (fun x => ((U x).im : ℂ)) =ᵐ[volume]
      fun x => ((weakPartialOn univ e U x).im : ℂ) := by
  obtain ⟨h1, h2, -⟩ := w1inf_deriv_spec isOpen_univ hU he
  have hU' := locallyIntegrableOn_univ_of_W1inf hU
  -- `Im z = Re (-i z)`
  have h2' := h2.const_mul (-Complex.I)
  have h3 : HasWeakDerivOn univ (pdList e) (fun x => ((U x).im : ℂ))
      (fun x => ((weakPartialOn univ e U x).im : ℂ)) :=
    (hasWeakDerivOn_re isOpen_univ (locInt_clm hU' ((-Complex.I) • 1))
      (locInt_clm h1 ((-Complex.I) • 1)) h2').congr_ae
      (Filter.Eventually.of_forall fun x _ => by simp)
      (Filter.Eventually.of_forall fun x _ => by simp)
  have h4 := weakDerivOn_ae_eq isOpen_univ (locInt_im h1) h3
  filter_upwards [h4] with x hx
  exact hx (mem_univ x)

/-- `‖∂_e Re Ũ‖_{L^∞} ≤ ‖Ũ‖_{W^{1,∞}}` for `|e| = 1`. -/
theorem eLpNorm_weakPartial_re_le {U : ℂ → ℂ} (hU : MemW1infOn univ U) {β : ℕ × ℕ}
    (hβ : β.1 + β.2 = 1) :
    eLpNorm (weakPartial β (fun x => ((U x).re : ℂ))) ⊤ volume ≤
      ENNReal.ofReal (normW1infOn univ U) :=
  eLpNorm_weakPartial_reim_le hU (fun z => (z.re : ℂ))
    (fun z => by rw [Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_re_le_norm z)
    (fun _ he => weakPartial_re_ae_eq hU he) hβ

/-- `‖∂_e Im Ũ‖_{L^∞} ≤ ‖Ũ‖_{W^{1,∞}}` for `|e| = 1`. -/
theorem eLpNorm_weakPartial_im_le {U : ℂ → ℂ} (hU : MemW1infOn univ U) {β : ℕ × ℕ}
    (hβ : β.1 + β.2 = 1) :
    eLpNorm (weakPartial β (fun x => ((U x).im : ℂ))) ⊤ volume ≤
      ENNReal.ofReal (normW1infOn univ U) :=
  eLpNorm_weakPartial_reim_le hU (fun z => (z.im : ℂ))
    (fun z => by rw [Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_im_le_norm z)
    (fun _ he => weakPartial_im_ae_eq hU he) hβ

/-! ### Changing the field away from the support -/

theorem dotGrad_ae_eq_of_eqOn {U U' f : ℂ → ℂ} {N V : Set ℂ} (hNV : N ⊆ V)
    (hUV : ∀ x ∈ V, U' x = U x) (h1 : ∀ᵐ x, x ∉ N → weakPartial (1, 0) f x = 0)
    (h2 : ∀ᵐ x, x ∉ N → weakPartial (0, 1) f x = 0) :
    dotGrad U f =ᵐ[volume] dotGrad U' f := by
  filter_upwards [h1, h2] with x hx1 hx2
  by_cases hx : x ∈ V
  · simp [dotGrad, hUV x hx]
  · have hxN : x ∉ N := fun h => hx (hNV h)
    simp [dotGrad, hx1 hxN, hx2 hxN]

theorem indicator_dotGrad_ae_eq_of_eqOn {U U' f : ℂ → ℂ} {N V N₁ : Set ℂ} (hNV : N ⊆ V)
    (hVN₁ : V ⊆ N₁) (hUV : ∀ x ∈ V, U' x = U x)
    (h1 : ∀ᵐ x, x ∉ N → weakPartial (1, 0) f x = 0)
    (h2 : ∀ᵐ x, x ∉ N → weakPartial (0, 1) f x = 0) :
    N₁.indicator (dotGrad U f) =ᵐ[volume] dotGrad U' f := by
  filter_upwards [h1, h2] with x hx1 hx2
  by_cases hx : x ∈ V
  · rw [indicator_of_mem (hVN₁ hx)]
    simp [dotGrad, hUV x hx]
  · have hxN : x ∉ N := fun h => hx (hNV h)
    by_cases hx' : x ∈ N₁
    · rw [indicator_of_mem hx']
      simp [dotGrad, hx1 hxN, hx2 hxN]
    · rw [indicator_of_notMem hx']
      simp [dotGrad, hx1 hxN, hx2 hxN]

/-- The weak derivatives of `Ũ` on the plane and of `U` on `N₁` agree a.e. on `V`, where
`Ũ = U`. -/
theorem weakPartialOn_ae_eq_of_eqOn {N₁ V : Set ℂ} (hN₁ : IsOpen N₁) (hV : IsOpen V)
    (hVN₁ : V ⊆ N₁) {U U' : ℂ → ℂ} (hUV : ∀ x ∈ V, U' x = U x) (hU : MemW1infOn N₁ U)
    (hU' : MemW1infOn univ U') {e : ℕ × ℕ}
    (he : e ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ))) :
    ∀ᵐ x, x ∈ V → weakPartialOn univ e U' x = weakPartialOn N₁ e U x := by
  obtain ⟨h1, h2, -⟩ := w1inf_deriv_spec isOpen_univ hU' he
  obtain ⟨h3, h4, -⟩ := w1inf_deriv_spec hN₁ hU he
  have h2' : HasWeakDerivOn V (pdList e) U (weakPartialOn univ e U') :=
    (h2.mono (subset_univ V)).congr_ae (Filter.Eventually.of_forall fun x hx => hUV x hx)
      (Filter.Eventually.of_forall fun _ _ => rfl)
  exact HasWeakDerivOn.ae_eq hV (h1.mono_set (subset_univ V)) (h3.mono_set hVN₁) h2'
    (h4.mono hVN₁)

theorem weakDivOn_univ_ae_eq_zero {N N₁ V : Set ℂ} (hN₁ : IsOpen N₁) (hV : IsOpen V)
    (hNV : N ⊆ V) (hVN₁ : V ⊆ N₁) {U U' : ℂ → ℂ} (hUV : ∀ x ∈ V, U' x = U x)
    (hU : MemW1infOn N₁ U) (hU' : MemW1infOn univ U')
    (hdiv : ∀ᵐ x ∂(volume.restrict N₁), weakDivOn N₁ U x = 0) :
    ∀ᵐ x, x ∈ N → weakDivOn univ U' x = 0 := by
  have h1 := weakPartialOn_ae_eq_of_eqOn hN₁ hV hVN₁ hUV hU hU' (e := (1, 0)) (by simp)
  have h2 := weakPartialOn_ae_eq_of_eqOn hN₁ hV hVN₁ hUV hU hU' (e := (0, 1)) (by simp)
  have h3 := (ae_restrict_iff' hN₁.measurableSet).1 hdiv
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3 hxN
  have hxV := hNV hxN
  unfold weakDivOn
  rw [hx1 hxV, hx2 hxV]
  exact hx3 (hVN₁ hxV)

end NonUniqueEuler.Sob.HkCalcAux
