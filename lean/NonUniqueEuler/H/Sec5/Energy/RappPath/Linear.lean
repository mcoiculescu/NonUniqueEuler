import NonUniqueEuler.H.Sec5.Energy.RappPath.Bridge
import NonUniqueEuler.I.Sec4.SemigroupConstruct
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec4.Sector

/-!
# Helpers for `R_app ∈ C([0,t];X^s)`: the term `L(G)w_app`

Helper of `P/Sec5/Energy/RappPath.lean` (`05_single_ring.tex:331`, "every term lies in
`C([0,t];H^s)`"). Namespace `NonUniqueEuler.OneRing.RappPathH`.

* `weakDerivOn_congr_ae` (copy of the proved helper of
  `H/Infra/AngularFourier/NormEquiv/Profile.lean`), `weakPartial_congr_ae`, `linFn_congr_ae`:
  the weak derivatives, hence `L(G)` on plane functions (`SectorSetting.linFn`: the transport part
  uses the weak angular derivative `Ang.thetaDeriv`, the coupling part is an integral), only see
  the a.e. class of the function;
* `toY_Lfn`, `memXFn_Lfn`: for `f ∈ X^{s+1}`, `toY s N (L(G)f) = Lin.L χ s G (toY (s+1) N f)`
  (`lem:semigroup-construct`(2), `semigroupConstruct_LinY`) and `L(G)f ∈ X^s` (`3`-fold symmetry
  from `linFn_rot`, `lem:sector`(2));
* `pathC_Lfn`: `L(G)` maps `C([0,T];X^{s+1})` to `C([0,T];X^s)` (a bounded operator).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.RappPathH

open RingData Sect Sob

/-- Weak derivatives on `V` only depend on the function a.e. on `V` (copy of
`Ang.NormEquivAux.weakDerivOn_congr_ae`). -/
theorem weakDerivOn_congr_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] {V : Set E} {vs : List E} {f f' : E → ℂ}
    (hfg : ∀ᵐ x, x ∈ V → f x = f' x) :
    weakDerivOn V vs f = weakDerivOn V vs f' := by
  have key : HasWeakDerivOn V vs f = HasWeakDerivOn V vs f' := by
    funext g
    have hI : ∀ φ : E → ℂ, IsTestFn V φ →
        ∫ x, f x * iterDirDeriv vs φ x = ∫ x, f' x * iterDirDeriv vs φ x := by
      intro φ hφ
      refine integral_congr_ae ?_
      filter_upwards [hfg] with x hx
      by_cases hxV : x ∈ V
      · rw [hx hxV]
      · have : iterDirDeriv vs φ x = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hxV ((hφ.iterDirDeriv vs).subset h)
        rw [this, mul_zero, mul_zero]
    apply propext
    constructor
    · intro H φ hφ
      rw [← hI φ hφ]
      exact H φ hφ
    · intro H φ hφ
      rw [hI φ hφ]
      exact H φ hφ
  unfold weakDerivOn
  rw [key]

/-- The weak partial derivatives only depend on the a.e. class. -/
theorem weakPartial_congr_ae (γ : ℕ × ℕ) {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    weakPartial γ f = weakPartial γ g := by
  unfold weakPartial weakPartialOn
  refine weakDerivOn_congr_ae ?_
  filter_upwards [h] with x hx _ using hx

/-- `L(G)` on plane functions only depends on the a.e. class. -/
theorem linFn_congr_ae (S : SectorSetting) (G : ℝ) {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    S.linFn G f = S.linFn G g := by
  funext x
  have hθ : Ang.thetaDeriv f x = Ang.thetaDeriv g x := by
    simp only [Ang.thetaDeriv, weakPartial_congr_ae _ h]
  have hc : S.couplingFn f x = S.couplingFn g x := by
    simp only [SectorSetting.couplingFn]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [h] with y hy
    rw [hy]
  simp only [SectorSetting.linFn, SectorSetting.transportPartFn, hθ, hc]

theorem Lfn_congr_ae (χ : ℝ → ℝ) (G : ℝ) {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    Lin.Lfn χ G f = Lin.Lfn χ G g :=
  linFn_congr_ae _ G h

/-- The operator `Lin.L χ s G` acts on functions by `L(G)`. -/
theorem L_fn (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (s : ℕ) (G : ℝ)
    (w : Y (s + 1) annN) : (Lin.L χ s G w).fn =ᵐ[volume] Lin.Lfn χ G w.fn :=
  SectorSetting.LinY_spec_of_exists (ringPhiSetting χ) s G
    (SectorSetting.semigroupConstruct_LinY (ringPhiSetting χ) (ringPhiSetting_valid hχ) s G) w

/-- For `f ∈ X^{s+1}`, the function of `Lin.L χ s G (toY (s+1) N f)` is `L(G)f` (a.e.). -/
theorem L_toY_fn (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {s : ℕ} (G : ℝ) {f : ℂ → ℂ}
    (hf : Lin.MemXFn (s + 1) f) :
    (Lin.L χ s G (toY (s + 1) annN f)).fn =ᵐ[volume] Lin.Lfn χ G f := by
  have h := L_fn χ hχ s G (toY (s + 1) annN f)
  rwa [Lfn_congr_ae χ G (toY_fn hf)] at h

/-- **`L(G)` maps `X^{s+1}` into `X^s`.** -/
theorem memXFn_Lfn (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {s : ℕ} (G : ℝ) {f : ℂ → ℂ}
    (hf : Lin.MemXFn (s + 1) f) : Lin.MemXFn s (Lin.Lfn χ G f) := by
  set y : Y (s + 1) annN := toY (s + 1) annN f with hydef
  have hyf : y.fn =ᵐ[volume] f := toY_fn hf
  have hL := L_toY_fn χ hχ G hf
  have hLy := Y_memH_fn (Lin.L χ s G y)
  refine ⟨(hLy.1.congr_ae hL).1, ?_, ?_⟩
  · filter_upwards [Y_fn_zero_outside (Lin.L χ s G y), hL] with x h1 h2 hx
    rw [← h2]
    exact h1 hx
  · -- `3`-fold symmetry: `L(G)` commutes with rotations (`lem:sector`(2))
    set φ : ℝ := 2 * Real.pi / ((3 : ℕ) : ℝ) with hφ
    have hrot := SectorSetting.linFn_rot (ringPhiSetting χ) (ringPhiSetting_valid hχ) s G y φ
    have hyrot : (fun x => y.fn (rot φ x)) =ᵐ[volume] y.fn := by
      have h1 : (fun x => y.fn (rot φ x)) =ᵐ[volume] fun x => f (rot φ x) :=
        (Polar.measurePreserving_rot φ).quasiMeasurePreserving.ae_eq_comp hyf
      exact h1.trans ((hf.2.2 : (fun x => f (rot φ x)) =ᵐ[volume] f).trans hyf.symm)
    have hLf : (ringPhiSetting χ).linFn G y.fn = Lin.Lfn χ G f := Lfn_congr_ae χ G hyf
    have h2 : (ringPhiSetting χ).linFn G (fun x => y.fn (rot φ x)) =
        (ringPhiSetting χ).linFn G y.fn := linFn_congr_ae _ G hyrot
    have hrot' : ((ringPhiSetting χ).linFn G fun x => y.fn (rot φ x)) =ᵐ[volume]
        fun x => (ringPhiSetting χ).linFn G y.fn (rot φ x) := hrot
    rw [h2, hLf] at hrot'
    exact hrot'.symm

/-- **`toY s N (L(G)f) = L(G)(toY (s+1) N f)`** for `f ∈ X^{s+1}`. -/
theorem toY_Lfn (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {s : ℕ} (G : ℝ) {f : ℂ → ℂ}
    (hf : Lin.MemXFn (s + 1) f) :
    toY s annN (Lin.Lfn χ G f) = Lin.L χ s G (toY (s + 1) annN f) := by
  have hL := L_toY_fn χ hχ G hf
  rw [← toY_congr_ae hL, toY_fn_self]

/-- **`L(G)` maps `C([0,T];X^{s+1})` to `C([0,T];X^s)`.** -/
theorem pathC_Lfn (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {s : ℕ} (G : ℝ) {T : ℝ}
    {u : ℝ → ℂ → ℂ} (hu : PathC (s + 1) T u) :
    PathC s T (fun τ => Lin.Lfn χ G (u τ)) := by
  refine ⟨fun τ hτ => memXFn_Lfn χ hχ G (hu.1 τ hτ), ?_⟩
  have hc : ContinuousOn (fun τ => Lin.L χ s G (toY (s + 1) annN (u τ))) (Icc (0 : ℝ) T) :=
    (Lin.L χ s G).continuous.comp_continuousOn hu.2
  refine hc.congr fun τ hτ => ?_
  exact toY_Lfn χ hχ G (hu.1 τ hτ)

end NonUniqueEuler.OneRing.RappPathH
