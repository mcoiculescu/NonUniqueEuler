import NonUniqueEuler.H.Sec5.Window.Approx.Bridge
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Sec4.SemigroupConstruct
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec4.Sector
import NonUniqueEuler.I.Sec5.Bilinear

/-!
# Helpers for `window_approx`: the operators `L(G)`, `B`, `h·∇` on plane functions

Helper of `P/Sec5/Window/Approx.lean` (`05_single_ring.tex:747-798`). Namespace
`NonUniqueEuler.OneRing.WAppH`. Several lemmas are copies (renamed into this namespace) of the
proved helpers `H/Sec5/Energy/RappPath/Linear.lean`, `H/Sec5/Energy/RappPath/Bilin.lean`,
`H/Sec5/Energy/RappPath/Terms.lean` and of `P/Infra/Sobolev/ReIm.lean` (`ReImAux`), which a proof
file may not import (import rules, `README.md`).

* `L(G)` on functions: `Lfn_congr_ae`, `L_fn`, `L_toY_fn`, `memXFn_Lfn`, `toY_Lfn`, `pathC_Lfn`,
  and the a.e. additivity `Lfn_add_ae`;
* bilinearity a.e.: `Bfn_sub_left_ae`, `Bfn_sub_right_ae`, `Bfn_diff_ae`, `Bfn_diff2_ae`,
  `hGrad_diff_ae`, `hGrad_add_ae`, `Bfn_zero_left`;
* realness: `weakPartial_im_ae` (weak derivatives of real functions are real), `Bfn_im_ae`,
  `hGrad_im_ae`, `forcing_im_ae`;
* paths: `pathC_Bfn2` (`B(u,v)` for two paths), `pathC_hGrad`, `pathC_hGradPhi`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate ContDiff

namespace NonUniqueEuler.OneRing.WAppH

open RingData Sect Sob

/-! ### `L(G)` on plane functions -/

/-- Weak derivatives on `V` only depend on the function a.e. on `V` (copy of
`RappPathH.weakDerivOn_congr_ae`). -/
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
  rwa [Lfn_congr_ae χ G (MemXFn.toY_fn hf)] at h

/-- The function of an element of `Y^s(N)` vanishes a.e. outside `N`. -/
theorem Y_fn_zero_outside {s : ℕ} (w : Y s annN) :
    ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → w.fn x = 0 := by
  have h2 : suppCLM s annN (w : SobTuple s) = 0 := by
    have := (Submodule.mem_inf.1 w.2).2
    rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at this
  rw [Lp.eq_zero_iff_ae_eq_zero] at h2
  have h1 := LpToLpRestrictCLM_coeFn ℂ annNᶜ (proj0 s (w : SobTuple s))
  have h4 : w.fn =ᵐ[(volume : Measure ℂ).restrict annNᶜ] 0 := h1.symm.trans h2
  rw [EventuallyEq, ae_restrict_iff' measurableSet_annN.compl] at h4
  filter_upwards [h4] with x hx hxN
  exact hx hxN

/-- **`L(G)` maps `X^{s+1}` into `X^s`** (copy of `RappPathH.memXFn_Lfn`). -/
theorem memXFn_Lfn (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {s : ℕ} (G : ℝ) {f : ℂ → ℂ}
    (hf : Lin.MemXFn (s + 1) f) : Lin.MemXFn s (Lin.Lfn χ G f) := by
  set y : Y (s + 1) annN := toY (s + 1) annN f with hydef
  have hyf : y.fn =ᵐ[volume] f := MemXFn.toY_fn hf
  have hL := L_toY_fn χ hχ G hf
  have hLy := Y_memH_fn (Lin.L χ s G y)
  refine ⟨(hLy.1.congr_ae hL).1, ?_, ?_⟩
  · filter_upwards [Y_fn_zero_outside (Lin.L χ s G y), hL] with x h1 h2 hx
    rw [← h2]
    exact h1 hx
  · set φ : ℝ := 2 * Real.pi / ((3 : ℕ) : ℝ) with hφ
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

/-- **`L(G)(f + g) = L(G)f + L(G)g` a.e.** for `f, g ∈ X^{s+1}`. -/
theorem Lfn_add_ae (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {s : ℕ} (G : ℝ) {f g : ℂ → ℂ}
    (hf : Lin.MemXFn (s + 1) f) (hg : Lin.MemXFn (s + 1) g) :
    Lin.Lfn χ G (f + g) =ᵐ[volume] Lin.Lfn χ G f + Lin.Lfn χ G g := by
  have hLf := memXFn_Lfn χ hχ G hf
  have hLg := memXFn_Lfn χ hχ G hg
  have hLfg := memXFn_Lfn χ hχ G (MemXFn.add hf hg)
  have heq : toY s annN (Lin.Lfn χ G (f + g)) =
      toY s annN (Lin.Lfn χ G f + Lin.Lfn χ G g) := by
    rw [toY_add' hLf hLg, toY_Lfn χ hχ G (MemXFn.add hf hg), toY_add' hf hg, map_add,
      toY_Lfn χ hχ G hf, toY_Lfn χ hχ G hg]
  have h1 := MemXFn.toY_fn hLfg
  have h2 := MemXFn.toY_fn (MemXFn.add hLf hLg)
  rw [heq] at h1
  exact h1.symm.trans h2

/-! ### Bilinearity a.e. -/

/-- Linearity of the chosen weak derivatives of `H^k` functions (copy of
`RappPathH.weakPartial_add_ae_eq`). -/
theorem weakPartial_add_ae_eq {k : ℕ} {f g : ℂ → ℂ} (hf : MemH k f) (hg : MemH k g)
    {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    weakPartial γ (f + g) =ᵐ[volume] weakPartial γ f + weakPartial γ g := by
  obtain ⟨hfm, hfd⟩ := MemH.memLp_weakPartial hf hγ
  obtain ⟨hgm, hgd⟩ := MemH.memLp_weakPartial hg hγ
  have hf0 : MemLp f 2 volume := (memH_iff.1 hf).1
  have hg0 : MemLp g 2 volume := (memH_iff.1 hg).1
  have hli : ∀ {u : ℂ → ℂ}, MemLp u 2 volume → LocallyIntegrableOn u univ := fun hu =>
    (hu.locallyIntegrable (by norm_num)).locallyIntegrableOn univ
  have hs := HasWeakDerivOn.add isOpen_univ (hli hf0) (hli hg0) (hli hfm) (hli hgm) hfd hgd
  exact MemH.weakPartial_ae_eq (hf.add hg).1 hγ (hfm.add hgm) hs

theorem weakPartial_sub_ae_eq {k : ℕ} {f g : ℂ → ℂ} (hf : MemH k f) (hg : MemH k g)
    {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    weakPartial γ (f - g) =ᵐ[volume] weakPartial γ f - weakPartial γ g := by
  have h := weakPartial_add_ae_eq (hf.sub hg).1 hg hγ
  rw [sub_add_cancel] at h
  filter_upwards [h] with x hx
  simp only [Pi.add_apply, Pi.sub_apply] at hx ⊢
  rw [hx]
  ring

theorem idx10_mem : ((1 : ℕ), (0 : ℕ)) ∈ multiIdx 1 := mem_multiIdx.2 (by simp)

theorem idx01_mem : ((0 : ℕ), (1 : ℕ)) ∈ multiIdx 1 := mem_multiIdx.2 (by simp)

theorem dotGrad_sub_right_ae (U : ℂ → ℂ) {w₁ w₂ : ℂ → ℂ} (h₁ : MemH 1 w₁) (h₂ : MemH 1 w₂) :
    dotGrad U (w₁ - w₂) =ᵐ[volume] dotGrad U w₁ - dotGrad U w₂ := by
  filter_upwards [weakPartial_sub_ae_eq h₁ h₂ idx10_mem, weakPartial_sub_ae_eq h₁ h₂ idx01_mem]
    with x hx1 hx2
  simp only [dotGrad, Pi.sub_apply] at hx1 hx2 ⊢
  rw [hx1, hx2]
  ring

theorem dotGrad_add_right_ae (U : ℂ → ℂ) {w₁ w₂ : ℂ → ℂ} (h₁ : MemH 1 w₁) (h₂ : MemH 1 w₂) :
    dotGrad U (w₁ + w₂) =ᵐ[volume] dotGrad U w₁ + dotGrad U w₂ := by
  filter_upwards [weakPartial_add_ae_eq h₁ h₂ idx10_mem, weakPartial_add_ae_eq h₁ h₂ idx01_mem]
    with x hx1 hx2
  simp only [dotGrad, Pi.add_apply] at hx1 hx2 ⊢
  rw [hx1, hx2]
  ring

theorem dotGrad_sub_left (U₁ U₂ w : ℂ → ℂ) :
    dotGrad (U₁ - U₂) w = dotGrad U₁ w - dotGrad U₂ w := by
  funext x
  simp only [dotGrad, Pi.sub_apply, Complex.sub_re, Complex.sub_im]
  push_cast
  ring

theorem hGrad_sub_field (h₁ h₂ g : ℂ → ℂ) :
    hGrad h₁ g - hGrad h₂ g = hGrad (h₁ - h₂) g := by
  simp only [hGrad, dotGrad_sub_left]

/-- An `X^0` function lies in `L¹`. -/
theorem memLp_one_of_memXFn {v : ℂ → ℂ} (hv : Lin.MemXFn 0 v) : MemLp v 1 volume := by
  have h2 : MemLp v 2 volume := (memH_iff.1 hv.1).1
  set v' : ℂ → ℂ := annN.indicator v with hv'def
  have hvv' : v =ᵐ[volume] v' := by
    filter_upwards [hv.2.1] with x hx
    by_cases hxN : x ∈ annN
    · rw [hv'def, indicator_of_mem hxN]
    · rw [hv'def, indicator_of_notMem hxN, hx hxN]
  have h2' : MemLp v' 2 volume := h2.ae_eq hvv'
  have hfin : (volume : Measure ℂ) annN ≠ ⊤ :=
    (isCompact_closedAnnulus _ _).measure_lt_top.ne
  have h1' : MemLp v' 1 volume :=
    h2'.mono_exponent_of_measure_support_ne_top (s := annN)
      (fun x hx => by rw [hv'def, indicator_of_notMem hx]) hfin (by norm_num)
  exact h1'.ae_eq hvv'.symm

theorem velocity_sub_ae {g₁ g₂ : ℂ → ℝ} (h₁ : MemLp g₁ 1 volume) (h₂ : MemLp g₂ 1 volume) :
    ∀ᵐ x ∂(volume : Measure ℂ),
      velocity (fun y => g₁ y - g₂ y) x = velocity g₁ x - velocity g₂ x := by
  filter_upwards [BS.ae_integrable_biotSavart_of_L1 h₁, BS.ae_integrable_biotSavart_of_L1 h₂]
    with x hx1 hx2
  simp only [velocity]
  rw [← integral_sub hx1 hx2]
  congr 1
  funext y
  push_cast
  ring

theorem velocityRe_sub_ae {v₁ v₂ : ℂ → ℂ} (h₁ : Lin.MemXFn 0 v₁) (h₂ : Lin.MemXFn 0 v₂) :
    ∀ᵐ x ∂(volume : Measure ℂ),
      BS.velocityRe (v₁ - v₂) x = BS.velocityRe v₁ x - BS.velocityRe v₂ x := by
  have h := velocity_sub_ae (memLp_one_of_memXFn h₁).re (memLp_one_of_memXFn h₂).re
  filter_upwards [h] with x hx
  simp only [BS.velocityRe, Pi.sub_apply, Complex.sub_re]
  exact hx

theorem velocityIm_sub_ae {v₁ v₂ : ℂ → ℂ} (h₁ : Lin.MemXFn 0 v₁) (h₂ : Lin.MemXFn 0 v₂) :
    ∀ᵐ x ∂(volume : Measure ℂ),
      BS.velocityIm (v₁ - v₂) x = BS.velocityIm v₁ x - BS.velocityIm v₂ x := by
  have h := velocity_sub_ae (memLp_one_of_memXFn h₁).im (memLp_one_of_memXFn h₂).im
  filter_upwards [h] with x hx
  simp only [BS.velocityIm, Pi.sub_apply, Complex.sub_im]
  exact hx

/-- `B(v₁ - v₂, w) = B(v₁, w) - B(v₂, w)` a.e. for `v₁, v₂ ∈ X^0`. -/
theorem Bfn_sub_left_ae {v₁ v₂ : ℂ → ℂ} (h₁ : Lin.MemXFn 0 v₁) (h₂ : Lin.MemXFn 0 v₂)
    (w : ℂ → ℂ) : Bfn (v₁ - v₂) w =ᵐ[volume] Bfn v₁ w - Bfn v₂ w := by
  filter_upwards [velocityRe_sub_ae h₁ h₂, velocityIm_sub_ae h₁ h₂] with x hx1 hx2
  simp only [Bfn, bsGrad, dotGrad, Pi.sub_apply]
  rw [hx1, hx2]
  simp only [Complex.sub_re, Complex.sub_im]
  push_cast
  ring

/-- `B(v, w₁ - w₂) = B(v, w₁) - B(v, w₂)` a.e. for `w₁, w₂ ∈ H^1`. -/
theorem Bfn_sub_right_ae (v : ℂ → ℂ) {w₁ w₂ : ℂ → ℂ} (h₁ : MemH 1 w₁) (h₂ : MemH 1 w₂) :
    Bfn v (w₁ - w₂) =ᵐ[volume] Bfn v w₁ - Bfn v w₂ := by
  filter_upwards [dotGrad_sub_right_ae (BS.velocityRe v) h₁ h₂,
    dotGrad_sub_right_ae (BS.velocityIm v) h₁ h₂] with x hx1 hx2
  simp only [Bfn, bsGrad, Pi.sub_apply] at hx1 hx2 ⊢
  rw [hx1, hx2]
  ring

/-- `B(v₁,w₁) - B(v₂,w₂) = B(v₁-v₂, w₁) + B(v₂, w₁-w₂)` a.e. -/
theorem Bfn_diff2_ae {v₁ v₂ w₁ w₂ : ℂ → ℂ} (hv₁ : Lin.MemXFn 0 v₁) (hv₂ : Lin.MemXFn 0 v₂)
    (hw₁ : MemH 1 w₁) (hw₂ : MemH 1 w₂) :
    Bfn v₁ w₁ - Bfn v₂ w₂ =ᵐ[volume] Bfn (v₁ - v₂) w₁ + Bfn v₂ (w₁ - w₂) := by
  have hl := Bfn_sub_left_ae hv₁ hv₂ w₁
  have hr := Bfn_sub_right_ae v₂ hw₁ hw₂
  filter_upwards [hl, hr] with x hx1 hx2
  simp only [Pi.add_apply, Pi.sub_apply] at hx1 hx2 ⊢
  rw [hx1, hx2]
  ring

/-- `B(v₁,v₁) - B(v₂,v₂) = B(v₁-v₂, v₁) + B(v₂, v₁-v₂)` a.e. for `v₁, v₂ ∈ X^1`. -/
theorem Bfn_diff_ae {v₁ v₂ : ℂ → ℂ} (h₁ : Lin.MemXFn 1 v₁) (h₂ : Lin.MemXFn 1 v₂) :
    Bfn v₁ v₁ - Bfn v₂ v₂ =ᵐ[volume] Bfn (v₁ - v₂) v₁ + Bfn v₂ (v₁ - v₂) :=
  Bfn_diff2_ae (MemXFn.mono h₁ (Nat.zero_le 1)) (MemXFn.mono h₂ (Nat.zero_le 1)) h₁.1 h₂.1

/-- `h₁·∇w₁ - h₂·∇w₂ = (h₁-h₂)·∇w₁ + h₂·∇(w₁-w₂)` a.e. for `w₁, w₂ ∈ H^1`. -/
theorem hGrad_diff_ae (h₁ h₂ : ℂ → ℂ) {w₁ w₂ : ℂ → ℂ} (hw₁ : MemH 1 w₁) (hw₂ : MemH 1 w₂) :
    hGrad h₁ w₁ - hGrad h₂ w₂ =ᵐ[volume] hGrad (h₁ - h₂) w₁ + hGrad h₂ (w₁ - w₂) := by
  have hr : hGrad h₂ (w₁ - w₂) =ᵐ[volume] hGrad h₂ w₁ - hGrad h₂ w₂ :=
    dotGrad_sub_right_ae h₂ hw₁ hw₂
  rw [← hGrad_sub_field]
  filter_upwards [hr] with x hx
  simp only [Pi.add_apply, Pi.sub_apply] at hx ⊢
  rw [hx]
  ring

/-- `h·∇(w₁ + w₂) = h·∇w₁ + h·∇w₂` a.e. for `w₁, w₂ ∈ H^1`. -/
theorem hGrad_add_ae (h : ℂ → ℂ) {w₁ w₂ : ℂ → ℂ} (hw₁ : MemH 1 w₁) (hw₂ : MemH 1 w₂) :
    hGrad h (w₁ + w₂) =ᵐ[volume] hGrad h w₁ + hGrad h w₂ :=
  dotGrad_add_right_ae h hw₁ hw₂

/-- The Biot–Savart velocity of `0` vanishes. -/
theorem velocity_zero' : velocity (fun _ : ℂ => (0 : ℝ)) = 0 := by
  funext x
  simp [velocity]

/-- `B(0, w) = 0`. -/
theorem Bfn_zero_left (w : ℂ → ℂ) : Bfn 0 w = 0 := by
  have hre : BS.velocityRe (0 : ℂ → ℂ) = 0 := by
    simpa [BS.velocityRe] using velocity_zero'
  have him : BS.velocityIm (0 : ℂ → ℂ) = 0 := by
    simpa [BS.velocityIm] using velocity_zero'
  funext x
  simp [Bfn, bsGrad, dotGrad, hre, him]

/-! ### Realness -/

/-- (Copy of `Sob.ReImAux.iterDirDeriv_conj`.) -/
theorem iterDirDeriv_conj {V : Set ℂ} {φ : ℂ → ℂ} (hφ : IsTestFn V φ) (vs : List ℂ) :
    iterDirDeriv vs (fun x => conj (φ x)) = fun x => conj (iterDirDeriv vs φ x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    simp only [iterDirDeriv_cons]
    rw [ih]
    have hd : DifferentiableAt ℝ (iterDirDeriv vs φ) x :=
      ((hφ.iterDirDeriv vs).smooth.differentiable (by simp)) x
    have h2 := (Complex.conjCLE.hasFDerivAt (x := iterDirDeriv vs φ x)).comp x hd.hasFDerivAt
    show fderiv ℝ (Complex.conjCLE ∘ iterDirDeriv vs φ) x v = _
    rw [h2.fderiv]
    rfl

/-- (Copy of `Sob.ReImAux.isTestFn_conj`.) -/
theorem isTestFn_conj {V : Set ℂ} {φ : ℂ → ℂ} (hφ : IsTestFn V φ) :
    IsTestFn V (fun x => conj (φ x)) := by
  refine ⟨Complex.conjCLE.contDiff.comp hφ.smooth,
    hφ.compact.comp_left (g := conj) (map_zero _), ?_⟩
  exact (tsupport_comp_subset (g := conj) (map_zero _) φ).trans hφ.subset

/-- `∂_{vs} (conj f) = conj (∂_{vs} f)` weakly (copy of `Sob.ReImAux.hasWeakDerivOn_conj`). -/
theorem hasWeakDerivOn_conj {V : Set ℂ} {vs : List ℂ} {f g : ℂ → ℂ}
    (h : HasWeakDerivOn V vs f g) :
    HasWeakDerivOn V vs (fun x => conj (f x)) (fun x => conj (g x)) := by
  intro φ hφ
  have hψ := isTestFn_conj hφ
  have k := h _ hψ
  have e1 : iterDirDeriv vs φ = fun x => conj (iterDirDeriv vs (fun x => conj (φ x)) x) := by
    rw [iterDirDeriv_conj hφ]
    simp
  rw [e1]
  have e2 : ∫ x, conj (f x) * conj (iterDirDeriv vs (fun x => conj (φ x)) x) =
      conj (∫ x, f x * iterDirDeriv vs (fun x => conj (φ x)) x) := by
    rw [← integral_conj]
    simp
  have e3 : ∫ x, conj (g x) * φ x = conj (∫ x, g x * conj (φ x)) := by
    rw [← integral_conj]
    simp
  rw [e2, e3, k]
  simp

/-- **The weak derivatives of a real `H^k` function are real** (a.e.). -/
theorem weakPartial_im_ae {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f)
    (hr : ∀ᵐ x ∂(volume : Measure ℂ), (f x).im = 0) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    ∀ᵐ x ∂(volume : Measure ℂ), (weakPartial γ f x).im = 0 := by
  obtain ⟨hgm, hgd⟩ := MemH.memLp_weakPartial hf hγ
  have hc := hasWeakDerivOn_conj hgd
  have hff : ∀ᵐ x ∂(volume : Measure ℂ), x ∈ univ → conj (f x) = f x := by
    filter_upwards [hr] with x hx _
    exact Complex.conj_eq_iff_im.2 hx
  have hc' : HasWeakDerivOn univ (pdList γ) f (fun x => conj (weakPartial γ f x)) :=
    hc.congr_ae hff (Eventually.of_forall fun _ _ => rfl)
  have hli : ∀ {u : ℂ → ℂ}, MemLp u 2 volume → LocallyIntegrableOn u univ := fun hu =>
    (hu.locallyIntegrable (by norm_num)).locallyIntegrableOn univ
  have hcm : MemLp (fun x => conj (weakPartial γ f x)) 2 volume := by
    have := hgm.re.ofReal (K := ℂ)
    have h2 := hgm.im.ofReal (K := ℂ)
    have h3 := this.sub (h2.const_mul Complex.I)
    refine h3.ae_eq (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    apply Complex.ext <;> simp
  have hu := HasWeakDerivOn.ae_eq isOpen_univ (hli hgm) (hli hcm) hgd hc'
  filter_upwards [hu] with x hx
  exact Complex.conj_eq_iff_im.1 (hx (mem_univ x)).symm

/-- `U·∇w` is real a.e. for `w ∈ H^1` real. -/
theorem dotGrad_im_ae (U : ℂ → ℂ) {w : ℂ → ℂ} (hw : MemH 1 w)
    (hr : ∀ᵐ x ∂(volume : Measure ℂ), (w x).im = 0) :
    ∀ᵐ x ∂(volume : Measure ℂ), (dotGrad U w x).im = 0 := by
  filter_upwards [weakPartial_im_ae hw hr idx10_mem, weakPartial_im_ae hw hr idx01_mem]
    with x h1 h2
  simp only [dotGrad, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, h1,
    h2]
  ring

theorem hGrad_im_ae (h : ℂ → ℂ) {w : ℂ → ℂ} (hw : MemH 1 w)
    (hr : ∀ᵐ x ∂(volume : Measure ℂ), (w x).im = 0) :
    ∀ᵐ x ∂(volume : Measure ℂ), (hGrad h w x).im = 0 :=
  dotGrad_im_ae h hw hr

/-- `B(v,w)` is real a.e. for `v` real and `w ∈ H^1` real. -/
theorem Bfn_im_ae {v w : ℂ → ℂ}
    (hvr : ∀ᵐ x ∂(volume : Measure ℂ), (v x).im = 0) (hw : MemH 1 w)
    (hwr : ∀ᵐ x ∂(volume : Measure ℂ), (w x).im = 0) :
    ∀ᵐ x ∂(volume : Measure ℂ), (Bfn v w x).im = 0 := by
  have him : BS.velocityIm v = 0 := by
    funext x
    have h0 : (fun y => (v y).im) =ᵐ[volume] fun _ => (0 : ℝ) := hvr
    have : velocity (fun y => (v y).im) x = velocity (fun _ => (0 : ℝ)) x := by
      simp only [velocity]
      refine integral_congr_ae ?_
      filter_upwards [h0] with y hy
      rw [hy]
    simp only [BS.velocityIm, this, velocity_zero', Pi.zero_apply]
  filter_upwards [dotGrad_im_ae (BS.velocityRe v) hw hwr] with x hx
  simp only [Bfn, bsGrad, him, Complex.neg_im, Complex.add_im, hx]
  simp [dotGrad]

/-- The forcing `-h·∇Φ` is real a.e. -/
theorem forcing_im_ae (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (h : ℝ → ℂ → ℂ) (v : ℝ) :
    ∀ᵐ x ∂(volume : Measure ℂ), (forcing χ h v x).im = 0 := by
  obtain ⟨hsmooth, hcpt, -⟩ := ringFacts_of_admissible hχ
  have hC : ContDiff ℝ ∞ (PhiC χ) := Complex.ofRealCLM.contDiff.comp hsmooth
  have hcC : HasCompactSupport (PhiC χ) := hcpt.comp_left Complex.ofReal_zero
  have hM : MemH 1 (PhiC χ) := (memH_of_contDiff_hasCompactSupport hC hcC 1).1
  have hr : ∀ᵐ x ∂(volume : Measure ℂ), (PhiC χ x).im = 0 :=
    Eventually.of_forall fun x => by simp [PhiC]
  filter_upwards [hGrad_im_ae (h v) hM hr] with x hx
  simp only [forcing, Complex.neg_im, hx, neg_zero]

/-! ### Paths of the nonlinear and field terms -/

/-- **`B(u,v) ∈ C([0,T];X^s)`** for `u, v ∈ C([0,T];X^{s+1})`, `s ≥ 2`. -/
theorem pathC_Bfn2 {s : ℕ} (hs : 2 ≤ s) {T : ℝ} {u v : ℝ → ℂ → ℂ} (hu : PathC (s + 1) T u)
    (hv : PathC (s + 1) T v) : PathC s T (fun τ => Bfn (u τ) (v τ)) := by
  refine pathC_of_tendsto (fun τ hτ => (bilinear_B hs (hu.1 τ hτ) (hv.1 τ hτ)).1)
    fun τ hτ => ?_
  have hv1 := PathC.tendsto_normH_sub hv hτ
  have hvN := PathC.tendsto_normH hv hτ
  have hu0 := PathC.tendsto_normH_sub_lower hu hτ
  refine tendsto_normH_sub_of_le (b := fun τ' => CB s * normH s (u τ' - u τ) *
      normH (s + 1) (v τ') + CB s * normH s (u τ) * normH (s + 1) (v τ' - v τ)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with τ' hτ'
    show normH s (Bfn (u τ') (v τ') - Bfn (u τ) (v τ)) ≤ _
    have hu1 := hu.1 τ' hτ'
    have hu0' := hu.1 τ hτ
    have hv1' := hv.1 τ' hτ'
    have hv0' := hv.1 τ hτ
    have hdu := MemXFn.sub hu1 hu0'
    have hdv := MemXFn.sub hv1' hv0'
    obtain ⟨hB1, hb1⟩ := bilinear_B hs hdu hv1'
    obtain ⟨hB2, hb2⟩ := bilinear_B hs hu0' hdv
    have hae := Bfn_diff2_ae (MemXFn.mono hu1 (by omega)) (MemXFn.mono hu0' (by omega))
      (hv1'.1.mono_order (by omega)) (hv0'.1.mono_order (by omega))
    exact (normH_le_of_ae_eq_add hB1.1 hB2.1 hae).trans (add_le_add hb1 hb2)
  · have := ((tendsto_const_nhds (x := CB s)).mul hu0 |>.mul hvN).add
      ((tendsto_const_nhds (x := CB s * normH s (u τ))).mul hv1)
    simpa using this

/-- **`h·∇w ∈ C([0,T];X^s)`** for `w ∈ C([0,T];X^{s+1})`, `s ≥ 2`, and `h ∈ C([0,T];C^s(N'))`
`3`-fold symmetric on `N'` (copy of `RappPathH.pathC_hGrad`). -/
theorem pathC_hGrad {s : ℕ} (hs : 2 ≤ s) {T : ℝ} {u h : ℝ → ℂ → ℂ} (hu : PathC (s + 1) T u)
    (hh : CkPathOn s annN' (Icc 0 T) h)
    (hsym : ∀ τ ∈ Icc (0 : ℝ) T, IsSymFieldOn annN' (h τ)) :
    PathC s T (fun τ => hGrad (h τ) (u τ)) := by
  refine pathC_of_tendsto
    (fun τ hτ => (bilinear_h hs (hu.1 τ hτ) (hh.1 τ hτ)).2.2.2 (hsym τ hτ)) fun τ hτ => ?_
  have ha1 := PathC.tendsto_normH_sub hu hτ
  have hN := PathC.tendsto_normH hu hτ
  have hc := hh.2 τ hτ
  refine tendsto_normH_sub_of_le (b := fun τ' => Ch s * normCk s annN' (h τ' - h τ) *
      normH (s + 1) (u τ') + Ch s * normCk s annN' (h τ) * normH (s + 1) (u τ' - u τ)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with τ' hτ'
    show normH s (hGrad (h τ') (u τ') - hGrad (h τ) (u τ)) ≤ _
    have h1 := hu.1 τ' hτ'
    have h0 := hu.1 τ hτ
    have hd := MemXFn.sub h1 h0
    have hcd : MemCk s annN' (h τ' - h τ) := ((hh.1 τ' hτ').sub (hh.1 τ hτ)).1
    obtain ⟨hH1, -, hb1, -⟩ := bilinear_h hs h1 hcd
    obtain ⟨hH2, -, hb2, -⟩ := bilinear_h hs hd (hh.1 τ hτ)
    have hae := hGrad_diff_ae (h τ') (h τ) (h1.1.mono_order (by omega))
      (h0.1.mono_order (by omega))
    exact (normH_le_of_ae_eq_add hH1 hH2 hae).trans (add_le_add hb1 hb2)
  · have := ((tendsto_const_nhds (x := Ch s)).mul hc |>.mul hN).add
      ((tendsto_const_nhds (x := Ch s * normCk s annN' (h τ))).mul ha1)
    simpa using this

/-- **`h·∇Φ ∈ C([0,T];X^s)`** for `h ∈ C([0,T];C^s(N'))` `3`-fold symmetric on `N'`, `s ≥ 2`
(copy of `RappPathH.pathC_hGradPhi`). -/
theorem pathC_hGradPhi (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 2 ≤ s) {T : ℝ} {h : ℝ → ℂ → ℂ} (hh : CkPathOn s annN' (Icc 0 T) h)
    (hsym : ∀ τ ∈ Icc (0 : ℝ) T, IsSymFieldOn annN' (h τ)) :
    PathC s T (fun τ => hGrad (h τ) (PhiC χ)) := by
  refine pathC_of_tendsto
    (fun τ hτ => (bilinear_Phi χ hχ hN hs (hh.1 τ hτ)).2.2.2 (hsym τ hτ)) fun τ hτ => ?_
  refine tendsto_normH_sub_of_le (b := fun τ' => Eig.Cnab χ s * normCk s annN' (h τ' - h τ))
    ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with τ' hτ'
    show normH s (hGrad (h τ') (PhiC χ) - hGrad (h τ) (PhiC χ)) ≤ _
    have hcd : MemCk s annN' (h τ' - h τ) := ((hh.1 τ' hτ').sub (hh.1 τ hτ)).1
    rw [hGrad_sub_field]
    exact (bilinear_Phi χ hχ hN hs hcd).2.2.1
  · simpa using (hh.2 τ hτ).const_mul (Eig.Cnab χ s)

/-- **The forcing `F = -h·∇Φ` is a path in `C([0,T];X^s)`** (`s ≥ 2`). -/
theorem pathC_forcing (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 2 ≤ s) {T : ℝ} {h : ℝ → ℂ → ℂ} (hh : CkPathOn s annN' (Icc 0 T) h)
    (hsym : ∀ τ ∈ Icc (0 : ℝ) T, IsSymFieldOn annN' (h τ)) :
    PathC s T (forcing χ h) := by
  have h1 := PathC.neg (pathC_hGradPhi χ hχ hN hs hh hsym)
  exact h1

end NonUniqueEuler.OneRing.WAppH
