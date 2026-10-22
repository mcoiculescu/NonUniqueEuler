import NonUniqueEuler.H.Sec5.Quiet.Approx.Bridge
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.Sobolev.EmbedLinf
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Sec4.SemigroupConstruct
import NonUniqueEuler.I.Sec4.RingFacts
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Helpers for `quiet_approx`: the a.e. calculus of the terms of `eq:ring`

Helper of `P/Sec5/Quiet/Approx.lean` (fully proved). Namespace `NonUniqueEuler.OneRing.QAppH`.

* weak partials: additivity, a.e. invariance, the zero function, realness (the conjugation
  argument is copied from the proved helper `H/Sec2/HkCalculus/ReIm.lean`);
* the Biot–Savart integrand `y ↦ K_BS(x-y) g(y)` is integrable for `g ∈ H^2` vanishing outside
  `N` (continuous representative, `lem:embed`(E2), and Mathlib's convolution existence), hence
  `K_BS * ·` is additive on such functions;
* `B(v,w)` and `h·∇w`: additivity in each argument (a.e.), a.e. invariance, finite sums, realness;
* `L(G)` on functions (`Lin.Lfn`): a.e. invariance, and `(Lin.L w).fn = Lin.Lfn w.fn` a.e.
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ComplexConjugate ContDiff

namespace NonUniqueEuler.OneRing.QAppH

open Sect Sob RingData

/-! ### Weak partial derivatives -/

theorem memLp_of_memH' {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) : MemLp f 2 volume := by
  have h := hf.memLp
  rwa [Measure.restrict_univ] at h

theorem locInt_of_memLp {u : ℂ → ℂ} (hu : MemLp u 2 volume) : LocallyIntegrableOn u univ :=
  (hu.locallyIntegrable (by norm_num)).locallyIntegrableOn univ

theorem weakPartial_add_ae {k : ℕ} {f g : ℂ → ℂ} (hf : MemH k f) (hg : MemH k g) {γ : ℕ × ℕ}
    (hγ : γ ∈ multiIdx k) :
    weakPartial γ (f + g) =ᵐ[volume] weakPartial γ f + weakPartial γ g := by
  obtain ⟨hfL, hfD⟩ := hf.memLp_weakPartial hγ
  obtain ⟨hgL, hgD⟩ := hg.memLp_weakPartial hγ
  have hD := HasWeakDerivOn.add isOpen_univ (locInt_of_memLp (memLp_of_memH' hf))
    (locInt_of_memLp (memLp_of_memH' hg)) (locInt_of_memLp hfL) (locInt_of_memLp hgL) hfD hgD
  exact (hf.add hg).1.weakPartial_ae_eq hγ (hfL.add hgL) hD

theorem weakPartial_congr_ae {k : ℕ} {f g : ℂ → ℂ} (hf : MemH k f) (hfg : f =ᵐ[volume] g)
    {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) : weakPartial γ f =ᵐ[volume] weakPartial γ g := by
  obtain ⟨hfL, hfD⟩ := hf.memLp_weakPartial hγ
  have hg := (hf.congr_ae hfg).1
  have hD : HasWeakDerivOn univ (pdList γ) g (weakPartial γ f) :=
    hfD.congr_ae (by filter_upwards [hfg] with x hx _ using hx)
      (Eventually.of_forall fun _ _ => rfl)
  exact (hg.weakPartial_ae_eq hγ hfL hD).symm

theorem weakPartial_zero_ae {k : ℕ} {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    weakPartial γ (0 : ℂ → ℂ) =ᵐ[volume] (0 : ℂ → ℂ) := by
  have h0 : MemH k (0 : ℂ → ℂ) := (memXFn_zero k).1
  have hD : HasWeakDerivOn univ (pdList γ) (0 : ℂ → ℂ) (0 : ℂ → ℂ) := by
    intro φ _
    simp
  exact h0.weakPartial_ae_eq hγ (MemLp.zero) hD

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

theorem isTestFn_conj {V : Set ℂ} {φ : ℂ → ℂ} (hφ : IsTestFn V φ) :
    IsTestFn V (fun x => conj (φ x)) := by
  refine ⟨Complex.conjCLE.contDiff.comp hφ.smooth,
    hφ.compact.comp_left (g := conj) (map_zero _), ?_⟩
  exact (tsupport_comp_subset (g := conj) (map_zero _) φ).trans hφ.subset

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

theorem locInt_conj {V : Set ℂ} {f : ℂ → ℂ} (hf : LocallyIntegrableOn f V) :
    LocallyIntegrableOn (fun x => conj (f x)) V := by
  intro x hx
  obtain ⟨t, ht, hi⟩ := hf x hx
  exact ⟨t, ht, Complex.conjCLE.toContinuousLinearMap.integrable_comp hi⟩

/-- Weak derivatives of real `H^k` functions are real a.e. -/
theorem weakPartial_isReal {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f)
    (hre : ∀ᵐ x ∂(volume : Measure ℂ), (f x).im = 0) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    ∀ᵐ x ∂(volume : Measure ℂ), (weakPartial γ f x).im = 0 := by
  obtain ⟨hL, hD⟩ := hf.memLp_weakPartial hγ
  have hg := locInt_of_memLp hL
  have h1 := hasWeakDerivOn_conj hD
  have h2 : HasWeakDerivOn univ (pdList γ) f (fun x => conj (weakPartial γ f x)) := by
    refine h1.congr_ae ?_ (Eventually.of_forall fun _ _ => rfl)
    filter_upwards [hre] with x hx _
    exact Complex.conj_eq_iff_im.2 hx
  have h3 := HasWeakDerivOn.ae_eq isOpen_univ hg (locInt_conj hg) hD h2
  filter_upwards [h3] with x hx
  exact Complex.conj_eq_iff_im.1 (hx (mem_univ x)).symm

theorem mem_multiIdx_10 {k : ℕ} (hk : 1 ≤ k) : ((1, 0) : ℕ × ℕ) ∈ multiIdx k :=
  mem_multiIdx.2 (by simpa using hk)

theorem mem_multiIdx_01 {k : ℕ} (hk : 1 ≤ k) : ((0, 1) : ℕ × ℕ) ∈ multiIdx k :=
  mem_multiIdx.2 (by simpa using hk)

/-! ### The Biot–Savart integral -/

theorem locallyIntegrable_kernel : LocallyIntegrable biotSavartKernel volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨r, hr, hkr⟩ := hk.isBounded.subset_ball_lt 0 0
  exact (BS.integral_norm_biotSavartKernel_ball hr).1.mono_set hkr

/-- For `φ` continuous with compact support, `y ↦ K_BS(x-y) φ(y)` is integrable. -/
theorem integrable_kernel_mul_of_continuous {φ : ℂ → ℂ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (x : ℂ) :
    Integrable (fun y => biotSavartKernel (x - y) * φ y) := by
  have h := hc.convolutionExists_left (L := ContinuousLinearMap.mul ℂ ℂ) hφ
    locallyIntegrable_kernel x
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [ContinuousLinearMap.mul_apply']
  ring

/-- For `g ∈ H^2` vanishing a.e. outside `N`, a continuous representative vanishing outside `N`. -/
theorem exists_cont_rep {g : ℂ → ℂ} (hg : MemH 2 g)
    (hgN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → g x = 0) :
    ∃ g' : ℂ → ℂ, Continuous g' ∧ g =ᵐ[volume] g' ∧ HasCompactSupport g' := by
  obtain ⟨g', hgc, hgg, -, -⟩ := Sob.Linf_le_H2 hg
  have hK : IsCompact annN := isCompact_closedAnnulus _ _
  have hopen : IsOpen annNᶜ := hK.isClosed.isOpen_compl
  have hae : g' =ᵐ[volume.restrict annNᶜ] (fun _ => (0 : ℂ)) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hopen.measurableSet]
    filter_upwards [hgg, hgN] with x hx1 hx2 hx3
    rw [← hx1]
    exact hx2 hx3
  have heq : EqOn g' (fun _ => (0 : ℂ)) annNᶜ :=
    Measure.eqOn_open_of_ae_eq hae hopen hgc.continuousOn continuousOn_const
  exact ⟨g', hgc, hgg, HasCompactSupport.intro hK fun x hx => heq hx⟩

/-- For `g ∈ H^2` vanishing a.e. outside `N` and any `x`, `y ↦ K_BS(x-y) ψ(g(y))` is integrable
for a continuous `ψ : ℂ → ℂ` with `ψ 0 = 0` (used with `ψ = Re`, `Im`). -/
theorem integrable_kernel_mul_comp {g : ℂ → ℂ} (hg : MemH 2 g)
    (hgN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → g x = 0) {ψ : ℂ → ℂ} (hψ : Continuous ψ)
    (hψ0 : ψ 0 = 0) (x : ℂ) :
    Integrable (fun y => biotSavartKernel (x - y) * ψ (g y)) := by
  obtain ⟨g', hgc, hgg, hcs⟩ := exists_cont_rep hg hgN
  have h := integrable_kernel_mul_of_continuous (hψ.comp hgc) (hcs.comp_left hψ0) x
  refine h.congr ?_
  filter_upwards [hgg] with y hy
  simp [hy]

theorem velocity_add {g₁ g₂ : ℂ → ℝ} (x : ℂ)
    (h₁ : Integrable (fun y => biotSavartKernel (x - y) * (g₁ y : ℂ)))
    (h₂ : Integrable (fun y => biotSavartKernel (x - y) * (g₂ y : ℂ))) :
    velocity (fun y => g₁ y + g₂ y) x = velocity g₁ x + velocity g₂ x := by
  unfold velocity
  rw [← integral_add h₁ h₂]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Complex.ofReal_add]
  ring

theorem velocity_neg (g : ℂ → ℝ) : velocity (fun y => -g y) = -velocity g := by
  funext x
  unfold velocity
  rw [Pi.neg_apply, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Complex.ofReal_neg]
  ring

theorem velocity_zero : velocity (fun _ => (0 : ℝ)) = 0 := by
  funext x
  simp [velocity]

theorem velocity_congr_ae {g g' : ℂ → ℝ} (h : g =ᵐ[volume] g') : velocity g = velocity g' := by
  funext x
  unfold velocity
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

theorem velocityRe_add {v₁ v₂ : ℂ → ℂ} (hv₁ : Lin.MemXFn 2 v₁) (hv₂ : Lin.MemXFn 2 v₂) :
    BS.velocityRe (v₁ + v₂) = BS.velocityRe v₁ + BS.velocityRe v₂ := by
  funext x
  have hre : Continuous (fun z : ℂ => ((z.re : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp Complex.continuous_re
  have h₁ := integrable_kernel_mul_comp hv₁.1 hv₁.2.1 hre (by simp) x
  have h₂ := integrable_kernel_mul_comp hv₂.1 hv₂.2.1 hre (by simp) x
  unfold BS.velocityRe
  simp only [Pi.add_apply, Complex.add_re]
  exact velocity_add x h₁ h₂

theorem velocityIm_add {v₁ v₂ : ℂ → ℂ} (hv₁ : Lin.MemXFn 2 v₁) (hv₂ : Lin.MemXFn 2 v₂) :
    BS.velocityIm (v₁ + v₂) = BS.velocityIm v₁ + BS.velocityIm v₂ := by
  funext x
  have him : Continuous (fun z : ℂ => ((z.im : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp Complex.continuous_im
  have h₁ := integrable_kernel_mul_comp hv₁.1 hv₁.2.1 him (by simp) x
  have h₂ := integrable_kernel_mul_comp hv₂.1 hv₂.2.1 him (by simp) x
  unfold BS.velocityIm
  simp only [Pi.add_apply, Complex.add_im]
  exact velocity_add x h₁ h₂

/-! ### `B(v,w) = -(K_BS * v)·∇w` and `h·∇w` -/

/-- Pointwise form of `dotGrad`. -/
theorem dotGrad_apply (U w : ℂ → ℂ) (x : ℂ) :
    dotGrad U w x = ((U x).re : ℂ) * weakPartial (1, 0) w x +
      ((U x).im : ℂ) * weakPartial (0, 1) w x := rfl

theorem dotGrad_add_left (U₁ U₂ w : ℂ → ℂ) :
    dotGrad (U₁ + U₂) w = fun x => dotGrad U₁ w x + dotGrad U₂ w x := by
  funext x
  simp only [dotGrad_apply, Pi.add_apply, Complex.add_re, Complex.add_im, Complex.ofReal_add]
  ring

theorem dotGrad_add_right_ae (U : ℂ → ℂ) {w₁ w₂ : ℂ → ℂ} (hw₁ : MemH 1 w₁) (hw₂ : MemH 1 w₂) :
    dotGrad U (w₁ + w₂) =ᵐ[volume] fun x => dotGrad U w₁ x + dotGrad U w₂ x := by
  filter_upwards [weakPartial_add_ae hw₁ hw₂ (mem_multiIdx_10 le_rfl),
    weakPartial_add_ae hw₁ hw₂ (mem_multiIdx_01 le_rfl)] with x h1 h2
  simp only [dotGrad_apply, h1, h2, Pi.add_apply]
  ring

theorem dotGrad_congr_ae (U : ℂ → ℂ) {w w' : ℂ → ℂ} (hw : MemH 1 w) (hww : w =ᵐ[volume] w') :
    dotGrad U w =ᵐ[volume] dotGrad U w' := by
  filter_upwards [weakPartial_congr_ae hw hww (mem_multiIdx_10 le_rfl),
    weakPartial_congr_ae hw hww (mem_multiIdx_01 le_rfl)] with x h1 h2
  simp only [dotGrad_apply, h1, h2]

theorem dotGrad_zero_right_ae (U : ℂ → ℂ) : dotGrad U 0 =ᵐ[volume] (0 : ℂ → ℂ) := by
  filter_upwards [weakPartial_zero_ae (k := 1) (mem_multiIdx_10 le_rfl),
    weakPartial_zero_ae (k := 1) (mem_multiIdx_01 le_rfl)] with x h1 h2
  simp only [dotGrad_apply, h1, h2, Pi.zero_apply, mul_zero, add_zero]

theorem dotGrad_isReal (U : ℂ → ℂ) {w : ℂ → ℂ} (hw : MemH 1 w)
    (hwR : ∀ᵐ x ∂(volume : Measure ℂ), (w x).im = 0) :
    ∀ᵐ x ∂(volume : Measure ℂ), (dotGrad U w x).im = 0 := by
  filter_upwards [weakPartial_isReal hw hwR (mem_multiIdx_10 le_rfl),
    weakPartial_isReal hw hwR (mem_multiIdx_01 le_rfl)] with x h1 h2
  simp [dotGrad_apply, Complex.add_im, Complex.mul_im, h1, h2]

theorem Bfn_apply (v w : ℂ → ℂ) (x : ℂ) :
    Bfn v w x = -(dotGrad (BS.velocityRe v) w x +
      Complex.I * dotGrad (BS.velocityIm v) w x) := rfl

theorem Bfn_add_left {v₁ v₂ : ℂ → ℂ} (hv₁ : Lin.MemXFn 2 v₁) (hv₂ : Lin.MemXFn 2 v₂)
    (w : ℂ → ℂ) : Bfn (v₁ + v₂) w = fun x => Bfn v₁ w x + Bfn v₂ w x := by
  funext x
  simp only [Bfn_apply, velocityRe_add hv₁ hv₂, velocityIm_add hv₁ hv₂, dotGrad_add_left]
  ring

theorem Bfn_add_right_ae (v : ℂ → ℂ) {w₁ w₂ : ℂ → ℂ} (hw₁ : MemH 1 w₁) (hw₂ : MemH 1 w₂) :
    Bfn v (w₁ + w₂) =ᵐ[volume] fun x => Bfn v w₁ x + Bfn v w₂ x := by
  filter_upwards [dotGrad_add_right_ae (BS.velocityRe v) hw₁ hw₂,
    dotGrad_add_right_ae (BS.velocityIm v) hw₁ hw₂] with x h1 h2
  simp only [Bfn_apply, h1, h2]
  ring

theorem Bfn_zero_left (w : ℂ → ℂ) : Bfn 0 w = 0 := by
  have h1 : BS.velocityRe (0 : ℂ → ℂ) = 0 := by
    unfold BS.velocityRe
    simpa using velocity_zero
  have h2 : BS.velocityIm (0 : ℂ → ℂ) = 0 := by
    unfold BS.velocityIm
    simpa using velocity_zero
  funext x
  simp [Bfn_apply, h1, h2, dotGrad_apply]

theorem Bfn_zero_right_ae (v : ℂ → ℂ) : Bfn v 0 =ᵐ[volume] (0 : ℂ → ℂ) := by
  filter_upwards [dotGrad_zero_right_ae (BS.velocityRe v),
    dotGrad_zero_right_ae (BS.velocityIm v)] with x h1 h2
  simp only [Bfn_apply, h1, h2, Pi.zero_apply]
  ring

theorem Bfn_congr_ae {v v' w w' : ℂ → ℂ} (hvv : v =ᵐ[volume] v') (hw : MemH 1 w)
    (hww : w =ᵐ[volume] w') : Bfn v w =ᵐ[volume] Bfn v' w' := by
  have h1 : BS.velocityRe v = BS.velocityRe v' := by
    unfold BS.velocityRe
    exact velocity_congr_ae (by filter_upwards [hvv] with y hy; rw [hy])
  have h2 : BS.velocityIm v = BS.velocityIm v' := by
    unfold BS.velocityIm
    exact velocity_congr_ae (by filter_upwards [hvv] with y hy; rw [hy])
  filter_upwards [dotGrad_congr_ae (BS.velocityRe v') hw hww,
    dotGrad_congr_ae (BS.velocityIm v') hw hww] with x e1 e2
  simp only [Bfn_apply, h1, h2, e1, e2]

theorem Bfn_isReal {v w : ℂ → ℂ} (hvR : ∀ᵐ x ∂(volume : Measure ℂ), (v x).im = 0)
    (hw : MemH 1 w) (hwR : ∀ᵐ x ∂(volume : Measure ℂ), (w x).im = 0) :
    ∀ᵐ x ∂(volume : Measure ℂ), (Bfn v w x).im = 0 := by
  have h2 : BS.velocityIm v = 0 := by
    unfold BS.velocityIm
    rw [velocity_congr_ae (g' := fun _ => (0 : ℝ)) hvR]
    exact velocity_zero
  filter_upwards [dotGrad_isReal (BS.velocityRe v) hw hwR] with x h1
  have h3 : dotGrad (0 : ℂ → ℂ) w x = 0 := by simp [dotGrad_apply]
  rw [Bfn_apply, h2, h3]
  simp [h1]

theorem hGrad_apply (h g : ℂ → ℂ) (x : ℂ) : hGrad h g x = dotGrad h g x := rfl

theorem hGrad_sub_left (h₁ h₂ w : ℂ → ℂ) :
    hGrad (h₁ - h₂) w = fun x => hGrad h₁ w x - hGrad h₂ w x := by
  funext x
  simp only [hGrad_apply, dotGrad_apply, Pi.sub_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_sub]
  ring

/-! ### Finite sums -/

theorem Bfn_sum_left {ι : Type*} (S : Finset ι) {v : ι → ℂ → ℂ}
    (hv : ∀ i ∈ S, Lin.MemXFn 2 (v i)) (w : ℂ → ℂ) :
    Bfn (∑ i ∈ S, v i) w = fun x => ∑ i ∈ S, Bfn (v i) w x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    funext x
    simp [Bfn_zero_left]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Bfn_add_left (hv a (Finset.mem_insert_self a S))
      (MemXFn.sum S fun i hi => hv i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hv i (Finset.mem_insert_of_mem hi)]
    funext x
    rw [Finset.sum_insert ha]

theorem memH_sum {k : ℕ} {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ S, MemH k (f i)) : MemH k (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (memXFn_zero k).1
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact ((hf a (Finset.mem_insert_self a S)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))).1

theorem Bfn_sum_right_ae (v : ℂ → ℂ) {ι : Type*} (S : Finset ι) {w : ι → ℂ → ℂ}
    (hw : ∀ i ∈ S, MemH 1 (w i)) :
    Bfn v (∑ i ∈ S, w i) =ᵐ[volume] fun x => ∑ i ∈ S, Bfn v (w i) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Bfn_zero_right_ae v
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := Bfn_add_right_ae v (hw a (Finset.mem_insert_self a S))
      (memH_sum S fun i hi => hw i (Finset.mem_insert_of_mem hi))
    filter_upwards [h1, ih fun i hi => hw i (Finset.mem_insert_of_mem hi)] with x e1 e2
    rw [e1, e2, Finset.sum_insert ha]

theorem hGrad_add_right_ae (h : ℂ → ℂ) {w₁ w₂ : ℂ → ℂ} (hw₁ : MemH 1 w₁) (hw₂ : MemH 1 w₂) :
    hGrad h (w₁ + w₂) =ᵐ[volume] fun x => hGrad h w₁ x + hGrad h w₂ x :=
  dotGrad_add_right_ae h hw₁ hw₂

theorem hGrad_congr_ae (h : ℂ → ℂ) {w w' : ℂ → ℂ} (hw : MemH 1 w) (hww : w =ᵐ[volume] w') :
    hGrad h w =ᵐ[volume] hGrad h w' :=
  dotGrad_congr_ae h hw hww

theorem hGrad_isReal (h : ℂ → ℂ) {w : ℂ → ℂ} (hw : MemH 1 w)
    (hwR : ∀ᵐ x ∂(volume : Measure ℂ), (w x).im = 0) :
    ∀ᵐ x ∂(volume : Measure ℂ), (hGrad h w x).im = 0 :=
  dotGrad_isReal h hw hwR

theorem hGrad_sum_right_ae (h : ℂ → ℂ) {ι : Type*} (S : Finset ι) {w : ι → ℂ → ℂ}
    (hw : ∀ i ∈ S, MemH 1 (w i)) :
    hGrad h (∑ i ∈ S, w i) =ᵐ[volume] fun x => ∑ i ∈ S, hGrad h (w i) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact dotGrad_zero_right_ae h
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := hGrad_add_right_ae h (hw a (Finset.mem_insert_self a S))
      (memH_sum S fun i hi => hw i (Finset.mem_insert_of_mem hi))
    filter_upwards [h1, ih fun i hi => hw i (Finset.mem_insert_of_mem hi)] with x e1 e2
    rw [e1, e2, Finset.sum_insert ha]

/-- `B(Σ_i v_i, Σ_l w_l) = Σ_i Σ_l B(v_i, w_l)` a.e. for `v_i ∈ X^2`, `w_l ∈ H^1`. -/
theorem Bfn_sum_sum_ae {ι κ : Type*} (S : Finset ι) (S' : Finset κ) {v : ι → ℂ → ℂ}
    {w : κ → ℂ → ℂ} (hv : ∀ i ∈ S, Lin.MemXFn 2 (v i)) (hw : ∀ l ∈ S', MemH 1 (w l)) :
    Bfn (∑ i ∈ S, v i) (∑ l ∈ S', w l) =ᵐ[volume]
      fun x => ∑ i ∈ S, ∑ l ∈ S', Bfn (v i) (w l) x := by
  rw [Bfn_sum_left S hv]
  have h := fun i (_ : i ∈ S) => Bfn_sum_right_ae (v i) S' hw
  have hall : ∀ᵐ x ∂(volume : Measure ℂ), ∀ i ∈ S,
      Bfn (v i) (∑ l ∈ S', w l) x = ∑ l ∈ S', Bfn (v i) (w l) x := by
    rw [Filter.eventually_all_finset]
    intro i hi
    exact h i hi
  filter_upwards [hall] with x hx
  exact Finset.sum_congr rfl hx

/-! ### `L(G)` on functions -/

theorem thetaDeriv_congr_ae {w w' : ℂ → ℂ} (hw : MemH 1 w) (hww : w =ᵐ[volume] w') :
    Ang.thetaDeriv w =ᵐ[volume] Ang.thetaDeriv w' := by
  filter_upwards [weakPartial_congr_ae hw hww (mem_multiIdx_10 le_rfl),
    weakPartial_congr_ae hw hww (mem_multiIdx_01 le_rfl)] with x h1 h2
  simp only [Ang.thetaDeriv, h1, h2]

/-- `L(G)w` on functions only sees the a.e. class of `w ∈ H^1`. -/
theorem Lfn_congr_ae (χ : ℝ → ℝ) (G : ℝ) {w w' : ℂ → ℂ} (hw : MemH 1 w)
    (hww : w =ᵐ[volume] w') : Lin.Lfn χ G w =ᵐ[volume] Lin.Lfn χ G w' := by
  have hc : (ringPhiSetting χ).couplingFn w = (ringPhiSetting χ).couplingFn w' := by
    funext x
    unfold SectorSetting.couplingFn
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hww] with y hy
    rw [hy]
  filter_upwards [thetaDeriv_congr_ae hw hww] with x hx
  simp only [Lin.Lfn, SectorSetting.linFn, SectorSetting.transportPartFn, hx, hc]

/-- `(L(G) w).fn = L(G) w.fn` a.e. for `w ∈ Y^{k+1}(N)`. -/
theorem L_fn_ae (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (k : ℕ) (G : ℝ) (w : Y (k + 1) annN) :
    (Lin.L χ k G w).fn =ᵐ[volume] Lin.Lfn χ G w.fn :=
  (ringPhiSetting χ).LinY_spec_of_exists k G
    ((ringPhiSetting χ).semigroupConstruct_LinY (ringPhiSetting_valid hχ) k G) w

/-- `(L(G) toY(f)).fn = L(G) f` a.e. for `f ∈ X^{k+1}`. -/
theorem L_toY_fn_ae (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (k : ℕ) (G : ℝ) {f : ℂ → ℂ}
    (hf : Lin.MemXFn (k + 1) f) :
    (Lin.L χ k G (toY (k + 1) annN f)).fn =ᵐ[volume] Lin.Lfn χ G f := by
  have hfn := MemXFn.toY_fn hf
  have h1 : MemH 1 (toY (k + 1) annN f).fn :=
    (Y_memH_fn (toY (k + 1) annN f)).1.mono_order (by omega)
  exact (L_fn_ae χ hχ k G _).trans (Lfn_congr_ae χ G h1 hfn)

end NonUniqueEuler.OneRing.QAppH
