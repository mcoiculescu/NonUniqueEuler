import NonUniqueEuler.H.SmoothB.IterHs.Slice
import NonUniqueEuler.I.Infra.Sobolev.Paths
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Helper for `lem:iter-Hs`: the energy identity for the top-order derivatives

Helper of `P/SmoothB/IterHs.lean` (`B_global_smooth.tex:322-336`). Generic facts, for a jointly
smooth family `w(t, x)` whose spatial supports lie in a fixed compact set for `t` in an open set:

* `inner_toHk_eq`: `⟪f, g⟫_{H^k} = ∑_{|γ| ≤ k} ∫ conj(∂^γ f) ∂^γ g` (classical derivatives) for
  smooth compactly supported `f`, `g`;
* `hasDerivAt_topEnergy`: `𝓗(t) = ∑_{|α| = k+1} ‖∂^α w(t)‖²_{L²}` is differentiable with
  `𝓗'(t) = 2 Re ∑_{|α| = k+1} ∫ conj(∂^α w(t)) ∂^α ∂_t w(t)` (from `I/Infra/Sobolev/Paths.lean`,
  as the difference of `‖w(t)‖²_{H^{k+1}}` and `‖w(t)‖²_{H^k}`);
* `re_integral_conj_mul_fderiv_eq_zero`: the transport term vanishes,
  `Re ∫ conj(f) u·∇f = ½ ∫ u·∇|f|² = 0` when `div u = 0` weakly;
* `norm_integral_conj_mul_le`: Cauchy–Schwarz in `L²`.
-/

noncomputable section

open MeasureTheory Set Metric Filter ComplexConjugate
open scoped ContDiff ENNReal Topology

namespace NonUniqueEuler.Smooth.IterHsH

open Sob

/-! ### Smoothness of classical derivatives -/

theorem contDiff_dirDeriv {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (v : ℂ) :
    ContDiff ℝ ∞ (dirDeriv v f) :=
  (ContDiff.fderiv_right (m := ∞) hf (by simp)).clm_apply contDiff_const

theorem contDiff_iterDirDeriv {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (vs : List ℂ) :
    ContDiff ℝ ∞ (iterDirDeriv vs f) := by
  induction vs with
  | nil => simpa using hf
  | cons v vs ih => simpa using contDiff_dirDeriv ih v

theorem contDiff_partialD {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (γ : ℕ × ℕ) :
    ContDiff ℝ ∞ (partialD γ f) :=
  contDiff_iterDirDeriv hf _

theorem hasCompactSupport_partialD {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (γ : ℕ × ℕ) : HasCompactSupport (partialD γ f) :=
  (IsTestFn.partialD ⟨hf, hc, subset_univ _⟩ γ).compact

theorem iterDirDeriv_neg (vs : List ℂ) (f : ℂ → ℂ) :
    iterDirDeriv vs (fun x => -f x) = fun x => -iterDirDeriv vs f x := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [iterDirDeriv_cons, ih]
    funext x
    simp only [dirDeriv, fderiv_fun_neg]
    rfl

theorem partialD_neg (γ : ℕ × ℕ) (f : ℂ → ℂ) :
    partialD γ (fun x => -f x) = fun x => -partialD γ f x :=
  iterDirDeriv_neg _ f

/-! ### The `H^k` inner product of smooth functions -/

/-- The stored derivatives of `toHk k f`, for `f` smooth with compact support, are the
classical derivatives a.e. (as in `P/Infra/Sobolev/Paths.lean`). -/
theorem der_toHk_ae_eq_partialD {k : ℕ} {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (γ : SobIdx k) :
    (toHk k f).der γ =ᵐ[volume] partialD γ.1 f := by
  have hmem : MemH k f := (memH_of_contDiff_hasCompactSupport hf hc k).1
  have htest : IsTestFn univ f := ⟨hf, hc, subset_univ _⟩
  have h1 : HasWeakDerivOn univ (pdList γ.1) f ((toHk k f).der γ) :=
    ((toHk k f).hasWeakDeriv γ).congr_ae
      (by filter_upwards [toHk_fn hmem] with x hx _ using hx)
      (Eventually.of_forall fun _ _ => rfl)
  have h2 : HasWeakDerivOn univ (pdList γ.1) f (partialD γ.1 f) :=
    hasWeakDerivOn_of_contDiffOn isOpen_univ (n := γ.1.1 + γ.1.2) (by simp)
      (hf.of_le (by exact_mod_cast le_top)).contDiffOn
  have hl1 : LocallyIntegrableOn ((toHk k f).der γ) univ :=
    ((Lp.memLp _).locallyIntegrable (by norm_num)).locallyIntegrableOn univ
  have hl2 : LocallyIntegrableOn (partialD γ.1 f) univ :=
    ((htest.partialD γ.1).continuous.locallyIntegrable).locallyIntegrableOn univ
  filter_upwards [HasWeakDerivOn.ae_eq isOpen_univ hl1 hl2 h1 h2] with x hx using hx trivial

/-- `⟪f, g⟫_{H^k} = ∑_{|γ| ≤ k} ∫ conj(∂^γ f) ∂^γ g` for smooth compactly supported `f`, `g`. -/
theorem inner_toHk_eq {k : ℕ} {f g : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    inner ℂ (toHk k f) (toHk k g) =
      ∑ γ ∈ multiIdx k, ∫ x, conj (partialD γ f x) * partialD γ g x := by
  rw [Hk.inner_eq, ← Finset.sum_coe_sort (multiIdx k)]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [der_toHk_ae_eq_partialD hf hfc γ, der_toHk_ae_eq_partialD hg hgc γ]
    with x h1 h2
  have e1 : ((toHk k f : SobTuple k).ofLp γ : ℂ → ℂ) x = partialD γ.1 f x := h1
  have e2 : ((toHk k g : SobTuple k).ofLp γ : ℂ → ℂ) x = partialD γ.1 g x := h2
  rw [e1, e2, RCLike.inner_apply']

/-! ### Time derivatives of jointly smooth families -/

section Family

variable {w : ℝ → ℂ → ℂ}

theorem hasDerivAt_time (hw : ContDiff ℝ ∞ (fun p : ℝ × ℂ => w p.1 p.2)) (t : ℝ) (x : ℂ) :
    HasDerivAt (fun s => w s x) (fderiv ℝ (fun p : ℝ × ℂ => w p.1 p.2) (t, x) (1, 0)) t := by
  have h1 : HasFDerivAt (fun p : ℝ × ℂ => w p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℂ => w p.1 p.2) (t, x)) (t, x) :=
    ((hw.differentiable (by simp)) (t, x)).hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℂ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact h1.comp_hasDerivAt t h2

theorem contDiff_timeDeriv (hw : ContDiff ℝ ∞ (fun p : ℝ × ℂ => w p.1 p.2)) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => deriv (fun s => w s x) t) := by
  have e : (fun x => deriv (fun s => w s x) t) =
      fun x => fderiv ℝ (fun p : ℝ × ℂ => w p.1 p.2) (t, x) (1, 0) :=
    funext fun x => (hasDerivAt_time hw t x).deriv
  rw [e]
  have hd : ContDiff ℝ ∞ (fderiv ℝ (fun p : ℝ × ℂ => w p.1 p.2)) :=
    ContDiff.fderiv_right (m := ∞) hw (by simp)
  exact (hd.clm_apply contDiff_const).comp ((contDiff_const (c := t)).prodMk contDiff_id)

theorem hasCompactSupport_timeDeriv {K : Set ℂ} (hK : IsCompact K) {I : Set ℝ} (hI : IsOpen I)
    (hsupp : ∀ t ∈ I, ∀ x ∉ K, w t x = 0) {t : ℝ} (ht : t ∈ I) :
    HasCompactSupport (fun x => deriv (fun s => w s x) t) := by
  refine HasCompactSupport.intro hK fun x hx => ?_
  have hev : (fun s => w s x) =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
    filter_upwards [hI.mem_nhds ht] with s hs using hsupp s hs x hx
  rw [hev.deriv_eq]
  simp

theorem contDiff_slice (hw : ContDiff ℝ ∞ (fun p : ℝ × ℂ => w p.1 p.2)) (s : ℝ) :
    ContDiff ℝ ∞ (w s) :=
  hw.comp ((contDiff_const (c := s)).prodMk contDiff_id)

/-- `d/dt ‖w(t)‖²_{H^k} = 2 Re ∑_{|γ| ≤ k} ∫ conj(∂^γ w(t)) ∂^γ ∂_t w(t)`. -/
theorem hasDerivAt_normH_sq {k : ℕ} (hw : ContDiff ℝ ∞ (fun p : ℝ × ℂ => w p.1 p.2))
    {K : Set ℂ} (hK : IsCompact K) {I : Set ℝ} (hI : IsOpen I)
    (hsupp : ∀ t ∈ I, ∀ x ∉ K, w t x = 0) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => normH k (w s) ^ 2)
      (2 * (∑ γ ∈ multiIdx k, ∫ x, conj (partialD γ (w t) x) *
        partialD γ (fun x => deriv (fun s => w s x) t) x).re) t := by
  have hwc : ∀ s ∈ I, HasCompactSupport (w s) := fun s hs =>
    HasCompactSupport.intro hK fun x hx => hsupp s hs x hx
  have h1 := hasDerivAt_norm_sq_Hk (hasDerivAt_toHk_of_contDiff (k := k) hw hK hI hsupp ht)
  rw [inner_toHk_eq (contDiff_slice hw t) (hwc t ht) (contDiff_timeDeriv hw t)
    (hasCompactSupport_timeDeriv hK hI hsupp ht)] at h1
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hI.mem_nhds ht] with s hs
  rw [norm_toHk (memH_of_contDiff_hasCompactSupport (contDiff_slice hw s) (hwc s hs) k).1]

/-- The top-order energy `𝓗(t) = ∑_{|α| = k+1} ‖∂^α w(t)‖²_{L²}` has derivative
`2 Re ∑_{|α| = k+1} ∫ conj(∂^α w(t)) ∂^α ∂_t w(t)`. -/
theorem hasDerivAt_topEnergy (k : ℕ) (hw : ContDiff ℝ ∞ (fun p : ℝ × ℂ => w p.1 p.2))
    {K : Set ℂ} (hK : IsCompact K) {I : Set ℝ} (hI : IsOpen I)
    (hsupp : ∀ t ∈ I, ∀ x ∉ K, w t x = 0) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => ∑ α ∈ Finset.antidiagonal (k + 1), l2 (partialD α (w s)) ^ 2)
      (2 * (∑ α ∈ Finset.antidiagonal (k + 1), ∫ x, conj (partialD α (w t) x) *
        partialD α (fun x => deriv (fun s => w s x) t) x).re) t := by
  have hwc : ∀ s ∈ I, HasCompactSupport (w s) := fun s hs =>
    HasCompactSupport.intro hK fun x hx => hsupp s hs x hx
  have h1 := hasDerivAt_normH_sq (k := k + 1) hw hK hI hsupp ht
  have h0 := hasDerivAt_normH_sq (k := k) hw hK hI hsupp ht
  have h2 := h1.sub h0
  rw [sum_multiIdx_succ, Complex.add_re, mul_add, add_sub_cancel_left] at h2
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [hI.mem_nhds ht] with s hs
  simp only [Pi.sub_apply]
  rw [normH_succ_sq_eq (contDiff_slice hw s) (hwc s hs) k]
  ring

end Family

/-! ### The transport term and Cauchy–Schwarz -/

theorem integrable_conj_mul {f g : ℂ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) : Integrable (fun x => conj (f x) * g x) := by
  have hc : HasCompactSupport (fun x => conj (f x) * g x) := by
    refine HasCompactSupport.intro hfc fun x hx => ?_
    simp [image_eq_zero_of_notMem_tsupport hx]
  exact ((Complex.continuous_conj.comp hf).mul hg).integrable_of_hasCompactSupport hc

/-- `Re ∫ conj(f) u·∇f = ½ ∫ u·∇|f|² = 0` when `div u = 0` weakly. -/
theorem re_integral_conj_mul_fderiv_eq_zero {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {u : ℂ → ℂ} (hu : Continuous u)
    (hdiv : Prelim.IsWeaklyDivFree u) :
    (∫ x, conj (f x) * fderiv ℝ f x (u x)).re = 0 := by
  set φ : ℂ → ℝ := fun x => ‖f x‖ ^ 2 with hφdef
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := (contDiff_norm_sq ℝ).comp hf
  have hφc : HasCompactSupport φ := by
    refine HasCompactSupport.intro hc fun x hx => ?_
    simp [hφdef, image_eq_zero_of_notMem_tsupport hx]
  obtain ⟨-, h0⟩ := hdiv φ hφ hφc
  have hdf : ∀ x, DifferentiableAt ℝ f x := fun x => (hf.differentiable (by simp)) x
  have hderiv : ∀ x, fderiv ℝ φ x (u x) = 2 * (conj (f x) * fderiv ℝ f x (u x)).re := by
    intro x
    have h := (hdf x).hasFDerivAt.norm_sq
    rw [h.fderiv, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, Complex.inner, mul_comm (fderiv ℝ f x (u x))]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have hint : Integrable (fun x => conj (f x) * fderiv ℝ f x (u x)) :=
    integrable_conj_mul hf.continuous hc ((hf.continuous_fderiv (by simp)).clm_apply hu)
  have hre : ∫ x, (conj (f x) * fderiv ℝ f x (u x)).re =
      (∫ x, conj (f x) * fderiv ℝ f x (u x)).re := integral_re hint
  rw [← hre]
  have e : (fun x => (conj (f x) * fderiv ℝ f x (u x)).re) =
      fun x => (1 / 2 : ℝ) * fderiv ℝ φ x (u x) := by
    funext x
    rw [hderiv x]
    ring
  rw [e, integral_const_mul, h0, mul_zero]

/-- Cauchy–Schwarz: `|∫ conj(f) g| ≤ ‖f‖_{L²} ‖g‖_{L²}`. -/
theorem norm_integral_conj_mul_le {f g : ℂ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖∫ x, conj (f x) * g x‖ ≤ l2 f * l2 g := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)
  rw [L2.inner_def, Lp.norm_toLp, Lp.norm_toLp] at h
  have e : ∫ x, inner ℂ ((hf.toLp f : ℂ → ℂ) x) ((hg.toLp g : ℂ → ℂ) x) =
      ∫ x, conj (f x) * g x := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2, RCLike.inner_apply']
  rw [e] at h
  exact h

end NonUniqueEuler.Smooth.IterHsH
