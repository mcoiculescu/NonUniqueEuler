import Mathlib.Analysis.InnerProductSpace.Calculus
import NonUniqueEuler.Defs.Infra.SobolevSpace
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.H.Infra.Sobolev.Paths.Taylor

/-!
# Proof: time-dependent `H^k` functions (library I-HK)

Proof of `I/Infra/Sobolev/Paths.lean` (same declarations, same statements).

* For a smooth compactly supported `f`, the stored derivatives of `toHk k f` are the classical
  `∂^γ f` a.e. (`der_toHk_ae_eq_partialD`: uniqueness of weak derivatives).
* For the jointly smooth family `W(s, x) = w s x`, `∂^γ W(s, ·)` is the slice of a jointly
  smooth `H_γ`, and `∂^γ ∂_t W(t, ·) = ∂_t H_γ(t, ·)` (`PathsH.exists_joint_iterDirDeriv`,
  symmetry of second derivatives).
* The first-order Taylor remainder of `H_γ` in time is `≤ ε |s - t| 1_K` uniformly in space
  (`PathsH.eLpNorm_taylor_le`: mean value theorem plus uniform continuity on a compact set),
  so every component of `toHk k (w s) - toHk k (w t) - (s - t) • toHk k (∂_t w(t))` is
  `o(|s - t|)` in `L²`, and so is the `H^k` norm `(∑_γ ‖·‖²)^{1/2}`.
* The norm identity is `HasDerivAt.norm_sq` for the real inner product space underlying
  `Hk k` (`InnerProductSpace.complexToReal`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace NonUniqueEuler.Sob

/-- The stored derivatives of `toHk k f`, for `f` smooth with compact support, are the
classical derivatives a.e. -/
theorem PathsH.der_toHk_ae_eq_partialD {k : ℕ} {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
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

theorem hasDerivAt_toHk_of_contDiff {k : ℕ} {w : ℝ → ℂ → ℂ}
    (hw : ContDiff ℝ ∞ (fun p : ℝ × ℂ => w p.1 p.2)) {K : Set ℂ} (hK : IsCompact K) {I : Set ℝ}
    (hI : IsOpen I) (hsupp : ∀ t ∈ I, ∀ x ∉ K, w t x = 0) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => toHk k (w s)) (toHk k (fun x => deriv (fun s => w s x) t)) t := by
  set W : ℝ × ℂ → ℂ := fun p => w p.1 p.2 with hWdef
  have hU : IsOpen (I ×ˢ Kᶜ) := hI.prod hK.isClosed.isOpen_compl
  have hWU : ∀ p ∈ I ×ˢ Kᶜ, W p = 0 := fun p hp => hsupp p.1 hp.1 p.2 hp.2
  have hdiff : ∀ p, DifferentiableAt ℝ W p := fun p => (hw.differentiable (by simp)) p
  have hslice : ContDiff ℝ ∞ (fun x : ℂ => ((t : ℝ), x)) := contDiff_const.prodMk contDiff_id
  -- the time derivative
  have hwt : (fun x => deriv (fun s => w s x) t) = fun x => fderiv ℝ W (t, x) (1, 0) :=
    funext fun x => (PathsH.hasDerivAt_time_slice (hdiff (t, x))).deriv
  rw [hwt]
  -- smoothness and supports of the slices
  have hws : ∀ s, ContDiff ℝ ∞ (w s) := fun s =>
    hw.comp ((contDiff_const (c := s)).prodMk contDiff_id)
  have hwc : ∀ s ∈ I, HasCompactSupport (w s) := fun s hs =>
    HasCompactSupport.intro hK fun x hx => hsupp s hs x hx
  have hwts : ContDiff ℝ ∞ (fun x => fderiv ℝ W (t, x) (1, 0)) :=
    (PathsH.contDiff_fderiv_apply hw (1, 0)).comp hslice
  have hwtc : HasCompactSupport (fun x => fderiv ℝ W (t, x) (1, 0)) :=
    HasCompactSupport.intro hK fun x hx => by
      simp [PathsH.fderiv_eq_zero_of_eqOn_zero hU hWU (p := (t, x)) ⟨ht, hx⟩]
  -- the joint spatial derivatives
  choose H hH hHU hsl htm using
    fun γ : SobIdx k => PathsH.exists_joint_iterDirDeriv hw hU hWU (pdList γ.1)
  have hHsupp : ∀ γ, ∀ s ∈ I, ∀ x ∉ K, H γ (s, x) = 0 := fun γ s hs x hx =>
    hHU γ (s, x) ⟨hs, hx⟩
  set D' : Hk k := toHk k (fun x => fderiv ℝ W (t, x) (1, 0)) with hD'
  -- the components of the remainder
  have hcomp : ∀ s ∈ I, ∀ γ : SobIdx k,
      ‖((toHk k (w s) - toHk k (w t) - (s - t) • D' : Hk k) : SobTuple k).ofLp γ‖ =
      (eLpNorm (fun x => H γ (s, x) - H γ (t, x) - (s - t) • fderiv ℝ (H γ) (t, x) (1, 0)) 2
        volume).toReal := by
    intro s hs γ
    rw [Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    have e1 := PathsH.der_toHk_ae_eq_partialD (hws s) (hwc s hs) γ
    have e2 := PathsH.der_toHk_ae_eq_partialD (hws t) (hwc t ht) γ
    have e3 := PathsH.der_toHk_ae_eq_partialD hwts hwtc (k := k) γ
    have hcoe : ((toHk k (w s) - toHk k (w t) - (s - t) • D' : Hk k) : SobTuple k).ofLp γ =
        (toHk k (w s) : SobTuple k).ofLp γ - (toHk k (w t) : SobTuple k).ofLp γ -
          (s - t) • (D' : SobTuple k).ofLp γ := rfl
    rw [hcoe]
    filter_upwards [Lp.coeFn_sub ((toHk k (w s) : SobTuple k).ofLp γ -
        (toHk k (w t) : SobTuple k).ofLp γ) ((s - t) • (D' : SobTuple k).ofLp γ),
      Lp.coeFn_sub ((toHk k (w s) : SobTuple k).ofLp γ) ((toHk k (w t) : SobTuple k).ofLp γ),
      Lp.coeFn_smul (s - t) ((D' : SobTuple k).ofLp γ), e1, e2, e3] with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.sub_apply, h2, h3, Pi.sub_apply, Pi.smul_apply]
    unfold Hk.der at h4 h5 h6
    rw [h4, h5, h6]
    exact congrArg₂ _ (congrArg₂ _ (hsl γ s x) (hsl γ t x)) (congrArg _ (htm γ t x))
  -- the `H^k` norm of the remainder is `o(|s - t|)`
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  set N : ℝ := (Fintype.card (SobIdx k) : ℝ) with hN
  set cK : ℝ := (volume K ^ (1 / (2 : ℝ))).toReal with hcK
  set a : ℝ := Real.sqrt N * cK with ha_def
  have ha : 0 ≤ a := mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg
  set ε : ℝ := c / (a + 1) with hε_def
  have hε : 0 < ε := div_pos hc (by linarith)
  have hev : ∀ᶠ s in 𝓝 t, s ∈ I ∧ ∀ γ : SobIdx k,
      (eLpNorm (fun x => H γ (s, x) - H γ (t, x) - (s - t) • fderiv ℝ (H γ) (t, x) (1, 0)) 2
        volume).toReal ≤ ε * |s - t| * cK :=
    Filter.Eventually.and (hI.mem_nhds ht)
      (eventually_all.2 fun γ => PathsH.eLpNorm_taylor_le (hH γ) hK hI (hHsupp γ) ht hε)
  filter_upwards [hev] with s ⟨hs, hγ⟩
  rw [Hk.norm_eq, Real.norm_eq_abs]
  have hb : 0 ≤ ε * |s - t| * cK := by positivity
  calc _ ≤ Real.sqrt (∑ _γ : SobIdx k, (ε * |s - t| * cK) ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro γ _
        rw [hcomp s hs γ]
        exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hγ γ) 2
    _ = Real.sqrt N * (ε * |s - t| * cK) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _),
          Real.sqrt_sq hb]
    _ = a * ε * |s - t| := by rw [ha_def]; ring
    _ ≤ c * |s - t| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        rw [hε_def, mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith

theorem continuousOn_toHk_of_contDiff {k : ℕ} {w : ℝ → ℂ → ℂ}
    (hw : ContDiff ℝ ∞ (fun p : ℝ × ℂ => w p.1 p.2)) {K : Set ℂ} (hK : IsCompact K) {I : Set ℝ}
    (hI : IsOpen I) (hsupp : ∀ t ∈ I, ∀ x ∉ K, w t x = 0) :
    ContinuousOn (fun s => toHk k (w s)) I := fun _ hs =>
  (hasDerivAt_toHk_of_contDiff hw hK hI hsupp hs).continuousAt.continuousWithinAt

/-- `d/dt ‖v(t)‖²_{H^k} = 2 Re ⟪v(t), v'(t)⟫_{H^k}`. -/
theorem hasDerivAt_norm_sq_Hk {k : ℕ} {v : ℝ → Hk k} {v' : Hk k} {t : ℝ}
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => ‖v s‖ ^ 2) (2 * (inner ℂ (v t) v').re) t := by
  let _ : InnerProductSpace ℝ (Hk k) := InnerProductSpace.complexToReal
  exact hv.norm_sq

end NonUniqueEuler.Sob
