import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.H.Sec5.ReductionEq.Paths
import NonUniqueEuler.H.Sec5.ReductionEq.Config
import NonUniqueEuler.H.Sec5.ReductionEq.Equation

/-!
# Proof: `lem:reduction`(3) and `eq:ring` (the perturbation equation of one ring)

Proof of `I/Sec5/ReductionEq.lean` (same declaration, same statement), following
`05_single_ring.tex:204-217`.

* `w = ω_r - Φ` is real by construction (`RingConfig.w_im`).
* `w ∈ C^∞(ℝ × ℝ²)` (`RedEqH.w_contDiff`), and the supports of `w(t)`, `t ∈ (-1, T+1)`, lie in a
  fixed compact set (`RedEqH.exists_compact_supp`); for `t ∈ [0,T]`, `w(t)` and `∂_t w(t)` vanish
  outside `N` (`supp ω_r(t) ⊂ N`, `supp Φ ⊂ N`). So `t ↦ w(t)` is a `C¹` path in `Y^k(N)` on
  `[0,T]` with derivative `∂_t w` (`RedEqH.hasDerivWithinAt_toY_of_contDiff`, from
  `I/Infra/Sobolev/Paths.lean`), and `w(t), ∂_t w(t) ∈ X^k` (smooth, compactly supported in `N`,
  `3`-fold symmetric).
* `∂_t w(t) = L(G)w + B(w,w) - h·∇w - h·∇Φ` a.e. for `t ∈ [0,T]` (`RedEqH.ringRHS_ae_eq_deriv`:
  transport equation, `lem:reduction`(2), `x^⊥·∇Φ = 0`); `Sect.toY` and `X^k` membership only
  see the a.e. class (`RedEqH.toY_congr_ae`, `memXFn_congr_ae`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- `X^k` membership only depends on the a.e. class. -/
private theorem memXFn_congr_ae {k : ℕ} {f g : ℂ → ℂ} (hf : Lin.MemXFn k f)
    (hfg : f =ᵐ[volume] g) : Lin.MemXFn k g := by
  obtain ⟨hH, hS, hR⟩ := hf
  refine ⟨(hH.congr_ae hfg).1, ?_, ?_⟩
  · filter_upwards [hS, hfg] with x hx hxe hxN
    rw [← hxe]
    exact hx hxN
  · have h1 : (fun x => f (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x)) =ᵐ[volume]
        fun x => g (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x) :=
      (Polar.measurePreserving_rot _).quasiMeasurePreserving.ae_eq_comp hfg
    exact h1.symm.trans (hR.trans hfg)

/-- A jointly smooth family, with spatial supports in a fixed compact set for `t ∈ (-1, T+1)`,
supported in `N` and `3`-fold symmetric for `t ∈ [0,T]`, lies in `X^k` at every `t ∈ [0,T]`. -/
private theorem memXFn_of_family {k : ℕ} {T : ℝ} {u : ℝ → ℂ → ℂ}
    (hu : ContDiff ℝ ∞ (fun p : ℝ × ℂ => u p.1 p.2)) {K' : Set ℂ} (hK' : IsCompact K')
    (hsupp : ∀ t ∈ Ioo (-1 : ℝ) (T + 1), ∀ x ∉ K', u t x = 0)
    (hN : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∉ annN, u t x = 0)
    (hrot : ∀ (t : ℝ) (x : ℂ), u t (rot (2 * Real.pi / 3) x) = u t x) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : Lin.MemXFn k (u t) := by
  have htI : t ∈ Ioo (-1 : ℝ) (T + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨(Sob.memH_of_contDiff_hasCompactSupport (RedEqH.contDiff_slice hu t)
    (HasCompactSupport.intro hK' (hsupp t htI)) k).1,
    Eventually.of_forall fun x hx => hN t ht x hx, ?_⟩
  have h3 : (2 * Real.pi / ((3 : ℕ) : ℝ)) = 2 * Real.pi / 3 := by norm_num
  show (fun x => u t (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x)) =ᵐ[volume] u t
  rw [h3]
  exact Eventually.of_forall fun x => hrot t x

/-- **`lem:reduction`(3) and `eq:ring`** (`05_single_ring.tex:118-126`). Under the hypotheses
of `lem:reduction` on `[0,T]`, if `supp ω_r(t) ⊂ N` for `t ∈ [0,T]`, then `w = ω_r - Φ` is real
valued, lies in `C¹([0,T]; X^k)` for every `k`, and solves
`∂_t w = L(G)w + B(w,w) - h·∇w - h·∇Φ` on `[0,T]` (`RingConfig.PertEq`). -/
theorem reduction_eq (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {c : RingConfig} {T : ℝ}
    (hc : c.Hyp T) (hsupp : c.RingSupportedIn T annN) :
    (∀ (t : ℝ) (x : ℂ), (c.w χ t x).im = 0) ∧ c.PertEq χ T := by
  refine ⟨c.w_im χ, fun k => ?_⟩
  have hT := hc.T_pos
  have hW : ContDiff ℝ ∞ (fun p : ℝ × ℂ => c.w χ p.1 p.2) := RedEqH.w_contDiff hχ hc
  have hW' : ContDiff ℝ ∞ (fun p : ℝ × ℂ => deriv (fun s => c.w χ s p.2) p.1) :=
    RedEqH.contDiff_deriv_fst hW
  obtain ⟨K', hK', hsuppK'⟩ := RedEqH.exists_compact_supp hχ hc
  have hI : IsOpen (Ioo (-1 : ℝ) (T + 1)) := isOpen_Ioo
  have hJI : Icc (0 : ℝ) T ⊆ Ioo (-1 : ℝ) (T + 1) :=
    Icc_subset_Ioo (by norm_num) (by linarith)
  have hKm : MeasurableSet annN := isCompact_annN.isClosed.measurableSet
  have hJ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∉ annN, c.w χ t x = 0 :=
    fun t ht x hx => RedEqH.w_eq_zero_of_not_mem hχ hsupp ht hx
  have hJ' : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∉ annN, deriv (fun s => c.w χ s x) t = 0 := by
    intro t ht x hx
    rw [RedEqH.deriv_w χ hc t x, RedEqH.fderiv_ringPart_eq_zero hsupp ht hx]
    simp
  have hsupp' : ∀ t ∈ Ioo (-1 : ℝ) (T + 1), ∀ x ∉ K', deriv (fun s => c.w χ s x) t = 0 :=
    fun t ht x hx => RedEqH.deriv_eq_zero_of_supp hI hsuppK' ht hx
  have hrot : ∀ (t : ℝ) (x : ℂ), c.w χ t (rot (2 * Real.pi / 3) x) = c.w χ t x :=
    RedEqH.w_rot hχ hc
  have hrot' : ∀ (t : ℝ) (x : ℂ),
      deriv (fun s => c.w χ s (rot (2 * Real.pi / 3) x)) t = deriv (fun s => c.w χ s x) t := by
    intro t x
    congr 1
    funext s
    exact hrot s x
  have hae : ∀ t ∈ Icc (0 : ℝ) T,
      (fun x => ringRHS χ c.G (c.h t) (c.w χ t) x) =ᵐ[volume]
        fun x => deriv (fun s => c.w χ s x) t :=
    fun t ht => RedEqH.ringRHS_ae_eq_deriv hχ hc hsupp ht
  refine ⟨⟨fun t ht => memXFn_of_family hW hK' hsuppK' hJ hrot ht,
      RedEqH.continuousOn_toY_of_contDiff hW hK' hI hsuppK' hJI hKm hJ⟩,
    ⟨fun t ht => memXFn_congr_ae
        (memXFn_of_family (u := fun t x => deriv (fun s => c.w χ s x) t) hW' hK' hsupp' hJ'
          hrot' ht) (hae t ht).symm,
      (RedEqH.continuousOn_toY_of_contDiff (u := fun t x => deriv (fun s => c.w χ s x) t)
        hW' hK' hI hsupp' hJI hKm hJ').congr fun t ht => RedEqH.toY_congr_ae (hae t ht)⟩,
    fun t ht => ?_⟩
  rw [RedEqH.toY_congr_ae (hae t ht)]
  exact RedEqH.hasDerivWithinAt_toY_of_contDiff hW hK' hI hsuppK' hJI hKm hJ hJ' ht

end OneRing

end NonUniqueEuler
