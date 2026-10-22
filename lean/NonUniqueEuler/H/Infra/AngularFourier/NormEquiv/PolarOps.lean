import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.I.Infra.Sobolev.Leibniz
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.CkNorm.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Helper for `P/Infra/AngularFourier/NormEquiv`: the polar operators `∂_r`, `∂_θ` on `H^k`
functions supported in an annulus

For `0 < ρ₋` and `F ∈ H^{m+1}` vanishing a.e. outside `N_* = {ρ₋ ≤ |x| ≤ ρ₊}`, the weak polar
derivatives `radDeriv F = cos θ ∂₁F + sin θ ∂₂F` and `thetaDeriv F = x₁∂₂F - x₂∂₁F` lie in `H^m`,
vanish outside `N_*`, and `‖·‖_{H^m} ≤ C ‖F‖_{H^{m+1}}` (Leibniz with the coefficients, which are
smooth near `N_*`). Iterating: `∂_θ^n ∂_r^i w ∈ H^{k-i-n}` for `w ∈ H^k`, `i + n ≤ k`, with norm
`≤ C ‖w‖_{H^k}` (`polar_iter`). This is the "easy direction" of the manuscript's comparison of
`‖w‖_{H^k}` with the polar derivatives (`04_ring.tex:851-857`).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Ang.NormEquivAux

open Sob

theorem isClosed_ann (ρm ρp : ℝ) : IsClosed {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp} :=
  (isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)

theorem isCompact_ann (ρm ρp : ℝ) : IsCompact {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp} := by
  refine (isCompact_closedBall (0 : ℂ) ρp).of_isClosed_subset (isClosed_ann ρm ρp) ?_
  intro x hx
  simpa [Metric.mem_closedBall, dist_zero_right] using hx.2

theorem ann_subset_ne {ρm ρp : ℝ} (hρm : 0 < ρm) :
    {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp} ⊆ {0}ᶜ := by
  intro x hx h0
  simp only [mem_singleton_iff] at h0
  have := hx.1
  rw [h0, norm_zero] at this
  linarith

/-- `x ↦ x.re / |x|` (resp. `x.im / |x|`) is smooth on `ℂ \ {0}`. -/
theorem contDiffOn_re_div_norm (m : ℕ) :
    ContDiffOn ℝ m (fun x : ℂ => ((x.re / ‖x‖ : ℝ) : ℂ)) {0}ᶜ := by
  have h1 : ContDiffOn ℝ m (fun x : ℂ => x.re / ‖x‖) {0}ᶜ := by
    refine (Complex.reCLM.contDiff.contDiffOn).div ?_ ?_
    · intro x hx
      exact (contDiffAt_norm ℝ (by simpa using hx)).contDiffWithinAt
    · intro x hx
      exact norm_ne_zero_iff.2 (by simpa using hx)
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h1

theorem contDiffOn_im_div_norm (m : ℕ) :
    ContDiffOn ℝ m (fun x : ℂ => ((x.im / ‖x‖ : ℝ) : ℂ)) {0}ᶜ := by
  have h1 : ContDiffOn ℝ m (fun x : ℂ => x.im / ‖x‖) {0}ᶜ := by
    refine (Complex.imCLM.contDiff.contDiffOn).div ?_ ?_
    · intro x hx
      exact (contDiffAt_norm ℝ (by simpa using hx)).contDiffWithinAt
    · intro x hx
      exact norm_ne_zero_iff.2 (by simpa using hx)
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h1

theorem memCk_re_div_norm (m : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) :
    MemCk m {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp} (fun x : ℂ => ((x.re / ‖x‖ : ℝ) : ℂ)) :=
  IsCkNear.memCk_of_isCompact
    ⟨{0}ᶜ, isOpen_compl_singleton, ann_subset_ne hρm, contDiffOn_re_div_norm m⟩
    (isCompact_ann ρm ρp)

theorem memCk_im_div_norm (m : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) :
    MemCk m {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp} (fun x : ℂ => ((x.im / ‖x‖ : ℝ) : ℂ)) :=
  IsCkNear.memCk_of_isCompact
    ⟨{0}ᶜ, isOpen_compl_singleton, ann_subset_ne hρm, contDiffOn_im_div_norm m⟩
    (isCompact_ann ρm ρp)

theorem memCk_re (m : ℕ) (ρm ρp : ℝ) :
    MemCk m {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp} (fun x : ℂ => ((x.re : ℝ) : ℂ)) := by
  refine IsCkNear.memCk_of_isCompact ⟨univ, isOpen_univ, subset_univ _, ?_⟩ (isCompact_ann ρm ρp)
  exact (Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff).contDiffOn

theorem memCk_im (m : ℕ) (ρm ρp : ℝ) :
    MemCk m {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp} (fun x : ℂ => ((x.im : ℝ) : ℂ)) := by
  refine IsCkNear.memCk_of_isCompact ⟨univ, isOpen_univ, subset_univ _, ?_⟩ (isCompact_ann ρm ρp)
  exact (Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).contDiffOn

/-- One coefficient times one first derivative: `χ ∂_γ F` with `|γ| = 1`. -/
theorem coeff_mul_partial {m : ℕ} {ρm ρp : ℝ} {χ F : ℂ → ℂ} {γ : ℕ × ℕ} (hγ : γ.1 + γ.2 = 1)
    (hχ : MemCk m {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp} χ) (hF : MemH (m + 1) F)
    (hFK : ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → F x = 0) :
    MemH m (fun x => χ x * weakPartial γ F x) ∧
      (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → χ x * weakPartial γ F x = 0) ∧
      normH m (fun x => χ x * weakPartial γ F x) ≤
        (m + 1) * 2 ^ m * normCk m {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp} χ * normH (m + 1) F := by
  have hF' : MemH (m + (γ.1 + γ.2)) F := by rw [hγ]; exact hF
  obtain ⟨hd, hdn⟩ := MemH.weakPartial hF'
  rw [hγ] at hdn
  have hγk : γ ∈ multiIdx (m + 1) := mem_multiIdx.2 (by omega)
  have hdK := MemH.weakPartial_eq_zero_outside (isClosed_ann ρm ρp) hF hFK hγk
  obtain ⟨hmem, hnorm⟩ := MemH.mul_of_memCk (isClosed_ann ρm ρp) hd hdK hχ
  refine ⟨hmem, ?_, ?_⟩
  · filter_upwards [hdK] with x hx hxK
    rw [hx hxK, mul_zero]
  · refine hnorm.trans ?_
    have h0 : 0 ≤ (m + 1 : ℝ) * 2 ^ m * normCk m {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp} χ :=
      mul_nonneg (by positivity) (normCk_nonneg _ _ _)
    exact mul_le_mul_of_nonneg_left hdn h0

theorem radDeriv_eq (F : ℂ → ℂ) :
    radDeriv F = (fun x => ((x.re / ‖x‖ : ℝ) : ℂ) * weakPartial (1, 0) F x) +
      (fun x => ((x.im / ‖x‖ : ℝ) : ℂ) * weakPartial (0, 1) F x) := rfl

theorem thetaDeriv_eq (F : ℂ → ℂ) :
    thetaDeriv F = (fun x => ((x.re : ℝ) : ℂ) * weakPartial (0, 1) F x) -
      (fun x => ((x.im : ℝ) : ℂ) * weakPartial (1, 0) F x) := rfl

/-- `∂_r` maps `H^{m+1}` functions supported in `N_*` to `H^m` functions supported in `N_*`, with
a bound uniform in `m ≤ k`. -/
theorem radDeriv_bound (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m ≤ k, ∀ F : ℂ → ℂ, MemH (m + 1) F →
      (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → F x = 0) →
      MemH m (radDeriv F) ∧ (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → radDeriv F x = 0) ∧
        normH m (radDeriv F) ≤ C * normH (m + 1) F := by
  set K : Set ℂ := {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp}
  have hc := memCk_re_div_norm k (ρp := ρp) hρm
  have hs := memCk_im_div_norm k (ρp := ρp) hρm
  refine ⟨(k + 1) * 2 ^ k * (normCk k K (fun x : ℂ => ((x.re / ‖x‖ : ℝ) : ℂ)) +
    normCk k K (fun x : ℂ => ((x.im / ‖x‖ : ℝ) : ℂ))), by
      have := normCk_nonneg k K (fun x : ℂ => ((x.re / ‖x‖ : ℝ) : ℂ))
      have := normCk_nonneg k K (fun x : ℂ => ((x.im / ‖x‖ : ℝ) : ℂ))
      positivity, fun m hm F hF hFK => ?_⟩
  obtain ⟨h1, h1K, h1n⟩ := coeff_mul_partial (γ := (1, 0)) rfl (hc.mono_order hm) hF hFK
  obtain ⟨h2, h2K, h2n⟩ := coeff_mul_partial (γ := (0, 1)) rfl (hs.mono_order hm) hF hFK
  obtain ⟨hadd, haddn⟩ := MemH.add h1 h2
  rw [radDeriv_eq]
  refine ⟨hadd, ?_, ?_⟩
  · filter_upwards [h1K, h2K] with x hx1 hx2 hx
    simp only [Pi.add_apply, hx1 hx, hx2 hx, add_zero]
  · refine haddn.trans ?_
    have hcm := normCk_mono_order hc hm
    have hsm := normCk_mono_order hs hm
    have hmk : (m + 1 : ℝ) * 2 ^ m ≤ (k + 1) * 2 ^ k := by
      have : (m : ℝ) ≤ k := by exact_mod_cast hm
      gcongr
      norm_num
    have hn := normH_nonneg (m + 1) F
    have hc0 := normCk_nonneg m K (fun x : ℂ => ((x.re / ‖x‖ : ℝ) : ℂ))
    have hs0 := normCk_nonneg m K (fun x : ℂ => ((x.im / ‖x‖ : ℝ) : ℂ))
    calc _ ≤ (m + 1) * 2 ^ m * normCk m K (fun x : ℂ => ((x.re / ‖x‖ : ℝ) : ℂ)) * normH (m + 1) F
          + (m + 1) * 2 ^ m * normCk m K (fun x : ℂ => ((x.im / ‖x‖ : ℝ) : ℂ)) *
            normH (m + 1) F := add_le_add h1n h2n
      _ = ((m + 1) * 2 ^ m) * (normCk m K (fun x : ℂ => ((x.re / ‖x‖ : ℝ) : ℂ)) +
            normCk m K (fun x : ℂ => ((x.im / ‖x‖ : ℝ) : ℂ))) * normH (m + 1) F := by ring
      _ ≤ _ := by gcongr

/-- `∂_θ` maps `H^{m+1}` functions supported in `N_*` to `H^m` functions supported in `N_*`, with
a bound uniform in `m ≤ k`. -/
theorem thetaDeriv_bound (k : ℕ) (ρm ρp : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m ≤ k, ∀ F : ℂ → ℂ, MemH (m + 1) F →
      (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → F x = 0) →
      MemH m (thetaDeriv F) ∧ (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → thetaDeriv F x = 0) ∧
        normH m (thetaDeriv F) ≤ C * normH (m + 1) F := by
  set K : Set ℂ := {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp}
  have hc := memCk_re k ρm ρp
  have hs := memCk_im k ρm ρp
  refine ⟨(k + 1) * 2 ^ k * (normCk k K (fun x : ℂ => ((x.re : ℝ) : ℂ)) +
    normCk k K (fun x : ℂ => ((x.im : ℝ) : ℂ))), by
      have := normCk_nonneg k K (fun x : ℂ => ((x.re : ℝ) : ℂ))
      have := normCk_nonneg k K (fun x : ℂ => ((x.im : ℝ) : ℂ))
      positivity, fun m hm F hF hFK => ?_⟩
  obtain ⟨h1, h1K, h1n⟩ := coeff_mul_partial (γ := (0, 1)) rfl (hc.mono_order hm) hF hFK
  obtain ⟨h2, h2K, h2n⟩ := coeff_mul_partial (γ := (1, 0)) rfl (hs.mono_order hm) hF hFK
  obtain ⟨hsub, hsubn⟩ := MemH.sub h1 h2
  rw [thetaDeriv_eq]
  refine ⟨hsub, ?_, ?_⟩
  · filter_upwards [h1K, h2K] with x hx1 hx2 hx
    simp only [Pi.sub_apply, hx1 hx, hx2 hx, sub_zero]
  · refine hsubn.trans ?_
    have hcm := normCk_mono_order hc hm
    have hsm := normCk_mono_order hs hm
    have hmk : (m + 1 : ℝ) * 2 ^ m ≤ (k + 1) * 2 ^ k := by
      have : (m : ℝ) ≤ k := by exact_mod_cast hm
      gcongr
      norm_num
    have hn := normH_nonneg (m + 1) F
    have hc0 := normCk_nonneg m K (fun x : ℂ => ((x.re : ℝ) : ℂ))
    have hs0 := normCk_nonneg m K (fun x : ℂ => ((x.im : ℝ) : ℂ))
    calc _ ≤ (m + 1) * 2 ^ m * normCk m K (fun x : ℂ => ((x.re : ℝ) : ℂ)) * normH (m + 1) F
          + (m + 1) * 2 ^ m * normCk m K (fun x : ℂ => ((x.im : ℝ) : ℂ)) *
            normH (m + 1) F := add_le_add h1n h2n
      _ = ((m + 1) * 2 ^ m) * (normCk m K (fun x : ℂ => ((x.re : ℝ) : ℂ)) +
            normCk m K (fun x : ℂ => ((x.im : ℝ) : ℂ))) * normH (m + 1) F := by ring
      _ ≤ _ := by gcongr

/-- Iterating an operator that lowers the order by one. -/
theorem iter_bound {T : (ℂ → ℂ) → ℂ → ℂ} {k : ℕ} {ρm ρp C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ m, m + 1 ≤ k → ∀ F : ℂ → ℂ, MemH (m + 1) F →
      (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → F x = 0) →
      MemH m (T F) ∧ (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → T F x = 0) ∧
        normH m (T F) ≤ C * normH (m + 1) F) :
    ∀ i ≤ k, ∀ F : ℂ → ℂ, MemH k F → (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → F x = 0) →
      MemH (k - i) (T^[i] F) ∧ (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → T^[i] F x = 0) ∧
        normH (k - i) (T^[i] F) ≤ C ^ i * normH k F := by
  intro i
  induction i with
  | zero =>
    intro _ F hF hFK
    refine ⟨by simpa using hF, by simpa using hFK, by simp⟩
  | succ i ih =>
    intro hi F hF hFK
    obtain ⟨h1, h1K, h1n⟩ := ih (by omega) F hF hFK
    have he : k - i = (k - (i + 1)) + 1 := by omega
    rw [he] at h1 h1n
    obtain ⟨h2, h2K, h2n⟩ := hT (k - (i + 1)) (by omega) _ h1 h1K
    rw [Function.iterate_succ_apply']
    refine ⟨h2, h2K, h2n.trans ?_⟩
    rw [pow_succ]
    calc C * normH (k - (i + 1) + 1) (T^[i] F) ≤ C * (C ^ i * normH k F) :=
          mul_le_mul_of_nonneg_left h1n hC
      _ = C ^ i * C * normH k F := by ring

/-- The polar derivatives `∂_θ^n ∂_r^i w` (`i + n ≤ k`) of `w ∈ H^k` supported in `N_*` lie in
`H^{k-(i+n)}`, vanish outside `N_*`, and are bounded by `C ‖w‖_{H^k}`. -/
theorem polar_iter (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ → ℂ, MemH k w → (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → w x = 0) →
      ∀ i n : ℕ, i + n ≤ k →
        MemH (k - (i + n)) (thetaDeriv^[n] (radDeriv^[i] w)) ∧
          (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → thetaDeriv^[n] (radDeriv^[i] w) x = 0) ∧
          normH (k - (i + n)) (thetaDeriv^[n] (radDeriv^[i] w)) ≤ C * normH k w := by
  obtain ⟨Cr, hCr, hr⟩ := radDeriv_bound k (ρp := ρp) hρm
  obtain ⟨Ct, hCt, ht⟩ := thetaDeriv_bound k ρm ρp
  set D : ℝ := max 1 (max Cr Ct)
  have hD1 : 1 ≤ D := le_max_left _ _
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  refine ⟨D ^ k, pow_nonneg hD0 _, fun w hw hwK i n hin => ?_⟩
  have hR := iter_bound (T := radDeriv) hCr
    (fun m hm F hF hFK => hr m (by omega) F hF hFK) i (by omega) w hw hwK
  obtain ⟨hR1, hR2, hR3⟩ := hR
  have hT := iter_bound (T := thetaDeriv) (k := k - i) hCt
    (fun m hm F hF hFK => ht m (by omega) F hF hFK) n (by omega) _ hR1 hR2
  obtain ⟨hT1, hT2, hT3⟩ := hT
  have he : k - i - n = k - (i + n) := by omega
  rw [he] at hT1 hT3
  refine ⟨hT1, hT2, hT3.trans ?_⟩
  have hw0 := normH_nonneg k w
  have hCtD : Ct ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have hCrD : Cr ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hR0 := normH_nonneg (k - i) (radDeriv^[i] w)
  calc Ct ^ n * normH (k - i) (radDeriv^[i] w) ≤ D ^ n * (Cr ^ i * normH k w) := by
        gcongr
    _ ≤ D ^ n * (D ^ i * normH k w) := by gcongr
    _ = D ^ (i + n) * normH k w := by ring
    _ ≤ D ^ k * normH k w := by gcongr

end NonUniqueEuler.Ang.NormEquivAux
