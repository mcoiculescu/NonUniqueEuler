import NonUniqueEuler.H.Sec3.RenormAllT.Basic
import NonUniqueEuler.H.Sec3.RenormAllT.Continuity
import NonUniqueEuler.I.Sec3.LipRenorm
import NonUniqueEuler.I.Sec3.WeakCont
import NonUniqueEuler.I.Sec3.VelocityField
import NonUniqueEuler.I.Sec3.WeakContRep
import NonUniqueEuler.I.Sec3.CutoffGrad

/-!
# Helpers for `lem:renorm-all-t`: the tail bound eq:tail

Helper file of `P/Sec3/RenormAllT.lean` (fully proved).

`tail` (`03_compactness.tex:676-685`): `|ω|` satisfies `(te)` with datum `|ω^in|`
(`lem:lip-renorm`); `lem:weak-cont` gives a weakly continuous representative `ũ`, which agrees
with `|ω(t)|` for every `t ∈ [0,T)` (both are weakly continuous on `[0,T']`, `T' < T`, the
second by the strong `L²` continuity of `ω`); `lem:weak-cont`(b) with `ψ = ς_R` and
eq:conservation for `|·|` give
`∫|ω(t)|(1-ς_R) = ∫|ω^in|(1-ς_R) - ∫_0^t∫|ω| v·∇ς_R`, and
`1_{|x|≥2R} ≤ 1-ς_R ≤ 1_{|x|≥R}`, `|∇ς_R| ≤ ‖∇ς‖_∞/R` give eq:tail.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Weak.RenormAllTH

/-- Pointwise: `| |s| ∇ς_R(y)·w | ≤ (‖∇ς‖_∞/R) |s w|`. -/
theorem enorm_flux_le {R : ℝ} (hR : 0 < R) (s : ℝ) (y w : ℂ) :
    ‖|s| * fderiv ℝ (sigmaCutR R) y w‖ₑ ≤
      ENNReal.ofReal (Smooth.gradSup sigmaCut / R) * ‖s • w‖ₑ := by
  have hG : 0 ≤ Smooth.gradSup sigmaCut / R := div_nonneg bddAbove_norm_fderiv_sigmaCut.2 hR.le
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hG]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_mul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
  have hL : ‖fderiv ℝ (sigmaCutR R) y w‖ ≤ Smooth.gradSup sigmaCut / R * ‖w‖ :=
    ((fderiv ℝ (sigmaCutR R) y).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_sigmaCutR_le hR y) (norm_nonneg w))
  calc |s| * ‖fderiv ℝ (sigmaCutR R) y w‖ ≤ |s| * (Smooth.gradSup sigmaCut / R * ‖w‖) :=
        mul_le_mul_of_nonneg_left hL (abs_nonneg s)
    _ = Smooth.gradSup sigmaCut / R * (|s| * ‖w‖) := by ring

theorem integrable_mul_of_bdd {g φ : ℂ → ℝ} (hg : Integrable g volume) (hφ : Continuous φ)
    (hb : ∀ x, |φ x| ≤ 1) : Integrable (fun x => g x * φ x) volume :=
  hg.norm.mono' (hg.1.mul hφ.aestronglyMeasurable) (Eventually.of_forall fun x => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (hb x))

theorem abs_sigmaCutR_le (R : ℝ) (x : ℂ) : |sigmaCutR R x| ≤ 1 :=
  abs_le.2 ⟨by linarith [sigmaCutR_nonneg R x], sigmaCutR_le_one R x⟩

theorem abs_one_sub_sigmaCutR_le (R : ℝ) (x : ℂ) : |1 - sigmaCutR R x| ≤ 1 :=
  abs_le.2 ⟨by linarith [sigmaCutR_le_one R x], by linarith [sigmaCutR_nonneg R x]⟩

theorem integral_mul_one_sub {g : ℂ → ℝ} (hg : Integrable g volume) (R : ℝ) :
    ∫ x, g x * (1 - sigmaCutR R x) = (∫ x, g x) - ∫ x, g x * sigmaCutR R x := by
  have h := integral_sub hg
    (integrable_mul_of_bdd hg (contDiff_sigmaCutR R).continuous (abs_sigmaCutR_le R))
  rw [← h]
  congr 1
  ext x
  ring

/-- `∫|ω^in|(1-ς_R) ≤ ∫_{|x|≥R}|ω^in|`. -/
theorem ofReal_integral_mul_one_sub_le {g : ℂ → ℝ} (hg : Integrable g volume) {R : ℝ}
    (hR : 0 < R) :
    ENNReal.ofReal (∫ x, |g x| * (1 - sigmaCutR R x)) ≤ ∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖g x‖ₑ := by
  have hS : MeasurableSet {x : ℂ | R ≤ ‖x‖} := measurableSet_le measurable_const measurable_norm
  have hnn : 0 ≤ᵐ[volume] fun x => |g x| * (1 - sigmaCutR R x) :=
    Eventually.of_forall fun x => mul_nonneg (abs_nonneg _) (sub_nonneg.2 (sigmaCutR_le_one R x))
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_mul_of_bdd (φ := fun x => 1 - sigmaCutR R x) hg.abs
      (continuous_const.sub (contDiff_sigmaCutR R).continuous) (abs_one_sub_sigmaCutR_le R))
    hnn, ← lintegral_indicator hS]
  refine lintegral_mono fun x => ?_
  by_cases hx : R ≤ ‖x‖
  · rw [indicator_of_mem (show x ∈ {x : ℂ | R ≤ ‖x‖} from hx), Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_of_le_one_right (abs_nonneg _) (by linarith [sigmaCutR_nonneg R x]))
  · rw [indicator_of_notMem (show x ∉ {x : ℂ | R ≤ ‖x‖} from hx),
      sigmaCutR_eq_one hR (not_le.1 hx)]
    simp

/-- `∫_{|x|≥2R}|ω(t)| ≤ ∫|ω(t)|(1-ς_R)`. -/
theorem lintegral_le_ofReal_integral_mul_one_sub {g : ℂ → ℝ} (hg : Integrable g volume) {R : ℝ}
    (hR : 0 < R) :
    ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖g x‖ₑ ≤ ENNReal.ofReal (∫ x, |g x| * (1 - sigmaCutR R x)) := by
  have hS : MeasurableSet {x : ℂ | 2 * R ≤ ‖x‖} :=
    measurableSet_le measurable_const measurable_norm
  have hnn : 0 ≤ᵐ[volume] fun x => |g x| * (1 - sigmaCutR R x) :=
    Eventually.of_forall fun x => mul_nonneg (abs_nonneg _) (sub_nonneg.2 (sigmaCutR_le_one R x))
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_mul_of_bdd (φ := fun x => 1 - sigmaCutR R x) hg.abs
      (continuous_const.sub (contDiff_sigmaCutR R).continuous) (abs_one_sub_sigmaCutR_le R))
    hnn]
  refine (setLIntegral_mono' hS fun x hx => ?_).trans (setLIntegral_le_lintegral _ _)
  rw [sigmaCutR_eq_zero hR hx, sub_zero, mul_one, Real.enorm_eq_ofReal_abs]

/-- eq:tail, given eq:conservation and the strong `L²` continuity of `ω` on `[0,T)`. -/
theorem tail {T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsRenormalizedWeakSolution 2 T ωin ω) (hc : IsWeakContL2On (Icc 0 T) ω)
    (hcons : ∀ t ∈ Ico 0 T, ∀ β : ℝ → ℝ, Equimeas.IsLipO β →
      Integrable (fun x => β (ω t x)) volume ∧ ∫ x, β (ω t x) = ∫ x, β (ωin x))
    (hL2 : ∀ t₀ ∈ Ico 0 T,
      Tendsto (fun t => eLpNorm (ω t - ω t₀) 2 volume) (𝓝[Ico 0 T] t₀) (𝓝 0)) :
    ∀ R : ℝ, 0 < R → ∀ t ∈ Ico 0 T,
      ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖ω t x‖ₑ ≤
        (∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖ωin x‖ₑ) +
          ENNReal.ofReal (Smooth.gradSup sigmaCut / R) *
            ∫⁻ p in slab T, ‖ω p.1 p.2 • velocityField ω p.1 p.2‖ₑ := by
  have hws := h.toIsWeakSolution
  have hT := hws.T_pos
  obtain ⟨-, h2⟩ := memLinfLp_of_isWeakSolution hws
  have ha2 := memLinfLp_abs h2
  obtain ⟨N, hN0, hN⟩ := exists_ae_eLpNorm_le ha2
  have hw : ∀ R : ℝ, 0 < R → Prelim.MemLinfLp (Ioo 0 T) (ball (0 : ℂ) R) 2 (velocityField ω) :=
    fun R hR => (hws.memLinfLp_velocityField hR).1
  have hin1 := hws.datum_memLp_one
  have hf₀ : Integrable ωin volume := memLp_one_iff_integrable.1 hin1
  have hain : LocallyIntegrable (fun x => |ωin x|) volume := hf₀.abs.locallyIntegrable
  have hte : SolvesTE 0 T (fun t x => |ω t x|) (velocityField ω) (fun x => |ωin x|) :=
    h.solvesTE_lipO _ Equimeas.isLipO_abs
  obtain ⟨ũ, -, hũc, -, hũae, -, -, -, -, hb, -, -⟩ := weakCont hT hN0 hw ha2 hain hte hN
  intro R hR t ht
  -- identification of `ũ(t)` with `|ω(t)|`
  set T' := (t + T) / 2 with hT'_def
  have hT'T : T' < T := by rw [hT'_def]; linarith [ht.2]
  have htT' : t ≤ T' := by rw [hT'_def]; linarith [ht.2]
  have hT'0 : 0 < T' := by rw [hT'_def]; linarith [ht.1, ht.2]
  have hrep : ũ t =ᵐ[volume] fun x => |ω t x| :=
    ae_eq_of_isWeakContL2On hT'0 (hũc.mono (Icc_subset_Icc_right hT'T.le))
      (isWeakContL2On_abs hc hT'T hL2)
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hT'T.le) hũae) t ⟨ht.1, htT'⟩
  obtain ⟨hFint, hid⟩ := hb (sigmaCutR R) (contDiff_sigmaCutR R) (hasCompactSupport_sigmaCutR hR)
    t ⟨ht.1, ht.2.le⟩
  have hũψ : ∫ x, ũ t x * sigmaCutR R x = ∫ x, |ω t x| * sigmaCutR R x :=
    integral_congr_ae (hrep.mono fun x hx => congrArg (· * sigmaCutR R x) hx)
  -- conservation for `|·|`
  have hf : Integrable (fun x => |ω t x|) volume := (hcons t ht _ Equimeas.isLipO_abs).1
  have hfeq : ∫ x, |ω t x| = ∫ x, |ωin x| := (hcons t ht _ Equimeas.isLipO_abs).2
  set I := ∫ s in Ioo 0 t, ∫ x, |ω s x| * fderiv ℝ (sigmaCutR R) x (velocityField ω s x)
    with hI_def
  have hreal : ∫ x, |ω t x| * (1 - sigmaCutR R x) =
      (∫ x, |ωin x| * (1 - sigmaCutR R x)) - I := by
    rw [integral_mul_one_sub hf, integral_mul_one_sub hf₀.abs, hfeq, ← hũψ, hid]
    ring
  -- the flux term
  have hIle : ‖I‖ₑ ≤ ENNReal.ofReal (Smooth.gradSup sigmaCut / R) *
      ∫⁻ p in slab T, ‖ω p.1 p.2 • velocityField ω p.1 p.2‖ₑ := by
    have hI : I = ∫ p in slabFrom 0 t,
        |ω p.1 p.2| * fderiv ℝ (sigmaCutR R) p.2 (velocityField ω p.1 p.2) :=
      integral_Ioo_integral_eq hFint
    rw [hI]
    have hsub : slabFrom 0 t ⊆ slab T :=
      prod_mono (Ioo_subset_Ioo_right ht.2.le) subset_rfl
    calc ‖∫ p in slabFrom 0 t,
          |ω p.1 p.2| * fderiv ℝ (sigmaCutR R) p.2 (velocityField ω p.1 p.2)‖ₑ
        ≤ ∫⁻ p in slabFrom 0 t,
          ‖|ω p.1 p.2| * fderiv ℝ (sigmaCutR R) p.2 (velocityField ω p.1 p.2)‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ p in slab T,
          ‖|ω p.1 p.2| * fderiv ℝ (sigmaCutR R) p.2 (velocityField ω p.1 p.2)‖ₑ :=
          lintegral_mono_set hsub
      _ ≤ ∫⁻ p in slab T, ENNReal.ofReal (Smooth.gradSup sigmaCut / R) *
          ‖ω p.1 p.2 • velocityField ω p.1 p.2‖ₑ :=
          lintegral_mono fun p => enorm_flux_le hR _ _ _
      _ = ENNReal.ofReal (Smooth.gradSup sigmaCut / R) *
          ∫⁻ p in slab T, ‖ω p.1 p.2 • velocityField ω p.1 p.2‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖ω t x‖ₑ
      ≤ ENNReal.ofReal (∫ x, |ω t x| * (1 - sigmaCutR R x)) :=
        lintegral_le_ofReal_integral_mul_one_sub ((hcons t ht _ Equimeas.isLipO_id).1) hR
    _ = ENNReal.ofReal ((∫ x, |ωin x| * (1 - sigmaCutR R x)) + -I) := by
        rw [hreal, sub_eq_add_neg]
    _ ≤ ENNReal.ofReal (∫ x, |ωin x| * (1 - sigmaCutR R x)) + ENNReal.ofReal (-I) :=
        ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (∫ x, |ωin x| * (1 - sigmaCutR R x)) + ‖I‖ₑ := by
        gcongr
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (neg_le_abs I)
    _ ≤ _ := add_le_add (ofReal_integral_mul_one_sub_le hf₀ hR) hIle

end NonUniqueEuler.Weak.RenormAllTH
