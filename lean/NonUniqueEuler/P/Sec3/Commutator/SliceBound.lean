import NonUniqueEuler.Defs.Sec3.Commutator
import NonUniqueEuler.I.Sec3.CommFormula
import NonUniqueEuler.I.Infra.Sobolev.DiffQuot
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Group.Prod

/-!
# Proof: the uniform commutator bound `eq:comm-bound` at a fixed time (`a = b = 2`)

Proof of `I/Sec3/Commutator/SliceBound.lean` (`03_compactness.tex:374-406`).

With `K = sup_z ‖Dρ(z)‖` and the second line of `eq:comm-formula`
(`commEps_eq_integral_ball`), for every `x`,
`|C_ε(t,x)| ≤ K ε⁻¹ ∫_{B₁} |u(t,x-εz)| |w(t,x) - w(t,x-εz)| dz`.
Integrating over `B_R`, swapping the integrals (Tonelli; the integrand is a.e.-measurable on the
product since `(x,z) ↦ x - εz` is quasi-measure-preserving), Cauchy–Schwarz in `x`, the
translation bound `‖u(· - εz)‖_{L²(B_R)} ≤ ‖u‖_{L²(B_{R+1})}` and the difference-quotient bound
`‖w - w(· - εz)‖_{L²(B_R)} ≤ ε|z| ‖w‖_{H¹(B_{R+1})}` (`Sob.MemHOn.eLpNorm_sub_comp_sub_le`)
give the bound with `C = K |B₁|`.

Deviation from the manuscript: instead of the `C¹` case plus mollification of `w`, the
difference-quotient bound for `H¹` (`I/Infra/Sobolev/DiffQuot.lean`) is applied directly.
Helper lemmas live in the namespace `NonUniqueEuler.Weak.SliceBoundH`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak

namespace SliceBoundH

/-- A function that is `L²` on every ball centred at `0` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_of_memLp_ball {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (h : ∀ r : ℝ, 0 < r → MemLp f 2 (volume.restrict (ball (0 : ℂ) r))) :
    AEStronglyMeasurable f volume := by
  have hU : AEStronglyMeasurable f (volume.restrict (⋃ n : ℕ, ball (0 : ℂ) (n + 1))) :=
    aestronglyMeasurable_iUnion_iff.2 fun n => (h _ (by positivity)).aestronglyMeasurable
  rwa [iUnion_ball_nat_succ, Measure.restrict_univ] at hU

/-- A product of two functions that are `L²` on every ball is locally integrable. -/
theorem locallyIntegrable_smul_of_memLp_ball {f : ℂ → ℝ} {g : ℂ → ℂ}
    (hf : ∀ r : ℝ, 0 < r → MemLp f 2 (volume.restrict (ball (0 : ℂ) r)))
    (hg : ∀ r : ℝ, 0 < r → MemLp g 2 (volume.restrict (ball (0 : ℂ) r))) :
    LocallyIntegrable (fun y => f y • g y) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨r, hr⟩ := hk.isBounded.subset_ball (0 : ℂ)
  have hr1 : (0 : ℝ) < max r 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have : MemLp (f • g) 1 (volume.restrict (ball (0 : ℂ) (max r 1))) :=
    (hg _ hr1).smul (hf _ hr1)
  exact IntegrableOn.mono_set (memLp_one_iff_integrable.1 this)
    (hr.trans (ball_subset_ball (le_max_left _ _)))

/-- A function that is `L²` on every ball is locally integrable. -/
theorem locallyIntegrable_of_memLp_ball {f : ℂ → ℝ}
    (h : ∀ r : ℝ, 0 < r → MemLp f 2 (volume.restrict (ball (0 : ℂ) r))) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨r, hr⟩ := hk.isBounded.subset_ball (0 : ℂ)
  have hr1 : (0 : ℝ) < max r 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) (max r 1))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  exact IntegrableOn.mono_set ((h _ hr1).integrable (by norm_num))
    (hr.trans (ball_subset_ball (le_max_left _ _)))

/-- `(x, z) ↦ x - ε z` is quasi-measure-preserving from `volume × volume` to `volume`. -/
theorem quasiMeasurePreserving_sub_smul (ε : ℝ) :
    Measure.QuasiMeasurePreserving (fun p : ℂ × ℂ => p.1 - ε • p.2)
      ((volume : Measure ℂ).prod volume) volume := by
  refine MeasureTheory.QuasiMeasurePreserving.prod_of_left (by fun_prop)
    (Filter.Eventually.of_forall fun z => ?_)
  exact (measurePreserving_sub_right volume (ε • z)).quasiMeasurePreserving

/-- Translation: for `‖h‖ ≤ 1`, `‖f(· - h)‖_{L²(B_R)} ≤ ‖f‖_{L²(B_{R+1})}`. -/
theorem eLpNorm_comp_sub_le {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : AEStronglyMeasurable f volume) {h : ℂ} (hh : ‖h‖ ≤ 1) (R : ℝ) :
    eLpNorm (fun x => f (x - h)) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
      eLpNorm f 2 (volume.restrict (ball (0 : ℂ) (R + 1))) := by
  have hT : MeasurePreserving (fun x : ℂ => x - h) volume volume :=
    measurePreserving_sub_right volume h
  have hT' := hT.restrict_preimage (measurableSet_ball (x := (0 : ℂ)) (ε := R + 1))
  have hsub : ball (0 : ℂ) R ⊆ (fun x : ℂ => x - h) ⁻¹' ball (0 : ℂ) (R + 1) := by
    intro x hx
    simp only [mem_preimage, mem_ball, dist_zero_right] at hx ⊢
    calc ‖x - h‖ ≤ ‖x‖ + ‖h‖ := norm_sub_le _ _
      _ < R + 1 := by linarith
  calc eLpNorm (fun x => f (x - h)) 2 (volume.restrict (ball (0 : ℂ) R))
      ≤ eLpNorm (fun x => f (x - h)) 2
          (volume.restrict ((fun x : ℂ => x - h) ⁻¹' ball (0 : ℂ) (R + 1))) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)
    _ = eLpNorm f 2 (volume.restrict (ball (0 : ℂ) (R + 1))) :=
        eLpNorm_comp_measurePreserving hf.restrict hT'

/-- Pointwise bound: `|C_ε(t,x)| ≤ K ε⁻¹ ∫_{B₁} |u(t,x-εz)| |w(t,x) - w(t,x-εz)| dz`. -/
theorem enorm_commEps_le {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ z, ‖fderiv ℝ ρ z‖ ≤ K) {ε : ℝ} (hε : 0 < ε)
    {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {t : ℝ} (hu : LocallyIntegrable (u t) volume)
    (huw : LocallyIntegrable (fun y => u t y • w t y) volume) (x : ℂ) :
    ‖commEps ρ ε u w t x‖ₑ ≤
      ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (K / ε) *
        ‖u t (x - ε • z) • (w t x - w t (x - ε • z))‖ₑ := by
  rw [commEps_eq_integral_ball hρ hε hu huw x]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  set d := w t x - w t (x - ε • z)
  rw [norm_mul, norm_smul]
  calc ‖u t (x - ε • z)‖ * ‖fderiv ℝ ρ z (ε⁻¹ • d)‖
      ≤ ‖u t (x - ε • z)‖ * (‖fderiv ℝ ρ z‖ * ‖ε⁻¹ • d‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ‖u t (x - ε • z)‖ * (K * (ε⁻¹ * ‖d‖)) := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le)]
        gcongr
        exact hK z
    _ = K / ε * (‖u t (x - ε • z)‖ * ‖d‖) := by ring

end SliceBoundH

open SliceBoundH in
/-- `eq:comm-bound` at a fixed time (`03_compactness.tex:403-406`, `a = b = 2`): there is a
constant `C` (depending only on `ρ`) such that, whenever `u(t) ∈ L²(B_r)` and `w(t) ∈ H¹(B_r)` for
every `r > 0`, for all `0 < ε ≤ 1` and `R > 0`,
`‖C_ε[u,w](t)‖_{L¹(B_R)} ≤ C ‖u(t)‖_{L²(B_{R+1})} ‖w(t)‖_{H¹(B_{R+1})}`. -/
theorem exists_lintegral_commEps_ball_le {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ → ℂ → ℝ) (w : ℝ → ℂ → ℂ) (t : ℝ),
      (∀ r : ℝ, 0 < r → MemLp (u t) 2 (volume.restrict (ball (0 : ℂ) r))) →
      (∀ r : ℝ, 0 < r → Sob.MemHOn 1 (ball (0 : ℂ) r) (w t)) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ R : ℝ, 0 < R →
        ∫⁻ x in ball (0 : ℂ) R, ‖commEps ρ ε u w t x‖ₑ ≤
          ENNReal.ofReal C * eLpNorm (u t) 2 (volume.restrict (ball (0 : ℂ) (R + 1))) *
            ENNReal.ofReal (Sob.normHOn 1 (ball (0 : ℂ) (R + 1)) (w t)) := by
  obtain ⟨K₀, hK₀⟩ := (hρ.contDiff.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hρ.hasCompactSupport.fderiv ℝ)
  set K := max K₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK : ∀ z, ‖fderiv ℝ ρ z‖ ≤ K := fun z => (hK₀ z).trans (le_max_left _ _)
  set m : ℝ≥0∞ := volume (ball (0 : ℂ) 1) with hm
  have hmtop : m ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨K * m.toReal, mul_nonneg hK0 ENNReal.toReal_nonneg, ?_⟩
  intro u w t hu hw ε hε hε1 R hR
  -- integrability and measurability at the time `t`
  have hwL2 : ∀ r : ℝ, 0 < r → MemLp (w t) 2 (volume.restrict (ball (0 : ℂ) r)) :=
    fun r hr => (hw r hr).memLp
  have hul : LocallyIntegrable (u t) volume := locallyIntegrable_of_memLp_ball hu
  have huw : LocallyIntegrable (fun y => u t y • w t y) volume :=
    locallyIntegrable_smul_of_memLp_ball hu hwL2
  have hum : AEStronglyMeasurable (u t) volume := aestronglyMeasurable_of_memLp_ball hu
  have hwm : AEStronglyMeasurable (w t) volume := aestronglyMeasurable_of_memLp_ball hwL2
  set U := eLpNorm (u t) 2 (volume.restrict (ball (0 : ℂ) (R + 1))) with hU
  set N := Sob.normHOn 1 (ball (0 : ℂ) (R + 1)) (w t) with hN
  have hN0 : 0 ≤ N := Sob.normHOn_nonneg _ _ _
  set G : ℂ → ℂ → ℝ≥0∞ := fun x z =>
    ENNReal.ofReal (K / ε) * ‖u t (x - ε • z) • (w t x - w t (x - ε • z))‖ₑ with hG
  -- Step 1: the pointwise bound
  have h1 : ∫⁻ x in ball (0 : ℂ) R, ‖commEps ρ ε u w t x‖ₑ ≤
      ∫⁻ x in ball (0 : ℂ) R, ∫⁻ z in ball (0 : ℂ) 1, G x z :=
    lintegral_mono fun x => enorm_commEps_le hρ hK0 hK hε hul huw x
  -- Step 2: Tonelli
  have hQ := quasiMeasurePreserving_sub_smul ε
  have hGm : AEMeasurable (Function.uncurry G)
      ((volume.restrict (ball (0 : ℂ) R)).prod (volume.restrict (ball (0 : ℂ) 1))) := by
    have hprod : AEStronglyMeasurable
        (fun p : ℂ × ℂ => u t (p.1 - ε • p.2) • (w t p.1 - w t (p.1 - ε • p.2)))
        ((volume : Measure ℂ).prod volume) :=
      (hum.comp_quasiMeasurePreserving hQ).smul
        ((hwm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).sub
          (hwm.comp_quasiMeasurePreserving hQ))
    have : AEMeasurable (Function.uncurry G) ((volume : Measure ℂ).prod volume) :=
      hprod.enorm.const_mul _
    refine this.mono_measure ?_
    rw [Measure.prod_restrict]
    exact Measure.restrict_le_self
  have h2 : ∫⁻ x in ball (0 : ℂ) R, ∫⁻ z in ball (0 : ℂ) 1, G x z =
      ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ x in ball (0 : ℂ) R, G x z :=
    lintegral_lintegral_swap hGm
  -- Step 3: the bound for a fixed shift `z ∈ B₁`
  have h3 : ∀ z ∈ ball (0 : ℂ) 1, ∫⁻ x in ball (0 : ℂ) R, G x z ≤
      ENNReal.ofReal K * U * ENNReal.ofReal N := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by simpa using hz
    have hεz : ‖ε • z‖ = ε * ‖z‖ := by
      rw [norm_smul, Real.norm_of_nonneg hε.le]
    have hεz1 : ‖ε • z‖ < 1 := by
      rw [hεz]
      calc ε * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
        _ < 1 := by linarith
    have hT : MeasurePreserving (fun x : ℂ => x - ε • z) volume volume :=
      measurePreserving_sub_right volume (ε • z)
    have hφ : AEStronglyMeasurable (fun x => u t (x - ε • z))
        (volume.restrict (ball (0 : ℂ) R)) :=
      (hum.comp_quasiMeasurePreserving hT.quasiMeasurePreserving).restrict
    have hψ : AEStronglyMeasurable (fun x => w t x - w t (x - ε • z))
        (volume.restrict (ball (0 : ℂ) R)) :=
      (hwm.sub (hwm.comp_quasiMeasurePreserving hT.quasiMeasurePreserving)).restrict
    -- Cauchy–Schwarz
    have hCS : ∫⁻ x in ball (0 : ℂ) R, ‖u t (x - ε • z) • (w t x - w t (x - ε • z))‖ₑ ≤
        eLpNorm (fun x => u t (x - ε • z)) 2 (volume.restrict (ball (0 : ℂ) R)) *
          eLpNorm (fun x => w t x - w t (x - ε • z)) 2 (volume.restrict (ball (0 : ℂ) R)) := by
      have := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hψ hφ
      rw [eLpNorm_one_eq_lintegral_enorm] at this
      exact this
    -- translation and the difference-quotient bound
    have hT1 := eLpNorm_comp_sub_le hum hεz1.le R
    have hDQ := Sob.MemHOn.eLpNorm_sub_comp_sub_le (hw (R + 1) (by linarith))
      (R := R) (h := ε • z) (by linarith)
    have hKN : ENNReal.ofReal (K / ε) * ENNReal.ofReal (‖ε • z‖ * N) ≤
        ENNReal.ofReal K * ENNReal.ofReal N := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hK0]
      apply ENNReal.ofReal_le_ofReal
      rw [hεz]
      have : K / ε * (ε * ‖z‖ * N) = K * N * ‖z‖ := by field_simp
      rw [this]
      calc K * N * ‖z‖ ≤ K * N * 1 := by
            gcongr
          _ = K * N := mul_one _
    calc ∫⁻ x in ball (0 : ℂ) R, G x z
        = ENNReal.ofReal (K / ε) *
            ∫⁻ x in ball (0 : ℂ) R, ‖u t (x - ε • z) • (w t x - w t (x - ε • z))‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (K / ε) * (U * ENNReal.ofReal (‖ε • z‖ * N)) := by
          gcongr
          exact hCS.trans (mul_le_mul' hT1 hDQ)
      _ = U * (ENNReal.ofReal (K / ε) * ENNReal.ofReal (‖ε • z‖ * N)) := by ring
      _ ≤ U * (ENNReal.ofReal K * ENNReal.ofReal N) := by gcongr
      _ = ENNReal.ofReal K * U * ENNReal.ofReal N := by ring
  -- Step 4: integrate over `z ∈ B₁`
  have h4 : ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ x in ball (0 : ℂ) R, G x z ≤
      ∫⁻ _ in ball (0 : ℂ) 1, ENNReal.ofReal K * U * ENNReal.ofReal N :=
    setLIntegral_mono measurable_const h3
  rw [setLIntegral_const] at h4
  calc ∫⁻ x in ball (0 : ℂ) R, ‖commEps ρ ε u w t x‖ₑ
      ≤ ENNReal.ofReal K * U * ENNReal.ofReal N * m := (h1.trans_eq h2).trans h4
    _ = ENNReal.ofReal (K * m.toReal) * U * ENNReal.ofReal N := by
        rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_toReal hmtop]
        ring

end NonUniqueEuler.Weak
