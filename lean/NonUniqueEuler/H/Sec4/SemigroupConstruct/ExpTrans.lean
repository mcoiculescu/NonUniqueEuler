import NonUniqueEuler.H.Sec4.SemigroupConstruct.SectorOps
import NonUniqueEuler.I.Infra.FaaDiBruno.ExpPhase
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Helpers for `lem:semigroup-construct`(1): the transport group on a sector

Helper file of `P/Sec4/SemigroupConstruct.lean` (fully proved). Manuscript `04_ring.tex:949-962`.

* `exp_transSec_spec`: `exp(t(-iℓΩ))` on `Y^s_ℓ` is multiplication by `e^{-iℓΩ(|x|;G)t}`. Proof:
  the partial sums of the exponential series converge in `Y^s_ℓ`, hence their functions converge
  in `L²`; along a subsequence they converge a.e. (`TendstoInMeasure.exists_seq_tendsto_ae`), while
  pointwise they are `(∑_{n<N} (t a)^n/n!) g = ` partial sums of `e^{ta} g` (`a = -iℓΩ`).
* `exists_iteratedDeriv_Omega_le`: `|∂_r^i Ω(r;G)| ≤ M` on `[ρ₋,ρ₊]` for `i ≤ k`, `|G| ≤ G₊`
  (`Ω(·;G) = Ω(·;0) + G r⁻²`, `‖Ω(·;G)‖_{C^k} ≤ ‖Ω(·;0)‖_{C^k} + G₊‖r⁻²‖_{C^k}`).
* `transport_sector`: the sector bound `‖e^{-iℓΩt}g‖_{s,ℓ} ≤ C_s(1+|t|)^s‖g‖_{s,ℓ}`, from the
  weighted Faà di Bruno bound `FaaDiBruno.exists_secNormSq_exp_mul_I_le` with `φ = -ℓΩt`,
  `A = |t| M` (`|∂^iφ| ≤ |ℓ||t|M ≤ |t|M(1+ℓ²)^{1/2}`).
-/

noncomputable section

open MeasureTheory Set Real Filter Topology
open scoped ContDiff Nat

namespace NonUniqueEuler.SGC

open Sob Sect Ang SectorSetting

/-! ### `L²` limits and pointwise limits -/

/-- An `L²` limit of a sequence of functions converging a.e. pointwise is the pointwise limit. -/
theorem ae_eq_of_tendsto_Lp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → Lp ℂ 2 μ} {L : Lp ℂ 2 μ} (hF : Tendsto F atTop (𝓝 L)) {f : ℕ → α → ℂ}
    {f₀ : α → ℂ} (hFf : ∀ N, (F N : α → ℂ) =ᵐ[μ] f N)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun N => f N x) atTop (𝓝 (f₀ x))) :
    (L : α → ℂ) =ᵐ[μ] f₀ := by
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ N, (F N : α → ℂ) x = f N x := ae_all_iff.2 hFf
  filter_upwards [hae, hall, hlim] with x hx hxN hxl
  have h1 : Tendsto (fun i => f (ns i) x) atTop (𝓝 (L x)) := by
    simpa only [hxN] using hx
  exact tendsto_nhds_unique h1 (hxl.comp hns.tendsto_atTop)

/-! ### The function map `Y^s_ℓ → L²` -/

variable {s : ℕ} {K : Set ℂ} {ℓ : ℤ}

/-- `g ↦ g.fn` as a continuous linear map into `L²`. -/
def fnL (s : ℕ) (K : Set ℂ) (ℓ : ℤ) : Ysec s K ℓ →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  (proj0 s).comp (YsecSub s K ℓ).subtypeL

theorem fnL_coe (g : Ysec s K ℓ) : ((fnL s K ℓ g : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) = g.fn :=
  rfl

/-! ### The exponential of a radial multiplier -/

theorem pow_apply_fn_of_mul {A : Ysec s K ℓ →L[ℂ] Ysec s K ℓ} {a : ℂ → ℂ}
    (hA : ∀ g, (A g).fn =ᵐ[volume] fun x => a x * g.fn x) (n : ℕ) (g : Ysec s K ℓ) :
    ((A ^ n) g).fn =ᵐ[volume] fun x => a x ^ n * g.fn x := by
  induction n with
  | zero => exact Eventually.of_forall fun x => by simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    filter_upwards [hA ((A ^ n) g), ih] with x h1 h2
    rw [h1, h2, pow_succ']
    ring

theorem exp_apply_fn_of_mul [CompleteSpace (Ysec s K ℓ)] {A : Ysec s K ℓ →L[ℂ] Ysec s K ℓ}
    {a : ℂ → ℂ} (hA : ∀ g, (A g).fn =ᵐ[volume] fun x => a x * g.fn x) (t : ℝ)
    (g : Ysec s K ℓ) :
    (NormedSpace.exp ((t : ℂ) • A) g).fn =ᵐ[volume]
      fun x => Complex.exp ((t : ℂ) * a x) * g.fn x := by
  set E : (Ysec s K ℓ →L[ℂ] Ysec s K ℓ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
    (fnL s K ℓ).comp (ContinuousLinearMap.apply ℂ (Ysec s K ℓ) g) with hE
  have hsum := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) • A)).mapL E
  have hB : ∀ g' : Ysec s K ℓ, (((t : ℂ) • A) g').fn =ᵐ[volume]
      fun x => ((t : ℂ) * a x) * g'.fn x := by
    intro g'
    filter_upwards [ysec_fn_smul (t : ℂ) (A g'), hA g'] with x h1 h2
    rw [ContinuousLinearMap.smul_apply, h1, Pi.smul_apply, h2, smul_eq_mul, mul_assoc]
  have hterm : ∀ n : ℕ, (E ((n !⁻¹ : ℂ) • ((t : ℂ) • A) ^ n) : ℂ → ℂ) =ᵐ[volume]
      fun x => (n !⁻¹ : ℂ) * ((t : ℂ) * a x) ^ n * g.fn x := by
    intro n
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul (n !⁻¹ : ℂ) (E (((t : ℂ) • A) ^ n)),
      pow_apply_fn_of_mul hB n g] with x hx hx'
    rw [hx, Pi.smul_apply, hE, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      fnL_coe, hx', smul_eq_mul]
    ring
  have hpart : ∀ N : ℕ, ((∑ n ∈ Finset.range N, E ((n !⁻¹ : ℂ) • ((t : ℂ) • A) ^ n) :
      Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[volume]
      fun x => (∑ n ∈ Finset.range N, (n !⁻¹ : ℂ) * ((t : ℂ) * a x) ^ n) * g.fn x := by
    intro N
    induction N with
    | zero =>
      filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with x hx
      simp only [Finset.range_zero, Finset.sum_empty, zero_mul]
      exact hx
    | succ N ih =>
      simp only [Finset.sum_range_succ]
      filter_upwards [Lp.coeFn_add (∑ n ∈ Finset.range N, E ((n !⁻¹ : ℂ) • ((t : ℂ) • A) ^ n))
        (E ((N !⁻¹ : ℂ) • ((t : ℂ) • A) ^ N)), ih, hterm N] with x h1 h2 h3
      rw [h1, Pi.add_apply, h2, h3]
      ring
  have hlim : ∀ x : ℂ, Tendsto
      (fun N => (∑ n ∈ Finset.range N, (n !⁻¹ : ℂ) * ((t : ℂ) * a x) ^ n) * g.fn x) atTop
      (𝓝 (Complex.exp ((t : ℂ) * a x) * g.fn x)) := by
    intro x
    have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) * a x)).tendsto_sum_nat
    rw [← Complex.exp_eq_exp_ℂ] at h
    simp only [smul_eq_mul] at h
    exact h.mul_const _
  have := ae_eq_of_tendsto_Lp hsum.tendsto_sum_nat hpart (Eventually.of_forall hlim)
  simpa only [hE, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, fnL_coe]
    using this

/-- `lem:semigroup-construct`(1), the formula on a sector. -/
theorem exp_transSec_spec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ)
    (G t : ℝ) (g : Ysec s S.Nstar ℓ) :
    (NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G) g).fn =ᵐ[volume]
      fun x => Complex.exp (-(Complex.I * (ℓ : ℂ) * ((S.Omega G ‖x‖ : ℝ) : ℂ) * (t : ℂ))) *
        g.fn x := by
  have h := exp_apply_fn_of_mul (a := fun x => transCoef S ℓ G ‖x‖)
    (transSec_spec S hS s ℓ G) t g
  filter_upwards [h] with x hx
  rw [hx, transCoef]
  congr 2
  ring

/-! ### Bounds on the derivatives of `Ω` -/

theorem contDiffOn_inv_sq : ContDiffOn ℝ ∞ (fun r : ℝ => (r ^ 2)⁻¹) (Ioi 0) :=
  ((contDiff_id.pow 2).contDiffOn).inv fun r hr => pow_ne_zero 2 (ne_of_gt hr)

theorem exists_iteratedDeriv_Omega_le (S : SectorSetting) (hS : S.Valid) (k : ℕ) {Gp : ℝ}
    (hGp : 0 ≤ Gp) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ G : ℝ, |G| ≤ Gp → ∀ i ≤ k, ∀ r ∈ Icc S.ρm S.ρp,
      |iteratedDeriv i (S.Omega G) r| ≤ M := by
  set U := Icc S.ρm S.ρp
  have h0 : MemCk k U (S.Omega 0) :=
    memCk_of_contDiffOn_Ioi (contDiffOn_Omega S hS 0) hS.ρm_pos k
  have h1 : MemCk k U (fun r : ℝ => (r ^ 2)⁻¹) :=
    memCk_of_contDiffOn_Ioi contDiffOn_inv_sq hS.ρm_pos k
  refine ⟨normCk k U (S.Omega 0) + Gp * normCk k U (fun r : ℝ => (r ^ 2)⁻¹),
    add_nonneg (normCk_nonneg _ _ _) (mul_nonneg hGp (normCk_nonneg _ _ _)),
    fun G hG i hi r hr => ?_⟩
  have hfun : S.Omega G = S.Omega 0 + G • (fun r : ℝ => (r ^ 2)⁻¹) := by
    funext r
    rw [Omega_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  obtain ⟨hm, hn⟩ := h0.add (h1.smul G)
  rw [← hfun] at hm hn
  rw [normCk_smul] at hn
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  refine (norm_iteratedFDeriv_le_normCk hm hi hr).trans (hn.trans ?_)
  linarith [mul_le_mul_of_nonneg_right hG (normCk_nonneg k U (fun r : ℝ => (r ^ 2)⁻¹))]

/-! ### The sector bound -/

/-- **`lem:semigroup-construct`(1), sector bound**. -/
theorem transport_sector (S : SectorSetting) (hS : S.Valid) (s : ℕ) {Gp : ℝ}
    (hGp : 0 ≤ Gp) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℤ) (G : ℝ), |G| ≤ Gp → ∀ (t : ℝ) (g : Ysec s S.Nstar ℓ),
      S.secNormY s (NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G) g) ≤
        C * (1 + |t|) ^ s * S.secNormY s g := by
  obtain ⟨CF, hCF, hF⟩ := FaaDiBruno.exists_secNormSq_exp_mul_I_le s
  obtain ⟨M, hM0, hM⟩ := exists_iteratedDeriv_Omega_le S hS s hGp
  refine ⟨Real.sqrt CF * (1 + M) ^ s, by positivity, fun ℓ G hG t g => ?_⟩
  set Eg := NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G) g with hEg
  set h := Polar.angularSector g.fn ℓ with hh
  set ph : ℝ → ℝ := fun r => (-(ℓ : ℝ) * t) * S.Omega G r with hph
  obtain ⟨hm, hsupp⟩ := prof_spec hS g
  obtain ⟨hmE, -⟩ := prof_spec hS Eg
  -- the profile of `e^{-iℓΩt} g`
  have hprof : Polar.angularSector Eg.fn ℓ =ᵐ[volume.restrict (Ioi 0)]
      fun r => Complex.exp ((ph r : ℂ) * Complex.I) * h r := by
    filter_upwards [angularSector_congr_ae (exp_transSec_spec S hS s ℓ G t g) ℓ,
      ae_restrict_mem measurableSet_Ioi] with r hr hr0
    rw [hr, angularSector_radial_mul
      (fun r => Complex.exp (-(Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ) * (t : ℂ))))
      g.fn ℓ (le_of_lt hr0)]
    simp only [hph, hh]
    congr 2
    push_cast
    ring
  have hphs : ContDiffOn ℝ s ph (Ioi 0) :=
    (contDiffOn_const.mul (contDiffOn_Omega S hS G)).of_le (by exact_mod_cast le_top)
  have hA : ∀ i, 1 ≤ i → i ≤ s → ∀ r ∈ Icc S.ρm S.ρp,
      |iteratedDeriv i ph r| ≤ (|t| * M) * Real.sqrt (1 + (ℓ : ℝ) ^ 2) := by
    intro i _ hi r hr
    have hd : iteratedDeriv i ph r = (-(ℓ : ℝ) * t) * iteratedDeriv i (S.Omega G) r :=
      iteratedDeriv_const_mul_field (-(ℓ : ℝ) * t) (S.Omega G)
    have hl : |(ℓ : ℝ)| ≤ Real.sqrt (1 + (ℓ : ℝ) ^ 2) := Real.abs_le_sqrt (by linarith)
    rw [hd, abs_mul, abs_mul, abs_neg]
    calc |(ℓ : ℝ)| * |t| * |iteratedDeriv i (S.Omega G) r|
        ≤ Real.sqrt (1 + (ℓ : ℝ) ^ 2) * |t| * M := by
          gcongr
          exact hM G hG i hi r hr
      _ = (|t| * M) * Real.sqrt (1 + (ℓ : ℝ) ^ 2) := by ring
  obtain ⟨-, hbound⟩ := hF ℓ (|t| * M) S.ρm S.ρp ph h hS.ρm_pos (by positivity) hphs hA hm hsupp
  have hEq : S.secNormY s Eg = Sob.secNorm s ℓ (Icc S.ρm S.ρp)
      (fun r => Complex.exp ((ph r : ℂ) * Complex.I) * h r) := by
    simp only [secNormY, Sob.secNorm]
    rw [secNormSq_congr_ae ℓ (fun r hr => lt_of_lt_of_le hS.ρm_pos hr.1) hmE hprof]
  rw [hEq]
  simp only [secNormY, Sob.secNorm]
  rw [← hh]
  have hsq0 : 0 ≤ Sob.secNormSq s ℓ (Icc S.ρm S.ρp) h :=
    secNormSq_nonneg s ℓ measurableSet_Icc (fun r hr => hS.ρm_pos.le.trans hr.1) _
  have h1 : 1 + |t| * M ≤ (1 + M) * (1 + |t|) := by nlinarith [abs_nonneg t]
  calc Real.sqrt (Sob.secNormSq s ℓ (Icc S.ρm S.ρp)
        (fun r => Complex.exp ((ph r : ℂ) * Complex.I) * h r))
      ≤ Real.sqrt (CF * (1 + |t| * M) ^ (2 * s) * Sob.secNormSq s ℓ (Icc S.ρm S.ρp) h) :=
        Real.sqrt_le_sqrt hbound
    _ = Real.sqrt CF * (1 + |t| * M) ^ s * Real.sqrt (Sob.secNormSq s ℓ (Icc S.ρm S.ρp) h) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hCF.le, pow_mul',
          Real.sqrt_sq (by positivity)]
    _ ≤ Real.sqrt CF * ((1 + M) * (1 + |t|)) ^ s *
          Real.sqrt (Sob.secNormSq s ℓ (Icc S.ρm S.ρp) h) := by
        gcongr
    _ = Real.sqrt CF * (1 + M) ^ s * (1 + |t|) ^ s *
          Real.sqrt (Sob.secNormSq s ℓ (Icc S.ρm S.ρp) h) := by
        rw [mul_pow]
        ring

end NonUniqueEuler.SGC
