import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.SmoothB.SmoothFlow
import NonUniqueEuler.I.Sec5.Setting
import NonUniqueEuler.I.Sec4.RingFacts

/-!
# Helpers for `thm:quiet`: bridges, paths, pointwise bounds, supports

Helper of `P/Sec5/Quiet.lean` (fully proved). Contents (namespace
`NonUniqueEuler.OneRing.QuietH`):

* `normH_eq_zero_of_ae`: an a.e. zero function has `H^k` norm `0`;
* `Y_ext_fn`, `toY_fn_and_norm`: for `f ∈ H^s` vanishing a.e. outside `N`,
  `(toY s N f).fn = f` a.e. and `‖toY s N f‖ = ‖f‖_{H^s}`;
* `continuousOn_normH`: `t ↦ ‖u(t)‖_{H^s}` is continuous on `[0,T]` for `u ∈ C([0,T];X^s)`;
* `PathC.mono`, `PathC1.mono`: restriction of paths to `[0,T']`, `T' ≤ T`;
* `abs_radComp_le`: `|h·e_r| ≤ |h|`; `bsNorm_ofReal`: `|(K_BS * g)(x)|` for a real `g`;
* `flow_continuous`: the flow `(t,y) ↦ Φ_t(y)` of a configuration is continuous
  (`thm:smooth`(4));
* `supp_of_movesRadially`: a radial displacement `≤ a/16` (resp. `≤ a/8`) of the trajectories of
  a ring starting at `Φ` keeps its support in `𝒩₋` (resp. in `N`) (`05_single_ring.tex:33-40`,
  `:526-529`).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.QuietH

open RingData Sect Sob

/-! ### Sobolev bridges -/

/-- An a.e. zero function has `H^k` norm `0`. -/
theorem normH_eq_zero_of_ae {k : ℕ} {f : ℂ → ℂ} (hf : f =ᵐ[volume] 0) : normH k f = 0 := by
  have h0 := Hk.memH_fn (0 : Hk k)
  have hz : (0 : Hk k).fn =ᵐ[volume] (0 : ℂ → ℂ) := by
    show ((((0 : Hk k) : SobTuple k).ofLp (idx0 k) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[volume] 0
    simpa using (Lp.coeFn_zero ℂ 2 (volume : Measure ℂ))
  have hfn : (0 : Hk k).fn =ᵐ[volume] f := hz.trans hf.symm
  rw [(h0.1.congr_ae hfn).2, h0.2, norm_zero]

/-- An element of `Y^s(K)` is determined by its function. -/
theorem Y_ext_fn {s : ℕ} {K : Set ℂ} {w₁ w₂ : Y s K} (h : w₁.fn =ᵐ[volume] w₂.fn) :
    w₁ = w₂ := by
  have : Y.toHk w₁ = Y.toHk w₂ := Hk.ext_fn h
  exact Subtype.ext (show (w₁ : SobTuple s) = w₂ from
    congrArg (fun F : Hk s => (F : SobTuple s)) this)

/-- The function of an element of `Y^s(K)` lies in `H^s`, with norm the norm of the element. -/
theorem memH_Yfn {s : ℕ} {K : Set ℂ} (w : Y s K) : MemH s w.fn ∧ normH s w.fn = ‖w‖ := by
  have h := Hk.memH_fn (Y.toHk w)
  exact ⟨h.1, h.2⟩

/-- For `f ∈ H^s` vanishing a.e. outside the measurable set `K`, `toY s K f` has function `f`
(a.e.) and norm `‖f‖_{H^s}`. -/
theorem toY_fn_and_norm {s : ℕ} {K : Set ℂ} (hKm : MeasurableSet K) {f : ℂ → ℂ}
    (hf : MemH s f) (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) :
    (toY s K f).fn =ᵐ[volume] f ∧ ‖toY s K f‖ = normH s f := by
  set F : Hk s := toHk s f with hFdef
  have hFf : F.fn =ᵐ[volume] f := toHk_fn hf
  have hmem : (F : SobTuple s) ∈ YSub s K := by
    refine Submodule.mem_inf.2 ⟨F.2, LinearMap.mem_ker.2 ?_⟩
    rw [ContinuousLinearMap.coe_coe]
    rw [Lp.eq_zero_iff_ae_eq_zero]
    have h1 := LpToLpRestrictCLM_coeFn ℂ Kᶜ (proj0 s (F : SobTuple s))
    have h2 : ((proj0 s (F : SobTuple s) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =
        F.fn := rfl
    have h3 : F.fn =ᵐ[(volume : Measure ℂ).restrict Kᶜ] 0 := by
      have hFf' : F.fn =ᵐ[(volume : Measure ℂ).restrict Kᶜ] f := ae_restrict_of_ae hFf
      refine hFf'.trans ?_
      rw [EventuallyEq, ae_restrict_iff' hKm.compl]
      filter_upwards [hK] with x hx hxK
      exact hx hxK
    show ((LpToLpRestrictCLM ℂ ℂ ℂ (volume : Measure ℂ) 2 Kᶜ) (proj0 s (F : SobTuple s)) :
        ℂ → ℂ) =ᵐ[(volume : Measure ℂ).restrict Kᶜ] 0
    refine h1.trans ?_
    rw [h2]
    exact h3
  set w : Y s K := ⟨(F : SobTuple s), hmem⟩
  have hw : w.fn =ᵐ[volume] f := hFf
  have hspec : (toY s K f).fn =ᵐ[volume] f := toY_spec ⟨w, hw⟩
  refine ⟨hspec, ?_⟩
  have hY := memH_Yfn (toY s K f)
  rw [← hY.2, (hY.1.congr_ae hspec).2]

/-- `annN` is measurable. -/
theorem measurableSet_annN : MeasurableSet annN :=
  isCompact_annN.isClosed.measurableSet

/-- For `f ∈ X^s`, `‖toY s N f‖ = ‖f‖_{H^s}`. -/
theorem norm_toY_of_memXFn {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    ‖toY s annN f‖ = normH s f :=
  (toY_fn_and_norm measurableSet_annN hf.1 hf.2.1).2

/-! ### Paths -/

/-- `t ↦ ‖u(t)‖_{H^s}` is continuous on `[0,T]` for `u ∈ C([0,T];X^s)`. -/
theorem continuousOn_normH {s : ℕ} {T : ℝ} {u : ℝ → ℂ → ℂ} (hu : PathC s T u) :
    ContinuousOn (fun t => normH s (u t)) (Icc 0 T) := by
  have h1 : ContinuousOn (fun t => ‖toY s annN (u t)‖) (Icc 0 T) := hu.2.norm
  refine h1.congr ?_
  intro t ht
  exact (norm_toY_of_memXFn (hu.1 t ht)).symm

theorem PathC.mono {s : ℕ} {T T' : ℝ} {u : ℝ → ℂ → ℂ} (hu : PathC s T u) (hT : T' ≤ T) :
    PathC s T' u :=
  ⟨fun t ht => hu.1 t ⟨ht.1, ht.2.trans hT⟩,
    hu.2.mono (Icc_subset_Icc le_rfl hT)⟩

theorem PathC1.mono {s : ℕ} {T T' : ℝ} {u u' : ℝ → ℂ → ℂ} (hu : PathC1 s T u u')
    (hT : T' ≤ T) : PathC1 s T' u u' :=
  ⟨PathC.mono hu.1 hT, PathC.mono hu.2.1 hT, fun t ht =>
    (hu.2.2 t ⟨ht.1, ht.2.trans hT⟩).mono (Icc_subset_Icc le_rfl hT)⟩

/-! ### Pointwise bounds -/

/-- `|h·e_r| ≤ |h|`. -/
theorem abs_radComp_le (F : ℂ → ℂ) (x : ℂ) : |radComp F x| ≤ ‖F x‖ := by
  unfold radComp
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_conj, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_norm]
  have h1 : ‖x‖⁻¹ * ‖x‖ ≤ 1 := by
    rcases eq_or_ne ‖x‖ 0 with h | h
    · simp [h]
    · rw [inv_mul_cancel₀ h]
  calc ‖F x‖ * (‖x‖⁻¹ * ‖x‖) ≤ ‖F x‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖F x‖ := mul_one _

/-- For a real function `g`, `|(K_BS * g)(x)| = |velocity g x|`. -/
theorem bsNorm_ofReal (g : ℂ → ℝ) (x : ℂ) :
    bsNorm (fun y => ((g y : ℝ) : ℂ)) x = ‖velocity g x‖ := by
  have hre : BS.velocityRe (fun y => ((g y : ℝ) : ℂ)) = velocity g := by
    unfold BS.velocityRe
    simp only [Complex.ofReal_re]
  have him : BS.velocityIm (fun y => ((g y : ℝ) : ℂ)) x = 0 := by
    unfold BS.velocityIm velocity
    simp
  rw [bsNorm, hre, him, norm_zero]
  simp [Real.sqrt_sq (norm_nonneg _)]

/-- `|(K_BS * w(τ))(x)| = |K_BS * (ω_r(τ) - Φ)(x)|`. -/
theorem bsNorm_w (c : RingConfig) (χ : ℝ → ℝ) (τ : ℝ) (x : ℂ) :
    bsNorm (c.w χ τ) x = ‖velocity (fun z => c.ringPart τ z - ringPhi χ z) x‖ :=
  bsNorm_ofReal (fun z => c.ringPart τ z - ringPhi χ z) x

/-! ### The flow -/

/-- The datum of a configuration is a smooth datum of `thm:smooth`. -/
theorem exists_isSmoothDatum {c : RingConfig} {T : ℝ} (hc : c.Hyp T) :
    ∃ R₀ : ℝ, Smooth.IsSmoothDatum c.datum R₀ := by
  obtain ⟨R₀, hR⟩ := hc.datum_hasCompactSupport.isCompact.isBounded.subset_ball (0 : ℂ)
  exact ⟨R₀, ⟨hc.datum_contDiff, hR⟩⟩

/-- The flow `(t,y) ↦ Φ_t(y)` of a configuration is continuous (`thm:smooth`(4)). -/
theorem flow_continuous {c : RingConfig} {T : ℝ} (hc : c.Hyp T) :
    Continuous (fun p : ℝ × ℂ => c.flow p.1 p.2) := by
  obtain ⟨R₀, hR⟩ := exists_isSmoothDatum hc
  exact (Smooth.flow_contDiff hR).1.continuous

/-! ### Supports -/

/-- **Radial motion and supports** (`05_single_ring.tex:33-40`, `:526-529`): if the ring starts
at `Φ` and its trajectories move radially by at most `δ` on `[0,t]`, then `supp ω_r(τ) ⊂ 𝒩₋` for
`τ ∈ [0,t]` when `δ ≤ a/16`, and `supp ω_r(τ) ⊂ N` when `δ ≤ a/8`. -/
theorem supp_of_movesRadially {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {c : RingConfig} {T : ℝ}
    (hc : c.Hyp T) (hr : c.ring0 = ringPhi χ) {t δ : ℝ} (hmove : c.MovesRadially t δ) :
    (δ ≤ a / 16 → c.RingSupportedIn t annNm) ∧ (δ ≤ a / 8 → c.RingSupportedIn t annN) := by
  have hF := ringFacts_of_admissible hχ
  have hsuppΦ : tsupport (ringPhi χ) ⊆ {y : ℂ | a ≤ ‖y‖ ∧ ‖y‖ ≤ 1} := hF.2.2.2.2.2.1
  have ha0 : 0 < a := hF.2.2.2.2.2.2.1
  have ha1 : a < 1 := hF.2.2.2.2.2.2.2
  have key := RingConfig.setting_movesRadially_tsupport hc hmove
  constructor
  · intro hδ τ hτ x hx
    obtain ⟨y, hy, -, hxy⟩ := key τ hτ x hx
    rw [hr] at hy
    have hy' := hsuppΦ hy
    have h1 := (abs_le.1 hxy)
    simp only [mem_annNm]
    constructor <;> nlinarith [hy'.1, hy'.2, h1.1, h1.2]
  · intro hδ τ hτ x hx
    obtain ⟨y, hy, -, hxy⟩ := key τ hτ x hx
    rw [hr] at hy
    have hy' := hsuppΦ hy
    have h1 := (abs_le.1 hxy)
    simp only [mem_annN]
    constructor <;> nlinarith [hy'.1, hy'.2, h1.1, h1.2]

end NonUniqueEuler.OneRing.QuietH
