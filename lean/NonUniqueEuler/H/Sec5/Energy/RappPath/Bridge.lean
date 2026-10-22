import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv

/-!
# Helpers for `R_app ∈ C([0,t];X^s)`: bridges between plane functions, `Y^s(N)` and paths

Helper of `P/Sec5/Energy/RappPath.lean` (proof of `lem:energy`, `05_single_ring.tex:331`).
Namespace `NonUniqueEuler.OneRing.RappPathH`. The first lemmas are copies of proved helpers of
other proofs (`H/Sec5/Active/Layer/Bridge.lean`, `H/Sec5/Energy/ToY.lean`), which a proof file
may not import (import rules, `README.md`).

* `Y_ext_fn`, `Y_memH_fn`, `Y_fn_zero_outside`, `exists_Y_of_memH`, `toY_fn_and_norm`,
  `toY_congr_ae`: elements of `Y^s(K)` and the chosen `Sect.toY s K f`;
* `MemXFn.add`, `.neg`, `.sub`, `.mono`, `toY_add`, `toY_sub`, `norm_toY_sub`: `X^s` is a linear
  space and `Sect.toY` is additive on it;
* `PathC.tendsto_normH_sub`, `PathC.tendsto_normH`: a path in `C([0,T];X^k)` is continuous in
  the `H^k` norm of the differences;
* `pathC_of_tendsto`: conversely, an `X^k`-valued family with `‖u(τ') - u(τ)‖_{H^k} → 0` is a
  path in `C([0,T];X^k)`; `PathC.add`, `PathC.sub`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.RappPathH

open RingData Sect Sob

/-! ### Elements of `Y^s(K)` -/

/-- An element of `Y^s(K)` is determined by its function. -/
theorem Y_ext_fn {s : ℕ} {K : Set ℂ} {w₁ w₂ : Y s K} (h : w₁.fn =ᵐ[volume] w₂.fn) :
    w₁ = w₂ := by
  have : Y.toHk w₁ = Y.toHk w₂ := Hk.ext_fn h
  exact Subtype.ext (show (w₁ : SobTuple s) = w₂ from
    congrArg (fun F : Hk s => (F : SobTuple s)) this)

/-- The function of an element of `Y^s(K)` lies in `H^s`, with norm the norm of the element. -/
theorem Y_memH_fn {s : ℕ} {K : Set ℂ} (w : Y s K) : MemH s w.fn ∧ normH s w.fn = ‖w‖ := by
  have h := Hk.memH_fn (Y.toHk w)
  exact ⟨h.1, h.2⟩

theorem stronglyMeasurable_tupleFn {s : ℕ} (F : SobTuple s) : StronglyMeasurable (tupleFn F) :=
  Lp.stronglyMeasurable _

theorem suppCLM_eq_zero_iff {s : ℕ} {K : Set ℂ} (F : SobTuple s) :
    suppCLM s K F = 0 ↔ ∀ᵐ x ∂volume, x ∉ K → tupleFn F x = 0 := by
  have hc := LpToLpRestrictCLM_coeFn ℂ (μ := (volume : Measure ℂ)) (p := 2) Kᶜ (proj0 s F)
  have hmeas : MeasurableSet {x | tupleFn F x = 0} :=
    (stronglyMeasurable_tupleFn F).measurable (measurableSet_singleton 0)
  rw [suppCLM, ContinuousLinearMap.comp_apply, Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h
    have h2 : tupleFn F =ᵐ[volume.restrict Kᶜ] 0 := hc.symm.trans h
    exact (ae_restrict_iff hmeas).1 h2
  · intro h
    have h2 : ∀ᵐ x ∂volume.restrict Kᶜ, tupleFn F x = 0 := (ae_restrict_iff hmeas).2 h
    filter_upwards [hc, h2] with x hx h2x
    rw [hx]
    exact h2x

theorem mem_YSub_iff {s : ℕ} {K : Set ℂ} (F : SobTuple s) :
    F ∈ YSub s K ↔ F ∈ HkSub s ∧ ∀ᵐ x ∂volume, x ∉ K → tupleFn F x = 0 := by
  rw [YSub, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    suppCLM_eq_zero_iff]

/-- The function of `w ∈ Y^s(K)` vanishes a.e. outside `K`. -/
theorem Y_fn_zero_outside {s : ℕ} {K : Set ℂ} (w : Y s K) :
    ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → w.fn x = 0 :=
  ((mem_YSub_iff (K := K) (w : SobTuple s)).1 w.2).2

/-- An `H^s` function vanishing a.e. outside `K` is (a.e.) the function of an element of
`Y^s(K)`. -/
theorem exists_Y_of_memH {s : ℕ} {K : Set ℂ} {f : ℂ → ℂ} (hf : MemH s f)
    (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) : ∃ w : Y s K, w.fn =ᵐ[volume] f := by
  obtain ⟨F, hF⟩ := memH_iff_exists_Hk.1 hf
  have hmem : (F : SobTuple s) ∈ YSub s K := by
    refine (mem_YSub_iff (F : SobTuple s)).2 ⟨F.2, ?_⟩
    have hF' : tupleFn (F : SobTuple s) =ᵐ[volume] f := hF
    filter_upwards [hF', hK] with x hx hKx hxK
    rw [hx]
    exact hKx hxK
  exact ⟨⟨(F : SobTuple s), hmem⟩, hF⟩

/-- For `f ∈ H^s` vanishing a.e. outside `K`, `toY s K f` has function `f` (a.e.) and norm
`‖f‖_{H^s}`. -/
theorem toY_fn_and_norm {s : ℕ} {K : Set ℂ} {f : ℂ → ℂ}
    (hf : MemH s f) (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) :
    (toY s K f).fn =ᵐ[volume] f ∧ ‖toY s K f‖ = normH s f := by
  have hspec : (toY s K f).fn =ᵐ[volume] f := toY_spec (exists_Y_of_memH hf hK)
  refine ⟨hspec, ?_⟩
  have hY := Y_memH_fn (toY s K f)
  rw [← hY.2, (hY.1.congr_ae hspec).2]

/-- `Sect.toY` only depends on the a.e. class of the function. -/
theorem toY_congr_ae {s : ℕ} {K : Set ℂ} {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    toY s K f = toY s K g := by
  classical
  by_cases hf : ∃ w : Y s K, w.fn =ᵐ[volume] f
  · have hg : ∃ w : Y s K, w.fn =ᵐ[volume] g := let ⟨w, hw⟩ := hf; ⟨w, hw.trans h⟩
    exact Y_ext_fn ((toY_spec hf).trans (h.trans (toY_spec hg).symm))
  · have hg : ¬ ∃ w : Y s K, w.fn =ᵐ[volume] g := fun ⟨w, hw⟩ => hf ⟨w, hw.trans h.symm⟩
    simp [toY, hf, hg]

/-- `toY s K w.fn = w`. -/
theorem toY_fn_self {s : ℕ} {K : Set ℂ} (w : Y s K) : toY s K w.fn = w :=
  Y_ext_fn (toY_spec ⟨w, Filter.EventuallyEq.rfl⟩)

/-! ### The space `X^s` -/

theorem MemXFn.add {s : ℕ} {f g : ℂ → ℂ} (hf : Lin.MemXFn s f) (hg : Lin.MemXFn s g) :
    Lin.MemXFn s (f + g) := by
  refine ⟨(hf.1.add hg.1).1, ?_, ?_⟩
  · filter_upwards [hf.2.1, hg.2.1] with x h1 h2 hx
    simp [h1 hx, h2 hx]
  · exact hf.2.2.add hg.2.2

theorem MemXFn.neg {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) : Lin.MemXFn s (-f) := by
  have hneg : (-1 : ℂ) • f = -f := by funext x; simp
  refine ⟨?_, ?_, ?_⟩
  · have h := (hf.1.const_smul (-1)).1
    rwa [hneg] at h
  · filter_upwards [hf.2.1] with x h1 hx
    simp [h1 hx]
  · exact hf.2.2.neg

theorem MemXFn.sub {s : ℕ} {f g : ℂ → ℂ} (hf : Lin.MemXFn s f) (hg : Lin.MemXFn s g) :
    Lin.MemXFn s (f - g) := by
  rw [sub_eq_add_neg]
  exact MemXFn.add hf (MemXFn.neg hg)

theorem MemXFn.mono {s s' : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s' f) (hs : s ≤ s') :
    Lin.MemXFn s f :=
  ⟨hf.1.mono_order hs, hf.2.1, hf.2.2⟩

/-- `X^s` membership only depends on the a.e. class. -/
theorem MemXFn.congr_ae {s : ℕ} {f g : ℂ → ℂ} (hf : Lin.MemXFn s f) (hfg : f =ᵐ[volume] g) :
    Lin.MemXFn s g := by
  refine ⟨(hf.1.congr_ae hfg).1, ?_, ?_⟩
  · filter_upwards [hf.2.1, hfg] with x h1 h2 hx
    rw [← h2]
    exact h1 hx
  · have hrot : (fun x => f (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x)) =ᵐ[volume]
        fun x => g (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x) :=
      (Polar.measurePreserving_rot _).quasiMeasurePreserving.ae_eq_comp hfg
    exact hrot.symm.trans ((hf.2.2 : (fun x => f (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x))
      =ᵐ[volume] f).trans hfg)

/-- For `f ∈ X^s`, the function of `toY s N f` is `f` (a.e.). -/
theorem toY_fn {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    (toY s annN f).fn =ᵐ[volume] f :=
  (toY_fn_and_norm hf.1 hf.2.1).1

/-- For `f ∈ X^s`, `‖toY s N f‖ = ‖f‖_{H^s}`. -/
theorem norm_toY {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    ‖toY s annN f‖ = normH s f :=
  (toY_fn_and_norm hf.1 hf.2.1).2

/-- The function of a sum. -/
theorem Y_fn_add {s : ℕ} {K : Set ℂ} (w₁ w₂ : Y s K) :
    (w₁ + w₂).fn =ᵐ[volume] fun x => w₁.fn x + w₂.fn x := by
  have h : ((w₁ + w₂ : Y s K) : SobTuple s).ofLp (idx0 s) =
      (w₁ : SobTuple s).ofLp (idx0 s) + (w₂ : SobTuple s).ofLp (idx0 s) := rfl
  show (((w₁ + w₂ : Y s K) : SobTuple s).ofLp (idx0 s) : ℂ → ℂ) =ᵐ[volume] _
  rw [h]
  exact Lp.coeFn_add _ _

/-- The function of a difference. -/
theorem Y_fn_sub {s : ℕ} {K : Set ℂ} (w₁ w₂ : Y s K) :
    (w₁ - w₂).fn =ᵐ[volume] fun x => w₁.fn x - w₂.fn x := by
  have h : ((w₁ - w₂ : Y s K) : SobTuple s).ofLp (idx0 s) =
      (w₁ : SobTuple s).ofLp (idx0 s) - (w₂ : SobTuple s).ofLp (idx0 s) := rfl
  show (((w₁ - w₂ : Y s K) : SobTuple s).ofLp (idx0 s) : ℂ → ℂ) =ᵐ[volume] _
  rw [h]
  exact Lp.coeFn_sub _ _

/-- `Sect.toY` is additive on `X^s`. -/
theorem toY_add {s : ℕ} {f g : ℂ → ℂ} (hf : Lin.MemXFn s f) (hg : Lin.MemXFn s g) :
    toY s annN (f + g) = toY s annN f + toY s annN g := by
  have h1 : (toY s annN f + toY s annN g).fn =ᵐ[volume] f + g := by
    filter_upwards [Y_fn_add (toY s annN f) (toY s annN g), toY_fn hf, toY_fn hg]
      with x hx h1 h2
    rw [hx, h1, h2]
    rfl
  exact Y_ext_fn ((toY_spec ⟨_, h1⟩).trans h1.symm)

/-- `Sect.toY` is additive on `X^s` (differences). -/
theorem toY_sub {s : ℕ} {f g : ℂ → ℂ} (hf : Lin.MemXFn s f) (hg : Lin.MemXFn s g) :
    toY s annN (f - g) = toY s annN f - toY s annN g := by
  have h1 : (toY s annN f - toY s annN g).fn =ᵐ[volume] f - g := by
    filter_upwards [Y_fn_sub (toY s annN f) (toY s annN g), toY_fn hf, toY_fn hg]
      with x hx h1 h2
    rw [hx, h1, h2]
    rfl
  exact Y_ext_fn ((toY_spec ⟨_, h1⟩).trans h1.symm)

/-- `‖toY f - toY g‖ = ‖f - g‖_{H^s}` on `X^s`. -/
theorem norm_toY_sub {s : ℕ} {f g : ℂ → ℂ} (hf : Lin.MemXFn s f) (hg : Lin.MemXFn s g) :
    ‖toY s annN f - toY s annN g‖ = normH s (f - g) := by
  rw [← toY_sub hf hg, norm_toY (MemXFn.sub hf hg)]

/-! ### Paths in `X^k` -/

/-- Along a path in `C([0,T];X^k)`, `‖u(τ') - u(τ)‖_{H^k} → 0` as `τ' → τ` in `[0,T]`. -/
theorem PathC.tendsto_normH_sub {k : ℕ} {T : ℝ} {u : ℝ → ℂ → ℂ} (hu : PathC k T u) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) T) :
    Tendsto (fun τ' => normH k (u τ' - u τ)) (𝓝[Icc (0 : ℝ) T] τ) (𝓝 0) := by
  have hc : Tendsto (fun τ' => ‖toY k annN (u τ') - toY k annN (u τ)‖)
      (𝓝[Icc (0 : ℝ) T] τ) (𝓝 0) := by
    have := (hu.2 τ hτ)
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero] at this
    exact this
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ' hτ'
  exact norm_toY_sub (hu.1 τ' hτ') (hu.1 τ hτ)

/-- Along a path in `C([0,T];X^k)`, `‖u(τ')‖_{H^k} → ‖u(τ)‖_{H^k}`. -/
theorem PathC.tendsto_normH {k : ℕ} {T : ℝ} {u : ℝ → ℂ → ℂ} (hu : PathC k T u) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) T) :
    Tendsto (fun τ' => normH k (u τ')) (𝓝[Icc (0 : ℝ) T] τ) (𝓝 (normH k (u τ))) := by
  have hc : Tendsto (fun τ' => ‖toY k annN (u τ')‖) (𝓝[Icc (0 : ℝ) T] τ)
      (𝓝 ‖toY k annN (u τ)‖) := ((hu.2 τ hτ).norm).tendsto
  rw [norm_toY (hu.1 τ hτ)] at hc
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ' hτ'
  exact norm_toY (hu.1 τ' hτ')

/-- **An `X^k`-valued family continuous in the `H^k` norm is a path in `C([0,T];X^k)`.** -/
theorem pathC_of_tendsto {k : ℕ} {T : ℝ} {u : ℝ → ℂ → ℂ}
    (hX : ∀ τ ∈ Icc (0 : ℝ) T, Lin.MemXFn k (u τ))
    (hlim : ∀ τ ∈ Icc (0 : ℝ) T,
      Tendsto (fun τ' => normH k (u τ' - u τ)) (𝓝[Icc (0 : ℝ) T] τ) (𝓝 0)) :
    PathC k T u := by
  refine ⟨hX, fun τ hτ => ?_⟩
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine (hlim τ hτ).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ' hτ'
  exact (norm_toY_sub (hX τ' hτ') (hX τ hτ)).symm

/-- A family with `‖u(τ') - u(τ)‖_{H^k} ≤ b(τ') → 0` is continuous in the `H^k` norm. -/
theorem tendsto_normH_sub_of_le {k : ℕ} {I : Set ℝ} {u : ℝ → ℂ → ℂ} {τ : ℝ} {b : ℝ → ℝ}
    (hle : ∀ᶠ τ' in 𝓝[I] τ, normH k (u τ' - u τ) ≤ b τ')
    (hb : Tendsto b (𝓝[I] τ) (𝓝 0)) :
    Tendsto (fun τ' => normH k (u τ' - u τ)) (𝓝[I] τ) (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall fun _ => normH_nonneg _ _) hle hb

theorem PathC.add {k : ℕ} {T : ℝ} {u v : ℝ → ℂ → ℂ} (hu : PathC k T u) (hv : PathC k T v) :
    PathC k T (fun τ => u τ + v τ) := by
  refine ⟨fun τ hτ => MemXFn.add (hu.1 τ hτ) (hv.1 τ hτ), ?_⟩
  refine (hu.2.add hv.2).congr fun τ hτ => ?_
  exact toY_add (hu.1 τ hτ) (hv.1 τ hτ)

theorem PathC.sub {k : ℕ} {T : ℝ} {u v : ℝ → ℂ → ℂ} (hu : PathC k T u) (hv : PathC k T v) :
    PathC k T (fun τ => u τ - v τ) := by
  refine ⟨fun τ hτ => MemXFn.sub (hu.1 τ hτ) (hv.1 τ hτ), ?_⟩
  refine (hu.2.sub hv.2).congr fun τ hτ => ?_
  exact toY_sub (hu.1 τ hτ) (hv.1 τ hτ)

end NonUniqueEuler.OneRing.RappPathH
