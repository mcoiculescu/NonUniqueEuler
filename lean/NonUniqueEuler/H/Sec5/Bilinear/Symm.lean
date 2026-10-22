import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Infra.Sobolev.RotDeriv
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.Symmetry
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helper for `lem:bilinear`: `3`-fold symmetry of the products (`05_single_ring.tex:272-275`)

Helper of `P/Sec5/Bilinear.lean`. "If `v`, `w` and `h` are `3`-fold symmetric, so are `K_BS * v`
(by the equivariance in the proof of `lem:reduction`), `∇w` and `∇Φ`, as vector fields; hence the
three scalar products are `3`-fold symmetric."

* `biotSavartKernel_rot`, `velocity_rot`: `K(Oz) = O K(z)`, and `(K * g)(Ox) = O (K * g)(x)` for
  every `x` when `g ∘ O = g` a.e. (change of variables `y = Oz`);
* `weakPartial_of_rot_ae_eq`: if `f ∈ H^1` and `f ∘ O_θ = f` a.e., then
  `∂₁f = cos θ (∂₁f)∘O + sin θ (∂₂f)∘O` and `∂₂f = -sin θ (∂₁f)∘O + cos θ (∂₂f)∘O` a.e.
  (`I/Infra/Sobolev/RotDeriv.lean`);
* `dotGrad_rot_ae_eq`: then `(h·∇f)(Ox) = (h·∇f)(x)` a.e., if `h(Ox) = O h(x)` on a rotation
  invariant set `U` outside which `∇f = 0` a.e.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff

namespace NonUniqueEuler

namespace OneRing

namespace BilinearH

open RingData

/-- `K(O_θ z) = O_θ K(z)`. -/
theorem biotSavartKernel_rot (θ : ℝ) (z : ℂ) :
    biotSavartKernel (rot θ z) = rot θ (biotSavartKernel z) := by
  simp only [biotSavartKernel, Polar.norm_rot]
  simp only [rot]
  ring

theorem measurableEmbedding_rot (θ : ℝ) : MeasurableEmbedding (rot θ) := by
  rw [Polar.rot_eq_rotation]
  exact (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding

/-- Equivariance of the Biot–Savart law: if `g ∘ O_θ = g` a.e., then
`(K * g)(O_θ x) = O_θ (K * g)(x)` for every `x`. -/
theorem velocity_rot {g : ℂ → ℝ} {θ : ℝ} (hg : (fun y => g (rot θ y)) =ᵐ[volume] g) (x : ℂ) :
    velocity g (rot θ x) = rot θ (velocity g x) := by
  unfold velocity
  rw [← (Polar.measurePreserving_rot θ).integral_comp (measurableEmbedding_rot θ)]
  have hsub : ∀ z, rot θ x - rot θ z = rot θ (x - z) := fun z => by simp [rot, mul_sub]
  simp_rw [hsub, biotSavartKernel_rot]
  rw [show rot θ (∫ y, biotSavartKernel (x - y) * (g y : ℂ)) =
      Complex.exp ((θ : ℂ) * Complex.I) * ∫ y, biotSavartKernel (x - y) * (g y : ℂ) from rfl,
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hg] with z hz
  rw [hz]
  simp only [rot]
  ring

/-- The velocity fields of a `3`-fold symmetric complex vorticity are equivariant. -/
theorem velocityRe_rot {v : ℂ → ℂ} {θ : ℝ} (hv : (fun y => v (rot θ y)) =ᵐ[volume] v) (x : ℂ) :
    BS.velocityRe v (rot θ x) = rot θ (BS.velocityRe v x) := by
  unfold BS.velocityRe
  refine velocity_rot ?_ x
  filter_upwards [hv] with y hy
  rw [hy]

theorem velocityIm_rot {v : ℂ → ℂ} {θ : ℝ} (hv : (fun y => v (rot θ y)) =ᵐ[volume] v) (x : ℂ) :
    BS.velocityIm v (rot θ x) = rot θ (BS.velocityIm v x) := by
  unfold BS.velocityIm
  refine velocity_rot ?_ x
  filter_upwards [hv] with y hy
  rw [hy]

/-- The weak derivative of a function is unchanged by an a.e. modification of the function. -/
theorem weakPartial_ae_eq_of_ae_eq {k : ℕ} {f g : ℂ → ℂ} (hf : Sob.MemH k f) (hg : Sob.MemH k g)
    (hfg : f =ᵐ[volume] g) {γ : ℕ × ℕ} (hγ : γ ∈ Sob.multiIdx k) :
    Sob.weakPartial γ g =ᵐ[volume] Sob.weakPartial γ f := by
  obtain ⟨hL, hW⟩ := hf.memLp_weakPartial hγ
  refine hg.weakPartial_ae_eq hγ hL (hW.congr_ae ?_ (Filter.Eventually.of_forall fun _ _ => rfl))
  filter_upwards [hfg] with x hx _ using hx

/-- Gradient of a rotation invariant `H^1` function: `∇f(x) = O_θ^T ∇f(O_θ x)` a.e. -/
theorem weakPartial_of_rot_ae_eq {f : ℂ → ℂ} (hf : Sob.MemH 1 f) {θ : ℝ}
    (hfs : (fun x => f (rot θ x)) =ᵐ[volume] f) :
    ∀ᵐ x ∂(volume : Measure ℂ),
      Sob.weakPartial (1, 0) f x = (Real.cos θ : ℂ) * Sob.weakPartial (1, 0) f (rot θ x) +
          (Real.sin θ : ℂ) * Sob.weakPartial (0, 1) f (rot θ x) ∧
        Sob.weakPartial (0, 1) f x = -(Real.sin θ : ℂ) * Sob.weakPartial (1, 0) f (rot θ x) +
          (Real.cos θ : ℂ) * Sob.weakPartial (0, 1) f (rot θ x) := by
  have hfr : Sob.MemH 1 (fun x => f (rot θ x)) := (hf.comp_rot θ).1
  obtain ⟨h1, h2⟩ := hf.weakPartial_comp_rot θ
  have e1 := weakPartial_ae_eq_of_ae_eq hfr hf hfs (γ := (1, 0)) (by simp [Sob.mem_multiIdx])
  have e2 := weakPartial_ae_eq_of_ae_eq hfr hf hfs (γ := (0, 1)) (by simp [Sob.mem_multiIdx])
  filter_upwards [h1, h2, e1, e2] with x hx1 hx2 hx3 hx4
  exact ⟨hx3.trans hx1, hx4.trans hx2⟩

theorem rot_re (θ : ℝ) (z : ℂ) : (rot θ z).re = Real.cos θ * z.re - Real.sin θ * z.im := by
  simp [rot, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem rot_im (θ : ℝ) (z : ℂ) : (rot θ z).im = Real.sin θ * z.re + Real.cos θ * z.im := by
  simp [rot, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- `(h·∇f)(O_θ x) = (h·∇f)(x)` a.e., for a rotation invariant `f ∈ H^1` whose gradient vanishes
a.e. outside a rotation invariant set `U`, and a field `h` with `h(O_θ x) = O_θ h(x)` on `U`. -/
theorem dotGrad_rot_ae_eq {f h : ℂ → ℂ} (hf : Sob.MemH 1 f) {θ : ℝ}
    (hfs : (fun x => f (rot θ x)) =ᵐ[volume] f) {U : Set ℂ} (hU : ∀ x, rot θ x ∈ U ↔ x ∈ U)
    (hsupp : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ U →
      Sob.weakPartial (1, 0) f x = 0 ∧ Sob.weakPartial (0, 1) f x = 0)
    (hh : ∀ x ∈ U, h (rot θ x) = rot θ (h x)) :
    (fun x => Sob.dotGrad h f (rot θ x)) =ᵐ[volume] Sob.dotGrad h f := by
  have hsr := (Polar.measurePreserving_rot θ).quasiMeasurePreserving.ae hsupp
  filter_upwards [weakPartial_of_rot_ae_eq hf hfs, hsupp, hsr] with x hx hs hs'
  simp only [Sob.dotGrad]
  by_cases hxU : x ∈ U
  · rw [hx.1, hx.2, hh x hxU, rot_re, rot_im]
    push_cast
    ring
  · have hxU' : rot θ x ∉ U := fun h' => hxU ((hU x).1 h')
    obtain ⟨a1, a2⟩ := hs hxU
    obtain ⟨b1, b2⟩ := hs' hxU'
    rw [a1, a2, b1, b2]
    simp

/-- The rotation by `2π/3` in `Ang.IsMFoldSymmetricC 3`. -/
theorem isMFoldSymmetricC_three_iff {f : ℂ → ℂ} :
    Ang.IsMFoldSymmetricC 3 f ↔ (fun x => f (rot (2 * Real.pi / 3) x)) =ᵐ[volume] f := by
  unfold Ang.IsMFoldSymmetricC
  norm_num

/-- `h·∇f` is `3`-fold symmetric (`05_single_ring.tex:272-275`). -/
theorem dotGrad_isMFoldSymmetricC {f h : ℂ → ℂ} (hf : Sob.MemH 1 f)
    (hfs : Ang.IsMFoldSymmetricC 3 f)
    (hsupp : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN' →
      Sob.weakPartial (1, 0) f x = 0 ∧ Sob.weakPartial (0, 1) f x = 0)
    (hh : IsSymFieldOn annN' h) : Ang.IsMFoldSymmetricC 3 (Sob.dotGrad h f) := by
  rw [isMFoldSymmetricC_three_iff] at hfs ⊢
  exact dotGrad_rot_ae_eq hf hfs (fun x => by simp [annN']) hsupp hh

end BilinearH

end OneRing

end NonUniqueEuler
