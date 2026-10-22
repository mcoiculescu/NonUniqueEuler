import NonUniqueEuler.H.Sec5.Energy.RappPath.Bridge
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Sec2.BSBasic

/-!
# Helpers for `R_app ∈ C([0,t];X^s)`: bilinearity (a.e.) of `B(v,w)` and `h·∇w`

Helper of `P/Sec5/Energy/RappPath.lean` (`05_single_ring.tex:331`). Namespace
`NonUniqueEuler.OneRing.RappPathH`.

* `weakPartial_add_ae_eq` (copy of the proved helper of `H/Infra/Sobolev/DotGradSharp/Deriv.lean`),
  `weakPartial_sub_ae_eq`: linearity of the weak derivatives of `H^k` functions;
* `memLp_one_re`, `memLp_one_im`: `Re v, Im v ∈ L¹` for `v ∈ X^0` (`L²` with compact support);
* `velocity_sub_ae`, `velocityRe_sub_ae`, `velocityIm_sub_ae`: `K_BS ∗ ·` is linear where the
  integrals converge, i.e. a.e. for `L¹` vorticities (`lem:BS-basic`(e),
  `BS.ae_integrable_biotSavart_of_L1`);
* `Bfn_diff_ae`: `B(v₁,v₁) - B(v₂,v₂) = B(v₁-v₂, v₁) + B(v₂, v₁-v₂)` a.e.;
* `hGrad_diff_ae`: `h₁·∇w₁ - h₂·∇w₂ = (h₁-h₂)·∇w₁ + h₂·∇(w₁-w₂)` a.e.;
* `hGrad_sub_field`: `h₁·∇g - h₂·∇g = (h₁-h₂)·∇g` (pointwise).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.RappPathH

open RingData Sect Sob

/-! ### Weak derivatives -/

/-- Linearity of the chosen weak derivatives of `H^k` functions (copy of
`Sob.DotGradSharpAux.weakPartial_add_ae_eq`). -/
theorem weakPartial_add_ae_eq {k : ℕ} {f g : ℂ → ℂ} (hf : MemH k f) (hg : MemH k g)
    {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    weakPartial γ (f + g) =ᵐ[volume] weakPartial γ f + weakPartial γ g := by
  obtain ⟨hfm, hfd⟩ := MemH.memLp_weakPartial hf hγ
  obtain ⟨hgm, hgd⟩ := MemH.memLp_weakPartial hg hγ
  have hf0 : MemLp f 2 volume := (memH_iff.1 hf).1
  have hg0 : MemLp g 2 volume := (memH_iff.1 hg).1
  have hli : ∀ {u : ℂ → ℂ}, MemLp u 2 volume → LocallyIntegrableOn u univ := fun hu =>
    (hu.locallyIntegrable (by norm_num)).locallyIntegrableOn univ
  have hs := HasWeakDerivOn.add isOpen_univ (hli hf0) (hli hg0) (hli hfm) (hli hgm) hfd hgd
  exact MemH.weakPartial_ae_eq (hf.add hg).1 hγ (hfm.add hgm) hs

/-- `∂^γ(f - g) = ∂^γ f - ∂^γ g` a.e. for `f, g ∈ H^k`, `|γ| ≤ k`. -/
theorem weakPartial_sub_ae_eq {k : ℕ} {f g : ℂ → ℂ} (hf : MemH k f) (hg : MemH k g)
    {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    weakPartial γ (f - g) =ᵐ[volume] weakPartial γ f - weakPartial γ g := by
  have h := weakPartial_add_ae_eq (hf.sub hg).1 hg hγ
  rw [sub_add_cancel] at h
  filter_upwards [h] with x hx
  simp only [Pi.add_apply, Pi.sub_apply] at hx ⊢
  rw [hx]
  ring

theorem idx10_mem : ((1 : ℕ), (0 : ℕ)) ∈ multiIdx 1 := mem_multiIdx.2 (by simp)

theorem idx01_mem : ((0 : ℕ), (1 : ℕ)) ∈ multiIdx 1 := mem_multiIdx.2 (by simp)

/-- `U·∇(w₁ - w₂) = U·∇w₁ - U·∇w₂` a.e. for `w₁, w₂ ∈ H^1`. -/
theorem dotGrad_sub_right_ae (U : ℂ → ℂ) {w₁ w₂ : ℂ → ℂ} (h₁ : MemH 1 w₁) (h₂ : MemH 1 w₂) :
    dotGrad U (w₁ - w₂) =ᵐ[volume] dotGrad U w₁ - dotGrad U w₂ := by
  filter_upwards [weakPartial_sub_ae_eq h₁ h₂ idx10_mem, weakPartial_sub_ae_eq h₁ h₂ idx01_mem]
    with x hx1 hx2
  simp only [dotGrad, Pi.sub_apply] at hx1 hx2 ⊢
  rw [hx1, hx2]
  ring

/-- `(U₁ - U₂)·∇w = U₁·∇w - U₂·∇w` (pointwise). -/
theorem dotGrad_sub_left (U₁ U₂ w : ℂ → ℂ) :
    dotGrad (U₁ - U₂) w = dotGrad U₁ w - dotGrad U₂ w := by
  funext x
  simp only [dotGrad, Pi.sub_apply, Complex.sub_re, Complex.sub_im]
  push_cast
  ring

/-- `h₁·∇g - h₂·∇g = (h₁ - h₂)·∇g` (pointwise). -/
theorem hGrad_sub_field (h₁ h₂ g : ℂ → ℂ) :
    hGrad h₁ g - hGrad h₂ g = hGrad (h₁ - h₂) g := by
  simp only [hGrad, dotGrad_sub_left]

/-! ### The Biot–Savart velocity is linear a.e. -/

/-- An `X^0` function lies in `L¹` (it is in `L²` and vanishes a.e. off the compact `N`). -/
theorem memLp_one_of_memXFn {v : ℂ → ℂ} (hv : Lin.MemXFn 0 v) : MemLp v 1 volume := by
  have h2 : MemLp v 2 volume := (memH_iff.1 hv.1).1
  set v' : ℂ → ℂ := annN.indicator v with hv'def
  have hvv' : v =ᵐ[volume] v' := by
    filter_upwards [hv.2.1] with x hx
    by_cases hxN : x ∈ annN
    · rw [hv'def, indicator_of_mem hxN]
    · rw [hv'def, indicator_of_notMem hxN, hx hxN]
  have h2' : MemLp v' 2 volume := h2.ae_eq hvv'
  have hfin : (volume : Measure ℂ) annN ≠ ⊤ :=
    (isCompact_closedAnnulus _ _).measure_lt_top.ne
  have h1' : MemLp v' 1 volume :=
    h2'.mono_exponent_of_measure_support_ne_top (s := annN)
      (fun x hx => by rw [hv'def, indicator_of_notMem hx]) hfin (by norm_num)
  exact h1'.ae_eq hvv'.symm

theorem memLp_one_re {v : ℂ → ℂ} (hv : Lin.MemXFn 0 v) :
    MemLp (fun y => (v y).re) 1 volume :=
  (memLp_one_of_memXFn hv).re

theorem memLp_one_im {v : ℂ → ℂ} (hv : Lin.MemXFn 0 v) :
    MemLp (fun y => (v y).im) 1 volume :=
  (memLp_one_of_memXFn hv).im

/-- `K_BS ∗ (g₁ - g₂) = K_BS ∗ g₁ - K_BS ∗ g₂` a.e. for `g₁, g₂ ∈ L¹`. -/
theorem velocity_sub_ae {g₁ g₂ : ℂ → ℝ} (h₁ : MemLp g₁ 1 volume) (h₂ : MemLp g₂ 1 volume) :
    ∀ᵐ x ∂(volume : Measure ℂ),
      velocity (fun y => g₁ y - g₂ y) x = velocity g₁ x - velocity g₂ x := by
  filter_upwards [BS.ae_integrable_biotSavart_of_L1 h₁, BS.ae_integrable_biotSavart_of_L1 h₂]
    with x hx1 hx2
  simp only [velocity]
  rw [← integral_sub hx1 hx2]
  congr 1
  funext y
  push_cast
  ring

theorem velocityRe_sub_ae {v₁ v₂ : ℂ → ℂ} (h₁ : Lin.MemXFn 0 v₁) (h₂ : Lin.MemXFn 0 v₂) :
    ∀ᵐ x ∂(volume : Measure ℂ),
      BS.velocityRe (v₁ - v₂) x = BS.velocityRe v₁ x - BS.velocityRe v₂ x := by
  have h := velocity_sub_ae (memLp_one_re h₁) (memLp_one_re h₂)
  filter_upwards [h] with x hx
  simp only [BS.velocityRe, Pi.sub_apply, Complex.sub_re]
  exact hx

theorem velocityIm_sub_ae {v₁ v₂ : ℂ → ℂ} (h₁ : Lin.MemXFn 0 v₁) (h₂ : Lin.MemXFn 0 v₂) :
    ∀ᵐ x ∂(volume : Measure ℂ),
      BS.velocityIm (v₁ - v₂) x = BS.velocityIm v₁ x - BS.velocityIm v₂ x := by
  have h := velocity_sub_ae (memLp_one_im h₁) (memLp_one_im h₂)
  filter_upwards [h] with x hx
  simp only [BS.velocityIm, Pi.sub_apply, Complex.sub_im]
  exact hx

/-! ### Bilinearity of `B` and of `h·∇w` -/

/-- `B(v₁ - v₂, w) = B(v₁, w) - B(v₂, w)` a.e. for `v₁, v₂ ∈ X^0`. -/
theorem Bfn_sub_left_ae {v₁ v₂ : ℂ → ℂ} (h₁ : Lin.MemXFn 0 v₁) (h₂ : Lin.MemXFn 0 v₂)
    (w : ℂ → ℂ) : Bfn (v₁ - v₂) w =ᵐ[volume] Bfn v₁ w - Bfn v₂ w := by
  filter_upwards [velocityRe_sub_ae h₁ h₂, velocityIm_sub_ae h₁ h₂] with x hx1 hx2
  simp only [Bfn, bsGrad, dotGrad, Pi.sub_apply]
  rw [hx1, hx2]
  simp only [Complex.sub_re, Complex.sub_im]
  push_cast
  ring

/-- `B(v, w₁ - w₂) = B(v, w₁) - B(v, w₂)` a.e. for `w₁, w₂ ∈ H^1`. -/
theorem Bfn_sub_right_ae (v : ℂ → ℂ) {w₁ w₂ : ℂ → ℂ} (h₁ : MemH 1 w₁) (h₂ : MemH 1 w₂) :
    Bfn v (w₁ - w₂) =ᵐ[volume] Bfn v w₁ - Bfn v w₂ := by
  filter_upwards [dotGrad_sub_right_ae (BS.velocityRe v) h₁ h₂,
    dotGrad_sub_right_ae (BS.velocityIm v) h₁ h₂] with x hx1 hx2
  simp only [Bfn, bsGrad, Pi.sub_apply] at hx1 hx2 ⊢
  rw [hx1, hx2]
  ring

/-- **`B(v₁,v₁) - B(v₂,v₂) = B(v₁-v₂, v₁) + B(v₂, v₁-v₂)` a.e.** for `v₁, v₂ ∈ X^1`. -/
theorem Bfn_diff_ae {v₁ v₂ : ℂ → ℂ} (h₁ : Lin.MemXFn 1 v₁) (h₂ : Lin.MemXFn 1 v₂) :
    Bfn v₁ v₁ - Bfn v₂ v₂ =ᵐ[volume] Bfn (v₁ - v₂) v₁ + Bfn v₂ (v₁ - v₂) := by
  have hl := Bfn_sub_left_ae (MemXFn.mono h₁ (Nat.zero_le 1)) (MemXFn.mono h₂ (Nat.zero_le 1)) v₁
  have hr := Bfn_sub_right_ae v₂ h₁.1 h₂.1
  filter_upwards [hl, hr] with x hx1 hx2
  simp only [Pi.add_apply, Pi.sub_apply] at hx1 hx2 ⊢
  rw [hx1, hx2]
  ring

/-- **`h₁·∇w₁ - h₂·∇w₂ = (h₁-h₂)·∇w₁ + h₂·∇(w₁-w₂)` a.e.** for `w₁, w₂ ∈ H^1`. -/
theorem hGrad_diff_ae (h₁ h₂ : ℂ → ℂ) {w₁ w₂ : ℂ → ℂ} (hw₁ : MemH 1 w₁) (hw₂ : MemH 1 w₂) :
    hGrad h₁ w₁ - hGrad h₂ w₂ =ᵐ[volume] hGrad (h₁ - h₂) w₁ + hGrad h₂ (w₁ - w₂) := by
  have hr : hGrad h₂ (w₁ - w₂) =ᵐ[volume] hGrad h₂ w₁ - hGrad h₂ w₂ :=
    dotGrad_sub_right_ae h₂ hw₁ hw₂
  rw [← hGrad_sub_field]
  filter_upwards [hr] with x hx
  simp only [Pi.add_apply, Pi.sub_apply] at hx ⊢
  rw [hx]
  ring

/-- The `H^k` norm of a function a.e. equal to a sum of two `H^k` functions. -/
theorem normH_le_of_ae_eq_add {k : ℕ} {f g₁ g₂ : ℂ → ℂ} (h₁ : MemH k g₁) (h₂ : MemH k g₂)
    (hf : f =ᵐ[volume] g₁ + g₂) : normH k f ≤ normH k g₁ + normH k g₂ := by
  have hs := h₁.add h₂
  rw [(hs.1.congr_ae hf.symm).2]
  exact hs.2

end NonUniqueEuler.OneRing.RappPathH
