import NonUniqueEuler.H.Sec2.HkCalculus.Cutoff
import NonUniqueEuler.I.Sec2.HkCalculus.TransportEnergy
import NonUniqueEuler.I.Infra.Sobolev.ReIm

/-!
# Helper for `P/Sec2/HkCalculus`: the energy claims of `lem:Hk-calculus`(1)

`02_prelim.tex:732-747`.
* `energy_main`: with `g = ∂^α w`, `∂^α(U·∇w) = [∂^α, U·∇]w + Ũ·∇g` (a.e., extended by `0`
  outside `N₁`) and `Re ⟨Ũ·∇g, g⟩ = 0` (`re_innerL2_dotGrad_self_eq_zero`,
  `I/Sec2/HkCalculus/TransportEnergy.lean`, for `div Ũ = 0` on `N`), so
  `|Re ⟨∂^α(U·∇w), ∂^α w⟩| ≤ ‖[∂^α, U·∇]w‖_{L²} ‖w‖_{H^k}`;
* `energy_real`: for real `w` (and real `U`) the inner product is real (weak derivatives of real
  functions are real).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

namespace NonUniqueEuler.Sob.HkCalcAux

theorem energy_main {k : ℕ} (hk : 3 ≤ k) {N N₁ V : Set ℂ} (hNc : IsCompact N)
    (hNV : N ⊆ V) (hVN₁ : V ⊆ N₁) {U Ũ w : ℂ → ℂ} (hUV : ∀ x ∈ V, Ũ x = U x)
    (hŨ : MemH k Ũ) (hŨw : MemW1infOn univ Ũ) (hw : MemH (k + 1) w)
    (hwN : ∀ᵐ x, x ∉ N → w x = 0) {α : ℕ × ℕ} (hα : α ∈ multiIdx k)
    (hC : MemLp (hkComm N₁ α U w) 2 volume) (hdiv : ∀ᵐ x, x ∈ N → weakDivOn univ Ũ x = 0) :
    |(Prelim.innerL2 (N₁.indicator (weakPartialOn N₁ α (dotGrad U w)))
        (weakPartial α w)).re| ≤ l2 (hkComm N₁ α U w) * normH k w := by
  have hα' := mem_multiIdx.1 hα
  have hN := hNc.isClosed
  set B := weakPartial α w with hBdef
  have hB1 : MemH 1 B := (MemH.weakPartial (k := 1) (γ := α) (hw.mono_order (by omega))).1
  have hBL : MemLp B 2 volume := memLp_of_memH hB1
  have hBN : ∀ᵐ x, x ∉ N → B x = 0 :=
    MemH.weakPartial_eq_zero_outside hN hw hwN (mem_multiIdx.2 (by omega))
  have hzB : ∀ e ∈ multiIdx 1, ∀ᵐ x, x ∉ N → weakPartial e B x = 0 :=
    fun e he => MemH.weakPartial_eq_zero_outside hN hB1 hBN he
  have hsplit : N₁.indicator (weakPartialOn N₁ α (dotGrad U w)) =
      fun x => hkComm N₁ α U w x + N₁.indicator (dotGrad U B) x := by
    funext x
    by_cases hx : x ∈ N₁
    · simp [hkComm, hx, hBdef]
    · simp [hkComm, hx]
  have hT : N₁.indicator (dotGrad U B) =ᵐ[volume] dotGrad Ũ B :=
    indicator_dotGrad_ae_eq_of_eqOn hNV hVN₁ hUV (hzB (1, 0) (mem_multiIdx.2 (by simp)))
      (hzB (0, 1) (mem_multiIdx.2 (by simp)))
  obtain ⟨hU₁, hU₂, -⟩ := hŨ.re_im
  have hk2 : 2 ≤ k := by omega
  have hTmem : MemLp (dotGrad Ũ B) 2 volume :=
    (l2_mul_le_of_H2_left (hU₁.mono_order hk2)
        (hB1.memLp_weakPartial (γ := (1, 0)) (mem_multiIdx.2 (by simp))).1).1.add
      (l2_mul_le_of_H2_left (hU₂.mono_order hk2)
        (hB1.memLp_weakPartial (γ := (0, 1)) (mem_multiIdx.2 (by simp))).1).1
  have hinner : Prelim.innerL2 (N₁.indicator (weakPartialOn N₁ α (dotGrad U w))) B =
      Prelim.innerL2 (hkComm N₁ α U w) B + Prelim.innerL2 (dotGrad Ũ B) B := by
    rw [hsplit, ← innerL2_add_left hC hTmem hBL]
    refine innerL2_congr_ae ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [hT] with x hx
    rw [hx]
  have hzero : (Prelim.innerL2 (dotGrad Ũ B) B).re = 0 :=
    re_innerL2_dotGrad_self_eq_zero hNc hB1 hBN hŨw hdiv
  rw [hinner, Complex.add_re, hzero, add_zero]
  calc |(Prelim.innerL2 (hkComm N₁ α U w) B).re| ≤ ‖Prelim.innerL2 (hkComm N₁ α U w) B‖ :=
        Complex.abs_re_le_norm _
    _ ≤ l2 (hkComm N₁ α U w) * l2 B := norm_innerL2_le hC hBL
    _ ≤ l2 (hkComm N₁ α U w) * normH k w :=
        mul_le_mul_of_nonneg_left ((hw.mono_order (by omega)).l2_weakPartial_le hα)
          (l2_nonneg _)

theorem ae_im_weakPartial_eq_zero {m : ℕ} {w : ℂ → ℂ} (hw : MemH m w)
    (hreal : ∀ᵐ x, (w x).im = 0) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx m) :
    ∀ᵐ x, (weakPartial γ w x).im = 0 := by
  obtain ⟨hL, hD⟩ := hw.memLp_weakPartial hγ
  have h := ae_im_eq_zero_of_hasWeakDerivOn isOpen_univ
    ((hL.locallyIntegrable (by norm_num)).locallyIntegrableOn univ) hD
    (hreal.mono fun x hx _ => hx)
  filter_upwards [h] with x hx
  exact hx (mem_univ x)

theorem energy_real {k : ℕ} {N₁ : Set ℂ} (hN₁ : IsOpen N₁) {U w : ℂ → ℂ}
    (hw : MemH (k + 1) w) {α : ℕ × ℕ} (hα : α ∈ multiIdx k)
    (hG : ∃ G : ℂ → ℂ, MemLp G 2 (volume.restrict N₁) ∧
      HasWeakDerivOn N₁ (pdList α) (dotGrad U w) G)
    (hreal : ∀ᵐ x, (w x).im = 0) :
    (Prelim.innerL2 (N₁.indicator (weakPartialOn N₁ α (dotGrad U w)))
      (weakPartial α w)).im = 0 := by
  have hα' := mem_multiIdx.1 hα
  have h₁ := ae_im_weakPartial_eq_zero hw hreal (γ := (1, 0)) (mem_multiIdx.2 (by simp))
  have h₂ := ae_im_weakPartial_eq_zero hw hreal (γ := (0, 1)) (mem_multiIdx.2 (by simp))
  have hB := ae_im_weakPartial_eq_zero hw hreal (γ := α) (mem_multiIdx.2 (by omega))
  have hdot : ∀ᵐ x, (dotGrad U w x).im = 0 := by
    filter_upwards [h₁, h₂] with x hx₁ hx₂
    simp [dotGrad, Complex.add_im, Complex.mul_im, hx₁, hx₂]
  obtain ⟨G, hGL, hGD⟩ := hG
  have hGloc : LocallyIntegrableOn G N₁ :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hGL.locallyIntegrable (by norm_num))
  obtain ⟨hloc, hD⟩ := weakDerivOn_spec hGloc hGD
  have hA := ae_im_eq_zero_of_hasWeakDerivOn hN₁ hloc hD (hdot.mono fun x hx _ => hx)
  have hF : ∀ᵐ x, N₁.indicator (weakPartialOn N₁ α (dotGrad U w)) x *
      conj (weakPartial α w x) =
      (((N₁.indicator (weakPartialOn N₁ α (dotGrad U w)) x *
        conj (weakPartial α w x)).re : ℝ) : ℂ) := by
    filter_upwards [hA, hB] with x hxA hxB
    have hI : (N₁.indicator (weakPartialOn N₁ α (dotGrad U w)) x).im = 0 := by
      by_cases hx : x ∈ N₁
      · rw [indicator_of_mem hx]; exact hxA hx
      · rw [indicator_of_notMem hx]; simp
    apply Complex.ext
    · simp
    · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, hI, hxB, Complex.ofReal_im]
      ring
  unfold Prelim.innerL2
  rw [integral_congr_ae hF, integral_complex_ofReal, Complex.ofReal_im]

end NonUniqueEuler.Sob.HkCalcAux
