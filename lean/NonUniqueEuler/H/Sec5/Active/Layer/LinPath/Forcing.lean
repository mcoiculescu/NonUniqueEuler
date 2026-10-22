import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec5.Bilinear
import NonUniqueEuler.I.Infra.CkNorm.Basic
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.H.Sec5.Active.Layer.LinPath.Bridge

/-!
# Helper for `wlin0_path`: the forcing `F(v) = -h(v)·∇Φ` is a real path in `C([0,T]; X^s)`

Helper of `P/Sec5/Active/Layer/LinPath.lean` (fully proved modulo the interface files it
imports). Namespace `NonUniqueEuler.OneRing.LinPathH`. A copy of the proved helper
`H/Sec5/Running/Forcing.lean` (helper of `P/Sec5/Running.lean`), which a proof file of another
proof may not import (import rules, `README.md`); the bridges come from
`H/Sec5/Active/Layer/LinPath/Bridge.lean`.

* `sq_norm_mul_hGradPhi`: the pointwise identity
  `|x|² h·∇Φ = Re(h x̄)·(x·∇Φ) + Im(h x̄)·(x^⊥·∇Φ)`, which reduces support and symmetry of
  `h·∇Φ` for a field `h ∈ C^0(N')` to those of the two smooth symmetric fields `x` and `x^⊥ = ix`
  (`lem:bilinear`(3) at level `2`, `bilinear_Phi`);
* `memXFn_neg_hGradPhi`: `-h·∇Φ ∈ X^k` for `h ∈ C^k(N')` symmetric (`lem:uniform` for the `H^k`
  bound, the identity above for support and symmetry);
* `isReal_neg_hGradPhi`: `-h·∇Φ` is real a.e.;
* `forcing_path`: `v ↦ toY s annN (F v)` is continuous on `[0,T]` into `Y^s(N)`, with values in
  `X^s`, real, and function `F v` a.e.
-/

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler.OneRing.LinPathH

open Sect Sob RingData

/-! ### Pointwise algebra -/

/-- `h·∇Φ` is (real-)linear in the field `h`. -/
theorem hGradPhi_sub (χ : ℝ → ℝ) (f g : ℂ → ℂ) (x : ℂ) :
    Eig.hGradPhi χ (f - g) x = Eig.hGradPhi χ f x - Eig.hGradPhi χ g x := by
  simp only [Eig.hGradPhi, Sob.dotGrad, Pi.sub_apply, Complex.sub_re, Complex.sub_im]
  push_cast
  ring

/-- The pointwise identity `|x|² h·∇Φ = Re(h x̄)(x·∇Φ) + Im(h x̄)(ix·∇Φ)`. -/
theorem sq_norm_mul_hGradPhi (χ : ℝ → ℝ) (hf : ℂ → ℂ) (x : ℂ) :
    ((‖x‖ ^ 2 : ℝ) : ℂ) * Eig.hGradPhi χ hf x =
      (((hf x * conj x).re : ℝ) : ℂ) * hGrad (fun y => y) (PhiC χ) x +
        (((hf x * conj x).im : ℝ) : ℂ) * hGrad (fun y => Complex.I * y) (PhiC χ) x := by
  have hn : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hn, ← hGrad_PhiC]
  simp only [hGrad, Sob.dotGrad, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im]
  push_cast
  ring

/-! ### The two smooth symmetric fields -/

theorem memCk_id (k : ℕ) : MemCk k annN' (fun y : ℂ => y) :=
  IsCkNear.memCk_of_isCompact ⟨univ, isOpen_univ, subset_univ _, contDiff_id.contDiffOn⟩
    (isCompact_closedAnnulus _ _)

theorem memCk_I_mul (k : ℕ) : MemCk k annN' (fun y : ℂ => Complex.I * y) :=
  IsCkNear.memCk_of_isCompact
    ⟨univ, isOpen_univ, subset_univ _, (contDiff_const.mul contDiff_id).contDiffOn⟩
    (isCompact_closedAnnulus _ _)

theorem isSymFieldOn_id : IsSymFieldOn annN' (fun y : ℂ => y) := fun _ _ => rfl

theorem isSymFieldOn_I_mul : IsSymFieldOn annN' (fun y : ℂ => Complex.I * y) := by
  intro x _
  simp only [rot]
  ring

theorem a_pos : 0 < a := Real.exp_pos _

theorem annN_subset_annN' : annN ⊆ annN' := by
  intro x hx
  have ha := a_pos
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The two auxiliary functions `x·∇Φ`, `ix·∇Φ` lie in `X^2`. -/
theorem memXFn_aux (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    Lin.MemXFn 2 (hGrad (fun y => y) (PhiC χ)) ∧
      Lin.MemXFn 2 (hGrad (fun y => Complex.I * y) (PhiC χ)) :=
  ⟨(bilinear_Phi χ hχ hN le_rfl (memCk_id 2)).2.2.2 isSymFieldOn_id,
    (bilinear_Phi χ hχ hN le_rfl (memCk_I_mul 2)).2.2.2 isSymFieldOn_I_mul⟩

/-- The angle `2π/3` written two ways. -/
theorem two_pi_div_three : 2 * Real.pi / ((3 : ℕ) : ℝ) = 2 * Real.pi / 3 := by norm_num

/-- Support and symmetry of `h·∇Φ` for a symmetric field `h` on `N'` (no regularity of `h`). -/
theorem supp_sym_hGradPhi (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {hf : ℂ → ℂ} (hsym : IsSymFieldOn annN' hf) :
    (∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → Eig.hGradPhi χ hf x = 0) ∧
      (fun x => Eig.hGradPhi χ hf (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x)) =ᵐ[volume]
        Eig.hGradPhi χ hf := by
  obtain ⟨hA, hB⟩ := memXFn_aux χ hχ hN
  set A := hGrad (fun y => y) (PhiC χ) with hAdef
  set B := hGrad (fun y => Complex.I * y) (PhiC χ) with hBdef
  have hsuppA : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → A x = 0 := hA.2.1
  have hsuppB : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → B x = 0 := hB.2.1
  have hsymA : (fun x => A (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x)) =ᵐ[volume] A := hA.2.2
  have hsymB : (fun x => B (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x)) =ᵐ[volume] B := hB.2.2
  have hsq : ∀ x, ((‖x‖ ^ 2 : ℝ) : ℂ) * Eig.hGradPhi χ hf x =
      (((hf x * conj x).re : ℝ) : ℂ) * A x + (((hf x * conj x).im : ℝ) : ℂ) * B x :=
    sq_norm_mul_hGradPhi χ hf
  have hcancel : ∀ {x : ℂ} {z w : ℂ}, x ≠ 0 → ((‖x‖ ^ 2 : ℝ) : ℂ) * z = ((‖x‖ ^ 2 : ℝ) : ℂ) * w →
      z = w := by
    intro x z w hx h
    have : ((‖x‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 hx)
    exact mul_left_cancel₀ this h
  refine ⟨?_, ?_⟩
  · filter_upwards [hsuppA, hsuppB, (volume : Measure ℂ).ae_ne 0] with x hxA hxB hx0 hx
    refine hcancel hx0 ?_
    rw [hsq, hxA hx, hxB hx]
    simp
  · filter_upwards [hsuppA, hsuppB, hsymA, hsymB] with x hxA hxB hxsA hxsB
    set θ : ℝ := 2 * Real.pi / ((3 : ℕ) : ℝ) with hθ
    by_cases hx0 : x = 0
    · subst hx0
      simp [rot]
    have hnorm : ‖rot θ x‖ = ‖x‖ := Polar.norm_rot θ x
    have hxr : rot θ x ≠ 0 := by
      intro h0
      apply hx0
      have : ‖rot θ x‖ = 0 := by rw [h0, norm_zero]
      rw [hnorm] at this
      exact norm_eq_zero.1 this
    refine hcancel hx0 ?_
    have hsqr := hsq (rot θ x)
    rw [hnorm] at hsqr
    rw [hsqr, hsq x, hxsA, hxsB]
    by_cases hxN' : x ∈ annN'
    · have hrot : hf (rot θ x) = rot θ (hf x) := by
        have := hsym x hxN'
        rw [hθ, two_pi_div_three]
        exact this
      have hprod : hf (rot θ x) * conj (rot θ x) = hf x * conj x := by
        rw [hrot]
        simp only [rot, map_mul]
        have he : Complex.exp ((θ : ℂ) * Complex.I) * conj (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
          norm_num
        calc Complex.exp (↑θ * Complex.I) * hf x *
              ((starRingEnd ℂ) (Complex.exp (↑θ * Complex.I)) * (starRingEnd ℂ) x)
            = (Complex.exp ((θ : ℂ) * Complex.I) * conj (Complex.exp ((θ : ℂ) * Complex.I))) *
                (hf x * conj x) := by ring
          _ = hf x * conj x := by rw [he, one_mul]
      rw [hprod]
    · have hxN : x ∉ annN := fun h => hxN' (annN_subset_annN' h)
      rw [hxA hxN, hxB hxN]
      simp

/-- **`-h·∇Φ ∈ X^k`** for a symmetric field `h ∈ C^k(N')`. -/
theorem memXFn_neg_hGradPhi (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {k : ℕ} {hf : ℂ → ℂ} (hhf : MemCk k annN' hf) (hsym : IsSymFieldOn annN' hf) :
    Lin.MemXFn k (fun x => -Eig.hGradPhi χ hf x) := by
  have hH : MemH k (Eig.hGradPhi χ hf) :=
    ((Eig.uniform_inequalities χ hχ hN).2.2 k hf hhf).1
  have hneg : (fun x => -Eig.hGradPhi χ hf x) = (-1 : ℂ) • Eig.hGradPhi χ hf := by
    funext x; simp
  obtain ⟨hsupp, hsymm⟩ := supp_sym_hGradPhi χ hχ hN hsym
  refine ⟨?_, ?_, ?_⟩
  · rw [hneg]; exact (hH.const_smul (-1)).1
  · filter_upwards [hsupp] with x hx hxN
    rw [hx hxN, neg_zero]
  · show (fun x => -Eig.hGradPhi χ hf (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x)) =ᵐ[volume]
      fun x => -Eig.hGradPhi χ hf x
    filter_upwards [hsymm] with x hx
    rw [hx]

/-! ### Realness -/

/-- The classical partial derivatives `∂₁, ∂₂` of a differentiable real function, complexified,
are real. -/
theorem fderiv_ofReal_apply {φ : ℂ → ℝ} {x : ℂ} (hφ : DifferentiableAt ℝ φ x) (v : ℂ) :
    fderiv ℝ (fun y => ((φ y : ℝ) : ℂ)) x v = ((fderiv ℝ φ x v : ℝ) : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt (x := φ x)).comp x hφ.hasFDerivAt
  rw [show (fun y => ((φ y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ φ from rfl, h.fderiv]
  rfl

/-- The weak partial derivatives `∂₁Φ, ∂₂Φ` of the ring are real a.e. -/
theorem weakPartial_PhiC_real (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) :
    (∀ᵐ x ∂(volume : Measure ℂ), (weakPartial (1, 0) (PhiC χ) x).im = 0) ∧
      ∀ᵐ x ∂(volume : Measure ℂ), (weakPartial (0, 1) (PhiC χ) x).im = 0 := by
  obtain ⟨hsmooth, hcpt, -⟩ := ringFacts_of_admissible hχ
  have hC : ContDiff ℝ ∞ (PhiC χ) := Complex.ofRealCLM.contDiff.comp hsmooth
  have hcC : HasCompactSupport (PhiC χ) := hcpt.comp_left Complex.ofReal_zero
  have hW := (memH_of_contDiff_hasCompactSupport hC hcC 1).2.1
  have hdiff : ∀ x, DifferentiableAt ℝ (ringPhi χ) x := fun x =>
    (hsmooth.differentiable (by simp)) x
  have h10 : (1, 0) ∈ multiIdx 1 := by decide
  have h01 : (0, 1) ∈ multiIdx 1 := by decide
  refine ⟨?_, ?_⟩
  · filter_upwards [hW (1, 0) h10] with x hx
    rw [hx]
    show (fderiv ℝ (fun y => ((ringPhi χ y : ℝ) : ℂ)) x (1 : ℂ)).im = 0
    rw [fderiv_ofReal_apply (hdiff x)]
    simp
  · filter_upwards [hW (0, 1) h01] with x hx
    rw [hx]
    show (fderiv ℝ (fun y => ((ringPhi χ y : ℝ) : ℂ)) x Complex.I).im = 0
    rw [fderiv_ofReal_apply (hdiff x)]
    simp

/-- `-h·∇Φ` is real a.e. -/
theorem isReal_neg_hGradPhi (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hf : ℂ → ℂ) :
    ∀ᵐ x ∂(volume : Measure ℂ), (-Eig.hGradPhi χ hf x).im = 0 := by
  obtain ⟨h1, h2⟩ := weakPartial_PhiC_real χ hχ
  filter_upwards [h1, h2] with x hx1 hx2
  have e1 : weakPartial (1, 0) (PhiC χ) x = ((weakPartial (1, 0) (PhiC χ) x).re : ℂ) :=
    Complex.ext rfl (by simpa using hx1)
  have e2 : weakPartial (0, 1) (PhiC χ) x = ((weakPartial (0, 1) (PhiC χ) x).re : ℂ) :=
    Complex.ext rfl (by simpa using hx2)
  rw [← hGrad_PhiC]
  simp only [hGrad, Sob.dotGrad]
  rw [e1, e2]
  simp only [Complex.neg_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-! ### The forcing path -/

/-- **The forcing path** (`05_single_ring.tex:601-604`): for `h` continuous on `[0,ū]` into
`C^s(N')` and `3`-fold symmetric, `v ↦ F(v) = -h(v)·∇Φ` is continuous on `[0,ū]` into `Y^s(N)`
(through `toY`), and every `toY s annN (F v)` lies in `X^s`, is real, and has function `F v`. -/
theorem forcing_path (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} {ubar : ℝ} {h : ℝ → ℂ → ℂ} (hh : CkPathOn s annN' (Icc 0 ubar) h)
    (hsym : ∀ u ∈ Icc (0 : ℝ) ubar, IsSymFieldOn annN' (h u)) :
    ContinuousOn (fun v => toY s annN (forcing χ h v)) (Icc 0 ubar) ∧
      ∀ v ∈ Icc (0 : ℝ) ubar,
        (toY s annN (forcing χ h v)).fn =ᵐ[volume] forcing χ h v ∧
          Lin.MemX (toY s annN (forcing χ h v)) ∧ (toY s annN (forcing χ h v)).IsReal := by
  have hX : ∀ v ∈ Icc (0 : ℝ) ubar, Lin.MemXFn s (forcing χ h v) := fun v hv => by
    rw [forcing_eq]
    exact memXFn_neg_hGradPhi χ hχ hN (hh.1 v hv) (hsym v hv)
  have hfn : ∀ v ∈ Icc (0 : ℝ) ubar, (toY s annN (forcing χ h v)).fn =ᵐ[volume] forcing χ h v :=
    fun v hv => MemXFn.toY_fn (hX v hv)
  refine ⟨?_, fun v hv => ⟨hfn v hv, MemXFn.memX_toY (hX v hv), ?_⟩⟩
  · intro v hv
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ v' ∈ Icc (0 : ℝ) ubar,
        ‖toY s annN (forcing χ h v') - toY s annN (forcing χ h v)‖ ≤
          Eig.Cnab χ s * normCk s annN' (h v' - h v) := by
      intro v' hv'
      rw [norm_sub_eq_normH (hfn v' hv') (hfn v hv)]
      have heq : (fun x => forcing χ h v' x - forcing χ h v x) =
          (-1 : ℂ) • Eig.hGradPhi χ (h v' - h v) := by
        funext x
        simp only [forcing_eq, Pi.smul_apply, smul_eq_mul, hGradPhi_sub]
        ring
      have hmem : MemCk s annN' (h v' - h v) := ((hh.1 v' hv').sub (hh.1 v hv)).1
      have hU := (Eig.uniform_inequalities χ hχ hN).2.2 s (h v' - h v) hmem
      rw [heq, (hU.1.const_smul (-1)).2]
      simpa using hU.2
    have hlim : Tendsto (fun v' => Eig.Cnab χ s * normCk s annN' (h v' - h v))
        (𝓝[Icc (0 : ℝ) ubar] v) (𝓝 0) := by
      simpa using (hh.2 v hv).const_mul (Eig.Cnab χ s)
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    exact eventually_nhdsWithin_of_forall hbound
  · have hr : ∀ᵐ x ∂(volume : Measure ℂ), (forcing χ h v x).im = 0 := by
      rw [forcing_eq]
      exact isReal_neg_hGradPhi χ hχ (h v)
    show ∀ᵐ x ∂(volume : Measure ℂ), ((toY s annN (forcing χ h v)).fn x).im = 0
    filter_upwards [hfn v hv, hr] with x h1 h2
    rw [h1, h2]

end NonUniqueEuler.OneRing.LinPathH
