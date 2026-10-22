import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec5.Bilinear
import NonUniqueEuler.I.Infra.CkNorm.Basic
import NonUniqueEuler.H.Sec8.Coupling.Bridge

/-!
# Helper for `lem:coupling`: the forcing `-h·∇Φ` is a path in `C([0,T]; X^s)`

Helper of `P/Sec8/Coupling.lean` (fully proved, modulo the interface files it imports).

The first group of lemmas is copied from `H/Sec5/Running/Forcing.lean` (helper of `lem:running`,
a helper of another proof cannot be imported), in the namespace `CouplingAux`:
* `hGradPhi_sub`, `sq_norm_mul_hGradPhi`: pointwise algebra of `h·∇Φ`;
* `supp_sym_hGradPhi`, `memXFn_neg_hGradPhi`: `-h·∇Φ ∈ X^k` for a symmetric `h ∈ C^k(N')`
  (`lem:uniform`, `lem:bilinear`(3));
* `forcing_path`: continuity into `Y^s(N)` (`lem:uniform`: `‖h·∇Φ‖_{H^s} ≤ C_∇(s)‖h‖_{C^s(N')}`).

New here: `forcing_pathC` (`08_kick.tex:113-120`, `:140-147`): a field continuous into
`C^s(N')` and `3`-fold symmetric on `[0,T]` gives `-h·∇Φ ∈ C([0,T];X^s)` (`OneRing.PathC`).
-/

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler.CouplingAux

open Sect Sob RingData OneRing

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

/-! ### The forcing path -/

/-- **The forcing path**: for `h` continuous on `[0,ū]` into `C^s(N')` and `3`-fold symmetric,
`v ↦ F(v) = -h(v)·∇Φ` is continuous on `[0,ū]` into `Y^s(N)` (through `toY`), and every `F v`
lies in `X^s`. -/
theorem forcing_path (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} {ubar : ℝ} {h : ℝ → ℂ → ℂ} (hh : CkPathOn s annN' (Icc 0 ubar) h)
    (hsym : ∀ u ∈ Icc (0 : ℝ) ubar, IsSymFieldOn annN' (h u)) :
    ContinuousOn (fun v => toY s annN (forcing χ h v)) (Icc 0 ubar) ∧
      ∀ v ∈ Icc (0 : ℝ) ubar, Lin.MemXFn s (forcing χ h v) := by
  have hX : ∀ v ∈ Icc (0 : ℝ) ubar, Lin.MemXFn s (forcing χ h v) := fun v hv => by
    rw [forcing_eq]
    exact memXFn_neg_hGradPhi χ hχ hN (hh.1 v hv) (hsym v hv)
  have hfn : ∀ v ∈ Icc (0 : ℝ) ubar, (toY s annN (forcing χ h v)).fn =ᵐ[volume] forcing χ h v :=
    fun v hv => (memX_toY (hX v hv)).1
  refine ⟨?_, hX⟩
  intro v hv
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

/-- **`-h·∇Φ ∈ C([0,T];X^s)`** (`OneRing.PathC`) for a field `h` continuous on `[0,T]` into
`C^s(N')` and `3`-fold symmetric (`08_kick.tex:113-120`, via `lem:uniform`). -/
theorem forcing_pathC (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} {T : ℝ} {h : ℝ → ℂ → ℂ} (hh : CkPathOn s annN' (Icc 0 T) h)
    (hsym : ∀ u ∈ Icc (0 : ℝ) T, IsSymFieldOn annN' (h u)) :
    PathC s T (forcing χ h) :=
  ⟨(forcing_path χ hχ hN hh hsym).2, (forcing_path χ hχ hN hh hsym).1⟩

end NonUniqueEuler.CouplingAux
