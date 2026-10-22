import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.Energy
import NonUniqueEuler.I.Sec5.Bilinear
import NonUniqueEuler.I.Infra.Sobolev.Norm

/-!
# Helpers for the initial layer of `thm:active`: the energy comparison with `w_app = wlin`

Helper of `P/Sec5/Active/Layer.lean` (fully proved modulo the interface files it imports).
Namespace `NonUniqueEuler.OneRing.LayerH`.

* `rapp_linPath`: with `w_app' = L(G)w_app + F`, the residual of `lem:energy` is
  `R_app = -B(w_app,w_app) + h·∇w_app` pointwise (`05_single_ring.tex:983-985`: "the term `F`
  cancels");
* `rapp_linPath_bound`: `‖R_app‖_{H^k} ≤ C_B(k)‖w_app‖_{H^k}‖w_app‖_{H^{k+1}} +
  C_h(k)‖h‖_{C^k(N')}‖w_app‖_{H^{k+1}}` (`lem:bilinear`(1),(2));
* `lay_pathC_restrict`, `lay_pathC1_restrict`, `lay_normH_eq_zero_of_ae`, `v_le_integral`
  (copies of `H/Sec5/Window/Comparison.lean`): `lem:energy` on `[0,t] ⊆ [0,ū]` with
  `w_app(0) = w(0)` (`05_single_ring.tex:983-988`);
* `integral_exp_const_le`: `∫₀^τ e^{Λ(τ-τ')}R dτ' ≤ τ e^{Λτ} R` for `Λ, R ≥ 0`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

namespace LayerH

/-- With `w_app' = L(G)w_app + F`, `R_app = -B(w_app,w_app) + h·∇w_app` (pointwise). -/
theorem rapp_linPath (χ : ℝ → ℝ) (G : ℝ) (h : ℝ → ℂ → ℂ) (wapp : ℝ → ℂ → ℂ) (τ : ℝ) :
    Rapp χ G h wapp (fun u x => Lin.Lfn χ G (wapp u) x + forcing χ h u x) τ =
      fun x => -Bfn (wapp τ) (wapp τ) x + hGrad (h τ) (wapp τ) x := by
  funext x
  simp only [Rapp, ringRHS, forcing]
  ring

/-- `‖-B(v,v) + h·∇v‖_{H^k} ≤ C_B(k)‖v‖_{H^k}‖v‖_{H^{k+1}} + C_h(k)‖h‖_{C^k(N')}‖v‖_{H^{k+1}}`
(`lem:bilinear`(1),(2)). -/
theorem rapp_linPath_bound {k : ℕ} (hk : 2 ≤ k) {v hf : ℂ → ℂ} (hv : Lin.MemXFn (k + 1) v)
    (hhf : MemCk k annN' hf) :
    Sob.normH k (fun x => -Bfn v v x + hGrad hf v x) ≤
      CB k * Sob.normH k v * Sob.normH (k + 1) v +
        Ch k * normCk k annN' hf * Sob.normH (k + 1) v := by
  obtain ⟨hBX, hBn⟩ := bilinear_B hk hv hv
  obtain ⟨hhm, -, hhn, -⟩ := bilinear_h hk hv hhf
  obtain ⟨hnegm, hnegn⟩ := hBX.1.const_smul (-1 : ℂ)
  have heq : (fun x => -Bfn v v x + hGrad hf v x) = (-1 : ℂ) • Bfn v v + hGrad hf v := by
    funext x
    simp
  rw [heq]
  refine (hnegm.add hhm).2.trans ?_
  rw [hnegn]
  simp only [norm_neg, norm_one, one_mul]
  exact add_le_add hBn hhn

theorem lay_pathC_restrict {s : ℕ} {T T' : ℝ} {u : ℝ → ℂ → ℂ} (h : PathC s T u)
    (hT : T' ≤ T) :
    PathC s T' u :=
  ⟨fun t ht => h.1 t ⟨ht.1, ht.2.trans hT⟩, h.2.mono (Icc_subset_Icc le_rfl hT)⟩

theorem lay_pathC1_restrict {s : ℕ} {T T' : ℝ} {u u' : ℝ → ℂ → ℂ} (h : PathC1 s T u u')
    (hT : T' ≤ T) : PathC1 s T' u u' :=
  ⟨lay_pathC_restrict h.1 hT, lay_pathC_restrict h.2.1 hT,
    fun t ht => (h.2.2 t ⟨ht.1, ht.2.trans hT⟩).mono (Icc_subset_Icc le_rfl hT)⟩

/-- A function that vanishes a.e. has `H^k` norm `0` (given any `H^k` function `g`). -/
theorem lay_normH_eq_zero_of_ae {k : ℕ} {f g : ℂ → ℂ} (hg : Sob.MemH k g)
    (hf : f =ᵐ[volume] (0 : ℂ → ℂ)) : Sob.normH k f = 0 := by
  have h0 := Sob.MemH.const_smul hg 0
  have hz : ((0 : ℂ) • g) = (0 : ℂ → ℂ) := by
    funext x
    simp
  rw [hz] at h0
  have h1 := Sob.MemH.congr_ae h0.1 hf.symm
  rw [h1.2, h0.2]
  simp

/-- **`lem:energy` on `[0,t]`** with `w_app(0) = w(0)` (`05_single_ring.tex:983-988`). -/
theorem v_le_integral {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 3 ≤ s) {c : RingConfig} {ubar t : ℝ} (hc : c.Hyp ubar)
    (ht : t ∈ Icc (0 : ℝ) ubar) (hG : c.G ∈ Icc (0 : ℝ) Gbar) (hsupp : c.RingSupportedIn t annN)
    (hw0 : c.w χ 0 = c.pert0 χ)
    {wapp wapp' : ℝ → ℂ → ℂ} (happ : PathC (s + 1) ubar wapp)
    (happ' : PathC1 s ubar wapp wapp')
    (hreal : ∀ u ∈ Icc (0 : ℝ) ubar, ∀ᵐ x ∂(volume : Measure ℂ), (wapp u x).im = 0)
    (happ0 : wapp 0 =ᵐ[volume] c.pert0 χ)
    (hw : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH s (c.w χ τ) ≤ 1)
    (hwapp : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH (s + 1) (wapp τ) ≤ 1)
    (hh : ∀ τ ∈ Icc (0 : ℝ) t, normCk (s + 1) annN' (c.h τ) ≤ 1)
    {R : ℝ → ℝ} (hRc : ContinuousOn R (Icc 0 t))
    (hR : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH s (Rapp χ c.G c.h wapp wapp' τ) ≤ R τ) :
    ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH s (c.w χ τ - wapp τ) ≤
      ∫ τ' in (0 : ℝ)..τ, Real.exp (Lam χ s * (τ - τ')) * R τ' := by
  intro τ hτ
  have hmem0 : Sob.MemH s (wapp 0) :=
    Sob.MemH.mono_order (happ.1 0 ⟨le_rfl, ht.1.trans ht.2⟩).1 (Nat.le_succ s)
  have hzero : Sob.normH s (c.w χ 0 - wapp 0) = 0 := by
    apply lay_normH_eq_zero_of_ae hmem0
    filter_upwards [happ0] with x hx
    simp [hw0, hx]
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · have hτ0 : τ = 0 := le_antisymm (ht0 ▸ hτ.2) hτ.1
    subst hτ0
    rw [hzero]
    simp
  have hct : c.Hyp t := hc.mono ht0 ht.2
  have hE := energy χ hχ hN hs hct hG hsupp (lay_pathC_restrict happ ht.2)
    (lay_pathC1_restrict happ' ht.2)
    (fun u hu => hreal u ⟨hu.1, hu.2.trans ht.2⟩) hw hwapp hh τ hτ
  rw [hzero, mul_zero, zero_add] at hE
  refine hE.trans ?_
  have hRc' : ContinuousOn (fun τ' => Real.exp (Lam χ s * (τ - τ')) * R τ') (uIcc 0 τ) := by
    rw [uIcc_of_le hτ.1]
    exact (by fun_prop : Continuous fun τ' => Real.exp (Lam χ s * (τ - τ'))).continuousOn.mul
      (hRc.mono (Icc_subset_Icc le_rfl hτ.2))
  by_cases hint : IntervalIntegrable
      (fun τ' => Real.exp (Lam χ s * (τ - τ')) * Sob.normH s (Rapp χ c.G c.h wapp wapp' τ'))
      volume 0 τ
  · apply intervalIntegral.integral_mono_on hτ.1 hint hRc'.intervalIntegrable
    intro τ' hτ'
    exact mul_le_mul_of_nonneg_left (hR τ' ⟨hτ'.1, hτ'.2.trans hτ.2⟩) (Real.exp_pos _).le
  · rw [intervalIntegral.integral_undef hint]
    apply intervalIntegral.integral_nonneg hτ.1
    intro τ' hτ'
    exact mul_nonneg (Real.exp_pos _).le ((Sob.normH_nonneg _ _).trans
      (hR τ' ⟨hτ'.1, hτ'.2.trans hτ.2⟩))

/-- `∫₀^τ e^{Λ(τ-τ')} R dτ' ≤ τ e^{Λτ} R` for `Λ ≥ 0`, `R ≥ 0`, `τ ≥ 0`. -/
theorem integral_exp_const_le {Λ R τ : ℝ} (hΛ : 0 ≤ Λ) (hR : 0 ≤ R) (hτ : 0 ≤ τ) :
    (∫ τ' in (0 : ℝ)..τ, Real.exp (Λ * (τ - τ')) * R) ≤ τ * (Real.exp (Λ * τ) * R) := by
  have hc : ContinuousOn (fun τ' => Real.exp (Λ * (τ - τ')) * R) (uIcc 0 τ) :=
    (by fun_prop : Continuous fun τ' => Real.exp (Λ * (τ - τ')) * R).continuousOn
  have h1 : (∫ τ' in (0 : ℝ)..τ, Real.exp (Λ * (τ - τ')) * R) ≤
      ∫ _ in (0 : ℝ)..τ, Real.exp (Λ * τ) * R := by
    apply intervalIntegral.integral_mono_on hτ hc.intervalIntegrable intervalIntegrable_const
    intro τ' hτ'
    apply mul_le_mul_of_nonneg_right _ hR
    apply Real.exp_le_exp.2
    nlinarith [hτ'.1]
  refine h1.trans (le_of_eq ?_)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

end LayerH

end OneRing

end NonUniqueEuler
