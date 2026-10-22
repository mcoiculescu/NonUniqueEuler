import NonUniqueEuler.H.Sec5.Energy.RappPath.Bilin
import NonUniqueEuler.I.Sec5.Bilinear
import NonUniqueEuler.I.Infra.CkNorm.Basic

/-!
# Helpers for `R_app ∈ C([0,t];X^s)`: the nonlinear and field terms are paths in `X^s`

Helper of `P/Sec5/Energy/RappPath.lean` (`05_single_ring.tex:331`). Namespace
`NonUniqueEuler.OneRing.RappPathH`. For `s ≥ 2` and `w ∈ C([0,T];X^{s+1})`:

* `pathC_Bfn`: `B(w,w) ∈ C([0,T];X^s)` (`lem:bilinear`(1), `bilinear_B`, and the a.e.
  bilinearity `Bfn_diff_ae`);
* `pathC_hGrad`: `h·∇w ∈ C([0,T];X^s)` for `h ∈ C([0,T];C^s(N'))`, `3`-fold symmetric on `N'`
  (`lem:bilinear`(2), `bilinear_h`, and `hGrad_diff_ae`);
* `pathC_hGradPhi`: `h·∇Φ ∈ C([0,T];X^s)` for the same `h` (`lem:bilinear`(3), `bilinear_Phi`,
  linear in `h`).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.RappPathH

open RingData Sect Sob

/-- `‖w(τ') - w(τ)‖_{H^s} → 0` along a path in `C([0,T];X^{s+1})`. -/
theorem PathC.tendsto_normH_sub_lower {s : ℕ} {T : ℝ} {u : ℝ → ℂ → ℂ} (hu : PathC (s + 1) T u)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) :
    Tendsto (fun τ' => normH s (u τ' - u τ)) (𝓝[Icc (0 : ℝ) T] τ) (𝓝 0) := by
  refine tendsto_normH_sub_of_le ?_ (PathC.tendsto_normH_sub hu hτ)
  filter_upwards [self_mem_nhdsWithin] with τ' hτ'
  exact (MemXFn.sub (hu.1 τ' hτ') (hu.1 τ hτ)).1.normH_mono (Nat.le_succ s)

/-- **`B(w,w) ∈ C([0,T];X^s)`** for `w ∈ C([0,T];X^{s+1})`, `s ≥ 2`. -/
theorem pathC_Bfn {s : ℕ} (hs : 2 ≤ s) {T : ℝ} {u : ℝ → ℂ → ℂ} (hu : PathC (s + 1) T u) :
    PathC s T (fun τ => Bfn (u τ) (u τ)) := by
  refine pathC_of_tendsto (fun τ hτ => (bilinear_B hs (hu.1 τ hτ) (hu.1 τ hτ)).1)
    fun τ hτ => ?_
  have ha1 := PathC.tendsto_normH_sub hu hτ
  have hN := PathC.tendsto_normH hu hτ
  have ha0 := PathC.tendsto_normH_sub_lower hu hτ
  refine tendsto_normH_sub_of_le (b := fun τ' => CB s * normH s (u τ' - u τ) *
      normH (s + 1) (u τ') + CB s * normH s (u τ) * normH (s + 1) (u τ' - u τ)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with τ' hτ'
    show normH s (Bfn (u τ') (u τ') - Bfn (u τ) (u τ)) ≤ _
    have h1 := hu.1 τ' hτ'
    have h0 := hu.1 τ hτ
    have hd := MemXFn.sub h1 h0
    obtain ⟨hB1, hb1⟩ := bilinear_B hs hd h1
    obtain ⟨hB2, hb2⟩ := bilinear_B hs h0 hd
    have hae := Bfn_diff_ae (MemXFn.mono h1 (by omega)) (MemXFn.mono h0 (by omega))
    exact (normH_le_of_ae_eq_add hB1.1 hB2.1 hae).trans (add_le_add hb1 hb2)
  · have := ((tendsto_const_nhds (x := CB s)).mul ha0 |>.mul hN).add
      ((tendsto_const_nhds (x := CB s * normH s (u τ))).mul ha1)
    simpa using this

/-- **`h·∇w ∈ C([0,T];X^s)`** for `w ∈ C([0,T];X^{s+1})`, `s ≥ 2`, and `h ∈ C([0,T];C^s(N'))`
`3`-fold symmetric on `N'`. -/
theorem pathC_hGrad {s : ℕ} (hs : 2 ≤ s) {T : ℝ} {u h : ℝ → ℂ → ℂ} (hu : PathC (s + 1) T u)
    (hh : CkPathOn s annN' (Icc 0 T) h)
    (hsym : ∀ τ ∈ Icc (0 : ℝ) T, IsSymFieldOn annN' (h τ)) :
    PathC s T (fun τ => hGrad (h τ) (u τ)) := by
  refine pathC_of_tendsto
    (fun τ hτ => (bilinear_h hs (hu.1 τ hτ) (hh.1 τ hτ)).2.2.2 (hsym τ hτ)) fun τ hτ => ?_
  have ha1 := PathC.tendsto_normH_sub hu hτ
  have hN := PathC.tendsto_normH hu hτ
  have hc := hh.2 τ hτ
  refine tendsto_normH_sub_of_le (b := fun τ' => Ch s * normCk s annN' (h τ' - h τ) *
      normH (s + 1) (u τ') + Ch s * normCk s annN' (h τ) * normH (s + 1) (u τ' - u τ)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with τ' hτ'
    show normH s (hGrad (h τ') (u τ') - hGrad (h τ) (u τ)) ≤ _
    have h1 := hu.1 τ' hτ'
    have h0 := hu.1 τ hτ
    have hd := MemXFn.sub h1 h0
    have hcd : MemCk s annN' (h τ' - h τ) := ((hh.1 τ' hτ').sub (hh.1 τ hτ)).1
    obtain ⟨hH1, -, hb1, -⟩ := bilinear_h hs h1 hcd
    obtain ⟨hH2, -, hb2, -⟩ := bilinear_h hs hd (hh.1 τ hτ)
    have hae := hGrad_diff_ae (h τ') (h τ) (h1.1.mono_order (by omega))
      (h0.1.mono_order (by omega))
    exact (normH_le_of_ae_eq_add hH1 hH2 hae).trans (add_le_add hb1 hb2)
  · have := ((tendsto_const_nhds (x := Ch s)).mul hc |>.mul hN).add
      ((tendsto_const_nhds (x := Ch s * normCk s annN' (h τ))).mul ha1)
    simpa using this

/-- **`h·∇Φ ∈ C([0,T];X^s)`** for `h ∈ C([0,T];C^s(N'))` `3`-fold symmetric on `N'`, `s ≥ 2`. -/
theorem pathC_hGradPhi (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 2 ≤ s) {T : ℝ} {h : ℝ → ℂ → ℂ} (hh : CkPathOn s annN' (Icc 0 T) h)
    (hsym : ∀ τ ∈ Icc (0 : ℝ) T, IsSymFieldOn annN' (h τ)) :
    PathC s T (fun τ => hGrad (h τ) (PhiC χ)) := by
  refine pathC_of_tendsto
    (fun τ hτ => (bilinear_Phi χ hχ hN hs (hh.1 τ hτ)).2.2.2 (hsym τ hτ)) fun τ hτ => ?_
  refine tendsto_normH_sub_of_le (b := fun τ' => Eig.Cnab χ s * normCk s annN' (h τ' - h τ))
    ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with τ' hτ'
    show normH s (hGrad (h τ') (PhiC χ) - hGrad (h τ) (PhiC χ)) ≤ _
    have hcd : MemCk s annN' (h τ' - h τ) := ((hh.1 τ' hτ').sub (hh.1 τ hτ)).1
    rw [hGrad_sub_field]
    exact (bilinear_Phi χ hχ hN hs hcd).2.2.1
  · simpa using (hh.2 τ hτ).const_mul (Eig.Cnab χ s)

end NonUniqueEuler.OneRing.RappPathH
