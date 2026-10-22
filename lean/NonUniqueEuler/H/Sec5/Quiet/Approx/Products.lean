import NonUniqueEuler.H.Sec5.Quiet.Approx.Calculus
import NonUniqueEuler.I.Sec5.Bilinear
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Infra.CkNorm.Basic

/-!
# Helpers for `quiet_approx`: the terms of `eq:ring` along paths

Helper of `P/Sec5/Quiet/Approx.lean` (fully proved). Namespace `NonUniqueEuler.OneRing.QAppH`.
`05_single_ring.tex:477-480` ("By induction on `j`, `lem:duhamel` and `lem:bilinear` show that
`g^{[j]} ∈ C([0,T];X^{k_j})`"):

* `pathC_Bfn`: `u, v ∈ C([0,T];X^{k+1})` ⇒ `B(u,v) ∈ C([0,T];X^k)` (`k ≥ 2`; bilinearity a.e. and
  `lem:bilinear`(1));
* `pathC_hGrad`: `h ∈ C([0,T];C^k(N'))` symmetric, `u ∈ C([0,T];X^{k+1})` ⇒
  `h·∇u ∈ C([0,T];X^k)` (`lem:bilinear`(2));
* `pathC_forcing`: `F = -h·∇Φ ∈ C([0,T];X^k)`, real, `‖F‖_{H^k} ≤ C_∇(k)‖h‖_{C^k(N')}`
  (`lem:bilinear`(3)).
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace NonUniqueEuler.OneRing.QAppH

open Sect Sob RingData

/-- `Φ ∈ X^k` for every `k` (copied from the proved helper `H/Sec5/Energy/Transport.lean`). -/
theorem memXFn_PhiC {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (k : ℕ) :
    Lin.MemXFn k (PhiC χ) := by
  obtain ⟨hsm, hcs, hrad, -, -, hts, ha, -⟩ := ringFacts_of_admissible hχ
  have hsm' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (PhiC χ) := Complex.ofRealCLM.contDiff.comp hsm
  have hcs' : HasCompactSupport (PhiC χ) := hcs.comp_left Complex.ofReal_zero
  refine ⟨(memH_of_contDiff_hasCompactSupport hsm' hcs' k).1, ?_, ?_⟩
  · refine Eventually.of_forall fun x hx => ?_
    have hxt : x ∉ tsupport (ringPhi χ) := by
      intro h
      obtain ⟨h1, h2⟩ := hts h
      exact hx ⟨by linarith, by linarith⟩
    simp [PhiC, image_eq_zero_of_notMem_tsupport hxt]
  · exact Eventually.of_forall fun x => by simp [PhiC, hrad _ x]

/-- `‖-f‖_{H^k} = ‖f‖_{H^k}`. -/
theorem normH_neg {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) : normH k (-f) = normH k f := by
  have hneg : (-1 : ℂ) • f = -f := by funext x; simp
  rw [← hneg, (hf.const_smul (-1)).2]
  simp

/-- `H^k` norm of `f₁ + f₂` when it is a.e. equal to a function. -/
theorem normH_le_of_ae_add {k : ℕ} {F f₁ f₂ : ℂ → ℂ} (h₁ : MemH k f₁) (h₂ : MemH k f₂)
    (hF : F =ᵐ[volume] fun x => f₁ x + f₂ x) : normH k F ≤ normH k f₁ + normH k f₂ := by
  have hs := h₁.add h₂
  have hF' : (f₁ + f₂) =ᵐ[volume] F := hF.symm
  rw [(hs.1.congr_ae hF').2]
  exact hs.2

/-- **`B(u,v)` along paths** (`k ≥ 2`). -/
theorem pathC_Bfn {k : ℕ} (hk : 2 ≤ k) {T : ℝ} {u v : ℝ → ℂ → ℂ} (hu : PathC (k + 1) T u)
    (hv : PathC (k + 1) T v) : PathC k T (fun τ => Bfn (u τ) (v τ)) := by
  have hX : ∀ τ ∈ Icc (0 : ℝ) T, Lin.MemXFn k (Bfn (u τ) (v τ)) := fun τ hτ =>
    (bilinear_B hk (hu.1 τ hτ) (hv.1 τ hτ)).1
  refine ⟨hX, fun τ₀ hτ₀ => ?_⟩
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hu₀ := hu.1 τ₀ hτ₀
  have hv₀ := hv.1 τ₀ hτ₀
  have hbound : ∀ τ ∈ Icc (0 : ℝ) T,
      ‖toY k annN (Bfn (u τ) (v τ)) - toY k annN (Bfn (u τ₀) (v τ₀))‖ ≤
        CB k * (‖toY (k + 1) annN (u τ) - toY (k + 1) annN (u τ₀)‖ *
            ‖toY (k + 1) annN (v τ)‖) +
          CB k * (normH k (u τ₀) * ‖toY (k + 1) annN (v τ) - toY (k + 1) annN (v τ₀)‖) := by
    intro τ hτ
    have huτ := hu.1 τ hτ
    have hvτ := hv.1 τ hτ
    have hΔu : Lin.MemXFn (k + 1) (u τ - u τ₀) := MemXFn.sub huτ hu₀
    have hΔv : Lin.MemXFn (k + 1) (v τ - v τ₀) := MemXFn.sub hvτ hv₀
    rw [norm_sub_eq_normH (MemXFn.toY_fn (hX τ hτ)) (MemXFn.toY_fn (hX τ₀ hτ₀))]
    -- the bilinear splitting
    have e1 : Bfn (u τ) (v τ) = fun x => Bfn (u τ - u τ₀) (v τ) x + Bfn (u τ₀) (v τ) x := by
      have : u τ = (u τ - u τ₀) + u τ₀ := by abel
      conv_lhs => rw [this]
      exact Bfn_add_left (MemXFn.mono hΔu (by omega)) (MemXFn.mono hu₀ (by omega)) (v τ)
    have e2 : Bfn (u τ₀) (v τ) =ᵐ[volume]
        fun x => Bfn (u τ₀) (v τ - v τ₀) x + Bfn (u τ₀) (v τ₀) x := by
      have : v τ = (v τ - v τ₀) + v τ₀ := by abel
      conv_lhs => rw [this]
      exact Bfn_add_right_ae (u τ₀) (hΔv.1.mono_order (by omega)) (hv₀.1.mono_order (by omega))
    have hsplit : (fun x => Bfn (u τ) (v τ) x - Bfn (u τ₀) (v τ₀) x) =ᵐ[volume]
        fun x => Bfn (u τ - u τ₀) (v τ) x + Bfn (u τ₀) (v τ - v τ₀) x := by
      filter_upwards [e2] with x hx
      rw [e1]
      beta_reduce
      rw [hx]
      ring
    have hB1 := bilinear_B hk (MemXFn.mono hΔu le_rfl) hvτ
    have hB2 := bilinear_B hk hu₀ hΔv
    refine (normH_le_of_ae_add hB1.1.1 hB2.1.1 hsplit).trans ?_
    have hn1 : normH k (u τ - u τ₀) ≤
        ‖toY (k + 1) annN (u τ) - toY (k + 1) annN (u τ₀)‖ := by
      rw [norm_sub_eq_normH (MemXFn.toY_fn huτ) (MemXFn.toY_fn hu₀)]
      exact hΔu.1.normH_mono (by omega)
    have hn2 : normH (k + 1) (v τ) = ‖toY (k + 1) annN (v τ)‖ := (MemXFn.norm_toY hvτ).symm
    have hn3 : normH (k + 1) (v τ - v τ₀) =
        ‖toY (k + 1) annN (v τ) - toY (k + 1) annN (v τ₀)‖ := by
      rw [norm_sub_eq_normH (MemXFn.toY_fn hvτ) (MemXFn.toY_fn hv₀)]
      rfl
    have hCB : 0 ≤ CB k := (CB_pos k).le
    have b1 : normH k (Bfn (u τ - u τ₀) (v τ)) ≤
        CB k * (‖toY (k + 1) annN (u τ) - toY (k + 1) annN (u τ₀)‖ *
          ‖toY (k + 1) annN (v τ)‖) := by
      refine hB1.2.trans ?_
      rw [mul_assoc, hn2]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hn1 (norm_nonneg _)) hCB
    have b2 : normH k (Bfn (u τ₀) (v τ - v τ₀)) ≤
        CB k * (normH k (u τ₀) * ‖toY (k + 1) annN (v τ) - toY (k + 1) annN (v τ₀)‖) := by
      refine hB2.2.trans ?_
      rw [mul_assoc, hn3]
    exact add_le_add b1 b2
  have hcu : Tendsto (fun τ => ‖toY (k + 1) annN (u τ) - toY (k + 1) annN (u τ₀)‖)
      (𝓝[Icc 0 T] τ₀) (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 (hu.2 τ₀ hτ₀)
  have hcv : Tendsto (fun τ => ‖toY (k + 1) annN (v τ) - toY (k + 1) annN (v τ₀)‖)
      (𝓝[Icc 0 T] τ₀) (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 (hv.2 τ₀ hτ₀)
  have hnv : Tendsto (fun τ => ‖toY (k + 1) annN (v τ)‖) (𝓝[Icc 0 T] τ₀)
      (𝓝 ‖toY (k + 1) annN (v τ₀)‖) := (hv.2 τ₀ hτ₀).norm
  have hlim : Tendsto (fun τ =>
      CB k * (‖toY (k + 1) annN (u τ) - toY (k + 1) annN (u τ₀)‖ *
            ‖toY (k + 1) annN (v τ)‖) +
          CB k * (normH k (u τ₀) * ‖toY (k + 1) annN (v τ) - toY (k + 1) annN (v τ₀)‖))
      (𝓝[Icc 0 T] τ₀) (𝓝 0) := by
    have := ((hcu.mul hnv).const_mul (CB k)).add ((hcv.const_mul (normH k (u τ₀))).const_mul (CB k))
    simpa using this
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall hbound) hlim

/-- **`h·∇u` along paths** (`k ≥ 2`). -/
theorem pathC_hGrad {k : ℕ} (hk : 2 ≤ k) {T : ℝ} {h : ℝ → ℂ → ℂ}
    (hh : CkPathOn k annN' (Icc 0 T) h) (hsym : ∀ τ ∈ Icc (0 : ℝ) T, IsSymFieldOn annN' (h τ))
    {u : ℝ → ℂ → ℂ} (hu : PathC (k + 1) T u) : PathC k T (fun τ => hGrad (h τ) (u τ)) := by
  have hX : ∀ τ ∈ Icc (0 : ℝ) T, Lin.MemXFn k (hGrad (h τ) (u τ)) := fun τ hτ =>
    (bilinear_h hk (hu.1 τ hτ) (hh.1 τ hτ)).2.2.2 (hsym τ hτ)
  refine ⟨hX, fun τ₀ hτ₀ => ?_⟩
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hu₀ := hu.1 τ₀ hτ₀
  have hh₀ := hh.1 τ₀ hτ₀
  have hChk : 0 ≤ Ch k := (bilinear_Ch hk).2
  have hbound : ∀ τ ∈ Icc (0 : ℝ) T,
      ‖toY k annN (hGrad (h τ) (u τ)) - toY k annN (hGrad (h τ₀) (u τ₀))‖ ≤
        Ch k * (normCk k annN' (h τ - h τ₀) * ‖toY (k + 1) annN (u τ)‖) +
          Ch k * (normCk k annN' (h τ₀) *
            ‖toY (k + 1) annN (u τ) - toY (k + 1) annN (u τ₀)‖) := by
    intro τ hτ
    have huτ := hu.1 τ hτ
    have hΔu : Lin.MemXFn (k + 1) (u τ - u τ₀) := MemXFn.sub huτ hu₀
    have hΔh : MemCk k annN' (h τ - h τ₀) := ((hh.1 τ hτ).sub hh₀).1
    rw [norm_sub_eq_normH (MemXFn.toY_fn (hX τ hτ)) (MemXFn.toY_fn (hX τ₀ hτ₀))]
    have e1 : hGrad (h τ₀) (u τ) =ᵐ[volume]
        fun x => hGrad (h τ₀) (u τ - u τ₀) x + hGrad (h τ₀) (u τ₀) x := by
      have : u τ = (u τ - u τ₀) + u τ₀ := by abel
      conv_lhs => rw [this]
      exact hGrad_add_right_ae (h τ₀) (hΔu.1.mono_order (by omega)) (hu₀.1.mono_order (by omega))
    have hsplit : (fun x => hGrad (h τ) (u τ) x - hGrad (h τ₀) (u τ₀) x) =ᵐ[volume]
        fun x => hGrad (h τ - h τ₀) (u τ) x + hGrad (h τ₀) (u τ - u τ₀) x := by
      filter_upwards [e1] with x hx
      rw [hGrad_sub_left]
      simp only
      rw [hx]
      ring
    have hb1 := bilinear_h hk huτ hΔh
    have hb2 := bilinear_h hk hΔu hh₀
    refine (normH_le_of_ae_add hb1.1 hb2.1 hsplit).trans (add_le_add ?_ ?_)
    · refine hb1.2.2.1.trans (le_of_eq ?_)
      rw [MemXFn.norm_toY huτ]
      ring
    · refine hb2.2.2.1.trans (le_of_eq ?_)
      rw [norm_sub_eq_normH (MemXFn.toY_fn huτ) (MemXFn.toY_fn hu₀), mul_assoc]
      rfl
  have hch : Tendsto (fun τ => normCk k annN' (h τ - h τ₀)) (𝓝[Icc 0 T] τ₀) (𝓝 0) :=
    hh.2 τ₀ hτ₀
  have hcu : Tendsto (fun τ => ‖toY (k + 1) annN (u τ) - toY (k + 1) annN (u τ₀)‖)
      (𝓝[Icc 0 T] τ₀) (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 (hu.2 τ₀ hτ₀)
  have hnu : Tendsto (fun τ => ‖toY (k + 1) annN (u τ)‖) (𝓝[Icc 0 T] τ₀)
      (𝓝 ‖toY (k + 1) annN (u τ₀)‖) := (hu.2 τ₀ hτ₀).norm
  have hlim : Tendsto (fun τ =>
      Ch k * (normCk k annN' (h τ - h τ₀) * ‖toY (k + 1) annN (u τ)‖) +
          Ch k * (normCk k annN' (h τ₀) *
            ‖toY (k + 1) annN (u τ) - toY (k + 1) annN (u τ₀)‖))
      (𝓝[Icc 0 T] τ₀) (𝓝 0) := by
    have := ((hch.mul hnu).const_mul (Ch k)).add
      ((hcu.const_mul (normCk k annN' (h τ₀))).const_mul (Ch k))
    simpa using this
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall hbound) hlim

/-- **The forcing `F = -h·∇Φ` along paths** (`k ≥ 2`): `F ∈ C([0,T];X^k)`, real, with
`‖F(τ)‖_{H^k} ≤ C_∇(k)‖h(τ)‖_{C^k(N')}`. -/
theorem pathC_forcing (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {k : ℕ} (hk : 2 ≤ k) {T : ℝ} {h : ℝ → ℂ → ℂ} (hh : CkPathOn k annN' (Icc 0 T) h)
    (hsym : ∀ τ ∈ Icc (0 : ℝ) T, IsSymFieldOn annN' (h τ)) :
    PathC k T (forcing χ h) ∧
      (∀ τ ∈ Icc (0 : ℝ) T, normH k (forcing χ h τ) ≤ Eig.Cnab χ k * normCk k annN' (h τ)) ∧
      ∀ τ ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure ℂ), (forcing χ h τ x).im = 0 := by
  have hF : ∀ τ, forcing χ h τ = -hGrad (h τ) (PhiC χ) := fun τ => rfl
  have hX : ∀ τ ∈ Icc (0 : ℝ) T, Lin.MemXFn k (forcing χ h τ) := fun τ hτ => by
    rw [hF]
    exact MemXFn.neg ((bilinear_Phi χ hχ hN hk (hh.1 τ hτ)).2.2.2 (hsym τ hτ))
  have hnorm : ∀ τ ∈ Icc (0 : ℝ) T,
      normH k (forcing χ h τ) ≤ Eig.Cnab χ k * normCk k annN' (h τ) := fun τ hτ => by
    have hB := bilinear_Phi χ hχ hN hk (hh.1 τ hτ)
    rw [hF, normH_neg hB.1]
    exact hB.2.2.1
  refine ⟨⟨hX, fun τ₀ hτ₀ => ?_⟩, hnorm, fun τ _ => ?_⟩
  · rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ τ ∈ Icc (0 : ℝ) T,
        ‖toY k annN (forcing χ h τ) - toY k annN (forcing χ h τ₀)‖ ≤
          Eig.Cnab χ k * normCk k annN' (h τ - h τ₀) := by
      intro τ hτ
      rw [norm_sub_eq_normH (MemXFn.toY_fn (hX τ hτ)) (MemXFn.toY_fn (hX τ₀ hτ₀))]
      have hΔh : MemCk k annN' (h τ - h τ₀) := ((hh.1 τ hτ).sub (hh.1 τ₀ hτ₀)).1
      have hB := bilinear_Phi χ hχ hN hk hΔh
      have heq : (fun x => forcing χ h τ x - forcing χ h τ₀ x) =
          -hGrad (h τ - h τ₀) (PhiC χ) := by
        funext x
        rw [hGrad_sub_left]
        simp only [hF, Pi.neg_apply]
        ring
      rw [heq, normH_neg hB.1]
      exact hB.2.2.1
    have hlim : Tendsto (fun τ => Eig.Cnab χ k * normCk k annN' (h τ - h τ₀))
        (𝓝[Icc (0 : ℝ) T] τ₀) (𝓝 0) := by
      simpa using (hh.2 τ₀ hτ₀).const_mul (Eig.Cnab χ k)
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall hbound) hlim
  · have hΦ := memXFn_PhiC hχ 1
    have hR := hGrad_isReal (h τ) hΦ.1 (Eventually.of_forall fun x => by simp [PhiC])
    filter_upwards [hR] with x hx
    rw [hF]
    simp [hx]

end NonUniqueEuler.OneRing.QAppH
