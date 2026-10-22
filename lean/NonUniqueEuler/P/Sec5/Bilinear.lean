import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec2.HkCalculus
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.Sobolev.Leibniz
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.EmbedLinf
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Infra.Sobolev.ReIm
import NonUniqueEuler.I.Infra.CkNorm.Basic
import NonUniqueEuler.H.Sec5.Bilinear.ChiN
import NonUniqueEuler.H.Sec5.Bilinear.Symm
import NonUniqueEuler.H.Sec5.Bilinear.Velocity

/-!
# Proof: the fixed auxiliary objects of Section 5 and `lem:bilinear`

Proof of `I/Sec5/Bilinear.lean` (`05_single_ring.tex:220-227`, `lem:bilinear` `:229-246`, proof
`:247-275`).

* `exists_chiN`: the cutoff `χ_N = b₂ - b₁` (`H/Sec5/Bilinear/ChiN.lean`).
* `CP_isHkCalcConst`, `Cel_isHkBSConst`: `lem:Hk-calculus` (`I/Sec2/HkCalculus.lean`).
* `bilinear_Ch` and (2): `I/Infra/Sobolev/Leibniz.lean` (`MemH.dotGrad_of_memCk` with `K = N`)
  bounds the set defining `C_h`; (2) with `C_h` follows by homogeneity (`normH_hGrad_le_Ch`:
  scale `h` by `(‖h‖ + ε)⁻¹`, `w` by `(‖w‖ + ε)⁻¹` and let `ε → 0`; this also covers the
  degenerate cases `‖h‖ = 0`, `‖w‖ = 0`).
* (1): on `N` (where `∇w` lives) `χ_B = 1`, so `B(v,w)` is a.e. the four-term expansion `bExp`
  in the real entries of `χ_B K_BS * v`; each product by `lem:Hk-calculus`(2) with `j = k`,
  `‖∂_i w‖_{H^k} ≤ ‖w‖_{H^{k+1}}`, the four entries summed by Cauchy–Schwarz
  (`Σ_4 ≤ 2 (Σ squares)^{1/2}`, `I/Infra/Sobolev/ReIm.lean`), and `lem:Hk-calculus`(3) with
  `j = k - 1`, `ρ = 4`.
* (3): `lem:uniform` (`I/Sec4/Uniform.lean`).
* (4): `K_BS * v` is continuous (`H/Sec5/Bilinear/Velocity.lean`), so `lem:embed`(E2) applies
  pointwise to `χ_B K_BS * v` (`χ_B = 1` on `\bar B_3`), and `lem:Hk-calculus`(3) with `j = 1`.
  (The proof gives the constant `C^el_1 ≤ C_BS`.)
* Supports: `∇w`, `∇Φ` vanish a.e. outside `N` (`MemH.weakPartial_eq_zero_outside`).
  Symmetry: `H/Sec5/Bilinear/Symm.lean`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- `05_single_ring.tex:221-223`: there is `χ_N ∈ C_c^∞(N₁)` with `χ_N = 1` on a neighbourhood
of `N`; together with `N` compact and `N₁ ⊇ N` open and bounded, this is the setting of
`lem:Hk-calculus` for `(N, N₁, χ_N)`. -/
theorem exists_chiN : ∃ χN : ℂ → ℝ, Sob.HkCalcSetting annN annN1 χN :=
  ⟨BilinearH.chiN, BilinearH.hkCalcSetting_chiN⟩

/-- `05_single_ring.tex:225-227`: the fixed `C_P(k)` is a constant of `lem:Hk-calculus`(1),(2)
for `max(k,3)`, `N`, `N₁`. -/
theorem CP_isHkCalcConst (k : ℕ) : Sob.IsHkCalcConst (max k 3) annN annN1 (CP k) := by
  obtain ⟨χN, hχN⟩ := exists_chiN
  exact Sob.isHkCalcConst_hkCalcConst (le_max_right k 3) hχN

/-- `05_single_ring.tex:223-225`: the fixed `C^el_j` is a constant of `lem:Hk-calculus`(3) for
`j`, `χ_B` and `ρ = 4`. -/
theorem Cel_isHkBSConst (j : ℕ) : Sob.IsHkBSConst j chiB 4 (Cel j) :=
  Sob.isHkBSConst_elConst j (by norm_num) chiB_contDiff chiB_hasCompactSupport
    tsupport_chiB_subset

namespace BilinearH

theorem annN_subset_annN' : annN ⊆ annN' := fun x hx => by
  rw [mem_annN] at hx
  rw [mem_annN']
  have := a_pos'
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem isClosed_annN : IsClosed annN := isCompact_annN.isClosed

theorem norm_le_two_of_mem_annN {x : ℂ} (hx : x ∈ annN) : ‖x‖ ≤ 2 := (mem_annN.1 hx).2

/-- `∇w` vanishes a.e. outside `N` for `w ∈ H^1` vanishing a.e. outside `N`. -/
theorem grad_zero_outside {w : ℂ → ℂ} (hw : Sob.MemH 1 w)
    (hwN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → w x = 0) :
    ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN →
      Sob.weakPartial (1, 0) w x = 0 ∧ Sob.weakPartial (0, 1) w x = 0 := by
  have h1 := hw.weakPartial_eq_zero_outside isClosed_annN hwN (γ := (1, 0))
    (by rw [Sob.mem_multiIdx]; norm_num)
  have h2 := hw.weakPartial_eq_zero_outside isClosed_annN hwN (γ := (0, 1))
    (by rw [Sob.mem_multiIdx]; norm_num)
  filter_upwards [h1, h2] with x hx1 hx2 hx
  exact ⟨hx1 hx, hx2 hx⟩

theorem grad_zero_outside' {w : ℂ → ℂ}
    (h : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN →
      Sob.weakPartial (1, 0) w x = 0 ∧ Sob.weakPartial (0, 1) w x = 0) :
    ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN' →
      Sob.weakPartial (1, 0) w x = 0 ∧ Sob.weakPartial (0, 1) w x = 0 := by
  filter_upwards [h] with x hx hx'
  exact hx fun h' => hx' (annN_subset_annN' h')

theorem dotGrad_zero_outside {h w : ℂ → ℂ}
    (hw : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN →
      Sob.weakPartial (1, 0) w x = 0 ∧ Sob.weakPartial (0, 1) w x = 0) :
    ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → Sob.dotGrad h w x = 0 := by
  filter_upwards [hw] with x hx hxN
  obtain ⟨h1, h2⟩ := hx hxN
  simp [Sob.dotGrad, h1, h2]

/-- Weak derivatives of a scalar multiple. -/
theorem weakPartial_smul_ae {k : ℕ} {w : ℂ → ℂ} (hw : Sob.MemH k w) (c : ℂ) {γ : ℕ × ℕ}
    (hγ : γ ∈ Sob.multiIdx k) :
    Sob.weakPartial γ (c • w) =ᵐ[volume] c • Sob.weakPartial γ w := by
  have hw' := (hw.const_smul c).1
  obtain ⟨hL, hW⟩ := hw.memLp_weakPartial hγ
  exact hw'.weakPartial_ae_eq hγ (hL.const_smul c) (hW.const_mul c)

/-- Homogeneity of `h·∇w` in `h` (real scalars) and `w`. -/
theorem hGrad_smul_ae {k : ℕ} {w : ℂ → ℂ} (hw : Sob.MemH (k + 1) w) (hf : ℂ → ℂ) (c c' : ℝ) :
    hGrad (c' • hf) ((c : ℂ) • w) =ᵐ[volume] ((c' * c : ℝ) : ℂ) • hGrad hf w := by
  have e1 := weakPartial_smul_ae hw (c : ℂ) (γ := (1, 0)) (by rw [Sob.mem_multiIdx]; omega)
  have e2 := weakPartial_smul_ae hw (c : ℂ) (γ := (0, 1)) (by rw [Sob.mem_multiIdx]; omega)
  filter_upwards [e1, e2] with x h1 h2
  simp only [hGrad, Sob.dotGrad, h1, h2, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  push_cast
  ring

theorem memXFn_smul {s : ℕ} {w : ℂ → ℂ} (hw : Lin.MemXFn s w) (c : ℂ) :
    Lin.MemXFn s (c • w) := by
  refine ⟨(hw.1.const_smul c).1, ?_, ?_⟩
  · filter_upwards [hw.2.1] with x hx hxN
    simp [hx hxN]
  · unfold Ang.IsMFoldSymmetricC
    filter_upwards [hw.2.2] with x hx
    simp only [Pi.smul_apply] at hx ⊢
    rw [hx]

/-- `‖h·∇w‖_{H^k} ≤ (‖h‖_{C^k(N')} + ε)(‖w‖_{H^{k+1}} + ε) C_h` for every `ε > 0`. -/
theorem normH_hGrad_le_eps {k : ℕ} {w hf : ℂ → ℂ} (hw : Lin.MemXFn (k + 1) w)
    (hhf : MemCk k annN' hf)
    (hbdd : BddAbove {x : ℝ | ∃ v hf : ℂ → ℂ, Lin.MemXFn (k + 1) v ∧ Sob.normH (k + 1) v ≤ 1 ∧
      MemCk k annN' hf ∧ normCk k annN' hf ≤ 1 ∧ x = Sob.normH k (hGrad hf v)})
    {ε : ℝ} (hε : 0 < ε) :
    Sob.normH k (hGrad hf w) ≤
      Ch k * (normCk k annN' hf + ε) * (Sob.normH (k + 1) w + ε) := by
  set A := normCk k annN' hf with hA
  set B := Sob.normH (k + 1) w with hB
  have hA0 : 0 ≤ A := normCk_nonneg _ _ _
  have hB0 : 0 ≤ B := Sob.normH_nonneg _ _
  have hAε : 0 < A + ε := by linarith
  have hBε : 0 < B + ε := by linarith
  set c : ℝ := (B + ε)⁻¹ with hc
  set c' : ℝ := (A + ε)⁻¹ with hc'
  have hc0 : 0 < c := inv_pos.2 hBε
  have hc'0 : 0 < c' := inv_pos.2 hAε
  -- the normalized pair lies in the set defining `C_h`
  have hw' : Lin.MemXFn (k + 1) ((c : ℂ) • w) := memXFn_smul hw _
  have hnw' : Sob.normH (k + 1) ((c : ℂ) • w) ≤ 1 := by
    rw [(hw.1.const_smul (c : ℂ)).2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0, hc,
      ← hB, inv_mul_le_one₀ hBε]
    linarith
  have hhf' : MemCk k annN' (c' • hf) := hhf.smul c'
  have hnhf' : normCk k annN' (c' • hf) ≤ 1 := by
    rw [normCk_smul, abs_of_pos hc'0, hc', ← hA, inv_mul_le_one₀ hAε]
    linarith
  have hmem : Sob.normH k (hGrad (c' • hf) ((c : ℂ) • w)) ≤ Ch k :=
    le_csSup hbdd ⟨(c : ℂ) • w, c' • hf, hw', hnw', hhf', hnhf', rfl⟩
  -- homogeneity
  obtain ⟨hG, -⟩ := Sob.MemH.dotGrad_of_memCk isClosed_annN hw.1 hw.2.1
    (hhf.mono_set annN_subset_annN')
  have hG' : Sob.MemH k (hGrad hf w) := hG
  obtain ⟨hGs, hGn⟩ := hG'.const_smul ((c' * c : ℝ) : ℂ)
  have heq : Sob.normH k (hGrad (c' • hf) ((c : ℂ) • w)) = (c' * c) * Sob.normH k (hGrad hf w) := by
    rw [(hGs.congr_ae (hGrad_smul_ae hw.1 hf c c').symm).2, hGn, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (mul_pos hc'0 hc0)]
  rw [heq] at hmem
  have hX0 := Sob.normH_nonneg k (hGrad hf w)
  have hprod : (A + ε) * (B + ε) * (c' * c) = 1 := by
    rw [hc, hc']
    field_simp
  calc Sob.normH k (hGrad hf w)
      = (A + ε) * (B + ε) * ((c' * c) * Sob.normH k (hGrad hf w)) := by
        rw [← mul_assoc, hprod, one_mul]
    _ ≤ (A + ε) * (B + ε) * Ch k := by gcongr
    _ = Ch k * (A + ε) * (B + ε) := by ring

end BilinearH

/-- **`lem:bilinear`, `C_h` is finite** (`05_single_ring.tex:232-235`): for `k ≥ 2` the set whose
supremum is `C_h(k)` (the values `‖h·∇w‖_{H^k}` over `w ∈ X^{k+1}`, `h ∈ C^k(N';ℝ²)` with
`‖w‖_{H^{k+1}} ≤ 1`, `‖h‖_{C^k(N')} ≤ 1`) is bounded above; in particular `0 ≤ C_h(k) < ∞`. -/
theorem bilinear_Ch {k : ℕ} (hk : 2 ≤ k) :
    BddAbove {x : ℝ | ∃ v hf : ℂ → ℂ, Lin.MemXFn (k + 1) v ∧ Sob.normH (k + 1) v ≤ 1 ∧
      MemCk k annN' hf ∧ normCk k annN' hf ≤ 1 ∧ x = Sob.normH k (hGrad hf v)} ∧
      0 ≤ Ch k := by
  refine ⟨⟨(k + 1) * 2 ^ (k + 1), ?_⟩, ?_⟩
  · rintro x ⟨v, hf, hv, hvn, hh, hhn, rfl⟩
    obtain ⟨-, hb⟩ := Sob.MemH.dotGrad_of_memCk BilinearH.isClosed_annN hv.1 hv.2.1
      (hh.mono_set BilinearH.annN_subset_annN')
    have h1 : normCk k annN hf ≤ 1 :=
      (normCk_mono_set hh BilinearH.annN_subset_annN').trans hhn
    have h0 := normCk_nonneg k annN hf
    have h0' := Sob.normH_nonneg (k + 1) v
    calc Sob.normH k (hGrad hf v)
        ≤ (k + 1) * 2 ^ (k + 1) * normCk k annN hf * Sob.normH (k + 1) v := hb
      _ ≤ (k + 1) * 2 ^ (k + 1) * 1 * 1 := by gcongr
      _ = (k + 1) * 2 ^ (k + 1) := by ring
  · unfold Ch
    exact Real.sSup_nonneg fun x ⟨v, hf, _, _, _, _, hx⟩ => hx ▸ Sob.normH_nonneg _ _

/-! ### Item (1): the four-term expansion of `B(v,w)` -/

namespace BilinearH

/-- `χ_B K_BS * Re v` (a real vector field in `ℂ`). -/
def cutRe (v : ℂ → ℂ) (x : ℂ) : ℂ := (chiB x : ℂ) * BS.velocityRe v x

/-- `χ_B K_BS * Im v` (a real vector field in `ℂ`). -/
def cutIm (v : ℂ → ℂ) (x : ℂ) : ℂ := (chiB x : ℂ) * BS.velocityIm v x

/-- `B(v,w)` on `N`, written with the four real entries of `χ_B K_BS * v`:
`-((u₁)₁∂₁w + (u₁)₂∂₂w + i((u₂)₁∂₁w + (u₂)₂∂₂w))`, `u₁ = χ_B K_BS * Re v`,
`u₂ = χ_B K_BS * Im v`. -/
def bExp (v w : ℂ → ℂ) : ℂ → ℂ :=
  (-1 : ℂ) •
    (((fun x => ((cutRe v x).re : ℂ)) * Sob.weakPartial (1, 0) w +
        (fun x => ((cutRe v x).im : ℂ)) * Sob.weakPartial (0, 1) w) +
      Complex.I •
        ((fun x => ((cutIm v x).re : ℂ)) * Sob.weakPartial (1, 0) w +
          (fun x => ((cutIm v x).im : ℂ)) * Sob.weakPartial (0, 1) w))

theorem Bfn_ae_eq_bExp {v w : ℂ → ℂ}
    (hw : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN →
      Sob.weakPartial (1, 0) w x = 0 ∧ Sob.weakPartial (0, 1) w x = 0) :
    Bfn v w =ᵐ[volume] bExp v w := by
  filter_upwards [hw] with x hx
  by_cases hxN : x ∈ annN
  · have h1 : chiB x = 1 := chiB_eq_one (by linarith [norm_le_two_of_mem_annN hxN])
    simp only [Bfn, bsGrad, Sob.dotGrad, bExp, cutRe, cutIm, h1, Pi.smul_apply, Pi.add_apply,
      Pi.mul_apply, smul_eq_mul, Complex.ofReal_one, one_mul]
    ring
  · obtain ⟨h1, h2⟩ := hx hxN
    simp [Bfn, bsGrad, Sob.dotGrad, bExp, h1, h2]

theorem Bfn_zero_outside {v w : ℂ → ℂ}
    (hw : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN →
      Sob.weakPartial (1, 0) w x = 0 ∧ Sob.weakPartial (0, 1) w x = 0) :
    ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → Bfn v w x = 0 := by
  filter_upwards [hw] with x hx hxN
  obtain ⟨h1, h2⟩ := hx hxN
  simp [Bfn, bsGrad, Sob.dotGrad, h1, h2]

/-- `x₁ + x₂ + x₃ + x₄ ≤ 2 (x₁² + x₂² + x₃² + x₄²)^{1/2}`. -/
theorem sum_four_le (x₁ x₂ x₃ x₄ : ℝ) :
    x₁ + x₂ + x₃ + x₄ ≤ 2 * Real.sqrt (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2) := by
  have h : ((x₁ + x₂ + x₃ + x₄) / 2) ^ 2 ≤ x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 := by
    nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ - x₃), sq_nonneg (x₁ - x₄),
      sq_nonneg (x₂ - x₃), sq_nonneg (x₂ - x₄), sq_nonneg (x₃ - x₄)]
  have := (le_abs_self _).trans (Real.abs_le_sqrt h)
  linarith

/-- The four real entries of `(a, b)`: `Σ ≤ 2 ‖(a,b)‖_{H^k}`. -/
theorem sum_four_le_normHC2 {k : ℕ} {a b : ℂ → ℂ} (ha : Sob.MemH k a) (hb : Sob.MemH k b) :
    Sob.normH k (fun x => ((a x).re : ℂ)) + Sob.normH k (fun x => ((a x).im : ℂ)) +
        Sob.normH k (fun x => ((b x).re : ℂ)) + Sob.normH k (fun x => ((b x).im : ℂ)) ≤
      2 * BS.normHC2 k a b := by
  obtain ⟨-, -, hna⟩ := ha.re_im
  obtain ⟨-, -, hnb⟩ := hb.re_im
  have := sum_four_le (Sob.normH k (fun x => ((a x).re : ℂ)))
    (Sob.normH k (fun x => ((a x).im : ℂ))) (Sob.normH k (fun x => ((b x).re : ℂ)))
    (Sob.normH k (fun x => ((b x).im : ℂ)))
  unfold BS.normHC2
  rw [← hna, ← hnb]
  convert this using 3
  ring

/-- The arithmetic of the bound in (1). -/
theorem bound_aux {N P₁ P₂ P₃ P₄ x₁ x₂ x₃ x₄ D₁ D₂ W C S E V' V : ℝ}
    (hN : N ≤ P₁ + P₂ + (P₃ + P₄))
    (h₁ : P₁ ≤ C * x₁ * D₁) (h₂ : P₂ ≤ C * x₂ * D₂) (h₃ : P₃ ≤ C * x₃ * D₁)
    (h₄ : P₄ ≤ C * x₄ * D₂)
    (hC : 0 ≤ C) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hx₃ : 0 ≤ x₃) (hx₄ : 0 ≤ x₄)
    (hD₁ : D₁ ≤ W) (hD₂ : D₂ ≤ W) (hW : 0 ≤ W)
    (hS : x₁ + x₂ + x₃ + x₄ ≤ 2 * S) (hSE : S ≤ E * V') (hE : 0 ≤ E) (hV : V' ≤ V) :
    N ≤ 2 * C * E * V * W := by
  have a₁ : C * x₁ * D₁ ≤ C * x₁ * W := mul_le_mul_of_nonneg_left hD₁ (mul_nonneg hC hx₁)
  have a₂ : C * x₂ * D₂ ≤ C * x₂ * W := mul_le_mul_of_nonneg_left hD₂ (mul_nonneg hC hx₂)
  have a₃ : C * x₃ * D₁ ≤ C * x₃ * W := mul_le_mul_of_nonneg_left hD₁ (mul_nonneg hC hx₃)
  have a₄ : C * x₄ * D₂ ≤ C * x₄ * W := mul_le_mul_of_nonneg_left hD₂ (mul_nonneg hC hx₄)
  have hCW : 0 ≤ C * W := mul_nonneg hC hW
  have hEV : S ≤ E * V := hSE.trans (mul_le_mul_of_nonneg_left hV hE)
  calc N ≤ P₁ + P₂ + (P₃ + P₄) := hN
    _ ≤ C * x₁ * W + C * x₂ * W + (C * x₃ * W + C * x₄ * W) :=
      add_le_add (add_le_add (h₁.trans a₁) (h₂.trans a₂)) (add_le_add (h₃.trans a₃) (h₄.trans a₄))
    _ = C * W * (x₁ + x₂ + x₃ + x₄) := by ring
    _ ≤ C * W * (2 * S) := mul_le_mul_of_nonneg_left hS hCW
    _ ≤ C * W * (2 * (E * V)) := mul_le_mul_of_nonneg_left (by linarith) hCW
    _ = 2 * C * E * V * W := by ring

theorem supp_ball_four {v : ℂ → ℂ} (hv : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → v x = 0) :
    ∀ᵐ x ∂(volume : Measure ℂ), x ∉ ball (0 : ℂ) 4 → v x = 0 := by
  filter_upwards [hv] with y hy hy4
  refine hy fun hyN => hy4 ?_
  rw [mem_ball_zero_iff]
  linarith [norm_le_two_of_mem_annN hyN]

end BilinearH

open BilinearH in
/-- **`lem:bilinear`(1)** (`05_single_ring.tex:236`, `:244-246`): for `k ≥ 2` and
`v, w ∈ X^{k+1}`, `B(v,w) = -(K_BS*v)·∇w` lies in `X^k` (in particular in `H^k` and supported in
`N`) and `‖B(v,w)‖_{H^k} ≤ C_B‖v‖_{H^k}‖w‖_{H^{k+1}}`. -/
theorem bilinear_B {k : ℕ} (hk : 2 ≤ k) {v w : ℂ → ℂ} (hv : Lin.MemXFn (k + 1) v)
    (hw : Lin.MemXFn (k + 1) w) :
    Lin.MemXFn k (Bfn v w) ∧
      Sob.normH k (Bfn v w) ≤ CB k * Sob.normH k v * Sob.normH (k + 1) w := by
  have hgrad := grad_zero_outside (hw.1.mono_order (by omega)) hw.2.1
  -- `lem:Hk-calculus`(3) with `j = k - 1`, `ρ = 4`
  have hvk1 : Sob.MemH (k - 1) v := hv.1.mono_order (by omega)
  obtain ⟨ha, hb, hab⟩ := Cel_isHkBSConst (k - 1) v hvk1 (supp_ball_four hv.2.1)
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at ha hb hab
  have ha' : Sob.MemH k (cutRe v) := ha
  have hb' : Sob.MemH k (cutIm v) := hb
  have hab' : BS.normHC2 k (cutRe v) (cutIm v) ≤ Cel (k - 1) * Sob.normH (k - 1) v := hab
  obtain ⟨hra, hia, hna⟩ := ha'.re_im
  obtain ⟨hrb, hib, hnb⟩ := hb'.re_im
  -- `∂_i w ∈ H^k`, `‖∂_i w‖_{H^k} ≤ ‖w‖_{H^{k+1}}`
  have hd1 : Sob.MemH k (Sob.weakPartial (1, 0) w) ∧
      Sob.normH k (Sob.weakPartial (1, 0) w) ≤ Sob.normH (k + 1) w :=
    Sob.MemH.weakPartial (γ := (1, 0)) hw.1
  have hd2 : Sob.MemH k (Sob.weakPartial (0, 1) w) ∧
      Sob.normH k (Sob.weakPartial (0, 1) w) ≤ Sob.normH (k + 1) w :=
    Sob.MemH.weakPartial (γ := (0, 1)) hw.1
  -- the four products, `lem:Hk-calculus`(2) with `j = k`
  have hprod := (CP_isHkCalcConst k).2
  have hkm : k ≤ max k 3 := le_max_left _ _
  obtain ⟨hp1, hb1⟩ := hprod k hk hkm _ _ hra hd1.1
  obtain ⟨hp2, hb2⟩ := hprod k hk hkm _ _ hia hd2.1
  obtain ⟨hp3, hb3⟩ := hprod k hk hkm _ _ hrb hd1.1
  obtain ⟨hp4, hb4⟩ := hprod k hk hkm _ _ hib hd2.1
  obtain ⟨hs1, hn1⟩ := hp1.add hp2
  obtain ⟨hs2, hn2⟩ := hp3.add hp4
  obtain ⟨hs3, hn3⟩ := hs2.const_smul Complex.I
  obtain ⟨hs4, hn4⟩ := hs1.add hs3
  obtain ⟨hs5, hn5⟩ := hs4.const_smul (-1 : ℂ)
  have hE : Sob.MemH k (bExp v w) := hs5
  have hEn : Sob.normH k (bExp v w) ≤
      Sob.normH k ((fun x => ((cutRe v x).re : ℂ)) * Sob.weakPartial (1, 0) w) +
        Sob.normH k ((fun x => ((cutRe v x).im : ℂ)) * Sob.weakPartial (0, 1) w) +
        (Sob.normH k ((fun x => ((cutIm v x).re : ℂ)) * Sob.weakPartial (1, 0) w) +
          Sob.normH k ((fun x => ((cutIm v x).im : ℂ)) * Sob.weakPartial (0, 1) w)) := by
    have e5 : Sob.normH k (bExp v w) = _ := hn5
    rw [e5, norm_neg, norm_one, one_mul]
    refine hn4.trans ?_
    rw [hn3, Complex.norm_I, one_mul]
    linarith
  -- `B(v,w) = bExp v w` a.e.
  have hae := Bfn_ae_eq_bExp (v := v) hgrad
  obtain ⟨hBm, hBn⟩ := hE.congr_ae hae.symm
  refine ⟨⟨hBm, Bfn_zero_outside hgrad, ?_⟩, ?_⟩
  · -- symmetry
    have hvs := isMFoldSymmetricC_three_iff.1 hv.2.2
    have hw1 : Sob.MemH 1 w := hw.1.mono_order (by omega)
    have h1 := dotGrad_isMFoldSymmetricC hw1 hw.2.2 (grad_zero_outside' hgrad)
      (h := BS.velocityRe v) (fun x _ => velocityRe_rot hvs x)
    have h2 := dotGrad_isMFoldSymmetricC hw1 hw.2.2 (grad_zero_outside' hgrad)
      (h := BS.velocityIm v) (fun x _ => velocityIm_rot hvs x)
    rw [isMFoldSymmetricC_three_iff] at h1 h2 ⊢
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [Bfn, bsGrad] at hx1 hx2 ⊢
    rw [hx1, hx2]
  · -- the bound
    rw [hBn]
    have hmono : Sob.normH (k - 1) v ≤ Sob.normH k v :=
      (hv.1.mono_order (by omega : k ≤ k + 1)).normH_mono (by omega)
    have key := bound_aux hEn hb1 hb2 hb3 hb4 (CP_pos k).le (Sob.normH_nonneg _ _)
      (Sob.normH_nonneg _ _) (Sob.normH_nonneg _ _) (Sob.normH_nonneg _ _) hd1.2 hd2.2
      (Sob.normH_nonneg _ _) (sum_four_le_normHC2 ha' hb') hab' (Cel_pos _).le hmono
    calc Sob.normH k (bExp v w)
        ≤ 2 * CP k * Cel (k - 1) * Sob.normH k v * Sob.normH (k + 1) w := key
      _ = CB k * Sob.normH k v * Sob.normH (k + 1) w := by unfold CB; ring

open BilinearH in
/-- **`lem:bilinear`(2)** (`05_single_ring.tex:237`, `:244-246`): for `k ≥ 2`, `w ∈ X^{k+1}` and
a vector field `h ∈ C^k(N';ℝ²)`, `h·∇w ∈ H^k` vanishes a.e. outside `N`,
`‖h·∇w‖_{H^k} ≤ C_h‖h‖_{C^k(N')}‖w‖_{H^{k+1}}`, and `h·∇w ∈ X^k` if `h` is `3`-fold symmetric. -/
theorem bilinear_h {k : ℕ} (hk : 2 ≤ k) {w hf : ℂ → ℂ} (hw : Lin.MemXFn (k + 1) w)
    (hhf : MemCk k annN' hf) :
    Sob.MemH k (hGrad hf w) ∧ (∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → hGrad hf w x = 0) ∧
      Sob.normH k (hGrad hf w) ≤ Ch k * normCk k annN' hf * Sob.normH (k + 1) w ∧
      (IsSymFieldOn annN' hf → Lin.MemXFn k (hGrad hf w)) := by
  obtain ⟨hG, -⟩ := Sob.MemH.dotGrad_of_memCk isClosed_annN hw.1 hw.2.1
    (hhf.mono_set annN_subset_annN')
  have hG' : Sob.MemH k (hGrad hf w) := hG
  have hgrad := grad_zero_outside (hw.1.mono_order (by omega)) hw.2.1
  have hzero : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → hGrad hf w x = 0 :=
    dotGrad_zero_outside hgrad
  have hbdd := (bilinear_Ch hk).1
  -- the bound, by homogeneity and `ε → 0`
  have hbound : Sob.normH k (hGrad hf w) ≤ Ch k * normCk k annN' hf * Sob.normH (k + 1) w := by
    have ht : Tendsto (fun ε : ℝ => Ch k * (normCk k annN' hf + ε) * (Sob.normH (k + 1) w + ε))
        (𝓝[>] 0) (𝓝 (Ch k * (normCk k annN' hf + 0) * (Sob.normH (k + 1) w + 0))) := by
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      exact ((continuous_const.mul (continuous_const.add continuous_id)).mul
        (continuous_const.add continuous_id)).tendsto 0
    have h := ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) =>
      normH_hGrad_le_eps hw hhf hbdd hε)
    simpa using h
  refine ⟨hG', hzero, hbound, fun hsym => ⟨hG', hzero, ?_⟩⟩
  exact dotGrad_isMFoldSymmetricC (hw.1.mono_order (by omega)) hw.2.2
    (grad_zero_outside' hgrad) hsym

open BilinearH in
/-- **`lem:bilinear`(3)** (`05_single_ring.tex:238-239`, `:244-246`): for `k ≥ 2` and a vector
field `h ∈ C^k(N';ℝ²)`, `h·∇Φ ∈ H^k` vanishes a.e. outside `N`,
`‖h·∇Φ‖_{H^k} ≤ C_∇(k)‖h‖_{C^k(N')}` with `C_∇(k)` of `lem:uniform`, and `h·∇Φ ∈ X^k` if `h` is
`3`-fold symmetric. -/
theorem bilinear_Phi (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {k : ℕ} (hk : 2 ≤ k) {hf : ℂ → ℂ} (hhf : MemCk k annN' hf) :
    Sob.MemH k (hGrad hf (PhiC χ)) ∧
      (∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → hGrad hf (PhiC χ) x = 0) ∧
      Sob.normH k (hGrad hf (PhiC χ)) ≤ Eig.Cnab χ k * normCk k annN' hf ∧
      (IsSymFieldOn annN' hf → Lin.MemXFn k (hGrad hf (PhiC χ))) := by
  obtain ⟨hm, hb⟩ := (Eig.uniform_inequalities χ hχ hN).2.2 k hf hhf
  obtain ⟨hsm, hcs, hrad, -, -, htsupp, -, -⟩ := ringFacts_of_admissible hχ
  have hPsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (PhiC χ) :=
    Complex.ofRealCLM.contDiff.comp hsm
  have hPc : HasCompactSupport (PhiC χ) := hcs.comp_left Complex.ofReal_zero
  have hPH : Sob.MemH 1 (PhiC χ) := (Sob.memH_of_contDiff_hasCompactSupport hPsm hPc 1).1
  have hPsupp : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → PhiC χ x = 0 := by
    refine Eventually.of_forall fun x hx => ?_
    have hx' : x ∉ tsupport (ringPhi χ) := fun h => by
      have h' := htsupp h
      apply hx
      rw [mem_annN]
      have := a_pos'
      exact ⟨by linarith [h'.1], by linarith [h'.2]⟩
    simp [PhiC, image_eq_zero_of_notMem_tsupport hx']
  have hgrad := grad_zero_outside hPH hPsupp
  have hzero : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → hGrad hf (PhiC χ) x = 0 :=
    dotGrad_zero_outside hgrad
  have hPsym : Ang.IsMFoldSymmetricC 3 (PhiC χ) := by
    refine Eventually.of_forall fun x => ?_
    simp [PhiC, hrad _ x]
  refine ⟨hm, hzero, hb, fun hsym => ⟨hm, hzero, ?_⟩⟩
  exact dotGrad_isMFoldSymmetricC hPH hPsym (grad_zero_outside' hgrad) hsym

open BilinearH in
/-- **`lem:bilinear`(4)** (`05_single_ring.tex:240-243`): for `k ≥ 2` and `v ∈ X^{k+1}`,
`|(K_BS*v)(x)| ≤ C_BS‖v‖_{H^1}` for every `|x| ≤ 3`. -/
theorem bilinear_BS {k : ℕ} (hk : 2 ≤ k) {v : ℂ → ℂ} (hv : Lin.MemXFn (k + 1) v) :
    ∀ x : ℂ, ‖x‖ ≤ 3 → bsNorm v x ≤ CBS * Sob.normH 1 v := by
  intro x hx
  have hv1 : Sob.MemH 1 v := hv.1.mono_order (by omega)
  have hv2 : Sob.MemH 2 v := hv.1.mono_order (by omega)
  obtain ⟨ha, hb, hab⟩ := Cel_isHkBSConst 1 v hv1 (supp_ball_four hv.2.1)
  have ha' : Sob.MemH 2 (cutRe v) := ha
  have hb' : Sob.MemH 2 (cutIm v) := hb
  have hab' : BS.normHC2 2 (cutRe v) (cutIm v) ≤ Cel 1 * Sob.normH 1 v := hab
  obtain ⟨hcR, hcI⟩ := continuous_velocity_of_memH hv2 isCompact_annN hv.2.1
  have hchi : Continuous (fun y => (chiB y : ℂ)) :=
    Complex.continuous_ofReal.comp chiB_contDiff.continuous
  have h1 := Sob.norm_le_normH_two_of_continuous ha' (hchi.mul hcR) x
  have h2 := Sob.norm_le_normH_two_of_continuous hb' (hchi.mul hcI) x
  have hx1 : chiB x = 1 := chiB_eq_one (by linarith)
  simp only [cutRe, cutIm, hx1, Complex.ofReal_one, one_mul] at h1 h2
  have hbs : bsNorm v x ≤ BS.normHC2 2 (cutRe v) (cutIm v) := by
    unfold bsNorm BS.normHC2
    apply Real.sqrt_le_sqrt
    have := norm_nonneg (BS.velocityRe v x)
    have := norm_nonneg (BS.velocityIm v x)
    gcongr
  have hCel := Cel_pos 1
  have hv0 := Sob.normH_nonneg 1 v
  calc bsNorm v x ≤ BS.normHC2 2 (cutRe v) (cutIm v) := hbs
    _ ≤ Cel 1 * Sob.normH 1 v := hab'
    _ ≤ CBS * Sob.normH 1 v := by unfold CBS; nlinarith

end OneRing

end NonUniqueEuler
