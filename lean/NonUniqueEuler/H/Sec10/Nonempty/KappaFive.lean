import NonUniqueEuler.H.Sec10.Nonempty.Kappa
import NonUniqueEuler.I.Sec5.ActiveT1

/-!
# Helper for `lem:nonempty`: (κ5) for small `κ`, uniformly in `G`

Helper of `P/Sec10/Nonempty.lean`, the treatment of (κ5) in the proof of `lem:nonempty`
(`10_parameters.tex:327-343`). Let `c = σ_b - σ' > 0`, `σ_max = max_{[0,G₁]} σ`. For `G ∈ [0,G₁]`,
`t₁(C₀,G) ≤ t̄₁(C₀)` (`active_tOne`) and `σ(G) ∈ [σ_b, σ_max]`, so `T̂ ≥ σ_max⁻¹ log(δ₀/κ)`. Once
`log(δ₀/κ) ≥ σ_max(t̄₁(C₀) + Y)`, `y = T̂ - t₁(C₀,G) ≥ Y ≥ 0` and
`ρ̂(T̂) = ⟨y⟩^p e^{-(σ(G)-σ')y} ≤ ⟨y⟩^p e^{-cy}`, which is `≤ ε` for `y ≥ Y`. This is the
manuscript's argument with the bound `K_c e^{-cy/2}` replaced by the limit `⟨y⟩^pe^{-cy} → 0`.

All lemmas are fully proved. Namespace `NonUniqueEuler.Relay.NonemptyH`.
-/

noncomputable section

open Set Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace NonemptyH

theorem jap_le_one_add_abs (y : ℝ) : Prelim.jap y ≤ 1 + |y| := by
  have h1 : Prelim.jap y ^ 2 ≤ (1 + |y|) ^ 2 := by
    rw [Prelim.jap_sq]
    nlinarith [abs_nonneg y, sq_abs y]
  exact (pow_le_pow_iff_left₀ (Prelim.jap_nonneg _) (by positivity) two_ne_zero).1 h1

/-- `⟨y⟩^p e^{-cy} → 0` as `y → ∞` (`c > 0`). -/
theorem tendsto_jap_pow_mul_exp_neg {c : ℝ} (hc : 0 < c) (N : ℕ) :
    Tendsto (fun y : ℝ => Prelim.jap y ^ N * Real.exp (-(c * y))) atTop (𝓝 0) := by
  have h := tendsto_one_add_pow_mul_exp_neg hc N
  refine squeeze_zero' (Eventually.of_forall fun y =>
    mul_nonneg (pow_nonneg (Prelim.jap_nonneg _) _) (Real.exp_pos _).le) ?_ h
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  rw [neg_mul]
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Prelim.jap_nonneg _) ?_ N)
    (Real.exp_pos _).le
  simpa [abs_of_nonneg hy] using jap_le_one_add_abs y

/-- `log(δ/κ) → ∞` as `κ → 0⁺` (`δ > 0`). -/
theorem tendsto_log_div_atTop {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun κ : ℝ => Real.log (δ / κ)) (𝓝[>] 0) atTop := by
  have h : Tendsto (fun κ : ℝ => Real.log δ + -Real.log κ) (𝓝[>] 0) atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with κ (hκ : 0 < κ)
  rw [Real.log_div hδ.ne' hκ.ne']
  ring

/-- `σ(G) ≤ σ_max` on `[0, G₁]`. -/
theorem sigma_le_sigmaMax {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) : Eig.sigma χ G ≤ OneRing.sigmaMax χ := by
  obtain ⟨-, -, -, -, G₁, -, hmax⟩ := Eig.propU_a χ hχ hN
  have hbdd : BddAbove (Eig.sigma χ '' Icc 0 Gbar) := by
    refine ⟨Eig.sigma χ G₁, ?_⟩
    rintro _ ⟨G', hG', rfl⟩
    exact hmax G' hG'
  exact le_csSup hbdd (mem_image_of_mem _ hG)

/-- `σ_b ≤ σ(G)` on `[0, G₁]`. -/
theorem sigb_le_sigma {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) : Eig.sigb χ ≤ Eig.sigma χ G := by
  obtain ⟨-, -, ⟨G₀, -, hsb, hmin⟩, -, -⟩ := Eig.propU_a χ hχ hN
  rw [hsb]
  exact hmin G hG

variable {p : Params}

/-- **(κ5) for small `κ`, uniformly in `G ∈ [0, G₁]`** (`10_parameters.tex:327-343`). -/
theorem eventually_k5 (hχ : IsAdmissibleCutoff p.χ) (hN : NumericalHypothesis p.χ)
    (hpos : p.ref.ConstPos) (hp : p.Structural) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∀ G ∈ Icc (0 : ℝ) Gbar,
      Eig.Cp * p.ref.C2 * (OneRing.rhoHat p.ref.P.χ p.ref.σ' p.ref.C0 G
          (OneRing.That (Eig.sigma p.ref.P.χ G) p.ref.P.δ₀ κ) + Real.sqrt κ) ≤
        Eig.cout p.ref.P.χ / (16 * Real.pi) := by
  have hCp : 0 < Eig.Cp * p.ref.C2 := hpos.Cp_C2_pos
  have hR : 0 < Eig.cout p.ref.P.χ / (16 * Real.pi) := by
    have := hpos.cout_pos
    positivity
  set ε : ℝ := Eig.cout p.ref.P.χ / (16 * Real.pi) / (2 * (Eig.Cp * p.ref.C2)) with hε_def
  have hε : 0 < ε := by positivity
  have hc : 0 < Eig.sigb p.χ - p.σ' := sub_pos.2 hp.p0.σ'_lt_sigb
  obtain ⟨Y, hY⟩ := eventually_atTop.1
    ((tendsto_jap_pow_mul_exp_neg hc OneRing.pW).eventually (eventually_le_nhds hε))
  set Y' : ℝ := max Y 0 with hY'_def
  have hY'0 : 0 ≤ Y' := le_max_right _ _
  have hsb : 0 < Eig.sigb p.χ := hpos.sigb_pos
  have hσM : 0 < OneRing.sigmaMax p.χ :=
    lt_of_lt_of_le hsb ((sigb_le_sigma hχ hN ⟨le_rfl, Gbar_pos.le⟩).trans
      (sigma_le_sigmaMax hχ hN ⟨le_rfl, Gbar_pos.le⟩))
  set tb : ℝ := OneRing.tOneBar p.χ p.σ' p.ref.C0 with htb_def
  have htb : 0 ≤ tb := Real.sInf_nonneg fun t ht => ht.1
  have hδ : 0 < p.δ₀ := hp.p1.δ₀_pos
  have hL : ∀ᶠ κ in 𝓝[>] (0 : ℝ), OneRing.sigmaMax p.χ * (tb + Y') ≤ Real.log (p.δ₀ / κ) :=
    (tendsto_log_div_atTop hδ).eventually (eventually_ge_atTop _)
  have hsq : ∀ᶠ κ in 𝓝[>] (0 : ℝ), Real.sqrt κ ≤ ε :=
    eventually_le_of_tendsto_zero tendsto_sqrt_nhdsGT hε
  filter_upwards [hL, self_mem_nhdsWithin, hsq] with κ hκL (hκ : 0 < κ) hκs G hG
  have hσlo : Eig.sigb p.χ ≤ Eig.sigma p.χ G := sigb_le_sigma hχ hN hG
  have hσhi : Eig.sigma p.χ G ≤ OneRing.sigmaMax p.χ := sigma_le_sigmaMax hχ hN hG
  have hσG : 0 < Eig.sigma p.χ G := lt_of_lt_of_le hsb hσlo
  obtain ⟨ht1, -⟩ := OneRing.active_tOne p.χ hχ hN ⟨hp.p0.σ'_gt, hp.p0.σ'_lt_sigb⟩
    p.ref.one_le_C0 hG hκ
  set L : ℝ := Real.log (p.δ₀ / κ) with hL_def
  have hLnn : 0 ≤ L := le_trans (by positivity) hκL
  have hT : tb + Y' ≤ (Eig.sigma p.χ G)⁻¹ * L := by
    have h1 : tb + Y' ≤ L / OneRing.sigmaMax p.χ := by
      rw [le_div_iff₀ hσM]; linarith
    have h2 : L / OneRing.sigmaMax p.χ ≤ L / Eig.sigma p.χ G :=
      div_le_div_of_nonneg_left hLnn hσG hσhi
    rw [inv_mul_eq_div]
    exact h1.trans h2
  set u : ℝ := OneRing.That (Eig.sigma p.χ G) p.δ₀ κ with hu_def
  have hu_eq : u = (Eig.sigma p.χ G)⁻¹ * L := rfl
  set t₁ : ℝ := OneRing.tOneOf (Eig.sigma p.χ G) p.σ' p.ref.C0 with ht₁_def
  have ht1' : t₁ ≤ tb := ht1
  have hy : Y' ≤ u - t₁ := by rw [hu_eq]; linarith
  have hy0 : 0 ≤ u - t₁ := hY'0.trans hy
  have hrho : OneRing.rhoHat p.χ p.σ' p.ref.C0 G u ≤ ε := by
    have hle : t₁ ≤ u := by linarith
    show OneRing.rhoHatOf (Eig.sigma p.χ G) p.σ' p.ref.C0 u ≤ ε
    rw [OneRing.rhoHatOf_of_le hle]
    refine le_trans ?_ (hY (u - t₁) ((le_max_left _ _).trans hy))
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (pow_nonneg (Prelim.jap_nonneg _) _)
    have : Eig.sigb p.χ - p.σ' ≤ Eig.sigma p.χ G - p.σ' := by linarith
    nlinarith
  have hsum : OneRing.rhoHat p.χ p.σ' p.ref.C0 G u + Real.sqrt κ ≤ 2 * ε := by linarith
  calc Eig.Cp * p.ref.C2 * (OneRing.rhoHat p.χ p.σ' p.ref.C0 G u + Real.sqrt κ)
      ≤ Eig.Cp * p.ref.C2 * (2 * ε) := mul_le_mul_of_nonneg_left hsum hCp.le
    _ = Eig.cout p.ref.P.χ / (16 * Real.pi) := by
        rw [hε_def]; field_simp
        exact mul_div_cancel_left₀ _ hCp.ne'

end NonemptyH

end Relay

end NonUniqueEuler
