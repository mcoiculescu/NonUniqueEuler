import NonUniqueEuler.H.Sec5.Quiet.Approx.Hierarchy
import NonUniqueEuler.H.Sec5.Quiet.Approx.Products
import NonUniqueEuler.H.Sec5.Quiet.Approx.MajInt
import NonUniqueEuler.I.Sec4.PropU

/-!
# Helpers for `quiet_approx`: the induction on `j` (regularity, equations, `eq:Q-hier`)

Helper of `P/Sec5/Quiet/Approx.lean` (fully proved). Namespace `NonUniqueEuler.OneRing.QAppH`.
Manuscript `05_single_ring.tex:474-492`. With `A = C_L C_bil` and a number `R` with
`A (N_Q A/σ_b + 1) ≤ R`, the constants `C^{(j)} = A R^{j-1}` satisfy the recursion inequality of
the manuscript (deviation: the manuscript defines `C^{(j)}` by the exact recursion; any constants
satisfying the inequality work, and this closed form avoids a recursive definition).

`hier_props`: for `1 ≤ j ≤ N_Q`, `w^{[j]} ∈ C([0,T];X^{k_j}) ∩ C¹([0,T];X^{k_j-1})` with
`∂_t w^{[j]} = L w^{[j]} + g^{[j]}`, real, `w^{[j]}(0) = 0`, `‖w^{[j]}(t)‖_{H^{k_j}} ≤
A R^{j-1} maj(t)^j` (`eq:Q-hier`), and `g^{[j]} ∈ C([0,T];X^{k_j})` real (`k_j = K - j`).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.QAppH

open Sect Sob RingData

/-! ### Small lemmas -/

theorem CkPathOn.mono_order {k k' : ℕ} {U : Set ℂ} {I : Set ℝ} {h : ℝ → ℂ → ℂ}
    (hh : CkPathOn k' U I h) (hk : k ≤ k') : CkPathOn k U I h := by
  refine ⟨fun t ht => (hh.1 t ht).mono_order hk, fun t ht => ?_⟩
  refine squeeze_zero' (Eventually.of_forall fun _ => normCk_nonneg _ _ _)
    (eventually_nhdsWithin_of_forall fun t' ht' => ?_) (hh.2 t ht)
  exact normCk_mono_order ((hh.1 t' ht').sub (hh.1 t ht)).1 hk

theorem isReal_sum {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ S, ∀ᵐ x ∂(volume : Measure ℂ), (f i x).im = 0) :
    ∀ᵐ x ∂(volume : Measure ℂ), ((∑ i ∈ S, f i) x).im = 0 := by
  have hall : ∀ᵐ x ∂(volume : Measure ℂ), ∀ i ∈ S, (f i x).im = 0 :=
    (Filter.eventually_all_finset S).2 hf
  filter_upwards [hall] with x hx
  rw [Finset.sum_apply, Complex.im_sum]
  exact Finset.sum_eq_zero hx

theorem isReal_sub {f g : ℂ → ℂ} (hf : ∀ᵐ x ∂(volume : Measure ℂ), (f x).im = 0)
    (hg : ∀ᵐ x ∂(volume : Measure ℂ), (g x).im = 0) :
    ∀ᵐ x ∂(volume : Measure ℂ), ((f - g) x).im = 0 := by
  filter_upwards [hf, hg] with x h1 h2
  simp [h1, h2]

theorem normH_sum_le {k : ℕ} {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ S, MemH k (f i)) : normH k (∑ i ∈ S, f i) ≤ ∑ i ∈ S, normH k (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 := (memXFn_zero k).1
    have hz : normH k (0 : ℂ → ℂ) = 0 := by
      have hY := Y_memH_fn (0 : Y k annN)
      rw [norm_zero] at hY
      rw [← hY.2]
      exact (hY.1.congr_ae (Y_fn_zero k annN)).2
    rw [hz]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hS := memH_sum S fun i hi => hf i (Finset.mem_insert_of_mem hi)
    refine ((hf a (Finset.mem_insert_self a S)).add hS).2.trans ?_
    exact add_le_add le_rfl (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem sigb_facts (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) : 0 < Eig.sigb χ ∧ Eig.sigb χ ≤ Eig.sigma χ G := by
  obtain ⟨-, -, ⟨G₀, -, hb, hmin⟩, hpos, -⟩ := Eig.propU_a χ hχ hN
  refine ⟨by linarith, ?_⟩
  rw [hb]
  exact hmin G hG

theorem eta_integrableOn {η : ℝ → ℝ} {T : ℝ} (hη : Measurable η)
    (hb : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ η t ∧ η t ≤ 1) : IntegrableOn η (Icc 0 T) := by
  refine IntegrableOn.of_bound measure_Icc_lt_top hη.aestronglyMeasurable 1 ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall fun t ht => by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hb t ht]

/-- The scalar step of the recursion for `C^{(j)} = A R^{j-1}` (`j = n + 1`). -/
theorem const_step {CL Cbil R σ σb : ℝ} {n NQ : ℕ} (hCL : 0 ≤ CL) (hCbil : 0 ≤ Cbil)
    (hR : CL * Cbil * (NQ * (CL * Cbil) / σb + 1) ≤ R) (hR0 : 0 ≤ R) (hσb : 0 < σb)
    (hσ : σb ≤ σ) (hn : 1 ≤ n) (hnQ : n ≤ NQ) :
    CL * (Cbil * ((n : ℝ) * n * (CL * Cbil) ^ 2 * R ^ (n - 1)) / (n * σ) +
        Cbil * (CL * Cbil * R ^ (n - 1))) ≤ CL * Cbil * R ^ n := by
  set A := CL * Cbil with hA
  have hA0 : 0 ≤ A := mul_nonneg hCL hCbil
  have hσ0 : 0 < σ := lt_of_lt_of_le hσb hσ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set X := R ^ (n - 1) with hX
  have hX0 : 0 ≤ X := pow_nonneg hR0 _
  have hRn : R ^ n = X * R := by
    rw [hX, ← pow_succ]
    congr 1
    omega
  have e1 : CL * (Cbil * ((n : ℝ) * n * A ^ 2 * X) / (n * σ) + Cbil * (A * X)) =
      A ^ 2 * X * (n * A / σ + 1) := by
    rw [hA]
    field_simp
  rw [e1, hRn]
  have h2 : (n : ℝ) * A / σ ≤ NQ * A / σb := by
    have h3 : (n : ℝ) * A ≤ NQ * A := mul_le_mul_of_nonneg_right (by exact_mod_cast hnQ) hA0
    calc (n : ℝ) * A / σ ≤ NQ * A / σ := div_le_div_of_nonneg_right h3 hσ0.le
      _ ≤ NQ * A / σb := div_le_div_of_nonneg_left (by positivity) hσb hσ
  calc A ^ 2 * X * (n * A / σ + 1) ≤ A ^ 2 * X * (NQ * A / σb + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = A * X * (A * (NQ * A / σb + 1)) := by ring
    _ ≤ A * X * R := mul_le_mul_of_nonneg_left hR (mul_nonneg hA0 hX0)
    _ = A * (X * R) := by ring

/-! ### The induction -/

/-- The properties of `w^{[j]}`, `g^{[j]}` proved by induction on `j`. -/
def HierProp (χ : ℝ → ℝ) (K : ℕ) (G T : ℝ) (h : ℝ → ℂ → ℂ) (η : ℝ → ℝ) (A R : ℝ) (j : ℕ) :
    Prop :=
  PathC (K - j) T (hw χ K G h j) ∧
    PathC1 (K - j - 1) T (hw χ K G h j)
      (fun t => Lin.Lfn χ G (hw χ K G h j t) + hg χ K G h j t) ∧
    (∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure ℂ), (hw χ K G h j t x).im = 0) ∧
    hw χ K G h j 0 =ᵐ[volume] 0 ∧
    (∀ t ∈ Icc (0 : ℝ) T,
      normH (K - j) (hw χ K G h j t) ≤ A * R ^ (j - 1) * maj (Eig.sigma χ G) η t ^ j) ∧
    PathC (K - j) T (hg χ K G h j) ∧
    (∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure ℂ), (hg χ K G h j t x).im = 0)

/-- The Duhamel part of the induction step. -/
theorem duh_part (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {K : ℕ} {G T : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) (hT : 0 < T) {h : ℝ → ℂ → ℂ} {j : ℕ} (hj : 1 ≤ j)
    (hjK : j + 1 ≤ K) (hgp : PathC (K - j) T (hg χ K G h j))
    (hgR : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure ℂ), (hg χ K G h j t x).im = 0) :
    PathC (K - j) T (hw χ K G h j) ∧
      PathC1 (K - j - 1) T (hw χ K G h j)
        (fun t => Lin.Lfn χ G (hw χ K G h j t) + hg χ K G h j t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure ℂ), (hw χ K G h j t x).im = 0) ∧
      hw χ K G h j 0 =ᵐ[volume] 0 := by
  rw [hw_eq χ K G h hj]
  obtain ⟨k, hk⟩ : ∃ k, K - j = k + 1 := ⟨K - j - 1, by omega⟩
  have hk' : K - j - 1 = k := by omega
  rw [hk', hk]
  rw [hk] at hgp
  obtain ⟨h1, h2, h3, h4⟩ := duhFn_spec χ hχ hG hT k hgp
  exact ⟨h1, h2, h4 hgR, h3⟩

theorem hier_props (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {sh NQ : ℕ} (hs : 3 ≤ sh) (hQ : 2 ≤ NQ)
    {CL Cbil R : ℝ} (hCL : 0 ≤ CL) (hCbil : 0 ≤ Cbil) (hR0 : 0 ≤ R)
    (hR : CL * Cbil * (NQ * (CL * Cbil) / Eig.sigb χ + 1) ≤ R)
    (hSb : ∀ k ≤ Mh sh NQ, ∀ G ∈ Icc (0 : ℝ) Gbar, ∀ t : ℝ, 0 ≤ t → ∀ w : Y k annN,
      Lin.MemX w → ‖Lin.S χ k G t w‖ ≤ CL * Real.exp (Eig.sigma χ G * t) * ‖w‖)
    (hBb : ∀ k, 2 ≤ k → k ≤ Mh sh NQ → CB k ≤ Cbil ∧ Ch k ≤ Cbil ∧ Eig.Cnab χ k ≤ Cbil)
    {G T : ℝ} {h : ℝ → ℂ → ℂ} {η : ℝ → ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) (hT : 0 < T)
    (hh : CkPathOn (Mh sh NQ) annN' (Icc 0 T) h)
    (hsym : ∀ t ∈ Icc (0 : ℝ) T, IsSymFieldOn annN' (h t)) (hηm : Measurable η)
    (hη : ∀ t ∈ Icc (0 : ℝ) T, normCk (Mh sh NQ) annN' (h t) ≤ η t ∧ η t ≤ 1) :
    ∀ j, 1 ≤ j → j ≤ NQ → HierProp χ (Mh sh NQ) G T h η (CL * Cbil) R j := by
  set K := Mh sh NQ with hKdef
  have hKv : K = sh + NQ + 1 := rfl
  obtain ⟨hσb, hσbσ⟩ := sigb_facts χ hχ hN hG
  have hσ : 0 < Eig.sigma χ G := lt_of_lt_of_le hσb hσbσ
  have hη0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ η t := fun t ht =>
    (normCk_nonneg _ _ _).trans (hη t ht).1
  have hηi : IntegrableOn η (Icc 0 T) :=
    eta_integrableOn hηm fun t ht => ⟨hη0 t ht, (hη t ht).2⟩
  obtain ⟨hM, -⟩ := majorant_of_pos hσ hηi hη0
  have hm0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ maj (Eig.sigma χ G) η t := fun t ht =>
    maj_nonneg hσ hηi hη0 ht
  have hηint : ∀ t ∈ Icc (0 : ℝ) T, IntervalIntegrable η volume 0 t := fun t ht =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2
      (hηi.mono_set (Icc_subset_Icc le_rfl ht.2))
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj1 hjQ
  have hhk : ∀ k ≤ K, CkPathOn k annN' (Icc 0 T) h := fun k hk => CkPathOn.mono_order hh hk
  have hnormh : ∀ k ≤ K, ∀ t ∈ Icc (0 : ℝ) T, normCk k annN' (h t) ≤ η t := fun k hk t ht =>
    (normCk_mono_order (hh.1 t ht) hk).trans (hη t ht).1
  rcases Nat.eq_or_lt_of_le hj1 with hj | hj
  · -- `j = 1`: the linear response
    subst hj
    have hK1 : 2 ≤ K - 1 := by omega
    obtain ⟨hFp, hFn, hFR⟩ := pathC_forcing χ hχ hN hK1 (hhk (K - 1) (by omega)) hsym
    rw [← hg_one χ K G h] at hFp hFn hFR
    obtain ⟨d1, d2, d3, d4⟩ := duh_part χ hχ hG hT (j := 1) le_rfl (by omega) hFp hFR
    refine ⟨d1, d2, d3, d4, fun t ht => ?_, hFp, hFR⟩
    rw [hw_eq χ K G h le_rfl]
    have hb := duhFn_bound χ hFp (hSb (K - 1) (by omega) G hG) ht
    refine hb.trans ?_
    have hCnab := (hBb (K - 1) hK1 (by omega)).2.2
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    have hi1 : IntervalIntegrable (fun τ => Real.exp (Eig.sigma χ G * (t - τ)) *
        normH (K - 1) (hg χ K G h 1 τ)) volume 0 t :=
      (((Continuous.continuousOn (by fun_prop)).mul
        ((PathC.continuousOn_normH hFp).mono hsub))).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hi2 : IntervalIntegrable (fun τ => Cbil * (Real.exp (Eig.sigma χ G * (t - τ)) * η τ))
        volume 0 t := by
      have := (hηint t ht).continuousOn_mul (g := fun τ => Real.exp (Eig.sigma χ G * (t - τ)))
        (Continuous.continuousOn (by fun_prop))
      exact this.const_mul Cbil
    have hmono : ∫ τ in (0 : ℝ)..t, Real.exp (Eig.sigma χ G * (t - τ)) *
        normH (K - 1) (hg χ K G h 1 τ) ≤
        ∫ τ in (0 : ℝ)..t, Cbil * (Real.exp (Eig.sigma χ G * (t - τ)) * η τ) := by
      refine intervalIntegral.integral_mono_on ht.1 hi1 hi2 fun τ hτ => ?_
      have hτT := hsub hτ
      have e1 : normH (K - 1) (hg χ K G h 1 τ) ≤ Cbil * η τ :=
        (hFn τ hτT).trans (mul_le_mul hCnab (hnormh (K - 1) (by omega) τ hτT)
          (normCk_nonneg _ _ _) hCbil)
      calc Real.exp (Eig.sigma χ G * (t - τ)) * normH (K - 1) (hg χ K G h 1 τ)
          ≤ Real.exp (Eig.sigma χ G * (t - τ)) * (Cbil * η τ) :=
            mul_le_mul_of_nonneg_left e1 (Real.exp_pos _).le
        _ = Cbil * (Real.exp (Eig.sigma χ G * (t - τ)) * η τ) := by ring
    rw [intervalIntegral.integral_const_mul] at hmono
    have hmaj : ∫ τ in (0 : ℝ)..t, Real.exp (Eig.sigma χ G * (t - τ)) * η τ =
        maj (Eig.sigma χ G) η t := rfl
    rw [hmaj] at hmono
    calc CL * ∫ τ in (0 : ℝ)..t, Real.exp (Eig.sigma χ G * (t - τ)) *
          normH (K - 1) (hg χ K G h 1 τ)
        ≤ CL * (Cbil * maj (Eig.sigma χ G) η t) := mul_le_mul_of_nonneg_left hmono hCL
      _ = CL * Cbil * R ^ (1 - 1) * maj (Eig.sigma χ G) η t ^ 1 := by ring
  · -- `j ≥ 2`
    have hj2 : 2 ≤ j := hj
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    have hn : 1 ≤ n := by omega
    have IH : ∀ i, 1 ≤ i → i ≤ n → HierProp χ K G T h η (CL * Cbil) R i := fun i hi1 hi2 =>
      ih i (by omega) hi1 (by omega)
    have hkj : 2 ≤ K - (n + 1) := by omega
    -- the forcing `g^{[j]}` along paths
    have hgfun : hg χ K G h (n + 1) = fun τ =>
        (∑ p ∈ pairs (n + 1), Bfn (hw χ K G h p.1 τ) (hw χ K G h p.2 τ)) -
          hGrad (h τ) (hw χ K G h (n + 1 - 1) τ) := funext (hg_of_two_le χ K G h hj2)
    have hlev1 : ∀ p ∈ pairs (n + 1), PathC (K - (n + 1) + 1) T (hw χ K G h p.1) := by
      intro p hp
      obtain ⟨hp1, hp2, hp3⟩ := mem_pairs.1 hp
      exact PathC.mono_level (IH p.1 hp1 (by omega)).1 (by omega)
    have hlev2 : ∀ p ∈ pairs (n + 1), PathC (K - (n + 1) + 1) T (hw χ K G h p.2) := by
      intro p hp
      obtain ⟨hp1, hp2, hp3⟩ := mem_pairs.1 hp
      exact PathC.mono_level (IH p.2 hp2 (by omega)).1 (by omega)
    have hlev3 : PathC (K - (n + 1) + 1) T (hw χ K G h (n + 1 - 1)) := by
      have : n + 1 - 1 = n := rfl
      rw [this]
      exact PathC.mono_level (IH n hn le_rfl).1 (by omega)
    have hgp : PathC (K - (n + 1)) T (hg χ K G h (n + 1)) := by
      rw [hgfun]
      exact PathC.sub (PathC.sum (pairs (n + 1)) fun p hp =>
        pathC_Bfn hkj (hlev1 p hp) (hlev2 p hp))
        (pathC_hGrad hkj (hhk _ (by omega)) hsym hlev3)
    have hgR : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure ℂ),
        (hg χ K G h (n + 1) t x).im = 0 := by
      intro t ht
      rw [hgfun]
      refine isReal_sub (isReal_sum _ fun p hp => ?_) ?_
      · obtain ⟨hp1, hp2, hp3⟩ := mem_pairs.1 hp
        exact Bfn_isReal ((IH p.1 hp1 (by omega)).2.2.1 t ht)
          (((IH p.2 hp2 (by omega)).1.1 t ht).1.mono_order (by omega))
          ((IH p.2 hp2 (by omega)).2.2.1 t ht)
      · exact hGrad_isReal (h t) (((IH n hn le_rfl).1.1 t ht).1.mono_order (by omega))
          ((IH n hn le_rfl).2.2.1 t ht)
    obtain ⟨d1, d2, d3, d4⟩ := duh_part χ hχ hG hT (j := n + 1) (by omega) (by omega) hgp hgR
    refine ⟨d1, d2, d3, d4, fun t ht => ?_, hgp, hgR⟩
    -- `eq:Q-hier` for `j = n + 1`
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    obtain ⟨hCBb, hChb, -⟩ := hBb (K - (n + 1)) hkj (by omega)
    set m := maj (Eig.sigma χ G) η with hmdef
    set A := CL * Cbil with hA
    have hA0 : 0 ≤ A := mul_nonneg hCL hCbil
    -- pointwise bound on `‖g^{[j]}(τ)‖`
    have hgb : ∀ τ ∈ Icc (0 : ℝ) T, normH (K - (n + 1)) (hg χ K G h (n + 1) τ) ≤
        Cbil * ((n : ℝ) * n * A ^ 2 * R ^ (n - 1)) * m τ ^ (n + 1) +
          Cbil * (A * R ^ (n - 1)) * η τ * m τ ^ n := by
      intro τ hτ
      have hm := hm0 τ hτ
      rw [hgfun]
      have hBX : ∀ p ∈ pairs (n + 1),
          Lin.MemXFn (K - (n + 1)) (Bfn (hw χ K G h p.1 τ) (hw χ K G h p.2 τ)) := fun p hp =>
        (bilinear_B hkj ((hlev1 p hp).1 τ hτ) ((hlev2 p hp).1 τ hτ)).1
      have hHX := bilinear_h hkj (hlev3.1 τ hτ) ((hhk (K - (n + 1)) (by omega)).1 τ hτ)
      have hsum := memH_sum (pairs (n + 1)) fun p hp => (hBX p hp).1
      refine ((hsum.sub hHX.1).2).trans (add_le_add ?_ ?_)
      · refine (normH_sum_le _ fun p hp => (hBX p hp).1).trans ?_
        have hterm : ∀ p ∈ pairs (n + 1),
            normH (K - (n + 1)) (Bfn (hw χ K G h p.1 τ) (hw χ K G h p.2 τ)) ≤
              Cbil * (A ^ 2 * R ^ (n - 1)) * m τ ^ (n + 1) := by
          intro p hp
          obtain ⟨hp1, hp2, hp3⟩ := mem_pairs.1 hp
          have hB := (bilinear_B hkj ((hlev1 p hp).1 τ hτ) ((hlev2 p hp).1 τ hτ)).2
          have hw1 : normH (K - (n + 1)) (hw χ K G h p.1 τ) ≤ A * R ^ (p.1 - 1) * m τ ^ p.1 :=
            (((IH p.1 hp1 (by omega)).1.1 τ hτ).1.normH_mono (by omega)).trans
              ((IH p.1 hp1 (by omega)).2.2.2.2.1 τ hτ)
          have hw2 : normH (K - (n + 1) + 1) (hw χ K G h p.2 τ) ≤
              A * R ^ (p.2 - 1) * m τ ^ p.2 :=
            (((IH p.2 hp2 (by omega)).1.1 τ hτ).1.normH_mono (by omega)).trans
              ((IH p.2 hp2 (by omega)).2.2.2.2.1 τ hτ)
          have hpow : R ^ (p.1 - 1) * R ^ (p.2 - 1) = R ^ (n - 1) := by
            rw [← pow_add]
            congr 1
            omega
          have hpowm : m τ ^ p.1 * m τ ^ p.2 = m τ ^ (n + 1) := by
            rw [← pow_add, hp3]
          calc normH (K - (n + 1)) (Bfn (hw χ K G h p.1 τ) (hw χ K G h p.2 τ))
              ≤ CB (K - (n + 1)) * normH (K - (n + 1)) (hw χ K G h p.1 τ) *
                  normH (K - (n + 1) + 1) (hw χ K G h p.2 τ) := hB
            _ ≤ Cbil * (A * R ^ (p.1 - 1) * m τ ^ p.1) * (A * R ^ (p.2 - 1) * m τ ^ p.2) :=
                mul_le_mul (mul_le_mul hCBb hw1 (normH_nonneg _ _) hCbil) hw2 (normH_nonneg _ _)
                  (mul_nonneg hCbil (le_trans (normH_nonneg _ _) hw1))
            _ = Cbil * (A ^ 2 * (R ^ (p.1 - 1) * R ^ (p.2 - 1))) * (m τ ^ p.1 * m τ ^ p.2) := by
                ring
            _ = Cbil * (A ^ 2 * R ^ (n - 1)) * m τ ^ (n + 1) := by rw [hpow, hpowm]
        refine (Finset.sum_le_sum hterm).trans ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((pairs (n + 1)).card : ℝ) ≤ (n : ℝ) * n := by
          have := card_pairs_le (n + 1)
          simp only [Nat.add_sub_cancel] at this
          exact_mod_cast this
        have hnn : 0 ≤ Cbil * (A ^ 2 * R ^ (n - 1)) * m τ ^ (n + 1) :=
          mul_nonneg (mul_nonneg hCbil (mul_nonneg (sq_nonneg _) (pow_nonneg hR0 _)))
            (pow_nonneg hm _)
        calc ((pairs (n + 1)).card : ℝ) * (Cbil * (A ^ 2 * R ^ (n - 1)) * m τ ^ (n + 1))
            ≤ (n : ℝ) * n * (Cbil * (A ^ 2 * R ^ (n - 1)) * m τ ^ (n + 1)) :=
              mul_le_mul_of_nonneg_right hcard hnn
          _ = Cbil * ((n : ℝ) * n * A ^ 2 * R ^ (n - 1)) * m τ ^ (n + 1) := by ring
      · have hwn : normH (K - (n + 1) + 1) (hw χ K G h (n + 1 - 1) τ) ≤
            A * R ^ (n - 1) * m τ ^ n := by
          have : n + 1 - 1 = n := rfl
          rw [this]
          have e : K - (n + 1) + 1 = K - n := by omega
          rw [e]
          exact (IH n hn le_rfl).2.2.2.2.1 τ hτ
        have hhn := hnormh (K - (n + 1)) (by omega) τ hτ
        calc normH (K - (n + 1)) (hGrad (h τ) (hw χ K G h (n + 1 - 1) τ))
            ≤ Ch (K - (n + 1)) * normCk (K - (n + 1)) annN' (h τ) *
                normH (K - (n + 1) + 1) (hw χ K G h (n + 1 - 1) τ) := hHX.2.2.1
          _ ≤ Cbil * η τ * (A * R ^ (n - 1) * m τ ^ n) :=
              mul_le_mul (mul_le_mul hChb hhn (normCk_nonneg _ _ _) hCbil) hwn (normH_nonneg _ _)
                (mul_nonneg hCbil (hη0 τ hτ))
          _ = Cbil * (A * R ^ (n - 1)) * η τ * m τ ^ n := by ring
    -- the Duhamel bound and the integration
    rw [hw_eq χ K G h (by omega)]
    have hb := duhFn_bound χ hgp (hSb (K - (n + 1)) (by omega) G hG) ht
    refine hb.trans ?_
    set P := Cbil * ((n : ℝ) * n * A ^ 2 * R ^ (n - 1)) with hP
    set Q := Cbil * (A * R ^ (n - 1)) with hQdef
    have hP0 : 0 ≤ P := by positivity
    have hQ0 : 0 ≤ Q := by positivity
    have hi1 : IntervalIntegrable (fun τ => Real.exp (Eig.sigma χ G * (t - τ)) *
        normH (K - (n + 1)) (hg χ K G h (n + 1) τ)) volume 0 t :=
      (((Continuous.continuousOn (by fun_prop)).mul
        ((PathC.continuousOn_normH hgp).mono hsub))).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hi2 : IntervalIntegrable (fun τ => P * Real.exp (-(n * Eig.sigma χ G) * (t - τ)) *
        m t ^ (n + 1) + Q * η τ * m t ^ n) volume 0 t := by
      have hc : IntervalIntegrable (fun τ => P * Real.exp (-(n * Eig.sigma χ G) * (t - τ)) *
          m t ^ (n + 1)) volume 0 t := (by fun_prop : Continuous fun τ =>
            P * Real.exp (-(n * Eig.sigma χ G) * (t - τ)) * m t ^ (n + 1)).intervalIntegrable _ _
      have hd : IntervalIntegrable (fun τ => Q * η τ * m t ^ n) volume 0 t := by
        have := ((hηint t ht).const_mul Q).mul_const (m t ^ n)
        simpa [mul_assoc] using this
      exact hc.add hd
    have hmono : ∫ τ in (0 : ℝ)..t, Real.exp (Eig.sigma χ G * (t - τ)) *
        normH (K - (n + 1)) (hg χ K G h (n + 1) τ) ≤
        ∫ τ in (0 : ℝ)..t, (P * Real.exp (-(n * Eig.sigma χ G) * (t - τ)) * m t ^ (n + 1) +
          Q * η τ * m t ^ n) := by
      refine intervalIntegral.integral_mono_on ht.1 hi1 hi2 fun τ hτ => ?_
      have hτT := hsub hτ
      have hM1 := (hM τ t hτ.1 hτ.2 ht.2).1
      calc Real.exp (Eig.sigma χ G * (t - τ)) * normH (K - (n + 1)) (hg χ K G h (n + 1) τ)
          ≤ Real.exp (Eig.sigma χ G * (t - τ)) * (P * m τ ^ (n + 1) + Q * η τ * m τ ^ n) :=
            mul_le_mul_of_nonneg_left (hgb τ hτT) (Real.exp_pos _).le
        _ ≤ P * Real.exp (-(n * Eig.sigma χ G) * (t - τ)) * m t ^ (n + 1) +
              Q * η τ * m t ^ n :=
            hier_pointwise hn hτ.2 hσ.le (hm0 τ hτT) hM1 hP0 hQ0 (hη0 τ hτT)
    have hM2 : ∫ τ in (0 : ℝ)..t, η τ ≤ m t := (hM 0 t le_rfl ht.1 ht.2).2.1
    have hint := hier_integral hn hσ (hm0 t ht) hP0 hQ0 (hηint t ht) hM2
    have hfin := const_step (n := n) (NQ := NQ) hCL hCbil hR hR0 hσb hσbσ hn (by omega)
    calc CL * ∫ τ in (0 : ℝ)..t, Real.exp (Eig.sigma χ G * (t - τ)) *
          normH (K - (n + 1)) (hg χ K G h (n + 1) τ)
        ≤ CL * ((P / (n * Eig.sigma χ G) + Q) * m t ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left (hmono.trans hint) hCL
      _ = CL * (P / (n * Eig.sigma χ G) + Q) * m t ^ (n + 1) := by ring
      _ ≤ CL * Cbil * R ^ n * m t ^ (n + 1) :=
          mul_le_mul_of_nonneg_right hfin (pow_nonneg (hm0 t ht) _)
      _ = A * R ^ (n + 1 - 1) * m t ^ (n + 1) := by rw [Nat.add_sub_cancel]

end NonUniqueEuler.OneRing.QAppH
