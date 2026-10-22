import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec4.PropSemigroup
import NonUniqueEuler.H.Sec5.Quiet.Approx.Residual

/-!
# Proof: the approximate solution of `thm:quiet` (`eq:Q-hier`, `eq:Q-res`)

Proof of `I/Sec5/Quiet/Approx.lean` (`05_single_ring.tex:440-513`). Helpers:
`H/Sec5/Quiet/Approx/*.lean` (namespace `NonUniqueEuler.OneRing.QAppH`).

1. Constants (`:440-461`): `σ'_0 = (9/200 + σ_b)/2`, `C_L = Σ_{k ≤ M_h} C_S(k,σ'_0)` (`prop:semigroup`,
   `QAppH.exists_CL`), `C_bil = Σ_{2 ≤ k ≤ M_h} (C_B(k) + C_h(k) + C_∇(k))` (`lem:bilinear`,
   `QAppH.exists_Cbil`), `A = C_L C_bil`, `R = A(N_Q A/σ_b + 1) + 1`, `C^{(j)} = A R^{j-1}`
   (deviation: a closed form satisfying the recursion inequality of the manuscript instead of the
   exact recursion; sums instead of maxima),
   `C_app = Σ_j C^{(j)} + C_bil(Σ_{i,l ≤ N_Q} C^{(i)}C^{(l)} + C^{(N_Q)})`.
2. The hierarchy `w^{[j]}` with regularity, equations and `eq:Q-hier`: `QAppH.hier_props`.
3. `w_app = Σ_{j ≤ N_Q} w^{[j]}`, `w_app' = L(G)w_app + Σ_j g^{[j]}` (a.e. equal to
   `Σ_j ∂_t w^{[j]}`, `QAppH.Lfn_sum_ae`): `QAppH.approx_paths`. The bounds: `QAppH.bound_wapp`,
   `QAppH.bound_diff` (`w^{[1]} = wlin` at level `s_h`, `QAppH.duhFn_level`) and `QAppH.bound_res`
   (the residual identity `QAppH.rapp_ae`, then `eq:Q-res`, `QAppH.res_bound`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

namespace QAppH

open Sect Sob

theorem Cnab_nonneg (χ : ℝ → ℝ) (k : ℕ) : 0 ≤ Eig.Cnab χ k := by
  unfold Eig.Cnab
  have := Sob.normH_nonneg (k + 1) fun y => ((ringPhi χ y : ℝ) : ℂ)
  positivity

theorem Ch_nonneg {k : ℕ} (hk : 2 ≤ k) : 0 ≤ Ch k := (bilinear_Ch hk).2

/-! ### The constants -/

/-- The semigroup constant `C_L = Σ_{k ≤ K} C_S(k, σ'_0)` (`prop:semigroup`, `σ'_0 = (9/200+σ_b)/2`). -/
theorem exists_CL (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    (K : ℕ) :
    ∃ CL : ℝ, 0 ≤ CL ∧ ∀ k ≤ K, ∀ G ∈ Icc (0 : ℝ) Gbar, ∀ t : ℝ, 0 ≤ t → ∀ w : Y k annN,
      Lin.MemX w → ‖Lin.S χ k G t w‖ ≤ CL * Real.exp (Eig.sigma χ G * t) * ‖w‖ := by
  have hσb : 211 / 2500 < Eig.sigb χ := (Eig.propU_a χ hχ hN).2.2.2.1
  have hσ0 : (9 / 200 + Eig.sigb χ) / 2 ∈ Ioo (9 / 200 : ℝ) (Eig.sigb χ) := by
    constructor <;> linarith
  choose CS hCSpos hCS using fun k : ℕ => Eig.propSemigroup_bounds χ hχ hN k hσ0
  refine ⟨∑ k ∈ Finset.range (K + 1), CS k, Finset.sum_nonneg fun k _ => (hCSpos k).le, ?_⟩
  intro k hk G hG t ht w hw
  have hle : CS k ≤ ∑ k ∈ Finset.range (K + 1), CS k :=
    Finset.single_le_sum (f := CS) (fun i _ => (hCSpos i).le) (Finset.mem_range.2 (by omega))
  refine ((hCS k G hG t ht).2.2 w hw).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le) (norm_nonneg _)

/-- The bilinear constant `C_bil = Σ_{2 ≤ k ≤ K} (C_B(k) + C_h(k) + C_∇(k))` (`lem:bilinear`). -/
theorem exists_Cbil (χ : ℝ → ℝ) (K : ℕ) :
    ∃ Cbil : ℝ, 0 ≤ Cbil ∧
      ∀ k, 2 ≤ k → k ≤ K → CB k ≤ Cbil ∧ Ch k ≤ Cbil ∧ Eig.Cnab χ k ≤ Cbil := by
  have hterm : ∀ k ∈ Finset.Icc 2 K, 0 ≤ CB k + Ch k + Eig.Cnab χ k := fun k hk => by
    have hk2 : 2 ≤ k := (Finset.mem_Icc.1 hk).1
    have h1 := (CB_pos k).le
    have h2 := Ch_nonneg hk2
    have h3 := Cnab_nonneg χ k
    linarith
  refine ⟨∑ k ∈ Finset.Icc 2 K, (CB k + Ch k + Eig.Cnab χ k), Finset.sum_nonneg hterm, ?_⟩
  intro k hk2 hkK
  have hle : CB k + Ch k + Eig.Cnab χ k ≤ ∑ k ∈ Finset.Icc 2 K, (CB k + Ch k + Eig.Cnab χ k) :=
    Finset.single_le_sum hterm (Finset.mem_Icc.2 ⟨hk2, hkK⟩)
  have h1 := (CB_pos k).le
  have h2 := Ch_nonneg hk2
  have h3 := Cnab_nonneg χ k
  exact ⟨by linarith, by linarith, by linarith⟩

/-! ### Abstract bounds at a fixed time -/

/-- `‖Σ_{j ≤ N_Q} W_j‖ ≤ (Σ_j c_j) m` from `‖W_j‖ ≤ c_j m^j`, `0 ≤ m ≤ 1`. -/
theorem wapp_bound {k NQ : ℕ} {W : ℕ → ℂ → ℂ} {c : ℕ → ℝ} {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hc : ∀ j, 0 ≤ c j) (hX : ∀ j ∈ Finset.Icc 1 NQ, MemH k (W j))
    (hb : ∀ j ∈ Finset.Icc 1 NQ, normH k (W j) ≤ c j * m ^ j) :
    normH k (∑ j ∈ Finset.Icc 1 NQ, W j) ≤ (∑ j ∈ Finset.Icc 1 NQ, c j) * m := by
  refine (normH_sum_le _ hX).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => (hb j hj).trans ?_
  have hj1 := (Finset.mem_Icc.1 hj).1
  have hpow : m ^ j ≤ m ^ 1 := pow_le_pow_of_le_one hm0 hm1 hj1
  rw [pow_one] at hpow
  exact mul_le_mul_of_nonneg_left hpow (hc j)

/-- `‖Σ_{2 ≤ j ≤ N_Q} W_j‖ ≤ (Σ_j c_j) m²` from `‖W_j‖ ≤ c_j m^j`, `0 ≤ m ≤ 1`. -/
theorem wdiff_bound {k NQ : ℕ} {W : ℕ → ℂ → ℂ} {c : ℕ → ℝ} {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hc : ∀ j, 0 ≤ c j) (hX : ∀ j ∈ Finset.Icc 1 NQ, MemH k (W j))
    (hb : ∀ j ∈ Finset.Icc 1 NQ, normH k (W j) ≤ c j * m ^ j) :
    normH k (∑ j ∈ Finset.Ioc 1 NQ, W j) ≤ (∑ j ∈ Finset.Icc 1 NQ, c j) * m ^ 2 := by
  have hIoc : ∀ j ∈ Finset.Ioc 1 NQ, j ∈ Finset.Icc 1 NQ := fun j hj => by
    rw [Finset.mem_Ioc] at hj
    exact Finset.mem_Icc.2 ⟨by omega, hj.2⟩
  refine (normH_sum_le _ fun j hj => hX j (hIoc j hj)).trans ?_
  have hsub : ∑ j ∈ Finset.Ioc 1 NQ, c j ≤ ∑ j ∈ Finset.Icc 1 NQ, c j :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => hIoc j hj) (fun j _ _ => hc j)
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hsub (sq_nonneg m))
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => (hb j (hIoc j hj)).trans ?_
  have hj2 : 2 ≤ j := by
    rw [Finset.mem_Ioc] at hj
    omega
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hm0 hm1 hj2) (hc j)

/-- `eq:Q-res` at a fixed time, for `-Σ_{i,l ≤ N_Q, i+l > N_Q} B(W_i,W_l) + h·∇W_{N_Q}`
(`05_single_ring.tex:506-511`). -/
theorem res_bound {sh NQ : ℕ} (hs : 2 ≤ sh) (hQ : 1 ≤ NQ) {W : ℕ → ℂ → ℂ} {c : ℕ → ℝ}
    {hf : ℂ → ℂ} {m e Cbil : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (he : 0 ≤ e) (hCbil : 0 ≤ Cbil)
    (hc : ∀ j, 0 ≤ c j) (hCB : CB sh ≤ Cbil) (hCh : Ch sh ≤ Cbil)
    (hX : ∀ j ∈ Finset.Icc 1 NQ, Lin.MemXFn (sh + 1) (W j))
    (hb : ∀ j ∈ Finset.Icc 1 NQ, normH (sh + 1) (W j) ≤ c j * m ^ j)
    (hhf : MemCk sh annN' hf) (hhe : normCk sh annN' hf ≤ e) :
    MemH sh (-(∑ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)).filter
          (fun p : ℕ × ℕ => ¬ p.1 + p.2 ≤ NQ), Bfn (W p.1) (W p.2)) + hGrad hf (W NQ)) ∧
    normH sh (-(∑ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)).filter
          (fun p : ℕ × ℕ => ¬ p.1 + p.2 ≤ NQ), Bfn (W p.1) (W p.2)) + hGrad hf (W NQ)) ≤
      Cbil * (∑ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)), c p.1 * c p.2) *
          m ^ (NQ + 1) + Cbil * c NQ * (e * m ^ NQ) := by
  have hS'S : ∀ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)).filter
      (fun p : ℕ × ℕ => ¬ p.1 + p.2 ≤ NQ),
      p.1 ∈ Finset.Icc 1 NQ ∧ p.2 ∈ Finset.Icc 1 NQ ∧ NQ + 1 ≤ p.1 + p.2 := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact ⟨hp.1.1, hp.1.2, by omega⟩
  have hBX : ∀ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)).filter
      (fun p : ℕ × ℕ => ¬ p.1 + p.2 ≤ NQ), Lin.MemXFn sh (Bfn (W p.1) (W p.2)) := fun p hp =>
    (bilinear_B hs (hX p.1 (hS'S p hp).1) (hX p.2 (hS'S p hp).2.1)).1
  have hBsum : MemH sh (∑ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)).filter
      (fun p : ℕ × ℕ => ¬ p.1 + p.2 ≤ NQ), Bfn (W p.1) (W p.2)) :=
    memH_sum _ fun p hp => (hBX p hp).1
  have hNQmem : NQ ∈ Finset.Icc 1 NQ := Finset.mem_Icc.2 ⟨hQ, le_rfl⟩
  have hHX := bilinear_h hs (hX NQ hNQmem) hhf
  have hneg : MemH sh (-(∑ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)).filter
      (fun p : ℕ × ℕ => ¬ p.1 + p.2 ≤ NQ), Bfn (W p.1) (W p.2))) := by
    have he1 : (-1 : ℂ) • (∑ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)).filter
        (fun p : ℕ × ℕ => ¬ p.1 + p.2 ≤ NQ), Bfn (W p.1) (W p.2)) =
        -(∑ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)).filter
          (fun p : ℕ × ℕ => ¬ p.1 + p.2 ≤ NQ), Bfn (W p.1) (W p.2)) := neg_one_smul ℂ _
    rw [← he1]
    exact (hBsum.const_smul (-1)).1
  refine ⟨(hneg.add hHX.1).1, ((hneg.add hHX.1).2).trans ?_⟩
  rw [normH_neg hBsum]
  -- the bilinear terms
  have hB1 : normH sh (∑ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)).filter
      (fun p : ℕ × ℕ => ¬ p.1 + p.2 ≤ NQ), Bfn (W p.1) (W p.2)) ≤
      Cbil * (∑ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)), c p.1 * c p.2) *
        m ^ (NQ + 1) := by
    refine (normH_sum_le _ fun p hp => (hBX p hp).1).trans ?_
    have hterm : ∀ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)).filter
        (fun p : ℕ × ℕ => ¬ p.1 + p.2 ≤ NQ), normH sh (Bfn (W p.1) (W p.2)) ≤
        Cbil * (c p.1 * c p.2) * m ^ (NQ + 1) := by
      intro p hp
      obtain ⟨hp1, hp2, hp3⟩ := hS'S p hp
      have hB := (bilinear_B hs (hX p.1 hp1) (hX p.2 hp2)).2
      have hw1 : normH sh (W p.1) ≤ c p.1 * m ^ p.1 :=
        ((hX p.1 hp1).1.normH_mono (Nat.le_succ sh)).trans (hb p.1 hp1)
      have hw2 := hb p.2 hp2
      have hpow : m ^ p.1 * m ^ p.2 ≤ m ^ (NQ + 1) := by
        rw [← pow_add]
        exact pow_le_pow_of_le_one hm0 hm1 hp3
      calc normH sh (Bfn (W p.1) (W p.2))
          ≤ CB sh * normH sh (W p.1) * normH (sh + 1) (W p.2) := hB
        _ ≤ Cbil * (c p.1 * m ^ p.1) * (c p.2 * m ^ p.2) :=
            mul_le_mul (mul_le_mul hCB hw1 (normH_nonneg _ _) hCbil) hw2
              (normH_nonneg _ _) (mul_nonneg hCbil ((normH_nonneg _ _).trans hw1))
        _ = Cbil * (c p.1 * c p.2) * (m ^ p.1 * m ^ p.2) := by ring
        _ ≤ Cbil * (c p.1 * c p.2) * m ^ (NQ + 1) :=
            mul_le_mul_of_nonneg_left hpow (mul_nonneg hCbil (mul_nonneg (hc _) (hc _)))
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hsub : ∑ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)).filter
        (fun p : ℕ × ℕ => ¬ p.1 + p.2 ≤ NQ), c p.1 * c p.2 ≤
        ∑ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)), c p.1 * c p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p _ _ => mul_nonneg (hc _) (hc _))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsub hCbil) (pow_nonneg hm0 _)
  -- the transport term
  have hB2 : normH sh (hGrad hf (W NQ)) ≤ Cbil * c NQ * (e * m ^ NQ) := by
    calc normH sh (hGrad hf (W NQ))
        ≤ Ch sh * normCk sh annN' hf * normH (sh + 1) (W NQ) := hHX.2.2.1
      _ ≤ Cbil * e * (c NQ * m ^ NQ) :=
          mul_le_mul (mul_le_mul hCh hhe (normCk_nonneg _ _ _) hCbil) (hb NQ hNQmem)
            (normH_nonneg _ _) (mul_nonneg hCbil he)
      _ = Cbil * c NQ * (e * m ^ NQ) := by ring
  exact add_le_add hB1 hB2

/-! ### The hierarchy at a fixed time -/

/-- `w^{[j]}(t) ∈ X^{s_h+1}` with `‖w^{[j]}(t)‖_{H^{s_h+1}} ≤ A R^{j-1} maj(t)^j` (`eq:Q-hier`,
`k_j = M_h - j ≥ s_h + 1`). -/
theorem hier_at {χ : ℝ → ℝ} {sh NQ : ℕ} {G T : ℝ} {h : ℝ → ℂ → ℂ} {η : ℝ → ℝ} {A R : ℝ}
    (hP : ∀ j ∈ Finset.Icc 1 NQ, HierProp χ (Mh sh NQ) G T h η A R j)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∀ j ∈ Finset.Icc 1 NQ, Lin.MemXFn (sh + 1) (hw χ (Mh sh NQ) G h j t) ∧
      normH (sh + 1) (hw χ (Mh sh NQ) G h j t) ≤
        A * R ^ (j - 1) * maj (Eig.sigma χ G) η t ^ j := by
  intro j hj
  have hjQ := (Finset.mem_Icc.1 hj).2
  have hKv : Mh sh NQ = sh + NQ + 1 := rfl
  have hle : sh + 1 ≤ Mh sh NQ - j := by omega
  exact ⟨MemXFn.mono ((hP j hj).1.1 t ht) hle,
    (((hP j hj).1.1 t ht).1.normH_mono hle).trans ((hP j hj).2.2.2.2.1 t ht)⟩

/-- Regularity, realness and initial value of `w_app = Σ_{j ≤ N_Q} w^{[j]}`, with
`w_app' = L(G)w_app + Σ_j g^{[j]}` (`05_single_ring.tex:494-497`). -/
theorem approx_paths (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {sh NQ : ℕ} {G T : ℝ}
    {h : ℝ → ℂ → ℂ} {η : ℝ → ℝ} {A R : ℝ}
    (hP : ∀ j ∈ Finset.Icc 1 NQ, HierProp χ (Mh sh NQ) G T h η A R j) :
    PathC (sh + 1) T (fun t => ∑ j ∈ Finset.Icc 1 NQ, hw χ (Mh sh NQ) G h j t) ∧
      PathC1 sh T (fun t => ∑ j ∈ Finset.Icc 1 NQ, hw χ (Mh sh NQ) G h j t)
        (fun t => Lin.Lfn χ G (∑ j ∈ Finset.Icc 1 NQ, hw χ (Mh sh NQ) G h j t) +
          ∑ j ∈ Finset.Icc 1 NQ, hg χ (Mh sh NQ) G h j t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure ℂ),
        ((∑ j ∈ Finset.Icc 1 NQ, hw χ (Mh sh NQ) G h j t) x).im = 0) ∧
      (∑ j ∈ Finset.Icc 1 NQ, hw χ (Mh sh NQ) G h j 0) =ᵐ[volume] (0 : ℂ → ℂ) := by
  have hKv : Mh sh NQ = sh + NQ + 1 := rfl
  refine ⟨PathC.sum (Finset.Icc 1 NQ) fun j hj => PathC.mono_level (hP j hj).1
      (by have := (Finset.mem_Icc.1 hj).2; omega), ?_, ?_, ?_⟩
  · have h1 := PathC1.sum (Finset.Icc 1 NQ) fun j hj => PathC1.mono_level (hP j hj).2.1
      (show sh ≤ Mh sh NQ - j - 1 by have := (Finset.mem_Icc.1 hj).2; omega)
    refine PathC1.congr_ae h1 (fun t _ => EventuallyEq.rfl) fun t ht => ?_
    have hL := Lfn_sum_ae χ hχ (k := sh) G (Finset.Icc 1 NQ)
      (f := fun j => hw χ (Mh sh NQ) G h j t) fun j hj => (hier_at hP ht j hj).1
    filter_upwards [hL] with x hx
    simp only [Pi.add_apply, Finset.sum_apply]
    rw [hx, Finset.sum_add_distrib]
  · intro t ht
    exact isReal_sum _ fun j hj => (hP j hj).2.2.1 t ht
  · have hall : ∀ᵐ x ∂(volume : Measure ℂ), ∀ j ∈ Finset.Icc 1 NQ,
        hw χ (Mh sh NQ) G h j 0 x = 0 :=
      (Filter.eventually_all_finset _).2 fun j hj => (hP j hj).2.2.2.1
    filter_upwards [hall] with x hx
    simp only [Finset.sum_apply, Pi.zero_apply]
    exact Finset.sum_eq_zero hx

/-- `‖w_app(t)‖_{H^{s_h+1}} ≤ (Σ_j C^{(j)}) maj(t)` (`05_single_ring.tex:512-513`). -/
theorem bound_wapp {χ : ℝ → ℝ} {sh NQ : ℕ} {G T : ℝ} {h : ℝ → ℂ → ℂ} {η : ℝ → ℝ} {A R : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hP : ∀ j ∈ Finset.Icc 1 NQ, HierProp χ (Mh sh NQ) G T h η A R j)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (hm0 : 0 ≤ maj (Eig.sigma χ G) η t)
    (hm1 : maj (Eig.sigma χ G) η t ≤ 1) :
    normH (sh + 1) (∑ j ∈ Finset.Icc 1 NQ, hw χ (Mh sh NQ) G h j t) ≤
      (∑ j ∈ Finset.Icc 1 NQ, A * R ^ (j - 1)) * maj (Eig.sigma χ G) η t :=
  wapp_bound (W := fun j => hw χ (Mh sh NQ) G h j t) (c := fun j => A * R ^ (j - 1)) hm0 hm1
    (fun _ => mul_nonneg hA (pow_nonneg hR _)) (fun j hj => (hier_at hP ht j hj).1.1)
    (fun j hj => (hier_at hP ht j hj).2)

/-- `‖w_app(t) - wlin(t)‖_{H^{s_h}} ≤ (Σ_j C^{(j)}) maj(t)²`: `w^{[1]} = wlin` (at level `s_h`)
and `eq:Q-hier` for `j ≥ 2`. -/
theorem bound_diff (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {sh NQ : ℕ} (hQ : 2 ≤ NQ)
    {G T : ℝ} {h : ℝ → ℂ → ℂ} {η : ℝ → ℝ} {A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hP : ∀ j ∈ Finset.Icc 1 NQ, HierProp χ (Mh sh NQ) G T h η A R j)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (hm0 : 0 ≤ maj (Eig.sigma χ G) η t)
    (hm1 : maj (Eig.sigma χ G) η t ≤ 1) :
    normH sh ((∑ j ∈ Finset.Icc 1 NQ, hw χ (Mh sh NQ) G h j t) - (wlin χ sh G h t).fn) ≤
      (∑ j ∈ Finset.Icc 1 NQ, A * R ^ (j - 1)) * maj (Eig.sigma χ G) η t ^ 2 := by
  have hKv : Mh sh NQ = sh + NQ + 1 := rfl
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 NQ := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hFp : PathC (Mh sh NQ - 1) T (forcing χ h) := by
    have := (hP 1 h1).2.2.2.2.2.1
    rwa [hg_one] at this
  have hlin : (wlin χ sh G h t).fn =ᵐ[volume] hw χ (Mh sh NQ) G h 1 t := by
    rw [wlin_fn, hw_eq χ (Mh sh NQ) G h le_rfl, hg_one]
    exact (duhFn_level χ hχ (show sh ≤ Mh sh NQ - 1 by omega) G hFp ht).symm
  have hsplit : ∑ j ∈ Finset.Icc 1 NQ, hw χ (Mh sh NQ) G h j t =
      hw χ (Mh sh NQ) G h 1 t + ∑ j ∈ Finset.Ioc 1 NQ, hw χ (Mh sh NQ) G h j t :=
    (Finset.add_sum_Ioc_eq_sum_Icc (f := fun j => hw χ (Mh sh NQ) G h j t)
      (by omega : 1 ≤ NQ)).symm
  have hdiff : (∑ j ∈ Finset.Icc 1 NQ, hw χ (Mh sh NQ) G h j t) - (wlin χ sh G h t).fn =ᵐ[volume]
      ∑ j ∈ Finset.Ioc 1 NQ, hw χ (Mh sh NQ) G h j t := by
    filter_upwards [hlin] with x hx
    rw [Pi.sub_apply, hx, hsplit, Pi.add_apply, add_sub_cancel_left]
  have hIoc : ∀ j ∈ Finset.Ioc 1 NQ, j ∈ Finset.Icc 1 NQ := fun j hj => by
    rw [Finset.mem_Ioc] at hj
    exact Finset.mem_Icc.2 ⟨by omega, hj.2⟩
  have hmemS : MemH sh (∑ j ∈ Finset.Ioc 1 NQ, hw χ (Mh sh NQ) G h j t) :=
    memH_sum _ fun j hj => (hier_at hP ht j (hIoc j hj)).1.1.mono_order (Nat.le_succ sh)
  rw [(hmemS.congr_ae hdiff.symm).2]
  exact wdiff_bound (W := fun j => hw χ (Mh sh NQ) G h j t) (c := fun j => A * R ^ (j - 1))
    hm0 hm1 (fun j => mul_nonneg hA (pow_nonneg hR _))
    (fun j hj => (hier_at hP ht j hj).1.1.mono_order (Nat.le_succ sh))
    (fun j hj => (((hier_at hP ht j hj).1.1.normH_mono (Nat.le_succ sh))).trans
      (hier_at hP ht j hj).2)

/-- `eq:Q-res` for `w_app` (`05_single_ring.tex:494-511`). -/
theorem bound_res (χ : ℝ → ℝ) {sh NQ : ℕ} (hs : 3 ≤ sh) (hQ : 2 ≤ NQ)
    {G T : ℝ} {h : ℝ → ℂ → ℂ} {η : ℝ → ℝ} {A R Cbil : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hCbil : 0 ≤ Cbil) (hCB : CB sh ≤ Cbil) (hCh : Ch sh ≤ Cbil)
    (hh : CkPathOn (Mh sh NQ) annN' (Icc 0 T) h)
    (hη : ∀ t ∈ Icc (0 : ℝ) T, normCk (Mh sh NQ) annN' (h t) ≤ η t ∧ η t ≤ 1)
    (hP : ∀ j ∈ Finset.Icc 1 NQ, HierProp χ (Mh sh NQ) G T h η A R j)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (hm0 : 0 ≤ maj (Eig.sigma χ G) η t)
    (hm1 : maj (Eig.sigma χ G) η t ≤ 1) :
    normH sh (Rapp χ G h (fun t => ∑ j ∈ Finset.Icc 1 NQ, hw χ (Mh sh NQ) G h j t)
        (fun t => Lin.Lfn χ G (∑ j ∈ Finset.Icc 1 NQ, hw χ (Mh sh NQ) G h j t) +
          ∑ j ∈ Finset.Icc 1 NQ, hg χ (Mh sh NQ) G h j t) t) ≤
      Cbil * (∑ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)),
          A * R ^ (p.1 - 1) * (A * R ^ (p.2 - 1))) * maj (Eig.sigma χ G) η t ^ (NQ + 1) +
        Cbil * (A * R ^ (NQ - 1)) * (η t * maj (Eig.sigma χ G) η t ^ NQ) := by
  have hKv : Mh sh NQ = sh + NQ + 1 := rfl
  have hR' := rapp_ae χ (Mh sh NQ) G h hQ t fun j hj =>
    MemXFn.mono (hier_at hP ht j hj).1 (by omega)
  have hη0 : 0 ≤ η t := (normCk_nonneg _ _ _).trans (hη t ht).1
  have hhe : normCk sh annN' (h t) ≤ η t :=
    (normCk_mono_order (hh.1 t ht) (show sh ≤ Mh sh NQ by omega)).trans (hη t ht).1
  obtain ⟨hmem, hbd⟩ := res_bound (W := fun j => hw χ (Mh sh NQ) G h j t)
    (c := fun j => A * R ^ (j - 1)) (by omega : 2 ≤ sh) (by omega : 1 ≤ NQ) hm0 hm1 hη0 hCbil
    (fun j => mul_nonneg hA (pow_nonneg hR _)) hCB hCh (fun j hj => (hier_at hP ht j hj).1)
    (fun j hj => (hier_at hP ht j hj).2)
    ((CkPathOn.mono_order hh (show sh ≤ Mh sh NQ by omega)).1 t ht) hhe
  rw [(hmem.congr_ae hR'.symm).2]
  exact hbd

end QAppH

/-- **The approximate solution of `thm:quiet`** (`05_single_ring.tex:440-513`, `eq:Q-hier`,
`eq:Q-res`). Assume (N1)–(N3), `s_h ≥ 3`, `N_Q ≥ 2`. There is `C_app ≥ 0` (depending only on
`Φ, G₁, s_h, N_Q`) such that for `G ∈ [0,G₁]`, `T > 0`, every field path `h` with
`h ∈ C([0,T];C^{M_h}(N'))`, `h(t)` `3`-fold symmetric on `N'`, and every measurable `η` with
`‖h(t)‖_{C^{M_h}(N')} ≤ η(t) ≤ 1` and `maj(t) ≤ 1` on `[0,T]`, there is a real
`w_app ∈ C([0,T];X^{s_h+1}) ∩ C¹([0,T];X^{s_h})` (derivative `w_app'`) with `w_app(0) = 0` and, on
`[0,T]`, `‖w_app‖_{H^{s_h+1}} ≤ C_app maj`, `‖w_app - wlin‖_{H^{s_h}} ≤ C_app maj²` and
`‖R_app‖_{H^{s_h}} ≤ C_app (maj^{N_Q+1} + η maj^{N_Q})`. -/
theorem quiet_approx (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {sh NQ : ℕ} (hs : 3 ≤ sh) (hQ : 2 ≤ NQ) :
    ∃ Capp : ℝ, 0 ≤ Capp ∧
      ∀ (G T : ℝ) (h : ℝ → ℂ → ℂ) (η : ℝ → ℝ), G ∈ Icc (0 : ℝ) Gbar → 0 < T →
        CkPathOn (Mh sh NQ) annN' (Icc 0 T) h →
        (∀ t ∈ Icc (0 : ℝ) T, IsSymFieldOn annN' (h t)) →
        Measurable η →
        (∀ t ∈ Icc (0 : ℝ) T, normCk (Mh sh NQ) annN' (h t) ≤ η t ∧ η t ≤ 1) →
        (∀ t ∈ Icc (0 : ℝ) T, maj (Eig.sigma χ G) η t ≤ 1) →
        ∃ wapp wapp' : ℝ → ℂ → ℂ,
          PathC (sh + 1) T wapp ∧ PathC1 sh T wapp wapp' ∧
          (∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure ℂ), (wapp t x).im = 0) ∧
          wapp 0 =ᵐ[volume] (0 : ℂ → ℂ) ∧
          ∀ t ∈ Icc (0 : ℝ) T,
            Sob.normH (sh + 1) (wapp t) ≤ Capp * maj (Eig.sigma χ G) η t ∧
            Sob.normH sh (wapp t - (wlin χ sh G h t).fn) ≤
              Capp * maj (Eig.sigma χ G) η t ^ 2 ∧
            Sob.normH sh (Rapp χ G h wapp wapp' t) ≤
              Capp * (maj (Eig.sigma χ G) η t ^ (NQ + 1) +
                η t * maj (Eig.sigma χ G) η t ^ NQ) := by
  obtain ⟨CL, hCL0, hSb⟩ := QAppH.exists_CL χ hχ hN (Mh sh NQ)
  obtain ⟨Cbil, hCbil0, hBb⟩ := QAppH.exists_Cbil χ (Mh sh NQ)
  have hσb0 : 0 < Eig.sigb χ := by
    have := (Eig.propU_a χ hχ hN).2.2.2.1
    linarith
  have hA0 : 0 ≤ CL * Cbil := mul_nonneg hCL0 hCbil0
  -- `R = A (N_Q A/σ_b + 1) + 1`
  obtain ⟨R, hR0, hRle⟩ : ∃ R : ℝ, 0 ≤ R ∧
      CL * Cbil * (NQ * (CL * Cbil) / Eig.sigb χ + 1) ≤ R := by
    have h0 : 0 ≤ CL * Cbil * (NQ * (CL * Cbil) / Eig.sigb χ + 1) :=
      mul_nonneg hA0 (add_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hA0) hσb0.le)
        zero_le_one)
    exact ⟨_, h0, le_rfl⟩
  -- the constants `Σ_j C^{(j)}`, `Σ_{i,l} C^{(i)} C^{(l)}`, `C^{(N_Q)}`
  obtain ⟨Csum, hCsum⟩ : ∃ x : ℝ, x = ∑ j ∈ Finset.Icc 1 NQ, CL * Cbil * R ^ (j - 1) :=
    ⟨_, rfl⟩
  obtain ⟨Cpair, hCpair⟩ : ∃ x : ℝ, x = ∑ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ :
      Finset (ℕ × ℕ)), CL * Cbil * R ^ (p.1 - 1) * (CL * Cbil * R ^ (p.2 - 1)) := ⟨_, rfl⟩
  obtain ⟨CNQ, hCNQ⟩ : ∃ x : ℝ, x = CL * Cbil * R ^ (NQ - 1) := ⟨_, rfl⟩
  have hCsum0 : 0 ≤ Csum := by
    rw [hCsum]
    exact Finset.sum_nonneg fun j _ => mul_nonneg hA0 (pow_nonneg hR0 _)
  have hCpair0 : 0 ≤ Cpair := by
    rw [hCpair]
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (mul_nonneg hA0 (pow_nonneg hR0 _)) (mul_nonneg hA0 (pow_nonneg hR0 _))
  have hCNQ0 : 0 ≤ CNQ := by
    rw [hCNQ]
    exact mul_nonneg hA0 (pow_nonneg hR0 _)
  have hP1 : 0 ≤ Cbil * Cpair := mul_nonneg hCbil0 hCpair0
  have hP2 : 0 ≤ Cbil * CNQ := mul_nonneg hCbil0 hCNQ0
  have hdist : Cbil * (Cpair + CNQ) = Cbil * Cpair + Cbil * CNQ := mul_add _ _ _
  refine ⟨Csum + Cbil * (Cpair + CNQ), by linarith, ?_⟩
  have hCsumle : Csum ≤ Csum + Cbil * (Cpair + CNQ) := by linarith
  have hC2le : Cbil * Cpair ≤ Csum + Cbil * (Cpair + CNQ) := by linarith
  have hC3le : Cbil * CNQ ≤ Csum + Cbil * (Cpair + CNQ) := by linarith
  intro G T h η hG hT hh hsym hηm hη hmaj
  -- the hierarchy
  have hP := QAppH.hier_props χ hχ hN hs hQ hCL0 hCbil0 hR0 hRle hSb hBb hG hT hh hsym hηm hη
  have hPj : ∀ j ∈ Finset.Icc 1 NQ, QAppH.HierProp χ (Mh sh NQ) G T h η (CL * Cbil) R j :=
    fun j hj => hP j (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2
  have hη0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ η t := fun t ht =>
    (normCk_nonneg _ _ _).trans (hη t ht).1
  have hηi : IntegrableOn η (Icc 0 T) :=
    QAppH.eta_integrableOn hηm fun t ht => ⟨hη0 t ht, (hη t ht).2⟩
  obtain ⟨hσb', hσbσ⟩ := QAppH.sigb_facts χ hχ hN hG
  have hσ : 0 < Eig.sigma χ G := lt_of_lt_of_le hσb' hσbσ
  have hBs := hBb sh (by omega) (by unfold Mh; omega)
  obtain ⟨p1, p2, p3, p4⟩ := QAppH.approx_paths χ hχ hPj
  refine ⟨_, _, p1, p2, p3, p4, fun t ht => ?_⟩
  have hmt : 0 ≤ maj (Eig.sigma χ G) η t := QAppH.maj_nonneg hσ hηi hη0 ht
  have hm1 := hmaj t ht
  refine ⟨?_, ?_, ?_⟩
  · -- `‖w_app‖_{H^{s_h+1}} ≤ C_app maj`
    refine (QAppH.bound_wapp hA0 hR0 hPj ht hmt hm1).trans ?_
    rw [← hCsum]
    exact mul_le_mul_of_nonneg_right hCsumle hmt
  · -- `‖w_app - wlin‖_{H^{s_h}} ≤ C_app maj²`
    refine (QAppH.bound_diff χ hχ hQ hA0 hR0 hPj ht hmt hm1).trans ?_
    rw [← hCsum]
    exact mul_le_mul_of_nonneg_right hCsumle (sq_nonneg _)
  · -- `eq:Q-res`
    have hQ1 : 0 ≤ maj (Eig.sigma χ G) η t ^ (NQ + 1) := pow_nonneg hmt _
    have hQ2 : 0 ≤ η t * maj (Eig.sigma χ G) η t ^ NQ := mul_nonneg (hη0 t ht) (pow_nonneg hmt _)
    have hres := QAppH.bound_res χ hs hQ hA0 hR0 hCbil0 hBs.1 hBs.2.1 hh hη hPj ht hmt hm1
    rw [← hCpair, ← hCNQ] at hres
    refine hres.trans ?_
    calc Cbil * Cpair * maj (Eig.sigma χ G) η t ^ (NQ + 1) +
          Cbil * CNQ * (η t * maj (Eig.sigma χ G) η t ^ NQ)
        ≤ (Csum + Cbil * (Cpair + CNQ)) * maj (Eig.sigma χ G) η t ^ (NQ + 1) +
          (Csum + Cbil * (Cpair + CNQ)) * (η t * maj (Eig.sigma χ G) η t ^ NQ) :=
          add_le_add (mul_le_mul_of_nonneg_right hC2le hQ1) (mul_le_mul_of_nonneg_right hC3le hQ2)
      _ = (Csum + Cbil * (Cpair + CNQ)) * (maj (Eig.sigma χ G) η t ^ (NQ + 1) +
          η t * maj (Eig.sigma χ G) η t ^ NQ) := by ring

end OneRing

end NonUniqueEuler
