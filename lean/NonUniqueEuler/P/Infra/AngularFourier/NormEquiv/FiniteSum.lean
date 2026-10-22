import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.I.Infra.AngularFourier.NormEquiv.ProfileDeriv
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.SobolevOneD.Basic
import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.FiniteSum.OneD
import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.FiniteSum.Plane

/-!
# Proof: `H^k` bound for finite sums of sector functions

Proof of `I/Infra/AngularFourier/NormEquiv/FiniteSum.lean` (manuscript `lem:norm-equiv`,
`04_ring.tex:843-864`, upper bound `‖w‖²_{H^k} ≤ C_k ∑_ℓ ‖g_ℓ‖²_{k,ℓ}`, for finite sector sums).

Induction on `k`, for all finite `S` and all families at once.
* `k = 0` (`FiniteSumAux.base_case`): Parseval for finite sector sums
  (`FiniteSumAux.l2_sq_sum_ofProfile`): `‖w‖²_{L²} = 2π ∑_{ℓ∈S} ‖h_ℓ‖²_{0,ℓ}`.
* `k → k+1` (`FiniteSumAux.step`): by `hasWeakDerivOn_ofProfile`
  (`I/Infra/AngularFourier/NormEquiv/ProfileDeriv.lean`), `∂₁w = X + Y` and `∂₂w = i(X - Y)` with
  `X = ∑_{ℓ∈S} A_ℓ(r) e^{i(ℓ-1)θ}`, `Y = ∑_{ℓ∈S} B_ℓ(r) e^{i(ℓ+1)θ}`, `A_ℓ, B_ℓ = (h_ℓ' ± ℓh_ℓ/r)/2`.
  These are finite sector sums over `S - 1` and `S + 1` (reindexing), with
  `‖A_ℓ‖²_{k,ℓ-1}, ‖B_ℓ‖²_{k,ℓ+1} ≤ K ‖h_ℓ‖²_{k+1,ℓ}` (`FiniteSumAux.profile_bound`), so the
  induction hypothesis bounds `‖X‖_{H^k}`, `‖Y‖_{H^k}`; then `FiniteSumAux.memH_succ_of_grad`.

The manuscript proves the upper bound through the converse polar formulas
`∂₁ = cos θ ∂_r - (sin θ/r)∂_θ`, `∂₂ = sin θ ∂_r + (cos θ/r)∂_θ`; here the same formulas are used
in complex form (`∂_z`, `∂_z̄` shift the sector by `∓1`), sector by sector.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang

namespace FiniteSumAux

open Sob

theorem sum_image_sub_one {β : Type*} [AddCommMonoid β] (S : Finset ℤ) (P : ℤ → ℝ → ℂ)
    (F : ℤ → (ℝ → ℂ) → β) :
    ∑ m ∈ S.image (fun ℓ => ℓ - 1), F m (P (m + 1)) = ∑ ℓ ∈ S, F (ℓ - 1) (P ℓ) := by
  rw [Finset.sum_image (by intro a _ b _ hab; simpa using hab)]
  simp only [sub_add_cancel]

theorem sum_image_add_one {β : Type*} [AddCommMonoid β] (S : Finset ℤ) (P : ℤ → ℝ → ℂ)
    (F : ℤ → (ℝ → ℂ) → β) :
    ∑ m ∈ S.image (fun ℓ => ℓ + 1), F m (P (m - 1)) = ∑ ℓ ∈ S, F (ℓ + 1) (P ℓ) := by
  rw [Finset.sum_image (by intro a _ b _ hab; simpa using hab)]
  simp only [add_sub_cancel_right]

/-- The case `k = 0`: Parseval. -/
theorem base_case {ρm ρp : ℝ} (hρm : 0 < ρm) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℤ) (h : ℤ → ℝ → ℂ),
      (∀ ℓ ∈ S, Sob.MemH1On 0 (Ioi 0) (h ℓ)) →
      (∀ ℓ ∈ S, ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h ℓ r = 0) →
      Sob.MemH 0 (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) ∧
        Sob.normH 0 (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) ^ 2 ≤
          C * ∑ ℓ ∈ S, Sob.secNormSq 0 ℓ (Icc ρm ρp) (h ℓ) := by
  refine ⟨2 * π, by positivity, fun S h hh hhI => ?_⟩
  obtain ⟨hmem, hl2⟩ := l2_sq_sum_ofProfile S h (fun ℓ hℓ => (hh ℓ hℓ).memLp) hhI
  obtain ⟨hH, hn⟩ := normH_zero hmem
  refine ⟨hH, ?_⟩
  rw [hn, hl2]
  refine le_of_eq ?_
  congr 1
  exact Finset.sum_congr rfl fun ℓ hℓ =>
    (secNormSq_zero_eq hρm ℓ (hh ℓ hℓ).memLp (hhI ℓ hℓ)).symm

/-- The induction step `k → k + 1`. -/
theorem step {k : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm)
    (ih : ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℤ) (h : ℤ → ℝ → ℂ),
      (∀ ℓ ∈ S, Sob.MemH1On k (Ioi 0) (h ℓ)) →
      (∀ ℓ ∈ S, ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h ℓ r = 0) →
      Sob.MemH k (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) ∧
        Sob.normH k (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) ^ 2 ≤
          C * ∑ ℓ ∈ S, Sob.secNormSq k ℓ (Icc ρm ρp) (h ℓ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℤ) (h : ℤ → ℝ → ℂ),
      (∀ ℓ ∈ S, Sob.MemH1On (k + 1) (Ioi 0) (h ℓ)) →
      (∀ ℓ ∈ S, ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h ℓ r = 0) →
      Sob.MemH (k + 1) (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) ∧
        Sob.normH (k + 1) (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) ^ 2 ≤
          C * ∑ ℓ ∈ S, Sob.secNormSq (k + 1) ℓ (Icc ρm ρp) (h ℓ) := by
  obtain ⟨C, hC, hCS⟩ := ih
  obtain ⟨K, hK, hKb⟩ := profile_bound k (ρp := ρp) hρm
  refine ⟨3 * ((k : ℝ) + 2) ^ 2 * (2 * π + 8 * C * K), by positivity, fun S h hh hhI => ?_⟩
  have hsub : Icc ρm ρp ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le hρm hr.1
  have hsubI : Icc ρm ρp ⊆ Ici 0 := hsub.trans Ioi_subset_Ici_self
  -- the profiles of `∂_z` and `∂_z̄`
  set A : ℤ → ℝ → ℂ := fun ℓ r =>
    (2 : ℂ)⁻¹ * (weakDeriv1On (Ioi 0) 1 (h ℓ) r + (ℓ : ℂ) * h ℓ r / (r : ℂ)) with hAdef
  set B : ℤ → ℝ → ℂ := fun ℓ r =>
    (2 : ℂ)⁻¹ * (weakDeriv1On (Ioi 0) 1 (h ℓ) r - (ℓ : ℂ) * h ℓ r / (r : ℂ)) with hBdef
  have hnℓ : ∀ ℓ : ℤ, ‖(ℓ : ℂ)‖ ^ 2 ≤ (ℓ : ℝ) ^ 2 := fun ℓ => by
    rw [Complex.norm_intCast, sq_abs]
  have hA : ∀ ℓ ∈ S, MemH1On k (Ioi 0) (A ℓ) ∧
      (∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → A ℓ r = 0) ∧
      secNormSq k (ℓ - 1) (Icc ρm ρp) (A ℓ) ≤ K * secNormSq (k + 1) ℓ (Icc ρm ρp) (h ℓ) :=
    fun ℓ hℓ => hKb ℓ (ℓ - 1) (ℓ : ℂ) (h ℓ) (hh ℓ hℓ) (hhI ℓ hℓ) (hnℓ ℓ)
      (by push_cast; nlinarith [sq_nonneg ((ℓ : ℝ) + 1)])
  have hB : ∀ ℓ ∈ S, MemH1On k (Ioi 0) (B ℓ) ∧
      (∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → B ℓ r = 0) ∧
      secNormSq k (ℓ + 1) (Icc ρm ρp) (B ℓ) ≤ K * secNormSq (k + 1) ℓ (Icc ρm ρp) (h ℓ) := by
    intro ℓ hℓ
    have e : B ℓ = fun r =>
        (2 : ℂ)⁻¹ * (weakDeriv1On (Ioi 0) 1 (h ℓ) r + (-(ℓ : ℂ)) * h ℓ r / (r : ℂ)) := by
      funext r
      simp only [hBdef]
      ring
    rw [e]
    exact hKb ℓ (ℓ + 1) (-(ℓ : ℂ)) (h ℓ) (hh ℓ hℓ) (hhI ℓ hℓ) (by rw [norm_neg]; exact hnℓ ℓ)
      (by push_cast; nlinarith [sq_nonneg ((ℓ : ℝ) - 1)])
  set X : ℂ → ℂ := ∑ ℓ ∈ S, ofProfile (ℓ - 1) (A ℓ) with hXdef
  set Y : ℂ → ℂ := ∑ ℓ ∈ S, ofProfile (ℓ + 1) (B ℓ) with hYdef
  set T := ∑ ℓ ∈ S, secNormSq (k + 1) ℓ (Icc ρm ρp) (h ℓ) with hTdef
  have hT0 : 0 ≤ T :=
    Finset.sum_nonneg fun ℓ _ => secNormSq_nonneg _ _ measurableSet_Icc hsubI _
  -- the induction hypothesis on `X` and `Y`
  have hX : MemH k X ∧ normH k X ^ 2 ≤ C * (K * T) := by
    obtain ⟨m1, n1⟩ := hCS (S.image fun ℓ => ℓ - 1) (fun m => A (m + 1))
      (fun m hm => by
        obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.1 hm
        simpa only [sub_add_cancel] using (hA ℓ hℓ).1)
      (fun m hm => by
        obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.1 hm
        simpa only [sub_add_cancel] using (hA ℓ hℓ).2.1)
    have e1 : ∑ m ∈ S.image (fun ℓ => ℓ - 1), ofProfile m (A (m + 1)) = X :=
      sum_image_sub_one S A (fun m g => ofProfile m g)
    have e2 : ∑ m ∈ S.image (fun ℓ => ℓ - 1), secNormSq k m (Icc ρm ρp) (A (m + 1)) =
        ∑ ℓ ∈ S, secNormSq k (ℓ - 1) (Icc ρm ρp) (A ℓ) :=
      sum_image_sub_one S A (fun m g => secNormSq k m (Icc ρm ρp) g)
    rw [e1] at m1 n1
    rw [e2] at n1
    refine ⟨m1, n1.trans (mul_le_mul_of_nonneg_left ?_ hC.le)⟩
    rw [hTdef, Finset.mul_sum]
    exact Finset.sum_le_sum fun ℓ hℓ => (hA ℓ hℓ).2.2
  have hY : MemH k Y ∧ normH k Y ^ 2 ≤ C * (K * T) := by
    obtain ⟨m1, n1⟩ := hCS (S.image fun ℓ => ℓ + 1) (fun m => B (m - 1))
      (fun m hm => by
        obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.1 hm
        simpa only [add_sub_cancel_right] using (hB ℓ hℓ).1)
      (fun m hm => by
        obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.1 hm
        simpa only [add_sub_cancel_right] using (hB ℓ hℓ).2.1)
    have e1 : ∑ m ∈ S.image (fun ℓ => ℓ + 1), ofProfile m (B (m - 1)) = Y :=
      sum_image_add_one S B (fun m g => ofProfile m g)
    have e2 : ∑ m ∈ S.image (fun ℓ => ℓ + 1), secNormSq k m (Icc ρm ρp) (B (m - 1)) =
        ∑ ℓ ∈ S, secNormSq k (ℓ + 1) (Icc ρm ρp) (B ℓ) :=
      sum_image_add_one S B (fun m g => secNormSq k m (Icc ρm ρp) g)
    rw [e1] at m1 n1
    rw [e2] at n1
    refine ⟨m1, n1.trans (mul_le_mul_of_nonneg_left ?_ hC.le)⟩
    rw [hTdef, Finset.mul_sum]
    exact Finset.sum_le_sum fun ℓ hℓ => (hB ℓ hℓ).2.2
  -- the first weak derivatives of `w`
  have hpd : ∀ ℓ ∈ S, HasWeakDerivOn univ (pdList (1, 0)) (ofProfile ℓ (h ℓ))
        (fun x => ofProfile (ℓ - 1) (A ℓ) x + ofProfile (ℓ + 1) (B ℓ) x) ∧
      HasWeakDerivOn univ (pdList (0, 1)) (ofProfile ℓ (h ℓ))
        (fun x => Complex.I * (ofProfile (ℓ - 1) (A ℓ) x - ofProfile (ℓ + 1) (B ℓ) x)) :=
    fun ℓ hℓ => hasWeakDerivOn_ofProfile hρm ((hh ℓ hℓ).mono_order (by omega)) (hhI ℓ hℓ) ℓ
  have hLh : ∀ ℓ ∈ S, MemLp (ofProfile ℓ (h ℓ)) 2 volume := fun ℓ hℓ =>
    memLp_ofProfile_supp (hh ℓ hℓ).memLp (hhI ℓ hℓ)
  have hLA : ∀ ℓ ∈ S, MemLp (ofProfile (ℓ - 1) (A ℓ)) 2 volume := fun ℓ hℓ =>
    memLp_ofProfile_supp (hA ℓ hℓ).1.memLp (hA ℓ hℓ).2.1
  have hLB : ∀ ℓ ∈ S, MemLp (ofProfile (ℓ + 1) (B ℓ)) 2 volume := fun ℓ hℓ =>
    memLp_ofProfile_supp (hB ℓ hℓ).1.memLp (hB ℓ hℓ).2.1
  have hd1 : HasWeakDerivOn univ (pdList (1, 0)) (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) (X + Y) := by
    have := hasWeakDerivOn_finset_sum S hLh
      (G := fun ℓ x => ofProfile (ℓ - 1) (A ℓ) x + ofProfile (ℓ + 1) (B ℓ) x)
      (fun ℓ hℓ => (hLA ℓ hℓ).add (hLB ℓ hℓ)) (fun ℓ hℓ => (hpd ℓ hℓ).1)
    have e : (∑ ℓ ∈ S, fun x => ofProfile (ℓ - 1) (A ℓ) x + ofProfile (ℓ + 1) (B ℓ) x) =
        X + Y := by
      funext x
      simp [hXdef, hYdef, Finset.sum_apply, Finset.sum_add_distrib]
    rwa [e] at this
  have hd2 : HasWeakDerivOn univ (pdList (0, 1)) (∑ ℓ ∈ S, ofProfile ℓ (h ℓ))
      (Complex.I • (X - Y)) := by
    have := hasWeakDerivOn_finset_sum S hLh
      (G := fun ℓ x => Complex.I * (ofProfile (ℓ - 1) (A ℓ) x - ofProfile (ℓ + 1) (B ℓ) x))
      (fun ℓ hℓ => ((hLA ℓ hℓ).sub (hLB ℓ hℓ)).const_mul Complex.I) (fun ℓ hℓ => (hpd ℓ hℓ).2)
    have e : (∑ ℓ ∈ S, fun x =>
          Complex.I * (ofProfile (ℓ - 1) (A ℓ) x - ofProfile (ℓ + 1) (B ℓ) x)) =
        Complex.I • (X - Y) := by
      funext x
      simp [hXdef, hYdef, Finset.sum_apply, Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
    rwa [e] at this
  -- assembling
  obtain ⟨hXm, hXn⟩ := hX
  obtain ⟨hYm, hYn⟩ := hY
  obtain ⟨hXY, nXY⟩ := hXm.add hYm
  obtain ⟨hXYs, nXYs⟩ := hXm.sub hYm
  obtain ⟨hIXY, nIXY⟩ := hXYs.const_smul Complex.I
  obtain ⟨hl2m, hl2⟩ := l2_sq_sum_ofProfile S h (fun ℓ hℓ => (hh ℓ hℓ).memLp) hhI
  obtain ⟨hres, nres⟩ := memH_succ_of_grad hl2m hd1 hd2 hXY hIXY
  refine ⟨hres, nres.trans ?_⟩
  have hw2 : l2 (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) ^ 2 ≤ 2 * π * T := by
    rw [hl2, hTdef]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ℓ hℓ => ?_) (by positivity)
    rw [← secNormSq_zero_eq hρm ℓ (hh ℓ hℓ).memLp (hhI ℓ hℓ)]
    exact secNormSq_mono_order (Nat.zero_le _) ℓ measurableSet_Icc hsubI _
  have hnX0 := normH_nonneg k X
  have hnY0 := normH_nonneg k Y
  have hXY2 : normH k (X + Y) ^ 2 ≤ 4 * C * K * T := by
    have h1 : normH k (X + Y) ^ 2 ≤ (normH k X + normH k Y) ^ 2 :=
      pow_le_pow_left₀ (normH_nonneg _ _) nXY 2
    nlinarith [sq_nonneg (normH k X - normH k Y)]
  have hIXY2 : normH k (Complex.I • (X - Y)) ^ 2 ≤ 4 * C * K * T := by
    rw [nIXY, Complex.norm_I, one_mul]
    have h1 : normH k (X - Y) ^ 2 ≤ (normH k X + normH k Y) ^ 2 :=
      pow_le_pow_left₀ (normH_nonneg _ _) nXYs 2
    nlinarith [sq_nonneg (normH k X - normH k Y)]
  calc 3 * ((k : ℝ) + 2) ^ 2 * (l2 (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) ^ 2 + normH k (X + Y) ^ 2 +
        normH k (Complex.I • (X - Y)) ^ 2)
      ≤ 3 * ((k : ℝ) + 2) ^ 2 * (2 * π * T + 4 * C * K * T + 4 * C * K * T) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add hw2 hXY2) hIXY2) (by positivity)
    _ = 3 * ((k : ℝ) + 2) ^ 2 * (2 * π + 8 * C * K) * T := by ring

end FiniteSumAux

/-- Finite sector sums `∑_{ℓ ∈ S} h_ℓ(r) e^{iℓθ}` of profiles `h_ℓ ∈ H^k((0,∞))` vanishing outside
`[ρ₋, ρ₊]` lie in `H^k`, with `‖∑_{ℓ∈S} h_ℓ e^{iℓθ}‖²_{H^k} ≤ C ∑_{ℓ∈S} ‖h_ℓ‖²_{k,ℓ}`, `C`
independent of `S`. -/
theorem exists_normH_sum_ofProfile_le (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℤ) (h : ℤ → ℝ → ℂ),
      (∀ ℓ ∈ S, Sob.MemH1On k (Ioi 0) (h ℓ)) →
      (∀ ℓ ∈ S, ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h ℓ r = 0) →
      Sob.MemH k (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) ∧
        Sob.normH k (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) ^ 2 ≤
          C * ∑ ℓ ∈ S, Sob.secNormSq k ℓ (Icc ρm ρp) (h ℓ) := by
  have _ := hρ
  induction k with
  | zero => exact FiniteSumAux.base_case hρm
  | succ k ih => exact FiniteSumAux.step hρm ih

end NonUniqueEuler.Ang
