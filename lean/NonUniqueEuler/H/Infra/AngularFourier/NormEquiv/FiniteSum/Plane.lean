import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.I.Infra.AngularFourier.Parseval
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.FiniteSum.OneD

/-!
# Helper for `P/Infra/AngularFourier/NormEquiv/FiniteSum`: finite sector sums on the plane

* `memH_succ_of_grad`: `U ∈ L²` with `∂₁U, ∂₂U ∈ H^k` lies in `H^{k+1}`, with
  `‖U‖²_{H^{k+1}} ≤ 3(k+2)² (‖U‖²_{L²} + ‖∂₁U‖²_{H^k} + ‖∂₂U‖²_{H^k})` (every `∂^γ`, `|γ| ≥ 1`,
  is `∂^β ∂₁` or `∂^β ∂₂`);
* `hasWeakDerivOn_finset_sum`: weak derivatives of finite sums of `L²` functions;
* `memLp_ofProfile_supp`, `angularSector_sum_ofProfile`, `l2_sq_sum_ofProfile`: Parseval for
  finite sector sums, `‖∑_{ℓ∈S} h_ℓ e^{iℓθ}‖²_{L²} = 2π ∑_{ℓ∈S} ∫₀^∞ |h_ℓ|² r dr`;
* `secNormSq_zero_eq`: `‖h‖²_{0,ℓ} = ∫₀^∞ |h|² r dr` for profiles supported in `[ρ₋, ρ₊]`.

The lemmas `continuous_angPhase_rot`, `intervalIntegrable_sectorProj_ofProfile`,
`sectorProj_sum_ofProfile`, `angPhase_ofReal` are copied from
`H/Infra/AngularFourier/NormEquiv/Profile.lean` (namespace `Ang.NormEquivAux`; a helper of a
different proof, which may not be imported here).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang.FiniteSumAux

open Sob

/-! ### From first derivatives to `H^{k+1}` -/

theorem card_multiIdx_le (k : ℕ) : ((multiIdx k).card : ℝ) ≤ (k + 1) ^ 2 := by
  have : (multiIdx k).card ≤ (k + 1) ^ 2 := by
    unfold multiIdx
    calc _ ≤ (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).card := Finset.card_filter_le _ _
      _ = (k + 1) ^ 2 := by simp [Finset.card_product, sq]
  exact_mod_cast this

theorem pdList_succ_fst (a b : ℕ) : (pdList (a, b) ++ pdList (1, 0)).Perm (pdList (a + 1, b)) := by
  have e : pdList (a + 1, b) = pdList (1, 0) ++ pdList (a, b) := by
    simp [pdList, List.replicate_succ]
  rw [e]
  exact List.perm_append_comm

theorem pdList_succ_snd (b : ℕ) : (pdList (0, b) ++ pdList (0, 1)).Perm (pdList (0, b + 1)) := by
  have e : pdList (0, b + 1) = pdList (0, 1) ++ pdList (0, b) := by
    simp [pdList, List.replicate_succ]
  rw [e]
  exact List.perm_append_comm

/-- `U ∈ L²` with weak derivatives `∂₁U = G₁`, `∂₂U = G₂` in `H^k` lies in `H^{k+1}`. -/
theorem memH_succ_of_grad {k : ℕ} {U G₁ G₂ : ℂ → ℂ} (hU : MemLp U 2 volume)
    (h₁ : HasWeakDerivOn univ (pdList (1, 0)) U G₁) (h₂ : HasWeakDerivOn univ (pdList (0, 1)) U G₂)
    (hG₁ : MemH k G₁) (hG₂ : MemH k G₂) :
    MemH (k + 1) U ∧ normH (k + 1) U ^ 2 ≤
      3 * ((k : ℝ) + 2) ^ 2 * (l2 U ^ 2 + normH k G₁ ^ 2 + normH k G₂ ^ 2) := by
  set S := l2 U + normH k G₁ + normH k G₂ with hS
  have n0 := l2_nonneg U
  have n1 := normH_nonneg k G₁
  have n2 := normH_nonneg k G₂
  have hd : ∀ γ ∈ multiIdx (k + 1), ∃ g : ℂ → ℂ, MemLp g 2 volume ∧
      HasWeakDerivOn univ (pdList γ) U g ∧ l2 g ≤ S := by
    intro γ hγ
    have hγ' := mem_multiIdx.1 hγ
    obtain ⟨a, b⟩ := γ
    simp only at hγ'
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb
        exact ⟨U, hU, fun φ _ => by simp [pdList], by linarith⟩
      · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        have hβ : ((0 : ℕ), b') ∈ multiIdx k := mem_multiIdx.2 (by simp only; omega)
        obtain ⟨g2, gd⟩ := hG₂.memLp_weakPartial hβ
        refine ⟨_, g2, (h₂.trans gd).perm (pdList_succ_snd b'), ?_⟩
        have := hG₂.l2_weakPartial_le hβ
        linarith
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      have hβ : (a', b) ∈ multiIdx k := mem_multiIdx.2 (by simp only; omega)
      obtain ⟨g1, gd⟩ := hG₁.memLp_weakPartial hβ
      refine ⟨_, g1, (h₁.trans gd).perm (pdList_succ_fst a' b), ?_⟩
      have := hG₁.l2_weakPartial_le hβ
      linarith
  have hmem : MemH (k + 1) U := memH_iff.2 ⟨hU, fun γ hγ => by
    obtain ⟨g, a, b, -⟩ := hd γ hγ
    exact ⟨g, a, b⟩⟩
  refine ⟨hmem, ?_⟩
  have hterm : ∀ γ ∈ multiIdx (k + 1), l2 (weakPartial γ U) ^ 2 ≤ S ^ 2 := by
    intro γ hγ
    obtain ⟨g, a, b, c⟩ := hd γ hγ
    have hae := hmem.weakPartial_ae_eq hγ a b
    have e : l2 (weakPartial γ U) = l2 g := by
      unfold l2
      rw [eLpNorm_congr_ae hae]
    rw [e]
    exact pow_le_pow_left₀ (l2_nonneg _) c 2
  have hS0 : 0 ≤ S := by positivity
  have hsum : normH (k + 1) U ^ 2 ≤ ((k : ℝ) + 2) ^ 2 * S ^ 2 := by
    rw [normH_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    have hc := card_multiIdx_le (k + 1)
    push_cast at hc
    calc _ ≤ ∑ γ ∈ multiIdx (k + 1), S ^ 2 := Finset.sum_le_sum hterm
      _ = (multiIdx (k + 1)).card * S ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((k : ℝ) + 1 + 1) ^ 2 * S ^ 2 := by gcongr
      _ = ((k : ℝ) + 2) ^ 2 * S ^ 2 := by ring
  have hS2 : S ^ 2 ≤ 3 * (l2 U ^ 2 + normH k G₁ ^ 2 + normH k G₂ ^ 2) := by
    rw [hS]
    nlinarith [sq_nonneg (l2 U - normH k G₁), sq_nonneg (l2 U - normH k G₂),
      sq_nonneg (normH k G₁ - normH k G₂)]
  calc normH (k + 1) U ^ 2 ≤ ((k : ℝ) + 2) ^ 2 * S ^ 2 := hsum
    _ ≤ ((k : ℝ) + 2) ^ 2 * (3 * (l2 U ^ 2 + normH k G₁ ^ 2 + normH k G₂ ^ 2)) := by gcongr
    _ = _ := by ring

/-! ### Finite sums -/

theorem locInt_univ {f : ℂ → ℂ} (hf : MemLp f 2 volume) : LocallyIntegrableOn f univ :=
  (hf.locallyIntegrable one_le_two).locallyIntegrableOn univ

/-- Weak derivatives of finite sums of `L²` functions. -/
theorem hasWeakDerivOn_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) {vs : List ℂ}
    {F G : ι → ℂ → ℂ} (hF : ∀ i ∈ s, MemLp (F i) 2 volume) (hG : ∀ i ∈ s, MemLp (G i) 2 volume)
    (h : ∀ i ∈ s, HasWeakDerivOn univ vs (F i) (G i)) :
    HasWeakDerivOn univ vs (∑ i ∈ s, F i) (∑ i ∈ s, G i) := by
  induction s using Finset.induction_on with
  | empty =>
    intro φ _
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hF' : ∀ i ∈ s, MemLp (F i) 2 volume := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hG' : ∀ i ∈ s, MemLp (G i) 2 volume := fun i hi => hG i (Finset.mem_insert_of_mem hi)
    have hsF : MemLp (∑ i ∈ s, F i) 2 volume := memLp_finsetSum' s hF'
    have hsG : MemLp (∑ i ∈ s, G i) 2 volume := memLp_finsetSum' s hG'
    exact HasWeakDerivOn.add isOpen_univ (locInt_univ (hF a (Finset.mem_insert_self a s)))
      (locInt_univ hsF) (locInt_univ (hG a (Finset.mem_insert_self a s))) (locInt_univ hsG)
      (h a (Finset.mem_insert_self a s))
      (ih hF' hG' fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ### Sectors of finite sector sums (copied from `NormEquiv/Profile.lean`) -/

theorem continuous_angPhase_rot (m : ℤ) (x : ℂ) :
    Continuous fun φ : ℝ => angPhase m (rot φ x) := by
  by_cases hx : x = 0
  · subst hx
    simp only [rot, mul_zero]
    exact continuous_const
  · have h1 : (fun φ : ℝ => angPhase m (rot φ x)) =
        fun φ : ℝ => (Complex.exp ((φ : ℂ) * Complex.I) * x / (‖x‖ : ℂ)) ^ m := by
      funext φ
      rw [angPhase, Polar.norm_rot]
      rfl
    rw [h1]
    refine Continuous.zpow₀ ?_ m fun φ => Or.inl ?_
    · exact ((Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).mul
        continuous_const).div_const _
    · refine div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) hx) ?_
      exact Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hx)

theorem intervalIntegrable_sectorProj_ofProfile (ℓ m : ℤ) (h : ℝ → ℂ) (x : ℂ) :
    IntervalIntegrable (fun φ : ℝ => Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) *
      ofProfile m h (rot φ x)) volume 0 (2 * π) := by
  refine Continuous.intervalIntegrable ?_ _ _
  have h1 : (fun φ : ℝ => Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * ofProfile m h (rot φ x)) =
      fun φ : ℝ => Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * (h ‖x‖ * angPhase m (rot φ x)) := by
    funext φ
    rw [ofProfile, Polar.norm_rot]
  rw [h1]
  refine Continuous.mul ?_ (continuous_const.mul (continuous_angPhase_rot m x))
  exact Complex.continuous_exp.comp
    (((continuous_const.mul Complex.continuous_ofReal).mul continuous_const).neg)

/-- `P_ℓ` of a finite sector sum. -/
theorem sectorProj_sum_ofProfile (ℓ : ℤ) (S : Finset ℤ) (h : ℤ → ℝ → ℂ) :
    sectorProj ℓ (∑ m ∈ S, ofProfile m (h m)) = if ℓ ∈ S then ofProfile ℓ (h ℓ) else 0 := by
  have hlin : ∀ x, sectorProj ℓ (∑ m ∈ S, ofProfile m (h m)) x =
      ∑ m ∈ S, sectorProj ℓ (ofProfile m (h m)) x := by
    intro x
    simp only [sectorProj, Finset.sum_apply, Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
    · intro m _
      exact intervalIntegrable_sectorProj_ofProfile ℓ m (h m) x
  funext x
  rw [hlin]
  simp only [sectorProj_ofProfile]
  simp only [ite_apply, Pi.zero_apply]
  rw [Finset.sum_ite_eq]

theorem angPhase_ofReal {r : ℝ} (hr : 0 < r) (m : ℤ) : angPhase m (r : ℂ) = 1 := by
  have h1 : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [angPhase, h1, div_self (Complex.ofReal_ne_zero.2 hr.ne'), one_zpow]

/-- The sectors of a finite sector sum: `h_m` in sector `m ∈ S`, `0` otherwise. -/
theorem angularSector_sum_ofProfile (S : Finset ℤ) (h : ℤ → ℝ → ℂ) (m : ℤ) {r : ℝ}
    (hr : 0 < r) :
    Polar.angularSector (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) m r = if m ∈ S then h m r else 0 := by
  have hx : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have h1 := sectorProj_eq_angularSector m (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) hx
  have hn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [sectorProj_sum_ofProfile, hn, angPhase_ofReal hr, mul_one] at h1
  rw [← h1]
  split_ifs
  · simp [ofProfile, angPhase_ofReal hr, abs_of_pos hr]
  · rfl

/-! ### Parseval for finite sums -/

/-- A profile in `L²((0,∞))` supported in `[ρ₋, ρ₊]` gives an `L²` sector function. -/
theorem memLp_ofProfile_supp {ℓ : ℤ} {ρm ρp : ℝ} {h : ℝ → ℂ}
    (hh : MemLp h 2 (volume.restrict (Ioi 0)))
    (hhI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0) :
    MemLp (ofProfile ℓ h) 2 volume := by
  refine (memLp_ofProfile_iff (ℓ := ℓ) hh.1).1.2 ?_
  have h2 : IntegrableOn (fun r => ‖h r‖ ^ 2) (Ioi 0) := hh.integrable_norm_pow two_ne_zero
  refine Integrable.mono' (h2.const_mul ρp)
    (h2.aestronglyMeasurable.mul continuous_id.aestronglyMeasurable) ?_
  filter_upwards [hhI, ae_restrict_mem measurableSet_Ioi] with r h1 hr0
  by_cases hrI : r ∈ Icc ρm ρp
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt hr0))]
    calc ‖h r‖ ^ 2 * r ≤ ‖h r‖ ^ 2 * ρp := mul_le_mul_of_nonneg_left hrI.2 (sq_nonneg _)
      _ = ρp * ‖h r‖ ^ 2 := mul_comm _ _
  · simp [h1 hrI]

/-- Parseval for a finite sector sum: `‖∑_{ℓ∈S} h_ℓ e^{iℓθ}‖²_{L²} = 2π ∑_{ℓ∈S} ∫₀^∞ |h_ℓ|² r dr`. -/
theorem l2_sq_sum_ofProfile {ρm ρp : ℝ} (S : Finset ℤ) (h : ℤ → ℝ → ℂ)
    (hL2 : ∀ ℓ ∈ S, MemLp (h ℓ) 2 (volume.restrict (Ioi 0)))
    (hI : ∀ ℓ ∈ S, ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h ℓ r = 0) :
    MemLp (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) 2 volume ∧
      l2 (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) ^ 2 =
        2 * π * ∑ ℓ ∈ S, ∫ r in Ioi 0, ‖h ℓ r‖ ^ 2 * r := by
  have hmem : MemLp (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) 2 volume :=
    memLp_finsetSum' S fun ℓ hℓ => memLp_ofProfile_supp (hL2 ℓ hℓ) (hI ℓ hℓ)
  refine ⟨hmem, ?_⟩
  have hs := hasSum_angularSector_sq hmem
  have hF : (fun m : ℤ => 2 * π *
        ∫ r in Ioi 0, ‖Polar.angularSector (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) m r‖ ^ 2 * r) =
      fun m => if m ∈ S then 2 * π * ∫ r in Ioi 0, ‖h m r‖ ^ 2 * r else 0 := by
    funext m
    have e : ∫ r in Ioi 0, ‖Polar.angularSector (∑ ℓ ∈ S, ofProfile ℓ (h ℓ)) m r‖ ^ 2 * r =
        ∫ r in Ioi 0, ‖(if m ∈ S then h m r else 0)‖ ^ 2 * r :=
      setIntegral_congr_fun measurableSet_Ioi fun r hr => by
        rw [angularSector_sum_ofProfile S h m hr]
    rw [e]
    by_cases hm : m ∈ S <;> simp [hm]
  rw [hF] at hs
  have hs2 : HasSum (fun m : ℤ => if m ∈ S then 2 * π * ∫ r in Ioi 0, ‖h m r‖ ^ 2 * r else 0)
      (∑ m ∈ S, if m ∈ S then 2 * π * ∫ r in Ioi 0, ‖h m r‖ ^ 2 * r else 0) :=
    hasSum_sum_of_ne_finset_zero fun m hm => by simp [hm]
  rw [hs.unique hs2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m hm => by simp [hm]

/-- `‖g‖²_{0,ℓ} = ∫₀^∞ |g|² r dr` for `g ∈ L²((0,∞))` supported in `[ρ₋, ρ₊]`, `ρ₋ > 0`. -/
theorem secNormSq_zero_eq {ρm ρp : ℝ} (hρm : 0 < ρm) (ℓ : ℤ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi 0)))
    (hgI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → g r = 0) :
    secNormSq 0 ℓ (Icc ρm ρp) g = ∫ r in Ioi 0, ‖g r‖ ^ 2 * r := by
  have hsub : Icc ρm ρp ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le hρm hr.1
  have h0 : HasWeakDerivOn (Ioi 0) (derivList 0) g g := fun φ _ => by simp [derivList]
  have hae : ∀ᵐ x, x ∈ Ioi (0 : ℝ) → weakDeriv1On (Ioi 0) 0 g x = g x :=
    weakDerivOn_ae_eq isOpen_Ioi (locInt_of_memLp hg) h0
  have hg0 : ∀ᵐ r, r ∈ Ioi (0 : ℝ) → r ∉ Icc ρm ρp → g r = 0 :=
    (ae_restrict_iff' measurableSet_Ioi).1 hgI
  simp only [secNormSq, zero_add, Finset.sum_range_one, secWeight, Nat.sub_self, pow_zero,
    one_mul]
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet hsub]
  · refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [hae] with r hr hrI
    rw [hr (hsub hrI)]
  · filter_upwards [hg0] with r hr hrd
    simp [hr hrd.1 hrd.2]

end NonUniqueEuler.Ang.FiniteSumAux
