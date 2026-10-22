import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.ConstMulAction
import NonUniqueEuler.Defs.Infra.Sobolev
import NonUniqueEuler.Statement.Plane
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.H.Infra.Sobolev.Symmetry.ChainRule
import NonUniqueEuler.H.Infra.Sobolev.Symmetry.Directions

/-!
# Proof: rotations, dilations, translations and conjugation in `H^k` (library I-HK)

Proof of `NonUniqueEuler/I/Infra/Sobolev/Symmetry.lean` (same declarations, same statements).

* A generic transport lemma (`SymmProof.transport`): for a change of variables `T` with constant
  derivative `L`, smooth inverse and `T_* vol = ν • vol`, weak derivatives of `f` in the
  directions `L(pdList γ)` give the weak derivatives `∂^γ (f ∘ T)` (chain rule
  `SymmAux.hasWeakDerivOn_comp`), with `‖g ∘ T‖²_{L²} = ν ‖g‖²_{L²}`.
* Rotations: the directions `e^{iθ} · 1`, `e^{iθ} · i` are unit vectors; the weak derivative of
  `f` along unit vectors `w₁ … wₙ` is bounded by `2ⁿ ∑_{|β| = n} ‖∂^β f‖²` (`SymmAux.dirs`), and
  regrouping by order (`SymmAux.sum_levels_le`) gives `‖f ∘ O_θ‖²_{H^k} ≤ 4^k ‖f‖²_{H^k}`.
  For `k ≤ 1` the pointwise identity `|cA + sB|² + |-sA + cB|² = |A|² + |B|²` gives equality.
* Dilations: `∂_{c vs} f = c^{|vs|} ∂_{vs} f` and `‖g(c ·)‖²_{L²} = |c|^{-2} ‖g‖²_{L²}`.
* Translations: measure preserving with `L = id`.
* Conjugation: `∂_{vs} conj f = conj ∂_{vs} f`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff ComplexConjugate

namespace NonUniqueEuler.Sob

namespace SymmProof

open SymmAux

/-! ### Generic transport under a change of variables -/

/-- `H^k` membership of `f ∘ T` from `L²` weak derivatives of `f` in the directions
`L (pdList γ)`. -/
theorem transport {k : ℕ} {f : ℂ → ℂ} (hf : MemLp f 2 volume) {T S : ℂ → ℂ}
    {L : ℂ →L[ℝ] ℂ} (hT : ∀ x, HasFDerivAt T L x) (hS : ContDiff ℝ ∞ S)
    (hST : ∀ x, S (T x) = x) (hTS : ∀ y, T (S y) = y) (hTm : MeasurableEmbedding T)
    {ν : ℝ≥0∞} (hν : ν ≠ ⊤) (hmap : Measure.map T volume = ν • volume)
    (hd : ∀ γ ∈ multiIdx k, ∃ G : ℂ → ℂ, MemLp G 2 volume ∧
      HasWeakDerivOn univ ((pdList γ).map L) f G) :
    MemH k (fun x => f (T x)) := by
  refine memH_iff.2 ⟨memLp_comp hTm hν hmap hf, fun γ hγ => ?_⟩
  obtain ⟨G, hG1, hG2⟩ := hd γ hγ
  exact ⟨_, memLp_comp hTm hν hmap hG1, hasWeakDerivOn_comp hT hS hST hTS hTm hmap hG2⟩

/-- The weak derivatives of `f ∘ T`. -/
theorem transport_ae {f : ℂ → ℂ} {T S : ℂ → ℂ}
    {L : ℂ →L[ℝ] ℂ} (hT : ∀ x, HasFDerivAt T L x) (hS : ContDiff ℝ ∞ S)
    (hST : ∀ x, S (T x) = x) (hTS : ∀ y, T (S y) = y) (hTm : MeasurableEmbedding T)
    {ν : ℝ≥0∞} (hν : ν ≠ ⊤) (hmap : Measure.map T volume = ν • volume)
    {γ : ℕ × ℕ} {G : ℂ → ℂ}
    (hG1 : MemLp G 2 volume) (hG2 : HasWeakDerivOn univ ((pdList γ).map L) f G) :
    weakPartial γ (fun x => f (T x)) =ᵐ[volume] fun x => G (T x) :=
  weakPartial_ae_eq_of (memLp_comp hTm hν hmap hG1)
    (hasWeakDerivOn_comp hT hS hST hTS hTm hmap hG2)

/-- The `L²` norms of the weak derivatives of `f ∘ T`. -/
theorem transport_l2 {f : ℂ → ℂ} {T S : ℂ → ℂ}
    {L : ℂ →L[ℝ] ℂ} (hT : ∀ x, HasFDerivAt T L x) (hS : ContDiff ℝ ∞ S)
    (hST : ∀ x, S (T x) = x) (hTS : ∀ y, T (S y) = y) (hTm : MeasurableEmbedding T)
    {ν : ℝ≥0∞} (hν0 : ν ≠ 0) (hν : ν ≠ ⊤) (hmap : Measure.map T volume = ν • volume)
    {γ : ℕ × ℕ} {G : ℂ → ℂ}
    (hG1 : MemLp G 2 volume) (hG2 : HasWeakDerivOn univ ((pdList γ).map L) f G) :
    l2 (weakPartial γ (fun x => f (T x))) ^ 2 = ν.toReal * l2 G ^ 2 := by
  rw [l2_congr_ae (transport_ae hT hS hST hTS hTm hν hmap hG1 hG2),
    l2_comp_sq hTm hν0 hmap]

/-! ### Rotations as changes of variables -/

theorem rot_eq_rotation (θ : ℝ) : rot θ = ⇑(rotation (Circle.exp θ)) := by
  funext x
  simp [rot, rotation_apply, Circle.coe_exp]

theorem rot_measurableEmbedding (θ : ℝ) : MeasurableEmbedding (rot θ) := by
  rw [rot_eq_rotation]
  exact (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding

theorem rot_map (θ : ℝ) : Measure.map (rot θ) volume = (1 : ℝ≥0∞) • volume := by
  rw [one_smul, rot_eq_rotation]
  exact (LinearIsometryEquiv.measurePreserving _).map_eq

theorem exists_rot_deriv (θ : ℝ) :
    ∃ L : ℂ →L[ℝ] ℂ, (∀ v, L v = Complex.exp (θ * Complex.I) * v) ∧
      ∀ x, HasFDerivAt (rot θ) L x := by
  refine ⟨((rotation (Circle.exp θ)).toContinuousLinearEquiv : ℂ →L[ℝ] ℂ), fun v => ?_,
    fun x => ?_⟩
  · simp [rotation_apply, Circle.coe_exp]
  · rw [rot_eq_rotation]
    exact (rotation (Circle.exp θ)).toContinuousLinearEquiv.hasFDerivAt

theorem rot_contDiff (θ : ℝ) : ContDiff ℝ ∞ (rot θ) := by
  unfold rot
  exact contDiff_const.mul contDiff_id

theorem rot_neg_rot (θ : ℝ) (x : ℂ) : rot (-θ) (rot θ x) = x := by
  simp only [rot, ← mul_assoc, ← Complex.exp_add]
  simp

theorem rot_rot_neg (θ : ℝ) (y : ℂ) : rot θ (rot (-θ) y) = y := by
  simpa using rot_neg_rot (-θ) y

theorem norm_of_mem_pdList {γ : ℕ × ℕ} {v : ℂ} (hv : v ∈ pdList γ) : ‖v‖ = 1 := by
  simp only [pdList, List.mem_append] at hv
  rcases hv with hv | hv <;> rw [List.eq_of_mem_replicate hv] <;> simp

theorem prod_map_rot_eq_one {θ : ℝ} {L : ℂ →L[ℝ] ℂ}
    (hLv : ∀ v, L v = Complex.exp (θ * Complex.I) * v) (γ : ℕ × ℕ) :
    (((pdList γ).map L).map fun w => ‖w‖ ^ 2).prod = 1 := by
  rw [List.map_map]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
  simp [hLv, norm_of_mem_pdList hv, Complex.norm_exp_ofReal_mul_I]

/-! ### The `k = 1` rotation identity -/

theorem l2_sq_eq_integral {g : ℂ → ℂ} (hg : MemLp g 2 volume) :
    l2 g ^ 2 = ∫ x, ‖g x‖ ^ 2 := by
  unfold l2
  rw [hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have h0 : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ≥0∞).toReal := integral_nonneg fun x => by positivity
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul h0]
  simp

theorem integrable_norm_sq {g : ℂ → ℂ} (hg : MemLp g 2 volume) :
    Integrable (fun x => ‖g x‖ ^ 2) := by
  have := hg.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
  simpa using this

theorem rot_identity (A B : ℂ) {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    ‖(c : ℂ) * A + (s : ℂ) * B‖ ^ 2 + ‖((-s : ℝ) : ℂ) * A + (c : ℂ) * B‖ ^ 2 =
      ‖A‖ ^ 2 + ‖B‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  linear_combination (A.re ^ 2 + A.im ^ 2 + B.re ^ 2 + B.im ^ 2) * h

theorem l2_rot_identity {A B : ℂ → ℂ} (hA : MemLp A 2 volume) (hB : MemLp B 2 volume)
    {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    l2 (fun x => (c : ℂ) * A x + (s : ℂ) * B x) ^ 2 +
        l2 (fun x => ((-s : ℝ) : ℂ) * A x + (c : ℂ) * B x) ^ 2 =
      l2 A ^ 2 + l2 B ^ 2 := by
  have h1 : MemLp (fun x => (c : ℂ) * A x + (s : ℂ) * B x) 2 volume :=
    (hA.const_mul _).add (hB.const_mul _)
  have h2 : MemLp (fun x => ((-s : ℝ) : ℂ) * A x + (c : ℂ) * B x) 2 volume :=
    (hA.const_mul _).add (hB.const_mul _)
  rw [l2_sq_eq_integral h1, l2_sq_eq_integral h2, l2_sq_eq_integral hA, l2_sq_eq_integral hB,
    ← integral_add (integrable_norm_sq h1) (integrable_norm_sq h2),
    ← integral_add (integrable_norm_sq hA) (integrable_norm_sq hB)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact rot_identity (A x) (B x) h

theorem sum_multiIdx_one (F : ℕ × ℕ → ℝ) :
    ∑ γ ∈ multiIdx 1, F γ = F (0, 0) + F (1, 0) + F (0, 1) := by
  simp [multiIdx, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ]
  ring

theorem hasWeakDerivOn_pdList_zero (f : ℂ → ℂ) : HasWeakDerivOn univ (pdList (0, 0)) f f := by
  have e : pdList (0, 0) = [] := by simp [pdList]
  rw [e]
  intro φ _
  simp

theorem sum_multiIdx_zero (F : ℕ × ℕ → ℝ) : ∑ γ ∈ multiIdx 0, F γ = F (0, 0) := by
  simp [multiIdx, Finset.sum_filter]

theorem normH_zero_eq {f : ℂ → ℂ} (hf : MemLp f 2 volume) : normH 0 f = l2 f := by
  rw [normH_eq, sum_multiIdx_zero, Real.sqrt_sq (l2_nonneg _)]
  exact l2_congr_ae (weakPartial_ae_eq_of hf (hasWeakDerivOn_pdList_zero f))

/-! ### Dilations as changes of variables -/

theorem pow_le_max_one_pow {c : ℝ} {n k : ℕ} (hnk : n ≤ k) :
    |c| ^ n ≤ max 1 (|c| ^ k) := by
  rcases le_total |c| 1 with h | h
  · exact (pow_le_one₀ (abs_nonneg c) h).trans (le_max_left _ _)
  · exact (pow_le_pow_right₀ h hnk).trans (le_max_right _ _)

theorem smul_hasFDerivAt (c : ℝ) (x : ℂ) :
    HasFDerivAt (fun x : ℂ => c • x) (c • ContinuousLinearMap.id ℝ ℂ) x :=
  (hasFDerivAt_id x).const_smul c

theorem smul_inv_contDiff (c : ℝ) : ContDiff ℝ ∞ (fun y : ℂ => c⁻¹ • y) :=
  ContDiff.const_smul c⁻¹ contDiff_id

theorem smul_measurableEmbedding {c : ℝ} (hc : c ≠ 0) :
    MeasurableEmbedding (fun x : ℂ => c • x) :=
  (Homeomorph.smulOfNeZero c hc).measurableEmbedding

theorem smul_map {c : ℝ} (hc : c ≠ 0) :
    Measure.map (fun x : ℂ => c • x) volume = ENNReal.ofReal |(c ^ 2)⁻¹| • volume := by
  have := Measure.map_addHaar_smul (volume : Measure ℂ) hc
  rwa [Complex.finrank_real_complex] at this

theorem smul_nu_ne_zero {c : ℝ} (hc : c ≠ 0) : ENNReal.ofReal |(c ^ 2)⁻¹| ≠ 0 :=
  (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero (pow_ne_zero 2 hc)))).ne'

/-- The dilation package: `H^k` membership, weak derivatives and their `L²` norms. -/
theorem smul_aux {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {c : ℝ} (hc : c ≠ 0) :
    MemH k (fun x => f (c • x)) ∧ ∀ γ ∈ multiIdx k,
      weakPartial γ (fun x => f (c • x)) =ᵐ[volume]
        (fun x => ((c ^ (γ.1 + γ.2) : ℝ) : ℂ) * weakPartial γ f (c • x)) ∧
      l2 (weakPartial γ (fun x => f (c • x))) ^ 2 =
        |(c ^ 2)⁻¹| * (|c| ^ (γ.1 + γ.2)) ^ 2 * l2 (weakPartial γ f) ^ 2 := by
  have hf2 := (memH_iff.1 hf).1
  have hT := smul_hasFDerivAt c
  have hS := smul_inv_contDiff c
  have hST : ∀ x : ℂ, c⁻¹ • (c • x) = x := fun x => inv_smul_smul₀ hc x
  have hTS : ∀ y : ℂ, c • (c⁻¹ • y) = y := fun y => smul_inv_smul₀ hc y
  have hTm := smul_measurableEmbedding hc
  have hmap := smul_map hc
  have hν : ENNReal.ofReal |(c ^ 2)⁻¹| ≠ ⊤ := ENNReal.ofReal_ne_top
  have hd : ∀ γ ∈ multiIdx k,
      MemLp (fun x => ((c ^ (γ.1 + γ.2) : ℝ) : ℂ) * weakPartial γ f x) 2 volume ∧
      HasWeakDerivOn univ ((pdList γ).map ⇑(c • ContinuousLinearMap.id ℝ ℂ)) f
        (fun x => ((c ^ (γ.1 + γ.2) : ℝ) : ℂ) * weakPartial γ f x) := by
    intro γ hγ
    obtain ⟨h1, h2⟩ := memH_spec hf hγ
    refine ⟨h1.const_mul _, ?_⟩
    have e : (pdList γ).map ⇑(c • ContinuousLinearMap.id ℝ ℂ) =
        (pdList γ).map (fun v => c • v) := by
      simp
    rw [e]
    have := hasWeakDerivOn_map_smul h2 c
    rwa [pdList_length] at this
  have hmem : MemH k (fun x => f (c • x)) :=
    transport hf2 hT hS hST hTS hTm hν hmap (fun γ hγ => ⟨_, (hd γ hγ).1, (hd γ hγ).2⟩)
  refine ⟨hmem, fun γ hγ => ⟨?_, ?_⟩⟩
  · exact transport_ae hT hS hST hTS hTm hν hmap (hd γ hγ).1 (hd γ hγ).2
  · rw [transport_l2 hT hS hST hTS hTm (smul_nu_ne_zero hc) hν hmap (hd γ hγ).1 (hd γ hγ).2,
      l2_const_mul, ENNReal.toReal_ofReal (abs_nonneg _), Complex.norm_real, Real.norm_eq_abs,
      abs_pow]
    ring

/-! ### Translations and conjugation -/

theorem add_measurableEmbedding (a : ℂ) : MeasurableEmbedding (fun x : ℂ => x + a) :=
  (Homeomorph.addRight a).measurableEmbedding

theorem add_map (a : ℂ) :
    Measure.map (fun x : ℂ => x + a) volume = (1 : ℝ≥0∞) • volume := by
  rw [one_smul]
  exact map_add_right_eq_self volume a

theorem memLp_conj {g : ℂ → ℂ} (hg : MemLp g 2 volume) :
    MemLp (fun x => conj (g x)) 2 volume :=
  hg.of_le (Complex.continuous_conj.comp_aestronglyMeasurable hg.1)
    (Filter.Eventually.of_forall fun x => by simp)

theorem l2_conj (g : ℂ → ℂ) : l2 (fun x => conj (g x)) = l2 g := by
  unfold l2
  rw [eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => Complex.norm_conj (g x))]

end SymmProof

open SymmAux SymmProof

theorem MemH.comp_rot {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) (θ : ℝ) :
    MemH k (fun x => f (rot θ x)) ∧ normH k (fun x => f (rot θ x)) ≤ 2 ^ k * normH k f := by
  obtain ⟨L, hLv, hL⟩ := exists_rot_deriv θ
  have hf2 := (memH_iff.1 hf).1
  have hdir : ∀ γ ∈ multiIdx k,
      MemLp (weakDerivOn univ ((pdList γ).map L) f) 2 volume ∧
      HasWeakDerivOn univ ((pdList γ).map L) f (weakDerivOn univ ((pdList γ).map L) f) ∧
      l2 (weakDerivOn univ ((pdList γ).map L) f) ^ 2 ≤ 2 ^ (γ.1 + γ.2) *
        ∑ β ∈ (multiIdx k).filter (fun β => β.1 + β.2 = γ.1 + γ.2),
          l2 (weakPartial β f) ^ 2 := by
    intro γ hγ
    have h := dirs hf ((pdList γ).map L) [] (fun u hu => by simp at hu)
      (by simpa [mem_multiIdx] using hγ)
    rw [prod_map_rot_eq_one hLv γ] at h
    simp only [List.nil_append, List.length_nil, zero_add, List.length_map, pdList_length,
      one_mul] at h
    exact h
  have hmem : MemH k (fun x => f (rot θ x)) :=
    transport hf2 hL (rot_contDiff (-θ)) (rot_neg_rot θ) (rot_rot_neg θ)
      (rot_measurableEmbedding θ) ENNReal.one_ne_top (rot_map θ)
      (fun γ hγ => ⟨_, (hdir γ hγ).1, (hdir γ hγ).2.1⟩)
  refine ⟨hmem, ?_⟩
  have hterm : ∀ γ ∈ multiIdx k, l2 (weakPartial γ (fun x => f (rot θ x))) ^ 2 ≤
      2 ^ (γ.1 + γ.2) * ∑ β ∈ (multiIdx k).filter (fun β => β.1 + β.2 = γ.1 + γ.2),
        l2 (weakPartial β f) ^ 2 := by
    intro γ hγ
    rw [transport_l2 hL (rot_contDiff (-θ)) (rot_neg_rot θ) (rot_rot_neg θ)
      (rot_measurableEmbedding θ) one_ne_zero ENNReal.one_ne_top (rot_map θ)
      (hdir γ hγ).1 (hdir γ hγ).2.1]
    simpa using (hdir γ hγ).2.2
  rw [normH_eq, normH_eq]
  have hsum := (Finset.sum_le_sum hterm).trans
    (sum_levels_le k (fun β => l2 (weakPartial β f) ^ 2) (fun β => sq_nonneg _))
  calc Real.sqrt (∑ γ ∈ multiIdx k, l2 (weakPartial γ (fun x => f (rot θ x))) ^ 2)
      ≤ Real.sqrt (4 ^ k * ∑ β ∈ multiIdx k, l2 (weakPartial β f) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = 2 ^ k * Real.sqrt (∑ γ ∈ multiIdx k, l2 (weakPartial γ f) ^ 2) := by
        rw [Real.sqrt_mul (by positivity),
          show (4 : ℝ) ^ k = (2 ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
          Real.sqrt_sq (by positivity)]

/-- For `k ≤ 1` rotations are isometries of `H^k`. -/
theorem MemH.normH_comp_rot_of_le_one {k : ℕ} (hk : k ≤ 1) {f : ℂ → ℂ} (hf : MemH k f)
    (θ : ℝ) : normH k (fun x => f (rot θ x)) = normH k f := by
  have hf2 := (memH_iff.1 hf).1
  interval_cases k
  · have hc := memLp_comp (rot_measurableEmbedding θ) ENNReal.one_ne_top (rot_map θ) hf2
    rw [normH_zero_eq hc, normH_zero_eq hf2]
    unfold l2
    rw [eLpNorm_comp (rot_measurableEmbedding θ) one_ne_zero (rot_map θ)]
    simp
  · obtain ⟨L, hLv, hL⟩ := exists_rot_deriv θ
    have hmem := (hf.comp_rot θ).1
    obtain ⟨hA1, hA2⟩ := memH_spec hf (γ := (1, 0)) (by simp [mem_multiIdx])
    obtain ⟨hB1, hB2⟩ := memH_spec hf (γ := (0, 1)) (by simp [mem_multiIdx])
    set A := weakPartial (1, 0) f
    set B := weakPartial (0, 1) f
    have hA2' : HasWeakDerivOn univ [1] f A := by simpa [pdList] using hA2
    have hB2' : HasWeakDerivOn univ [Complex.I] f B := by simpa [pdList] using hB2
    set c := Real.cos θ
    set s := Real.sin θ
    have hcs : c ^ 2 + s ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    have hL1 : L 1 = c • (1 : ℂ) + s • Complex.I := by
      rw [hLv]
      apply Complex.ext <;> simp [c, s, Complex.mul_re, Complex.mul_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.cos_ofReal_re,
        Complex.sin_ofReal_re]
    have hLI : L Complex.I = (-s) • (1 : ℂ) + c • Complex.I := by
      rw [hLv]
      apply Complex.ext <;> simp [c, s, Complex.mul_re, Complex.mul_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.cos_ofReal_re,
        Complex.sin_ofReal_re]
    have h10 : HasWeakDerivOn univ ((pdList (1, 0)).map L) f
        (fun x => (c : ℂ) * A x + (s : ℂ) * B x) := by
      have e : (pdList (1, 0)).map L = [c • (1 : ℂ) + s • Complex.I] := by simp [pdList, hL1]
      rw [e]
      exact hasWeakDerivOn_cons_add (locInt_of_memLp hf2) (locInt_of_memLp hA1)
        (locInt_of_memLp hB1) c s hA2' hB2'
    have h01 : HasWeakDerivOn univ ((pdList (0, 1)).map L) f
        (fun x => ((-s : ℝ) : ℂ) * A x + (c : ℂ) * B x) := by
      have e : (pdList (0, 1)).map L = [(-s) • (1 : ℂ) + c • Complex.I] := by
        simp [pdList, hLI]
      rw [e]
      exact hasWeakDerivOn_cons_add (locInt_of_memLp hf2) (locInt_of_memLp hA1)
        (locInt_of_memLp hB1) (-s) c hA2' hB2'
    have h00 : HasWeakDerivOn univ ((pdList (0, 0)).map L) f f := by
      have e : (pdList (0, 0)).map L = [] := by simp [pdList]
      rw [e]
      intro φ _
      simp
    have m10 : MemLp (fun x => (c : ℂ) * A x + (s : ℂ) * B x) 2 volume :=
      (hA1.const_mul _).add (hB1.const_mul _)
    have m01 : MemLp (fun x => ((-s : ℝ) : ℂ) * A x + (c : ℂ) * B x) 2 volume :=
      (hA1.const_mul _).add (hB1.const_mul _)
    have t := fun {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx 1) {G : ℂ → ℂ} (hG1 : MemLp G 2 volume)
        (hG2 : HasWeakDerivOn univ ((pdList γ).map L) f G) =>
      transport_l2 hL (rot_contDiff (-θ)) (rot_neg_rot θ) (rot_rot_neg θ)
        (rot_measurableEmbedding θ) one_ne_zero ENNReal.one_ne_top (rot_map θ) hG1 hG2
    have t00 := t (γ := (0, 0)) (by simp [mem_multiIdx]) hf2 h00
    have t10 := t (γ := (1, 0)) (by simp [mem_multiIdx]) m10 h10
    have t01 := t (γ := (0, 1)) (by simp [mem_multiIdx]) m01 h01
    have f00 : l2 (weakPartial (0, 0) f) = l2 f :=
      l2_congr_ae (weakPartial_ae_eq_of hf2 (hasWeakDerivOn_pdList_zero f))
    simp only [ENNReal.toReal_one, one_mul] at t00 t10 t01
    rw [normH_eq, normH_eq, sum_multiIdx_one, sum_multiIdx_one, t00, t10, t01, f00,
      add_assoc, l2_rot_identity hA1 hB1 hcs, ← add_assoc]

theorem MemH.comp_smul {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {c : ℝ} (hc : c ≠ 0) :
    MemH k (fun x => f (c • x)) ∧
      normH k (fun x => f (c • x)) ≤ |c|⁻¹ * max 1 (|c| ^ k) * normH k f := by
  obtain ⟨hmem, hγ⟩ := smul_aux hf hc
  refine ⟨hmem, ?_⟩
  set M := max 1 (|c| ^ k)
  have hM : 0 ≤ |c|⁻¹ * M :=
    mul_nonneg (inv_nonneg.2 (abs_nonneg c)) (zero_le_one.trans (le_max_left _ _))
  have hterm : ∀ γ ∈ multiIdx k, l2 (Sob.weakPartial γ (fun x => f (c • x))) ^ 2 ≤
      (|c|⁻¹ * M) ^ 2 * l2 (Sob.weakPartial γ f) ^ 2 := by
    intro γ hγk
    rw [(hγ γ hγk).2]
    have hn : |c| ^ (γ.1 + γ.2) ≤ M := pow_le_max_one_pow (mem_multiIdx.1 hγk)
    calc |(c ^ 2)⁻¹| * (|c| ^ (γ.1 + γ.2)) ^ 2 * l2 (Sob.weakPartial γ f) ^ 2
        = (|c|⁻¹) ^ 2 * (|c| ^ (γ.1 + γ.2)) ^ 2 * l2 (Sob.weakPartial γ f) ^ 2 := by
          rw [abs_inv, abs_pow, inv_pow]
      _ ≤ (|c|⁻¹) ^ 2 * M ^ 2 * l2 (Sob.weakPartial γ f) ^ 2 := by
          gcongr
      _ = (|c|⁻¹ * M) ^ 2 * l2 (Sob.weakPartial γ f) ^ 2 := by ring
  rw [normH_eq, normH_eq]
  calc Real.sqrt (∑ γ ∈ multiIdx k, l2 (Sob.weakPartial γ (fun x => f (c • x))) ^ 2)
      ≤ Real.sqrt ((|c|⁻¹ * M) ^ 2 * ∑ γ ∈ multiIdx k, l2 (Sob.weakPartial γ f) ^ 2) := by
        rw [Finset.mul_sum]
        exact Real.sqrt_le_sqrt (Finset.sum_le_sum hterm)
    _ = |c|⁻¹ * M * Real.sqrt (∑ γ ∈ multiIdx k, l2 (Sob.weakPartial γ f) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM]

/-- Weak derivatives of a dilation: `∂^γ (f(c ·)) = c^{|γ|} (∂^γ f)(c ·)`. -/
theorem MemH.weakPartial_comp_smul {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {c : ℝ} (hc : c ≠ 0)
    {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    weakPartial γ (fun x => f (c • x)) =ᵐ[volume]
      fun x => ((c ^ (γ.1 + γ.2) : ℝ) : ℂ) * weakPartial γ f (c • x) :=
  ((smul_aux hf hc).2 γ hγ).1

theorem MemH.comp_add {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) (a : ℂ) :
    MemH k (fun x => f (x + a)) ∧ normH k (fun x => f (x + a)) = normH k f := by
  have hf2 := (memH_iff.1 hf).1
  have hT : ∀ x : ℂ, HasFDerivAt (fun x : ℂ => x + a) (ContinuousLinearMap.id ℝ ℂ) x :=
    fun x => (hasFDerivAt_id x).add_const a
  have hS : ContDiff ℝ ∞ (fun y : ℂ => y - a) := contDiff_id.sub contDiff_const
  have hST : ∀ x : ℂ, x + a - a = x := fun x => add_sub_cancel_right x a
  have hTS : ∀ y : ℂ, y - a + a = y := fun y => sub_add_cancel y a
  have hTm := add_measurableEmbedding a
  have hmap := add_map a
  have hd : ∀ γ ∈ multiIdx k, MemLp (Sob.weakPartial γ f) 2 volume ∧
      HasWeakDerivOn univ ((pdList γ).map ⇑(ContinuousLinearMap.id ℝ ℂ)) f
        (Sob.weakPartial γ f) := by
    intro γ hγ
    obtain ⟨h1, h2⟩ := memH_spec hf hγ
    refine ⟨h1, ?_⟩
    simpa using h2
  have hmem : MemH k (fun x => f (x + a)) :=
    transport hf2 hT hS hST hTS hTm ENNReal.one_ne_top hmap
      (fun γ hγ => ⟨_, (hd γ hγ).1, (hd γ hγ).2⟩)
  refine ⟨hmem, ?_⟩
  rw [normH_eq, normH_eq]
  congr 1
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [transport_l2 hT hS hST hTS hTm one_ne_zero ENNReal.one_ne_top hmap (hd γ hγ).1
    (hd γ hγ).2]
  simp

theorem MemH.conj {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) :
    MemH k (fun x => conj (f x)) ∧ normH k (fun x => conj (f x)) = normH k f := by
  have hf2 := (memH_iff.1 hf).1
  have hmem : MemH k (fun x => conj (f x)) :=
    memH_iff.2 ⟨memLp_conj hf2, fun γ hγ =>
      ⟨_, memLp_conj (memH_spec hf hγ).1, hasWeakDerivOn_conj (memH_spec hf hγ).2⟩⟩
  refine ⟨hmem, ?_⟩
  rw [normH_eq, normH_eq]
  congr 1
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [l2_congr_ae (weakPartial_ae_eq_of (memLp_conj (memH_spec hf hγ).1)
    (hasWeakDerivOn_conj (memH_spec hf hγ).2)), l2_conj]

end NonUniqueEuler.Sob
