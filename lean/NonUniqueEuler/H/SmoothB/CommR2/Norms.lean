import NonUniqueEuler.H.SmoothB.CommR2.Calc
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.Defs.Sec2.Conventions

/-!
# Helper for `lem:comm-R2`: Sobolev norms of smooth functions, computed classically

Helper of `P/SmoothB/CommR2.lean` (`B_global_smooth.tex:149-175`, step 5 of the proof sketch of
`I/SmoothB/CommR2.lean`). For a smooth function the chosen weak derivatives are the classical
ones a.e. (uniqueness of locally integrable weak derivatives, `I/Infra/Sobolev/WeakDeriv.lean`;
the argument follows `H/Sec2/BSSmooth/Weak.lean`), so
* `‖f‖²_{H^k} = ∑_{|γ| ≤ k} ‖∂^γ f‖²_{L²}` (`normH_eq_of_smooth`) and
* `‖∇u‖²_{H^k} = ∑_l ∑_{|γ| ≤ k} ‖∂^{γ+e_l} u‖²_{L²}` (`gradNormH_sq_eq`),
with no integrability hypothesis (if a derivative is not in `L²`, both sides use the junk
value `0` in the same way). From these:
* `l2_partialD_le_normH`: `‖∂^γ f‖_{L²} ≤ ‖f‖_{H^k}` for `|γ| ≤ k`;
* `normH_one_partialD_le`: `‖∂^γ f‖_{H¹} ≤ ‖f‖_{H^k}` for `|γ| + 1 ≤ k`;
* `l2_partialD_le_gradNormH`: `‖∂^β u‖_{L²} ≤ ‖∇u‖_{H^k}` for `1 ≤ |β| ≤ k + 1`;
* `normH_one_partialD_le_gradNormH`: `‖∂^β u‖_{H¹} ≤ ‖∇u‖_{H^k}` for `1 ≤ |β| ≤ k`;
* `memH_of_smooth`: a smooth function with `∂^γ f ∈ L²` for `|γ| ≤ k` is in `H^k`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal

namespace NonUniqueEuler.Smooth.CommR2Aux

open Sob

/-- The chosen weak derivative of an a.e. modification of a smooth `G` is the classical one. -/
theorem weakPartial_ae_eq_of_ae_eq_smooth {W G : ℂ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hWG : W =ᵐ[volume] G) (γ : ℕ × ℕ) : weakPartial γ W =ᵐ[volume] partialD γ G := by
  have hc : ContDiffOn ℝ ((pdList γ).length : ℕ) G univ :=
    (hG.of_le (by exact_mod_cast le_top)).contDiffOn
  have h1 : HasWeakDerivOn univ (pdList γ) G (iterDirDeriv (pdList γ) G) :=
    hasWeakDerivOn_of_contDiffOn isOpen_univ le_rfl hc
  have h2 : HasWeakDerivOn univ (pdList γ) W (iterDirDeriv (pdList γ) G) := by
    refine h1.congr_ae ?_ (Eventually.of_forall fun x _ => rfl)
    filter_upwards [hWG] with x hx using fun _ => hx.symm
  have := weakDerivOn_ae_eq isOpen_univ
    ((contDiff_iterDirDeriv hG _).continuous.locallyIntegrable.locallyIntegrableOn _) h2
  filter_upwards [this] with x hx using hx (mem_univ x)

theorem normH_eq_of_ae_eq_smooth {W G : ℂ → ℂ} (hG : ContDiff ℝ ∞ G) (hWG : W =ᵐ[volume] G)
    (k : ℕ) : normH k W = Real.sqrt (∑ γ ∈ multiIdx k, l2 (partialD γ G) ^ 2) := by
  rw [normH_eq]
  congr 1
  refine Finset.sum_congr rfl fun γ _ => ?_
  congr 1
  unfold l2
  rw [eLpNorm_congr_ae (weakPartial_ae_eq_of_ae_eq_smooth hG hWG γ)]

/-- `‖f‖_{H^k}` of a smooth function, computed with classical derivatives. -/
theorem normH_eq_of_smooth {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    normH k f = Real.sqrt (∑ γ ∈ multiIdx k, l2 (partialD γ f) ^ 2) :=
  normH_eq_of_ae_eq_smooth hf (EventuallyEq.refl _ _) k

/-- The unit multi-index `e_l`. -/
def unitIdx (l : Fin 2) : ℕ × ℕ := if l = 0 then (1, 0) else (0, 1)

theorem pdList_unitIdx (l : Fin 2) : pdList (unitIdx l) = [Prelim.e2 l] := by
  fin_cases l <;> simp [unitIdx, pdList, Prelim.e2]

theorem unitIdx_size (l : Fin 2) : (unitIdx l).1 + (unitIdx l).2 = 1 := by
  fin_cases l <;> simp [unitIdx]

theorem partialD_unitIdx (l : Fin 2) (h : ℂ → ℂ) :
    partialD (unitIdx l) h = dirDeriv (Prelim.e2 l) h := by
  simp [partialD, pdList_unitIdx]

/-- Every `β ≠ 0` is `γ + e_l` for some `l`. -/
theorem exists_eq_add_unitIdx {β : ℕ × ℕ} (hβ : 1 ≤ β.1 + β.2) :
    ∃ l : Fin 2, ∃ γ : ℕ × ℕ, β = γ + unitIdx l := by
  rcases Nat.eq_zero_or_pos β.1 with h | h
  · refine ⟨1, (β.1, β.2 - 1), ?_⟩
    ext <;> simp [unitIdx]; omega
  · refine ⟨0, (β.1 - 1, β.2), ?_⟩
    ext <;> simp [unitIdx]; omega

theorem gradNormH_nonneg (k : ℕ) (u : ℂ → ℂ) : 0 ≤ Prelim.gradNormH k u :=
  Real.sqrt_nonneg _

/-- `‖∇u‖²_{H^k} = ∑_l ∑_{|γ| ≤ k} ‖∂^{γ+e_l} u‖²_{L²}` for smooth `u`. -/
theorem gradNormH_sq_eq {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u) (k : ℕ) :
    Prelim.gradNormH k u ^ 2 =
      ∑ l : Fin 2, ∑ γ ∈ multiIdx k, l2 (partialD (γ + unitIdx l) u) ^ 2 := by
  have key : ∀ l : Fin 2, normH k (weakPartial (unitIdx l) u) ^ 2 =
      ∑ γ ∈ multiIdx k, l2 (partialD (γ + unitIdx l) u) ^ 2 := by
    intro l
    have hG : ContDiff ℝ ∞ (partialD (unitIdx l) u) := contDiff_partialD hu _
    have hW := weakPartial_ae_eq_of_ae_eq_smooth hu (EventuallyEq.refl _ u) (unitIdx l)
    rw [normH_eq_of_ae_eq_smooth hG hW, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [partialD_partialD hu]
  rw [Prelim.gradNormH, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)), Fin.sum_univ_two,
    ← key 0, ← key 1]
  rfl

/-- Reindexing a sum over `multiIdx j` by `δ ↦ δ + γ` into `multiIdx k`. -/
theorem sum_multiIdx_add_le {F : ℕ × ℕ → ℝ} (hF : ∀ δ, 0 ≤ F δ) {j k : ℕ} {γ : ℕ × ℕ}
    (h : j + (γ.1 + γ.2) ≤ k) :
    ∑ δ ∈ multiIdx j, F (δ + γ) ≤ ∑ δ ∈ multiIdx k, F δ := by
  rw [← Finset.sum_image (g := fun δ => δ + γ) (fun a _ b _ hab => add_right_cancel hab)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hF _
  intro δ hδ
  simp only [Finset.mem_image] at hδ
  obtain ⟨d, hd, rfl⟩ := hδ
  rw [mem_multiIdx] at hd ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- `‖∂^γ f‖_{L²} ≤ ‖f‖_{H^k}` for smooth `f` and `|γ| ≤ k`. -/
theorem l2_partialD_le_normH {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) {k : ℕ} {γ : ℕ × ℕ}
    (hγ : γ.1 + γ.2 ≤ k) : l2 (partialD γ f) ≤ normH k f := by
  rw [normH_eq_of_smooth hf]
  exact Real.le_sqrt_of_sq_le
    (Finset.single_le_sum (f := fun γ => l2 (partialD γ f) ^ 2) (fun _ _ => sq_nonneg _)
      (mem_multiIdx.2 hγ))

/-- `‖∂^γ f‖_{H¹} ≤ ‖f‖_{H^k}` for smooth `f` and `|γ| + 1 ≤ k`. -/
theorem normH_one_partialD_le {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) {k : ℕ} {γ : ℕ × ℕ}
    (hγ : γ.1 + γ.2 + 1 ≤ k) : normH 1 (partialD γ f) ≤ normH k f := by
  rw [normH_eq_of_smooth (contDiff_partialD hf γ), normH_eq_of_smooth hf]
  refine Real.sqrt_le_sqrt ?_
  have h := sum_multiIdx_add_le (F := fun δ => l2 (partialD δ f) ^ 2) (fun _ => sq_nonneg _)
    (j := 1) (k := k) (γ := γ) (by omega)
  refine le_of_eq_of_le (Finset.sum_congr rfl fun δ _ => ?_) h
  rw [partialD_partialD hf]

theorem sum_le_gradNormH_sq {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u) (k : ℕ) (l : Fin 2) :
    ∑ γ ∈ multiIdx k, l2 (partialD (γ + unitIdx l) u) ^ 2 ≤ Prelim.gradNormH k u ^ 2 := by
  rw [gradNormH_sq_eq hu]
  exact Finset.single_le_sum
    (f := fun l => ∑ γ ∈ multiIdx k, l2 (partialD (γ + unitIdx l) u) ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ l)

/-- `‖∂^β u‖_{L²} ≤ ‖∇u‖_{H^k}` for smooth `u` and `1 ≤ |β| ≤ k + 1`. -/
theorem l2_partialD_le_gradNormH {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u) {k : ℕ} {β : ℕ × ℕ}
    (hβ1 : 1 ≤ β.1 + β.2) (hβ2 : β.1 + β.2 ≤ k + 1) :
    l2 (partialD β u) ≤ Prelim.gradNormH k u := by
  obtain ⟨l, γ, rfl⟩ := exists_eq_add_unitIdx hβ1
  have hl := unitIdx_size l
  simp only [Prod.fst_add, Prod.snd_add] at hβ2
  have h1 : l2 (partialD (γ + unitIdx l) u) ^ 2 ≤ Prelim.gradNormH k u ^ 2 :=
    le_trans (Finset.single_le_sum (f := fun γ => l2 (partialD (γ + unitIdx l) u) ^ 2)
      (fun _ _ => sq_nonneg _) (mem_multiIdx.2 (by omega))) (sum_le_gradNormH_sq hu k l)
  exact (pow_le_pow_iff_left₀ (l2_nonneg _) (gradNormH_nonneg _ _) two_ne_zero).1 h1

/-- `‖∂^β u‖_{H¹} ≤ ‖∇u‖_{H^k}` for smooth `u` and `1 ≤ |β| ≤ k`. -/
theorem normH_one_partialD_le_gradNormH {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u) {k : ℕ}
    {β : ℕ × ℕ} (hβ1 : 1 ≤ β.1 + β.2) (hβ2 : β.1 + β.2 ≤ k) :
    normH 1 (partialD β u) ≤ Prelim.gradNormH k u := by
  obtain ⟨l, γ, rfl⟩ := exists_eq_add_unitIdx hβ1
  have hl := unitIdx_size l
  simp only [Prod.fst_add, Prod.snd_add] at hβ2
  have hs := normH_eq_of_smooth (contDiff_partialD hu (γ + unitIdx l)) 1
  have h1 : normH 1 (partialD (γ + unitIdx l) u) ^ 2 ≤ Prelim.gradNormH k u ^ 2 := by
    rw [hs, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    have h := sum_multiIdx_add_le (F := fun δ => l2 (partialD (δ + unitIdx l) u) ^ 2)
      (fun _ => sq_nonneg _) (j := 1) (k := k) (γ := γ) (by omega)
    refine le_trans (le_of_eq_of_le (Finset.sum_congr rfl fun δ _ => ?_) h)
      (sum_le_gradNormH_sq hu k l)
    rw [partialD_partialD hu, add_assoc]
  exact (pow_le_pow_iff_left₀ (normH_nonneg _ _) (gradNormH_nonneg _ _) two_ne_zero).1 h1

/-- A smooth function whose classical derivatives of order `≤ k` are in `L²` lies in `H^k`. -/
theorem memH_of_smooth {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) {k : ℕ}
    (hL2 : ∀ γ ∈ multiIdx k, MemLp (partialD γ f) 2 volume) : MemH k f := by
  rw [memH_iff]
  refine ⟨by simpa [partialD, pdList] using hL2 (0, 0) (zero_mem_multiIdx k), fun γ hγ => ?_⟩
  refine ⟨partialD γ f, hL2 γ hγ, ?_⟩
  exact hasWeakDerivOn_of_contDiffOn isOpen_univ le_rfl
    (hf.of_le (by exact_mod_cast le_top)).contDiffOn

end NonUniqueEuler.Smooth.CommR2Aux
