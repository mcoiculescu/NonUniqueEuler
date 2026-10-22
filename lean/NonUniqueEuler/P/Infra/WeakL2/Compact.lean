import NonUniqueEuler.Defs.Infra.WeakL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Proof of the interface I-WEAKL2 (`I/Infra/WeakL2/Compact.lean`)

Weak sequential compactness and diagonal extraction. Same declarations, same statements as the
interface file; see its docstring for the description and the manuscript consumers
(`03_compactness.tex`: `lem:weak-cont`, `prop:compact`; `prop:stable`; `lem:velocity`(b)).

Proof structure.
* `exists_diagonal_subseq`: the nested subsequences `nestSeq ψ k` (`φ_0 = ψ_0`,
  `φ_{k+1} = φ_k ∘ ψ_{k+1}`) and the diagonal `n ↦ φ_n n`. For `n ≥ k` the diagonal takes values
  in `range φ_k`, so it is `φ_k ∘ θ` eventually, for a strictly monotone `θ`
  (`exists_strictMono_reindex`).
* `exists_subseq_tendsto_forall`: diagonal extraction + Bolzano–Weierstrass
  (`tendsto_subseq_of_bounded`).
* `exists_tendsto_inner_of_dense`: under a bound, convergence of `⟪u i, d⟫` on a dense set gives
  convergence of `⟪u i, y⟫` for all `y` (Cauchy filter in `ℝ`).
* `exists_weakTendsto_of_dense_aux`: the limit functional is linear, bounded by `M`, and is
  represented by a vector (Riesz, `InnerProductSpace.toDual`).
* `exists_subseq_weakTendsto`: extract a subsequence along which `⟪u (φ n), u k⟫` converges for
  every `k`; the set of `y` with `⟪u (φ n), y⟫` convergent is a submodule containing
  `S = span (range u)` and `Sᗮ`, and `S ⊔ Sᗮ` is dense.
-/

noncomputable section

open Filter Topology Set
open scoped InnerProductSpace

namespace NonUniqueEuler.WeakL2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Diagonal extraction -/

/-- The nested subsequences built from a choice function `ψ`:
`nestSeq ψ 0 = ψ 0 id`, `nestSeq ψ (k + 1) = nestSeq ψ k ∘ ψ (k + 1) (nestSeq ψ k)`. -/
private def nestSeq (ψ : ℕ → (ℕ → ℕ) → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => ψ 0 id
  | k + 1 => nestSeq ψ k ∘ ψ (k + 1) (nestSeq ψ k)

/-- Re-indexing: if `φ` and `f` are strictly monotone, `φ k = f k` and `φ n ∈ range f` for all
`n ≥ k`, then `φ = f ∘ θ` on `[k, ∞)` for a strictly monotone `θ`. -/
private lemma exists_strictMono_reindex {φ f : ℕ → ℕ} (hφ : StrictMono φ) (hf : StrictMono f)
    (k : ℕ) (hk : φ k = f k) (hr : ∀ n, k ≤ n → ∃ m, f m = φ n) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ n, k ≤ n → φ n = f (θ n) := by
  choose! g hg using hr
  refine ⟨fun n => if k ≤ n then g n else n, ?_, ?_⟩
  · refine strictMono_nat_of_lt_succ fun n => ?_
    by_cases h : k ≤ n
    · have h1 : k ≤ n + 1 := h.trans n.le_succ
      simp only [h, h1, ↓reduceIte]
      rw [← hf.lt_iff_lt, hg n h, hg (n + 1) h1]
      exact hφ n.lt_succ_self
    · simp only [h, ↓reduceIte]
      by_cases h1 : k ≤ n + 1
      · simp only [h1, ↓reduceIte]
        have hkn : k = n + 1 := by omega
        subst hkn
        have : g (n + 1) = n + 1 := hf.injective (by rw [hg _ le_rfl, hk])
        omega
      · simp only [h1, ↓reduceIte]
        omega
  · intro n hn
    simp only [hn, ↓reduceIte, hg n hn]

/-- **Diagonal extraction.** Let `Q k φ` be countably many properties of subsequences `φ`, each
stable under passing to a further subsequence (`hsub`) and under changing finitely many terms
(`htail`). If every subsequence has a further subsequence with property `Q k` (`hex`), then
some subsequence has all the properties `Q k`. -/
theorem exists_diagonal_subseq (Q : ℕ → (ℕ → ℕ) → Prop)
    (htail : ∀ (k : ℕ) (φ ψ : ℕ → ℕ), Q k φ → (∀ᶠ n in atTop, φ n = ψ n) → Q k ψ)
    (hsub : ∀ (k : ℕ) (φ ψ : ℕ → ℕ), Q k φ → StrictMono ψ → Q k (φ ∘ ψ))
    (hex : ∀ (k : ℕ) (φ : ℕ → ℕ), StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Q k (φ ∘ ψ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, Q k φ := by
  choose! ψ hψm hψQ using hex
  have hmono : ∀ k, StrictMono (nestSeq ψ k) := by
    intro k
    induction k with
    | zero => exact hψm 0 id strictMono_id
    | succ k ih => exact ih.comp (hψm (k + 1) _ ih)
  have hQ : ∀ k, Q k (nestSeq ψ k) := by
    intro k
    cases k with
    | zero => exact hψQ 0 id strictMono_id
    | succ k => exact hψQ (k + 1) _ (hmono k)
  have hrange : ∀ k n, k ≤ n → ∀ m, ∃ m', nestSeq ψ k m' = nestSeq ψ n m := by
    intro k n hkn
    induction n, hkn using Nat.le_induction with
    | base => exact fun m => ⟨m, rfl⟩
    | succ n _ ih => exact fun m => ih _
  have hdiag : StrictMono fun n => nestSeq ψ n n := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    show nestSeq ψ n n < nestSeq ψ n (ψ (n + 1) (nestSeq ψ n) (n + 1))
    exact hmono n (lt_of_lt_of_le n.lt_succ_self ((hψm (n + 1) _ (hmono n)).id_le _))
  refine ⟨fun n => nestSeq ψ n n, hdiag, fun k => ?_⟩
  obtain ⟨θ, hθ, hθeq⟩ := exists_strictMono_reindex hdiag (hmono k) k rfl
    (fun n hn => hrange k n hn n)
  refine htail k _ _ (hsub k _ θ (hQ k) hθ) ?_
  filter_upwards [eventually_ge_atTop k] with n hn
  exact (hθeq n hn).symm

/-- **Bolzano–Weierstrass, diagonal form.** Countably many bounded real sequences have a common
subsequence along which all of them converge. -/
theorem exists_subseq_tendsto_forall (a : ℕ → ℕ → ℝ) (ha : ∀ k, ∃ M, ∀ n, |a k n| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, ∃ c : ℝ, Tendsto (fun n => a k (φ n)) atTop (𝓝 c) := by
  refine exists_diagonal_subseq
    (fun k φ => ∃ c : ℝ, Tendsto (fun n => a k (φ n)) atTop (𝓝 c)) ?_ ?_ ?_
  · rintro k φ ψ ⟨c, hc⟩ hφψ
    refine ⟨c, hc.congr' ?_⟩
    filter_upwards [hφψ] with n hn
    rw [hn]
  · rintro k φ ψ ⟨c, hc⟩ hψ
    exact ⟨c, hc.comp hψ.tendsto_atTop⟩
  · intro k φ _
    obtain ⟨M, hM⟩ := ha k
    obtain ⟨c, -, ψ, hψ, hc⟩ := tendsto_subseq_of_bounded (x := fun n => a k (φ n))
      (Metric.isBounded_Icc (-M) M) (fun n => abs_le.mp (hM (φ n)))
    exact ⟨ψ, hψ, c, hc⟩

/-! ### Weak limits from a dense set -/

/-- Under a uniform bound, convergence of `⟪u i, d⟫` for `d` in a dense set implies convergence of
`⟪u i, y⟫` for every `y`: the image filter is Cauchy. -/
private lemma exists_tendsto_inner_of_dense {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → E} {M : ℝ} (hu : ∀ᶠ i in l, ‖u i‖ ≤ M) {D : Set E} (hD : Dense D)
    (h : ∀ y ∈ D, ∃ c : ℝ, Tendsto (fun i => ⟪u i, y⟫_ℝ) l (𝓝 c)) (y : E) :
    ∃ c : ℝ, Tendsto (fun i => ⟪u i, y⟫_ℝ) l (𝓝 c) := by
  rw [← cauchy_map_iff_exists_tendsto, Metric.cauchy_iff]
  refine ⟨inferInstance, fun ε hε => ?_⟩
  have hM1 : 0 < |M| + 1 := by positivity
  set δ := ε / (4 * (|M| + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hMδ' : (|M| + 1) * δ = ε / 4 := by
    rw [hδ]
    field_simp
  have hMδ : |M| * δ < ε / 4 := by
    have : (|M| + 1) * δ = |M| * δ + δ := by ring
    linarith
  obtain ⟨d, hdD, hyd⟩ := hD.exists_dist_lt y hδpos
  obtain ⟨c, hc⟩ := h d hdD
  have hc' := (Metric.tendsto_nhds.mp hc) (ε / 4) (by positivity)
  refine ⟨(fun i => ⟪u i, y⟫_ℝ) '' {i | ‖u i‖ ≤ M ∧ dist ⟪u i, d⟫_ℝ c < ε / 4},
    image_mem_map (hu.and hc'), ?_⟩
  have key : ∀ k, ‖u k‖ ≤ M → |⟪u k, y⟫_ℝ - ⟪u k, d⟫_ℝ| ≤ |M| * δ := by
    intro k hk
    rw [← inner_sub_right]
    calc |⟪u k, y - d⟫_ℝ| ≤ ‖u k‖ * ‖y - d‖ := abs_real_inner_le_norm _ _
      _ ≤ |M| * δ := by
        refine mul_le_mul (hk.trans (le_abs_self M)) ?_ (norm_nonneg _) (abs_nonneg _)
        rw [← dist_eq_norm]
        exact hyd.le
  rintro _ ⟨i, ⟨hi1, hi2⟩, rfl⟩ _ ⟨j, ⟨hj1, hj2⟩, rfl⟩
  rw [Real.dist_eq] at hi2 hj2 ⊢
  have ki := abs_le.mp (key i hi1)
  have kj := abs_le.mp (key j hj1)
  have li := abs_lt.mp hi2
  have lj := abs_lt.mp hj2
  rw [abs_lt]
  constructor <;> linarith [ki.1, ki.2, kj.1, kj.2, li.1, li.2, lj.1, lj.2]

/-- Existence of the weak limit (auxiliary form, used before its public restatement
`exists_weakTendsto_of_dense` below). -/
private lemma exists_weakTendsto_of_dense_aux [CompleteSpace E] {ι : Type*} {l : Filter ι}
    [l.NeBot] {u : ι → E} {M : ℝ} (hu : ∀ᶠ i in l, ‖u i‖ ≤ M) {D : Set E} (hD : Dense D)
    (h : ∀ y ∈ D, ∃ c : ℝ, Tendsto (fun i => ⟪u i, y⟫_ℝ) l (𝓝 c)) :
    ∃ x : E, ‖x‖ ≤ M ∧ WeakTendsto u l x := by
  choose c hc using exists_tendsto_inner_of_dense hu hD h
  have hM : 0 ≤ M := by
    obtain ⟨i, hi⟩ := hu.exists
    exact (norm_nonneg _).trans hi
  let f : E →ₗ[ℝ] ℝ :=
    { toFun := c
      map_add' := fun y z => tendsto_nhds_unique (hc (y + z))
        (by simpa only [inner_add_right] using (hc y).add (hc z))
      map_smul' := fun r y => tendsto_nhds_unique (hc (r • y))
        (by simpa only [real_inner_smul_right, smul_eq_mul, RingHom.id_apply] using
          (hc y).const_mul r) }
  have hbound : ∀ y, ‖f y‖ ≤ M * ‖y‖ := by
    intro y
    refine le_of_tendsto (hc y).norm ?_
    filter_upwards [hu] with i hi
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  let F : StrongDual ℝ E := f.mkContinuous M hbound
  refine ⟨(InnerProductSpace.toDual ℝ E).symm F, ?_, ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le f hM hbound
  · intro y
    rw [InnerProductSpace.toDual_symm_apply]
    exact hc y

/-! ### Weak sequential compactness -/

/-- **Weak sequential compactness** of closed balls of a real Hilbert space. -/
theorem exists_subseq_weakTendsto [CompleteSpace E] {u : ℕ → E} {M : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : E, ‖x‖ ≤ M ∧ WeakTendsto (u ∘ φ) atTop x := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hu 0)
  obtain ⟨φ, hφ, hconv⟩ := exists_subseq_tendsto_forall (fun k n => ⟪u n, u k⟫_ℝ)
    (fun k => ⟨M * M, fun n =>
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (hu n) (hu k) (norm_nonneg _) hM)⟩)
  -- the submodule of the `y` along which the inner products converge
  let C : Submodule ℝ E :=
    { carrier := {y | ∃ c : ℝ, Tendsto (fun n => ⟪u (φ n), y⟫_ℝ) atTop (𝓝 c)}
      add_mem' := by
        rintro y z ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, by simpa only [inner_add_right] using ha.add hb⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r y ⟨a, ha⟩
        exact ⟨r * a, by simpa only [real_inner_smul_right] using ha.const_mul r⟩ }
  let S : Submodule ℝ E := Submodule.span ℝ (range u)
  have hSC : S ≤ C := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hconv k
  have hSoC : Sᗮ ≤ C := by
    intro y hy
    refine ⟨0, ?_⟩
    have h0 : ∀ n, ⟪u (φ n), y⟫_ℝ = 0 := fun n =>
      Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (mem_range_self (φ n)) : u (φ n) ∈ S) hy
    simp only [h0]
    exact tendsto_const_nhds
  have hdense : Dense ((S ⊔ Sᗮ : Submodule ℝ E) : Set E) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      ← Submodule.inf_orthogonal]
    exact Sᗮ.inf_orthogonal_eq_bot
  obtain ⟨x, hx, hw⟩ := exists_weakTendsto_of_dense_aux (l := atTop) (u := u ∘ φ) (M := M)
    (Eventually.of_forall fun n => hu _) hdense (fun y hy => sup_le hSC hSoC hy)
  exact ⟨φ, hφ, x, hx, hw⟩

/-- Weak sequential compactness for countably many bounded sequences at once (diagonal
extraction, e.g. over a countable set of times). -/
theorem exists_subseq_weakTendsto_forall [CompleteSpace E] (u : ℕ → ℕ → E) (M : ℕ → ℝ)
    (hu : ∀ k n, ‖u k n‖ ≤ M k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : ℕ → E,
      ∀ k, ‖x k‖ ≤ M k ∧ WeakTendsto (fun n => u k (φ n)) atTop (x k) := by
  let Q : ℕ → (ℕ → ℕ) → Prop := fun k φ =>
    ∃ x : E, ‖x‖ ≤ M k ∧ WeakTendsto (fun n => u k (φ n)) atTop x
  have htail : ∀ (k : ℕ) (φ ψ : ℕ → ℕ), Q k φ → (∀ᶠ n in atTop, φ n = ψ n) → Q k ψ := by
    rintro k φ ψ ⟨x, hx, hw⟩ hφψ
    refine ⟨x, hx, fun y => (hw y).congr' ?_⟩
    filter_upwards [hφψ] with n hn
    rw [hn]
  have hsub : ∀ (k : ℕ) (φ ψ : ℕ → ℕ), Q k φ → StrictMono ψ → Q k (φ ∘ ψ) := by
    rintro k φ ψ ⟨x, hx, hw⟩ hψ
    exact ⟨x, hx, hw.subseq hψ⟩
  have hex : ∀ (k : ℕ) (φ : ℕ → ℕ), StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Q k (φ ∘ ψ) := by
    intro k φ _
    obtain ⟨ψ, hψ, x, hx, hw⟩ :=
      exists_subseq_weakTendsto (u := fun n => u k (φ n)) (M := M k) (fun n => hu k (φ n))
    exact ⟨ψ, hψ, x, hx, hw⟩
  obtain ⟨φ, hφ, hQ⟩ := exists_diagonal_subseq Q htail hsub hex
  choose x hx using hQ
  exact ⟨φ, hφ, x, hx⟩

/-- A bounded family converges weakly to `x` as soon as `⟪u i, y⟫ → ⟪x, y⟫` for `y` in a dense
set. -/
theorem weakTendsto_of_dense {ι : Type*} {l : Filter ι} {u : ι → E} {x : E} {M : ℝ}
    (hu : ∀ᶠ i in l, ‖u i‖ ≤ M) {D : Set E} (hD : Dense D)
    (h : ∀ y ∈ D, Tendsto (fun i => ⟪u i, y⟫_ℝ) l (𝓝 ⟪x, y⟫_ℝ)) :
    WeakTendsto u l x := by
  intro y
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hA : 0 < |M| + ‖x‖ + 1 := by positivity
  set δ := ε / (2 * (|M| + ‖x‖ + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hAδ' : (|M| + ‖x‖ + 1) * δ = ε / 2 := by
    rw [hδ]
    field_simp
  have hAδ : (|M| + ‖x‖) * δ < ε / 2 := by
    have : (|M| + ‖x‖ + 1) * δ = (|M| + ‖x‖) * δ + δ := by ring
    linarith
  obtain ⟨d, hdD, hyd⟩ := hD.exists_dist_lt y hδpos
  have h2 := Metric.tendsto_nhds.mp (h d hdD) (ε / 2) (by positivity)
  filter_upwards [hu, h2] with i hi1 hi2
  rw [Real.dist_eq] at hi2 ⊢
  have e : ⟪u i, y⟫_ℝ - ⟪x, y⟫_ℝ = ⟪u i - x, y - d⟫_ℝ + (⟪u i, d⟫_ℝ - ⟪x, d⟫_ℝ) := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  have b : |⟪u i - x, y - d⟫_ℝ| ≤ (|M| + ‖x‖) * δ := by
    calc |⟪u i - x, y - d⟫_ℝ| ≤ ‖u i - x‖ * ‖y - d‖ := abs_real_inner_le_norm _ _
      _ ≤ (|M| + ‖x‖) * δ := by
        refine mul_le_mul ((norm_sub_le _ _).trans ?_) ?_ (norm_nonneg _) (by positivity)
        · linarith [le_abs_self M]
        · rw [← dist_eq_norm]
          exact hyd.le
  rw [e]
  have b' := abs_le.mp b
  have l' := abs_lt.mp hi2
  rw [abs_lt]
  constructor <;> linarith [b'.1, b'.2, l'.1, l'.2]

/-- **Existence of the weak limit.** A bounded family whose inner products with the vectors of a
dense set converge has a weak limit, of norm `≤ M` (Riesz representation). -/
theorem exists_weakTendsto_of_dense [CompleteSpace E] {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → E} {M : ℝ} (hu : ∀ᶠ i in l, ‖u i‖ ≤ M) {D : Set E} (hD : Dense D)
    (h : ∀ y ∈ D, ∃ c : ℝ, Tendsto (fun i => ⟪u i, y⟫_ℝ) l (𝓝 c)) :
    ∃ x : E, ‖x‖ ≤ M ∧ WeakTendsto u l x :=
  exists_weakTendsto_of_dense_aux hu hD h

end NonUniqueEuler.WeakL2
