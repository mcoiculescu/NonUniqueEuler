import NonUniqueEuler.H.Sec5.Quiet.Approx.DuhamelFn

/-!
# Helpers for `quiet_approx`: the hierarchy `w^{[j]}` (definitions and combinatorics)

Helper of `P/Sec5/Quiet/Approx.lean` (fully proved). Namespace `NonUniqueEuler.OneRing.QAppH`.
Manuscript `05_single_ring.tex:466-473`: `w^{[1]} = wlin`, and for `j ≥ 2`
`w^{[j]}(t) = ∫₀ᵗ e^{(t-τ)L} g^{[j]}(τ) dτ`, `g^{[j]} = Σ_{i+l=j} B(w^{[i]},w^{[l]}) - h·∇w^{[j-1]}`,
built at level `k_j = M_h - j` (here `K - j`).

* `pairs j`: the pairs `(i,l)`, `i, l ≥ 1`, `i + l = j`;
* `gStep`, `wStep`, `hist`: one step of the recursion and the history of the first `n` terms
  (a simple recursion on `n`, so no well-founded recursion is needed);
* `hw j = w^{[j]}`, `hg j = g^{[j]}` (`g^{[1]} = F = -h·∇Φ`), with the fixed-point equation
  `hw_eq : w^{[j]} = ∫ e^{(t-τ)L} g^{[j]}` for `j ≥ 1`;
* the combinatorial identities of the residual (`05_single_ring.tex:497-506`).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.QAppH

open Sect Sob RingData

/-- The pairs `(i, l)` with `i, l ≥ 1` and `i + l = j`. -/
def pairs (j : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico 1 j ×ˢ Finset.Ico 1 j).filter fun p => p.1 + p.2 = j

theorem mem_pairs {j : ℕ} {p : ℕ × ℕ} :
    p ∈ pairs j ↔ 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 + p.2 = j := by
  simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico]
  omega

theorem card_pairs_le (j : ℕ) : (pairs j).card ≤ (j - 1) * (j - 1) := by
  refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
  rw [Finset.card_product, Nat.card_Ico]

/-- One step of the recursion: `g^{[j]}` from the earlier terms `W`. -/
def gStep (χ : ℝ → ℝ) (h : ℝ → ℂ → ℂ) (W : ℕ → ℝ → ℂ → ℂ) (j : ℕ) (τ : ℝ) : ℂ → ℂ :=
  if j = 1 then forcing χ h τ else
    (∑ p ∈ pairs j, Bfn (W p.1 τ) (W p.2 τ)) - hGrad (h τ) (W (j - 1) τ)

/-- One step of the recursion: `w^{[j]} = ∫ e^{(t-τ)L} g^{[j]}` at level `K - j`. -/
def wStep (χ : ℝ → ℝ) (K : ℕ) (G : ℝ) (h : ℝ → ℂ → ℂ) (W : ℕ → ℝ → ℂ → ℂ) (j : ℕ) :
    ℝ → ℂ → ℂ :=
  duhFn χ (K - j) G (gStep χ h W j)

/-- The first `n` terms of the hierarchy (`hist n j = w^{[j]}` for `j ≤ n`). -/
def hist (χ : ℝ → ℝ) (K : ℕ) (G : ℝ) (h : ℝ → ℂ → ℂ) : ℕ → ℕ → ℝ → ℂ → ℂ
  | 0 => fun _ => 0
  | n + 1 => fun j => if j = n + 1 then wStep χ K G h (hist χ K G h n) j else hist χ K G h n j

/-- `w^{[j]}`. -/
def hw (χ : ℝ → ℝ) (K : ℕ) (G : ℝ) (h : ℝ → ℂ → ℂ) (j : ℕ) : ℝ → ℂ → ℂ :=
  hist χ K G h j j

/-- `g^{[j]}`. -/
def hg (χ : ℝ → ℝ) (K : ℕ) (G : ℝ) (h : ℝ → ℂ → ℂ) (j : ℕ) : ℝ → ℂ → ℂ :=
  gStep χ h (hw χ K G h) j

theorem hist_eq (χ : ℝ → ℝ) (K : ℕ) (G : ℝ) (h : ℝ → ℂ → ℂ) :
    ∀ n j, j ≤ n → hist χ K G h n j = hw χ K G h j := by
  intro n
  induction n with
  | zero =>
    intro j hj
    have : j = 0 := by omega
    subst this
    rfl
  | succ n ih =>
    intro j hj
    rcases Nat.lt_or_ge j (n + 1) with h1 | h1
    · have hne : j ≠ n + 1 := by omega
      show (if j = n + 1 then wStep χ K G h (hist χ K G h n) j else hist χ K G h n j) = _
      simp only [hne, ↓reduceIte]
      exact ih j (by omega)
    · have : j = n + 1 := by omega
      subst this
      rfl

theorem gStep_congr {χ : ℝ → ℝ} {h : ℝ → ℂ → ℂ} {W W' : ℕ → ℝ → ℂ → ℂ} {j : ℕ} (hj : 1 ≤ j)
    (hWW : ∀ i, 1 ≤ i → i < j → W i = W' i) : gStep χ h W j = gStep χ h W' j := by
  funext τ
  unfold gStep
  split_ifs with h1
  · rfl
  · have hs : ∑ p ∈ pairs j, Bfn (W p.1 τ) (W p.2 τ) =
        ∑ p ∈ pairs j, Bfn (W' p.1 τ) (W' p.2 τ) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨h1', h2', h3'⟩ := mem_pairs.1 hp
      rw [hWW p.1 h1' (by omega), hWW p.2 h2' (by omega)]
    rw [hs, hWW (j - 1) (by omega) (by omega)]

/-- The fixed-point equation of the hierarchy. -/
theorem hw_eq (χ : ℝ → ℝ) (K : ℕ) (G : ℝ) (h : ℝ → ℂ → ℂ) {j : ℕ} (hj : 1 ≤ j) :
    hw χ K G h j = duhFn χ (K - j) G (hg χ K G h j) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  show (if n + 1 = n + 1 then wStep χ K G h (hist χ K G h n) (n + 1)
    else hist χ K G h n (n + 1)) = _
  simp only [↓reduceIte]
  unfold wStep hg
  rw [gStep_congr hj fun i hi1 hi2 => hist_eq χ K G h n i (by omega)]

theorem hg_one (χ : ℝ → ℝ) (K : ℕ) (G : ℝ) (h : ℝ → ℂ → ℂ) :
    hg χ K G h 1 = forcing χ h := by
  funext τ
  simp [hg, gStep]

theorem hg_of_two_le (χ : ℝ → ℝ) (K : ℕ) (G : ℝ) (h : ℝ → ℂ → ℂ) {j : ℕ} (hj : 2 ≤ j)
    (τ : ℝ) : hg χ K G h j τ =
      (∑ p ∈ pairs j, Bfn (hw χ K G h p.1 τ) (hw χ K G h p.2 τ)) -
        hGrad (h τ) (hw χ K G h (j - 1) τ) := by
  simp only [hg, gStep, show j ≠ 1 by omega, ↓reduceIte]

/-! ### Combinatorics of the residual -/

/-- `Σ_{j=2}^{N} Σ_{i+l=j} f(i,l) = Σ_{i,l ≤ N, i+l ≤ N} f(i,l)`. -/
theorem sum_pairs_eq {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ × ℕ → M) :
    ∑ j ∈ Finset.Ioc 1 N, ∑ p ∈ pairs j, f p =
      ∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N : Finset (ℕ × ℕ)).filter
        (fun p : ℕ × ℕ => p.1 + p.2 ≤ N), f p := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.Ioc 1 N) (g := fun p : ℕ × ℕ => p.1 + p.2)]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ioc] at hj
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [mem_pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    simp only [Finset.mem_Ioc]
    omega

/-- `Σ_{j=2}^{N} f(j-1) = Σ_{l=1}^{N-1} f(l)`. -/
theorem sum_Ioc_pred {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    ∑ j ∈ Finset.Ioc 1 N, f (j - 1) = ∑ l ∈ Finset.Ico 1 N, f l := by
  refine Finset.sum_nbij' (fun j => j - 1) (fun l => l + 1) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Ioc, Finset.mem_Ico] at hj ⊢
    omega
  · intro l hl
    simp only [Finset.mem_Ioc, Finset.mem_Ico] at hl ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Ioc] at hj
    omega
  · intro l _
    omega
  · intro j _
    rfl

end NonUniqueEuler.OneRing.QAppH
