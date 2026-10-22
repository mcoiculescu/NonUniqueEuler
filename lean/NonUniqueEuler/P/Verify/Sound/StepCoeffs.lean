import NonUniqueEuler.Defs.Verify.Encl
import NonUniqueEuler.I.Verify.TaylorCoef
import NonUniqueEuler.I.Verify.TaylorRecurrence
import NonUniqueEuler.I.Verify.ProfileBasic
import NonUniqueEuler.I.Verify.ProfileOmega

/-!
# Proof: Proposition A.3, step (iii): the coefficients `V_k` and `Ψ_k`

Proof of `NonUniqueEuler/I/Verify/Sound/StepCoeffs.lean` (same declarations, statements copied
verbatim). Manuscript: proof of Proposition A.3 (`prop:enclosure`), step (iii)
(`A_verification.tex:404-412` and `428-430`). Code: `Verify/Comp/Evans.lean` (`stepCoeffs`,
`psiCoeffs`).

Used black boxes: `taylorCoeff_add`, `taylorCoeff_const`, `taylorCoeff_const_mul`,
`taylorCoeff_mul`, `taylorCoeff_ofReal` (`I/Verify/TaylorCoef`); `taylorCoeff_inv`,
`taylorCoeff_ode2` (`I/Verify/TaylorRecurrence`); `contDiff_prof`,
`taylorCoeff_deriv_prof_eq` (`I/Verify/ProfileBasic`); `contDiff_gInt`,
`add_I_mul_ofReal_ne_zero` (`I/Verify/ProfileOmega`). The containment facts of the code's
operations are the proved lemmas of `Defs/Verify/{Sem,SemOps,SemCInv}.lean`.

The proof follows the manuscript: with `D = λ + iℓ(g e^{-2ξ} + G e^{-2ξ})` (written
`D = u·i + λ`, `u = (g e^{-2ξ} + G e^{-2ξ})ℓ` real) and `R = 1/D`, the code's arrays enclose
`D_k`, `R_k` (reciprocal recurrence) and `V_k = iℓ Σ_{r≤k} (ϖ')_r R_{k-r} + ℓ²[k=0]`; the
recurrences built by `buildArray` are handled by one invariant principle
(`buildArray_inv_getD`), which is a strong induction on the index.
-/

noncomputable section

open Set
open scoped ContDiff

namespace NonUniqueEuler.Verify

open AppA RingData

/-! ### Array helpers -/

private theorem getD_eq_getElem' {α : Type} (a : Array α) {i : ℕ} (h : i < a.size) (d : α) :
    a.getD i d = a[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some]

private theorem getD_ofFn' {α : Type} {n : ℕ} (f : Fin n → α) {i : ℕ} (h : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  rw [getD_eq_getElem' _ (by simpa using h), Array.getElem_ofFn]

/-- Invariant principle for `buildArray` (strong induction on the index): if every entry of
the initial array satisfies `P`, and `step a` satisfies `P` at index `a.size` whenever every
entry of `a` does (for the sizes that occur), then every entry of the result satisfies `P`. -/
private theorem buildArray_inv {α : Type} (P : ℕ → α → Prop) (step : Array α → α) :
    ∀ (arr : Array α) (n : ℕ), (∀ m (hm : m < arr.size), P m arr[m]) →
    (∀ a : Array α, arr.size ≤ a.size → a.size < arr.size + n →
      (∀ m (hm : m < a.size), P m a[m]) → P a.size (step a)) →
    ∀ m (hm : m < (buildArray step arr n).size), P m (buildArray step arr n)[m]
  | arr, 0, h0, _ => h0
  | arr, n + 1, h0, hstep => by
    have h0' : ∀ m (hm : m < (arr.push (step arr)).size), P m (arr.push (step arr))[m] := by
      intro m hm
      rw [Array.size_push] at hm
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | h
      · rw [Array.getElem_push_lt h]; exact h0 m h
      · subst h; rw [Array.getElem_push_eq]; exact hstep arr le_rfl (by omega) h0
    exact buildArray_inv P step (arr.push (step arr)) n h0' fun a h1 h2 ha =>
      hstep a (by rw [Array.size_push] at h1; omega) (by rw [Array.size_push] at h2; omega) ha

/-- `buildArray_inv`, in the `getD` form in which the code reads its arrays. -/
private theorem buildArray_inv_getD {α : Type} (P : ℕ → α → Prop) (step : Array α → α)
    (arr : Array α) (n : ℕ) (d : α) (h0 : ∀ m < arr.size, P m (arr.getD m d))
    (hstep : ∀ a : Array α, arr.size ≤ a.size → a.size < arr.size + n →
      (∀ m < a.size, P m (a.getD m d)) → P a.size (step a)) :
    ∀ m < arr.size + n, P m ((buildArray step arr n).getD m d) := by
  intro m hm
  have hs : m < (buildArray step arr n).size := by rw [size_buildArray]; exact hm
  rw [getD_eq_getElem' _ hs]
  refine buildArray_inv P step arr n (fun m hm => ?_) (fun a h1 h2 ha => ?_) m hs
  · have := h0 m hm; rwa [getD_eq_getElem' _ hm] at this
  · exact hstep a h1 h2 fun m hm => by rw [getD_eq_getElem' _ hm]; exact ha m hm

/-! ### Taylor-coefficient helpers -/

private theorem taylorCoeff_add_const' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} (hg : ContDiff ℝ ∞ g) (c : F) (k : ℕ) (x : ℝ) :
    taylorCoeff (fun y => g y + c) k x = taylorCoeff g k x + if k = 0 then c else 0 := by
  rcases k with _ | k
  · simp [taylorCoeff_zero]
  · rw [taylorCoeff_add (g := fun _ => c) hg contDiff_const,
      taylorCoeff_const c (Nat.succ_ne_zero k)]
    simp

private theorem contDiff_ofReal_comp {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun y => (u y : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hu

private theorem taylorCoeff_ofReal_mul_I {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (k : ℕ) (x : ℝ) :
    taylorCoeff (fun y => (u y : ℂ) * Complex.I) k x = ((taylorCoeff u k x : ℝ) : ℂ) * Complex.I := by
  have h1 : (fun y => (u y : ℂ) * Complex.I) = fun y => Complex.I * (u y : ℂ) := by
    funext y; ring
  rw [h1, taylorCoeff_const_mul (contDiff_ofReal_comp hu) Complex.I, taylorCoeff_ofReal hu,
    mul_comm]

private theorem taylorCoeff_one' (f : ℝ → ℂ) (x : ℝ) : taylorCoeff f 1 x = deriv f x := by
  simp [taylorCoeff, iteratedDeriv_one]

/-! ### The coefficients `V_k` -/

/-- **The coefficients `V_k`** (`_step_coeffs`): from enclosures of the coefficients of
`g e^{-2ξ}`, `e^{-2ξ}` and `(AB)'` on `S ⊆ [ξa, ξb]`, `λ ∈ lam` with `Re λ > 0` and `G ∈ Gb`,
the array `stepCoeffs` encloses the Taylor coefficients `V_k(ξ)`, `k < N`, of the coefficient
`V = ℓ² + iℓϖ'/(λ + iℓΩ_G)` of the Evans equation at every `ξ ∈ S`. -/
theorem stepCoeffs_sound {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {p ℓ : ℕ} {lam : CBox}
    {Gb : Ball} {z : ℂ} (hz : z ∈ lam) (hz0 : 0 < z.re) {G : ℝ} (hG : G ∈ Gb) {S : Set ℝ}
    (hS : S ⊆ Icc ξa ξb) {N : ℕ} {Omg em2 fs : ℕ → Ball}
    (hO : CoeffEncl (omegaFn χ) S N Omg)
    (hE : CoeffEncl (fun x => Real.exp (-2 * x)) S N em2)
    (hF : CoeffEncl (deriv profW) S N fs) :
    CoeffEnclC (riccatiCoeff χ ℓ z G) S N
      fun k => (stepCoeffs p lam Gb ℓ Omg em2 fs N).getD k CBox.zero := by
  intro ξ hξ k hk
  have hξab : ξ ∈ Icc ξa ξb := hS hξ
  have hN : 0 < N := by omega
  -- smoothness
  have hexp : ContDiff ℝ ∞ (fun x : ℝ => Real.exp (-2 * x)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have homg : ContDiff ℝ ∞ (omegaFn χ) := (contDiff_gInt hχ).mul hexp
  have hOm : ContDiff ℝ ∞ (fun y => omegaFn χ y + G * Real.exp (-2 * y)) :=
    homg.add (contDiff_const.mul hexp)
  -- `u = (g e^{-2ξ} + G e^{-2ξ}) ℓ`
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ → ℝ, u = fun x => (omegaFn χ x + G * Real.exp (-2 * x)) * ℓ :=
    ⟨_, rfl⟩
  have hu : ContDiff ℝ ∞ u := by rw [hu_def]; exact hOm.mul contDiff_const
  have hu_k : ∀ j, taylorCoeff u j ξ =
      (taylorCoeff (omegaFn χ) j ξ + G * taylorCoeff (fun x => Real.exp (-2 * x)) j ξ) * ℓ := by
    intro j
    have e1 : u = fun y => (ℓ : ℝ) * (omegaFn χ y + G * Real.exp (-2 * y)) := by
      rw [hu_def]; funext y; ring
    rw [e1, taylorCoeff_const_mul hOm, taylorCoeff_add homg (contDiff_const.mul hexp),
      taylorCoeff_const_mul hexp]
    ring
  -- `D = u i + λ`
  obtain ⟨Dfun, hD_def⟩ : ∃ D : ℝ → ℂ, D = fun x => (u x : ℂ) * Complex.I + z := ⟨_, rfl⟩
  have hD_eq : ∀ x, Dfun x = z + Complex.I * (ℓ : ℂ) * ((OmegaG χ G x : ℝ) : ℂ) := by
    intro x
    simp only [hD_def, hu_def, OmegaG_eq_omegaFn]
    push_cast; ring
  have hD : ContDiff ℝ ∞ Dfun := by
    rw [hD_def]; exact ((contDiff_ofReal_comp hu).mul contDiff_const).add contDiff_const
  have hDne : ∀ x, Dfun x ≠ 0 := fun x => by
    rw [hD_eq]; exact add_I_mul_ofReal_ne_zero hz0 ℓ _
  have hD_k : ∀ j, taylorCoeff Dfun j ξ =
      ((taylorCoeff u j ξ : ℝ) : ℂ) * Complex.I + if j = 0 then z else 0 := by
    intro j
    rw [hD_def, taylorCoeff_add_const' ((contDiff_ofReal_comp hu).mul contDiff_const) z j ξ,
      taylorCoeff_ofReal_mul_I hu]
  -- `R = 1/D`
  obtain ⟨Rfun, hR_def⟩ : ∃ R : ℝ → ℂ, R = fun x => (Dfun x)⁻¹ := ⟨_, rfl⟩
  have hR : ContDiff ℝ ∞ Rfun := by rw [hR_def]; exact hD.inv hDne
  -- `V = iℓ (ϖ' R) + ℓ²`
  have hdp : ContDiff ℝ ∞ (deriv (prof χ)) := (contDiff_infty_iff_deriv.mp (contDiff_prof hχ)).2
  have hdpC : ContDiff ℝ ∞ (fun x => ((deriv (prof χ) x : ℝ) : ℂ)) := contDiff_ofReal_comp hdp
  have hV_eq : riccatiCoeff χ ℓ z G = fun x =>
      (Complex.I * (ℓ : ℂ)) * (((deriv (prof χ) x : ℝ) : ℂ) * Rfun x) + (ℓ : ℂ) ^ 2 := by
    funext x
    simp only [riccatiCoeff, hR_def]
    rw [← hD_eq x]
    ring
  have hV_k : taylorCoeff (riccatiCoeff χ ℓ z G) k ξ =
      Complex.I * ((∑ r ∈ Finset.range (k + 1),
        ((taylorCoeff (deriv profW) r ξ : ℝ) : ℂ) * taylorCoeff Rfun (k - r) ξ) * (ℓ : ℂ)) +
        if k = 0 then (((ℓ * ℓ : ℕ) : ℝ) : ℂ) else 0 := by
    rw [hV_eq, taylorCoeff_add_const' (contDiff_const.mul (hdpC.mul hR)),
      taylorCoeff_const_mul (hdpC.mul hR), taylorCoeff_mul hdpC hR]
    simp_rw [taylorCoeff_ofReal hdp, taylorCoeff_deriv_prof_eq hχ hξab]
    split_ifs <;> push_cast <;> ring
  -- the code
  show taylorCoeff (riccatiCoeff χ ℓ z G) k ξ ∈
    (stepCoeffs p lam Gb ℓ Omg em2 fs N).getD k CBox.zero
  unfold stepCoeffs
  extract_lets D Dk R0 R
  -- the coefficients `D_j`
  have hDk : ∀ j < N, taylorCoeff Dfun j ξ ∈ Dk j := by
    intro j hj
    simp only [Dk, D]
    rw [getD_ofFn' _ hj]
    dsimp only
    rw [hD_k j, hu_k j]
    have hb := Ball.mem_mulNat (p := p)
      (Ball.mem_add (p := p) (hO ξ hξ j hj) (Ball.mem_mul (p := p) hG (hE ξ hξ j hj))) ℓ
    split_ifs with hj0
    · exact CBox.mem_add (CBox.mem_ofIm hb) hz
    · rw [add_zero]; exact CBox.mem_ofIm hb
  -- `R_0`
  have hR0 : (Dfun ξ)⁻¹ ∈ R0 := by
    have h := hDk 0 hN
    rw [taylorCoeff_zero] at h
    exact CBox.mem_invTight h
  -- the coefficients `R_j`
  have hRk : ∀ j < N, taylorCoeff Rfun j ξ ∈ R.getD j CBox.zero := by
    intro j hj
    simp only [R]
    refine buildArray_inv_getD (fun m x => taylorCoeff Rfun m ξ ∈ x) _ #[R0] (N - 1) CBox.zero
      ?_ ?_ j (by simp; omega)
    · intro m hm
      simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add,
        Nat.lt_one_iff] at hm
      subst hm
      simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_cons_zero,
        Option.getD_some]
      rw [taylorCoeff_zero, hR_def]
      exact hR0
    · intro a h1 h2 ha
      simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add] at h1 h2
      obtain ⟨K, hK⟩ : ∃ K, a.size = K + 1 := ⟨a.size - 1, by omega⟩
      try dsimp only
      rw [hK]
      have hrec : taylorCoeff Rfun (K + 1) ξ = -((Dfun ξ)⁻¹ *
          (taylorCoeff Dfun 1 ξ * taylorCoeff Rfun (K + 1 - 1) ξ +
            ∑ i ∈ Finset.range (K + 1 - 1),
              taylorCoeff Dfun (2 + i) ξ * taylorCoeff Rfun (K + 1 - (2 + i)) ξ)) := by
        rw [hR_def, taylorCoeff_inv hD hDne K ξ, Finset.sum_range_succ']
        have hsum : ∑ i ∈ Finset.range (K + 1 - 1), taylorCoeff Dfun (2 + i) ξ *
              taylorCoeff (fun y => (Dfun y)⁻¹) (K + 1 - (2 + i)) ξ =
            ∑ i ∈ Finset.range K, taylorCoeff Dfun (i + 1 + 1) ξ *
              taylorCoeff (fun y => (Dfun y)⁻¹) (K - (i + 1)) ξ := by
          rw [Nat.add_sub_cancel]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show 2 + i = i + 1 + 1 by omega, show K + 1 - (i + 1 + 1) = K - (i + 1) by omega]
        rw [hsum, Nat.add_sub_cancel]
        simp only [zero_add, Nat.sub_zero]
        ring
      rw [hrec]
      refine CBox.mem_neg (CBox.mem_mul hR0 ?_)
      refine CBox.mem_foldSum
        (y := fun j => taylorCoeff Dfun j ξ * taylorCoeff Rfun (K + 1 - j) ξ)
        (CBox.mem_mul (hDk 1 (by omega)) (ha _ (by omega))) fun i hi => ?_
      exact CBox.mem_mul (hDk (2 + i) (by omega)) (ha _ (by omega))
  -- `V_k`
  rw [getD_ofFn' _ hk]
  dsimp only
  rw [hV_k]
  have hsum := CBox.mem_cauchyBC (p := p) (a := fs) (b := fun j => R.getD j CBox.zero)
    (x := fun i => taylorCoeff (deriv profW) i ξ) (w := fun i => taylorCoeff Rfun i ξ) (k := k)
    (fun i hi => hF ξ hξ i (by omega)) (fun i hi => hRk i (by omega))
  have hs := CBox.mem_mulI (CBox.mem_mulNat (p := p) hsum ℓ)
  split_ifs with hk0
  · exact CBox.mem_addBall hs (Ball.mem_ofNat _)
  · rw [add_zero]; exact hs

/-! ### The coefficients `Ψ_k` -/

/-- **The coefficients `Ψ_k`** (`_psi_coeffs`): for a smooth solution of `ψ'' = Vψ` and a point
`ξ` at which `Q` encloses `V_k(ξ)` (`k < N`), `p0 ∋ ψ(ξ)` and `p1 ∋ ψ'(ξ)`, the array
`psiCoeffs` encloses `ψ_k(ξ)` for `k ≤ N + 1`. -/
theorem psiCoeffs_sound {p : ℕ} {ψ V : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hV : ContDiff ℝ ∞ V)
    (hode : ∀ x, deriv (deriv ψ) x = V x * ψ x) {ξ : ℝ} {N : ℕ} {Q : Array CBox}
    {p0 p1 : CBox} (hQ : ∀ k < N, taylorCoeff V k ξ ∈ Q.getD k CBox.zero)
    (h0 : ψ ξ ∈ p0) (h1 : deriv ψ ξ ∈ p1) :
    ∀ k < N + 2, taylorCoeff ψ k ξ ∈ (psiCoeffs p Q p0 p1 N).getD k CBox.zero := by
  intro k hk
  unfold psiCoeffs
  refine buildArray_inv_getD (fun m x => taylorCoeff ψ m ξ ∈ x) _ #[p0, p1] N CBox.zero
    ?_ ?_ k (by simp; omega)
  · intro m hm
    simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add] at hm
    interval_cases m
    · simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_cons_zero,
        Option.getD_some]
      rw [taylorCoeff_zero]; exact h0
    · simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some]
      rw [taylorCoeff_one']; exact h1
  · intro a h1a h2a ha
    simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add] at h1a h2a
    obtain ⟨K, hK⟩ : ∃ K, a.size = K + 2 := ⟨a.size - 2, by omega⟩
    try dsimp only
    rw [hK, Nat.add_sub_cancel]
    have hrec := taylorCoeff_ode2 hψ hV hode K ξ
    have hc : (((K + 1) * (K + 2) : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (K + 1) * (K + 2) ≠ 0)
    have e : taylorCoeff ψ (K + 2) ξ =
        (∑ r ∈ Finset.range (K + 1), taylorCoeff V r ξ * taylorCoeff ψ (K - r) ξ) /
          (((K + 1) * (K + 2) : ℕ) : ℂ) := by
      rw [eq_div_iff hc, ← hrec]; push_cast; ring
    rw [e]
    exact CBox.mem_divNat (CBox.mem_cauchy (x := fun r => taylorCoeff V r ξ)
      (y := fun r => taylorCoeff ψ r ξ) (fun i hi => hQ i (by omega))
      (fun i hi => ha i (by omega))) _

end NonUniqueEuler.Verify
