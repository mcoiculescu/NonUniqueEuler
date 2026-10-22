import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `lem:comm-R2`: classical calculus of iterated directional derivatives

Helper of `P/SmoothB/CommR2.lean` (`B_global_smooth.tex:149-175`). For smooth functions on the
plane:
* directional derivatives commute, so `iterDirDeriv vs f` depends only on `vs` up to
  permutation (`iterDirDeriv_perm`; the proof is copied from `P/Infra/Sobolev/WeakDeriv.lean`,
  where it is a private helper of another proof);
* `∂^γ ∂^δ f = ∂^{γ+δ} f` (`partialD_partialD`), and every list of directions in `{1, i}` is a
  permutation of some `pdList β` (`exists_perm_pdList`);
* the Leibniz formula in "subset" form (`iterDirDeriv_mul`):
  `∂_{vs}(a h) = a ∂_{vs} h + ∑_{(w₁,w₂) ∈ splitsPos vs} ∂_{w₁} a ∂_{w₂} h`, where `splitsPos vs`
  lists the splittings of `vs` into a nonempty sublist `w₁` and its complement `w₂`; there are
  `2^{|vs|} - 1` of them (`length_splitsPos`). This replaces the multi-index form
  `∑_{0<β≤α} C(α,β) ∂^β a ∂^{α-β} h` of the manuscript (`C(α,β)` counts the sublists);
* `∂_{vs}(L ∘ f) = L ∘ ∂_{vs} f` for a real-linear `L : ℂ →L[ℝ] ℂ` (real and imaginary parts).
-/

noncomputable section

open scoped ContDiff

namespace NonUniqueEuler.Smooth.CommR2Aux

open Sob

/-! ### Smoothness and commutation (copied from `P/Infra/Sobolev/WeakDeriv.lean`) -/

theorem contDiff_dirDeriv {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (v : ℂ) :
    ContDiff ℝ ∞ (dirDeriv v φ) :=
  (ContDiff.fderiv_right (m := ∞) h (by simp)).clm_apply contDiff_const

theorem contDiff_iterDirDeriv {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (vs : List ℂ) :
    ContDiff ℝ ∞ (iterDirDeriv vs φ) := by
  induction vs with
  | nil => simpa using h
  | cons v vs ih => simpa using contDiff_dirDeriv ih v

theorem contDiff_partialD {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (γ : ℕ × ℕ) :
    ContDiff ℝ ∞ (partialD γ φ) :=
  contDiff_iterDirDeriv h _

theorem differentiable_iterDirDeriv {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (vs : List ℂ) :
    Differentiable ℝ (iterDirDeriv vs φ) :=
  (contDiff_iterDirDeriv h vs).differentiable (by simp)

theorem dirDeriv_dirDeriv_eq {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (v w x : ℂ) :
    dirDeriv v (dirDeriv w φ) x = fderiv ℝ (fderiv ℝ φ) x v w := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (ContDiff.fderiv_right (m := ∞) h (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun y => fderiv ℝ φ y w) ((fderiv ℝ (fderiv ℝ φ) x).flip w) x := by
    have := (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
    simpa using this
  show fderiv ℝ (fun y => fderiv ℝ φ y w) x v = _
  rw [hx.fderiv]
  rfl

theorem dirDeriv_comm {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (v w : ℂ) :
    dirDeriv v (dirDeriv w φ) = dirDeriv w (dirDeriv v φ) := by
  funext x
  rw [dirDeriv_dirDeriv_eq h, dirDeriv_dirDeriv_eq h]
  exact (h.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

/-- For smooth `φ`, `iterDirDeriv vs φ` only depends on `vs` up to permutation. -/
theorem iterDirDeriv_perm {vs ws : List ℂ} (hp : vs.Perm ws) {φ : ℂ → ℂ}
    (h : ContDiff ℝ ∞ φ) : iterDirDeriv vs φ = iterDirDeriv ws φ := by
  induction hp with
  | nil => rfl
  | cons x _ ih => simp only [iterDirDeriv_cons, ih]
  | swap x y l =>
    simp only [iterDirDeriv_cons]
    exact dirDeriv_comm (contDiff_iterDirDeriv h l) y x
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### Multi-indices and lists of directions -/

theorem pdList_add_perm (γ δ : ℕ × ℕ) : (pdList γ ++ pdList δ).Perm (pdList (γ + δ)) := by
  simp only [pdList, Prod.fst_add, Prod.snd_add, List.replicate_add, List.append_assoc]
  refine List.Perm.append_left _ ?_
  have h := (List.perm_append_comm (l₁ := List.replicate γ.2 Complex.I)
    (l₂ := List.replicate δ.1 (1 : ℂ))).append_right (List.replicate δ.2 Complex.I)
  simpa only [List.append_assoc] using h

/-- `∂^γ ∂^δ f = ∂^{γ+δ} f` for smooth `f`. -/
theorem partialD_partialD {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (γ δ : ℕ × ℕ) :
    partialD γ (partialD δ f) = partialD (γ + δ) f := by
  simp only [partialD]
  rw [← iterDirDeriv_append]
  exact iterDirDeriv_perm (pdList_add_perm γ δ) hf

theorem mem_pdList {γ : ℕ × ℕ} {v : ℂ} (hv : v ∈ pdList γ) : v = 1 ∨ v = Complex.I := by
  simp only [pdList, List.mem_append, List.mem_replicate] at hv
  rcases hv with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2

/-- A list of directions in `{1, i}` is a permutation of `pdList β`, `|β| = |w|`. -/
theorem exists_perm_pdList {w : List ℂ} (hw : ∀ v ∈ w, v = 1 ∨ v = Complex.I) :
    ∃ β : ℕ × ℕ, w.Perm (pdList β) ∧ β.1 + β.2 = w.length := by
  induction w with
  | nil => exact ⟨(0, 0), by simp [pdList], rfl⟩
  | cons v w ih =>
    obtain ⟨β, hβ, hl⟩ := ih (fun x hx => hw x (by simp [hx]))
    rcases hw v (by simp) with rfl | rfl
    · refine ⟨(β.1 + 1, β.2), ?_, by simp; omega⟩
      simp only [pdList, List.replicate_succ, List.cons_append]
      exact hβ.cons 1
    · refine ⟨(β.1, β.2 + 1), ?_, by simp; omega⟩
      simp only [pdList, List.replicate_succ]
      exact (hβ.cons _).trans List.perm_middle.symm

/-! ### Linearity and the Leibniz rule -/

theorem dirDeriv_add {f₁ f₂ : ℂ → ℂ} (h₁ : Differentiable ℝ f₁) (h₂ : Differentiable ℝ f₂)
    (v : ℂ) : dirDeriv v (fun x => f₁ x + f₂ x) = fun x => dirDeriv v f₁ x + dirDeriv v f₂ x := by
  funext x
  simp only [dirDeriv]
  rw [fderiv_fun_add (h₁ x) (h₂ x)]
  rfl

theorem dirDeriv_mul {a h : ℂ → ℂ} (ha : Differentiable ℝ a) (hh : Differentiable ℝ h)
    (v : ℂ) : dirDeriv v (fun x => a x * h x) =
      fun x => dirDeriv v a x * h x + a x * dirDeriv v h x := by
  funext x
  simp only [dirDeriv]
  rw [fderiv_fun_mul (ha x) (hh x)]
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem iterDirDeriv_add {f₁ f₂ : ℂ → ℂ} (h₁ : ContDiff ℝ ∞ f₁) (h₂ : ContDiff ℝ ∞ f₂)
    (vs : List ℂ) : iterDirDeriv vs (fun x => f₁ x + f₂ x) =
      fun x => iterDirDeriv vs f₁ x + iterDirDeriv vs f₂ x := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [iterDirDeriv_cons, ih, dirDeriv_add (differentiable_iterDirDeriv h₁ vs)
      (differentiable_iterDirDeriv h₂ vs)]
    rfl

theorem dirDeriv_listSum {ι : Type*} (L : List ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i ∈ L, Differentiable ℝ (F i)) (v : ℂ) :
    Differentiable ℝ (fun x => (L.map (fun i => F i x)).sum) ∧
      dirDeriv v (fun x => (L.map (fun i => F i x)).sum) =
        fun x => (L.map (fun i => dirDeriv v (F i) x)).sum := by
  induction L with
  | nil =>
    refine ⟨by simp, ?_⟩
    funext x
    simp [dirDeriv]
  | cons i L ih =>
    have hi := hF i (by simp)
    obtain ⟨h1, h2⟩ := ih (fun j hj => hF j (by simp [hj]))
    simp only [List.map_cons, List.sum_cons]
    refine ⟨hi.add h1, ?_⟩
    rw [dirDeriv_add hi h1, h2]

/-- The splittings `(w₁, w₂)` of a list of directions into a nonempty sublist `w₁` and its
complement `w₂` (Leibniz formula in subset form). -/
def splitsPos : List ℂ → List (List ℂ × List ℂ)
  | [] => []
  | v :: vs => ([v], vs) :: ((splitsPos vs).map (fun p => (v :: p.1, p.2)) ++
      (splitsPos vs).map (fun p => (p.1, v :: p.2)))

theorem mem_splitsPos {vs : List ℂ} {p : List ℂ × List ℂ} (hp : p ∈ splitsPos vs) :
    p.1 ≠ [] ∧ (p.1 ++ p.2).Perm vs := by
  induction vs generalizing p with
  | nil => simp [splitsPos] at hp
  | cons v vs ih =>
    simp only [splitsPos, List.mem_cons, List.mem_append, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · simp
    · obtain ⟨_, h2⟩ := ih hq
      exact ⟨by simp, by simpa using h2.cons v⟩
    · obtain ⟨h1, h2⟩ := ih hq
      exact ⟨h1, List.perm_middle.trans (h2.cons v)⟩

theorem length_splitsPos (vs : List ℂ) : (splitsPos vs).length + 1 = 2 ^ vs.length := by
  induction vs with
  | nil => simp [splitsPos]
  | cons v vs ih =>
    simp only [splitsPos, List.length_cons, List.length_append, List.length_map, pow_succ]
    omega

/-- The Leibniz formula for iterated directional derivatives of a product of smooth
functions, with the term without derivatives on `a` separated. -/
theorem iterDirDeriv_mul {a h : ℂ → ℂ} (ha : ContDiff ℝ ∞ a) (hh : ContDiff ℝ ∞ h)
    (vs : List ℂ) :
    iterDirDeriv vs (fun y => a y * h y) = fun x => a x * iterDirDeriv vs h x +
      ((splitsPos vs).map (fun p => iterDirDeriv p.1 a x * iterDirDeriv p.2 h x)).sum := by
  induction vs with
  | nil =>
    funext x
    simp [splitsPos]
  | cons v vs ih =>
    rw [iterDirDeriv_cons, ih]
    have hP : ∀ p ∈ splitsPos vs,
        Differentiable ℝ (fun x => iterDirDeriv p.1 a x * iterDirDeriv p.2 h x) :=
      fun p _ => (differentiable_iterDirDeriv ha p.1).mul (differentiable_iterDirDeriv hh p.2)
    obtain ⟨hS, hS'⟩ := dirDeriv_listSum (splitsPos vs) _ hP v
    have ha' : Differentiable ℝ a := ha.differentiable (by simp)
    rw [dirDeriv_add (f₁ := fun x => a x * iterDirDeriv vs h x)
      (ha'.mul (differentiable_iterDirDeriv hh vs)) hS,
      dirDeriv_mul ha' (differentiable_iterDirDeriv hh vs), hS']
    funext x
    have hprod : ∀ p ∈ splitsPos vs,
        dirDeriv v (fun x => iterDirDeriv p.1 a x * iterDirDeriv p.2 h x) x =
          iterDirDeriv (v :: p.1) a x * iterDirDeriv p.2 h x +
            iterDirDeriv p.1 a x * iterDirDeriv (v :: p.2) h x := by
      intro p _
      rw [dirDeriv_mul (differentiable_iterDirDeriv ha p.1) (differentiable_iterDirDeriv hh p.2)]
      rfl
    beta_reduce
    rw [List.map_congr_left hprod, List.sum_map_add]
    simp only [splitsPos, List.map_cons, List.sum_cons, List.map_append, List.sum_append,
      List.map_map, Function.comp_def, iterDirDeriv_cons, iterDirDeriv_nil]
    ring

/-- `∂_{vs}(L ∘ f) = L ∘ ∂_{vs} f` for a real-linear map `L`. -/
theorem iterDirDeriv_clm_comp (L : ℂ →L[ℝ] ℂ) {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (vs : List ℂ) : iterDirDeriv vs (fun x => L (f x)) = fun x => L (iterDirDeriv vs f x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [iterDirDeriv_cons, iterDirDeriv_cons, ih]
    funext x
    have hd : DifferentiableAt ℝ (iterDirDeriv vs f) x := differentiable_iterDirDeriv hf vs x
    have h1 : HasFDerivAt (fun y => L (iterDirDeriv vs f y)) (L.comp (fderiv ℝ (iterDirDeriv vs f) x)) x :=
      L.hasFDerivAt.comp x hd.hasFDerivAt
    simp only [dirDeriv]
    rw [h1.fderiv]
    rfl

end NonUniqueEuler.Smooth.CommR2Aux
