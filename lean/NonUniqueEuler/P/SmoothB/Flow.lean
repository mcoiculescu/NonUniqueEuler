import NonUniqueEuler.Defs.SmoothB.Flow
import NonUniqueEuler.Defs.Sec2.Conventions
import NonUniqueEuler.I.SmoothB.ODE
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Connected.Clopen
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant

/-!
# Proof of `lem:flow` (flows of smooth vector fields bounded on slabs)

Proof of the interface `NonUniqueEuler/I/SmoothB/Flow.lean` (`B_global_smooth.tex:47-110`).

* (a) global existence: `lem:ode`(iii) (`ode_global`) with `M(T) = sup |u|`, `L(T) = 0`;
* (b) cocycle identity: the maximality (uniqueness) of the maximal solution through
  `(τ, Φ_u(τ, s, y))`;
* (c) displacement bound: the mean value inequality on the convex slab `[-T, T]`;
* (a) smoothness: for fixed `k ≥ 1` and `(s, y)`, the set `G` of times `τ` such that `Φ_u` is
  `C^k` near `(τ, s, y)` is open (`ContDiffAt.eventually`), closed (if `τ ∈ closure G`, pick
  `τ' ∈ G` in the box of `lem:ode`(ii) around `(τ, Φ_u(τ, s, y))`, then
  `Φ_u(t, s', y') = Φ_u(t, τ', Φ_u(τ', s', y'))` is a composition of `C^k` maps near
  `(τ, s, y)`), and contains `s` (`lem:ode`(ii) at `(s, y)`). Since `ℝ` is connected, `G = ℝ`.
  This replaces the manuscript's chain of times obtained from the Lebesgue number lemma
  (`B_global_smooth.tex:73-99`) by a connectedness argument; the local step is the same.
* (d) variational equation: `D_y Φ_u(τ, s, y) = D_x Φ_u(τ, t, x) ∘ D_y Φ_u(t, s, y)` with
  `x = Φ_u(t, s, y)` (cocycle and chain rule), and the local variational equation of
  `lem:ode`(ii) at `(t, x)`, where `D_x Φ_u(t, t, ·) = id`. This replaces the manuscript's
  exchange of mixed derivatives.
* (d) Liouville: `det Y = (Y 1).re (Y i).im - (Y 1).im (Y i).re` (matrix in the basis `1, i`);
  its time derivative is `(div u) det Y = 0` by a direct `2 × 2` computation, so `det Y` is
  constant, equal to `det Y(s) = det id = 1`.
-/

noncomputable section

open Set
open scoped ContDiff Topology

namespace NonUniqueEuler.Smooth

variable {u : ℝ → ℂ → ℂ}

/-! ### Basic consequences of the hypotheses -/

private lemma IsSmoothBoundedField.contDiffOn_nat (hu : IsSmoothBoundedField u) (k : ℕ) :
    ContDiffOn ℝ k (Function.uncurry u) univ :=
  (hu.contDiff.of_le (mod_cast le_top)).contDiffOn

/-- `lem:flow`(a), global existence: `Φ_u(t, s, y)` is defined for all `(t, s, y)`, and
`t ↦ Φ_u(t, s, y)` is the maximal solution of `ẋ = u(t, x)`, `x(s) = y`, on all of `ℝ`. -/
theorem flowOf_global (hu : IsSmoothBoundedField u) (s : ℝ) (y : ℂ) :
    maxDomain u univ s y = univ ∧ IsMaxSol u univ s y univ (fun t => flowOf u t s y) := by
  have h1 : ContDiff ℝ 1 (Function.uncurry u) := hu.contDiff.of_le (mod_cast le_top)
  refine ode_global h1 (fun T hT => ?_) s y
  obtain ⟨M, hM⟩ := hu.bounded T hT
  exact ⟨M, 0, fun t ht x => by simpa using hM t ht x⟩

private lemma flowOf_init (hu : IsSmoothBoundedField u) (s : ℝ) (y : ℂ) :
    flowOf u s s y = y :=
  (flowOf_global hu s y).2.init

private lemma flowOf_self (hu : IsSmoothBoundedField u) (s : ℝ) : flowOf u s s = id :=
  funext fun y => flowOf_init hu s y

private lemma flowOf_hasDerivAt (hu : IsSmoothBoundedField u) (s : ℝ) (y : ℂ) (t : ℝ) :
    HasDerivAt (fun r => flowOf u r s y) (u t (flowOf u t s y)) t :=
  (flowOf_global hu s y).2.hasDerivAt t (mem_univ t)

private lemma flowOf_continuous_time (hu : IsSmoothBoundedField u) (s : ℝ) (y : ℂ) :
    Continuous fun r => flowOf u r s y :=
  continuous_iff_continuousAt.2 fun t => (flowOf_hasDerivAt hu s y t).continuousAt

/-- `lem:flow`(b), the cocycle identity `Φ_u(t, τ, Φ_u(τ, s, y)) = Φ_u(t, s, y)`. -/
theorem flowOf_cocycle (hu : IsSmoothBoundedField u) (t τ s : ℝ) (y : ℂ) :
    flowOf u t τ (flowOf u τ s y) = flowOf u t s y := by
  obtain ⟨-, hmax⟩ := flowOf_global hu τ (flowOf u τ s y)
  have hloc : IsLocalSol u univ τ (flowOf u τ s y) univ (fun r => flowOf u r s y) :=
    { isOpen := isOpen_univ
      ordConnected := ordConnected_univ
      mem := mem_univ τ
      init := rfl
      graph := fun _ _ => mem_univ _
      hasDerivAt := fun r _ => flowOf_hasDerivAt hu s y r }
  exact ((hmax.maximal _ _ hloc).2 (mem_univ t)).symm

/-! ### Smoothness (`lem:flow`(a)) -/

/-- `Φ_u` is `C^k` near the diagonal point `(s, s, y)` (`lem:ode`(ii) at `(s, y)`). -/
private lemma contDiffAt_flowOf_diag (hu : IsSmoothBoundedField u) {k : ℕ} (hk : 1 ≤ k)
    (s : ℝ) (y : ℂ) :
    ContDiffAt ℝ k (fun p : ℝ × ℝ × ℂ => flowOf u p.1 p.2.1 p.2.2) (s, s, y) := by
  obtain ⟨I, 𝒰, hI, -, h𝒰, hsI, hy𝒰, -, -, hC, -⟩ :=
    ode_local_contDiff isOpen_univ hk (hu.contDiffOn_nat k) (mem_univ (s, y))
  exact hC.contDiffAt ((hI.prod (hI.prod h𝒰)).mem_nhds ⟨hsI, hsI, hy𝒰⟩)

/-- For fixed `k ≥ 1` and `(s, y)`, `Φ_u` is `C^k` near `(t, s, y)` for every `t`: the set of
good times is clopen and contains `s`. -/
private lemma contDiffAt_flowOf (hu : IsSmoothBoundedField u) {k : ℕ} (hk : 1 ≤ k)
    (s : ℝ) (y : ℂ) (t : ℝ) :
    ContDiffAt ℝ k (fun p : ℝ × ℝ × ℂ => flowOf u p.1 p.2.1 p.2.2) (t, s, y) := by
  set Φ := fun p : ℝ × ℝ × ℂ => flowOf u p.1 p.2.1 p.2.2 with hΦ
  set G : Set ℝ := {τ | ContDiffAt ℝ k Φ (τ, s, y)} with hG
  have hemb : Continuous fun r : ℝ => ((r, s, y) : ℝ × ℝ × ℂ) := by fun_prop
  have hopen : IsOpen G := by
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    have hev : ∀ᶠ p in 𝓝 ((τ, s, y) : ℝ × ℝ × ℂ), ContDiffAt ℝ k Φ p :=
      ContDiffAt.eventually hτ (by simp)
    exact hemb.continuousAt.preimage_mem_nhds hev
  have hclosed : IsClosed G := by
    refine isClosed_of_closure_subset fun τ hτ => ?_
    obtain ⟨I, 𝒰, hI, -, h𝒰, hτI, hγ𝒰, -, -, hC, -⟩ :=
      ode_local_contDiff isOpen_univ hk (hu.contDiffOn_nat k)
        (mem_univ ((τ, flowOf u τ s y) : ℝ × ℂ))
    have hN : I ∩ (fun r => flowOf u r s y) ⁻¹' 𝒰 ∈ 𝓝 τ :=
      Filter.inter_mem (hI.mem_nhds hτI)
        ((flowOf_continuous_time hu s y).continuousAt.preimage_mem_nhds (h𝒰.mem_nhds hγ𝒰))
    obtain ⟨τ', ⟨hτ'I, hτ'𝒰⟩, hτ'G⟩ := mem_closure_iff_nhds.1 hτ _ hN
    -- the map `(t, x) ↦ Φ_u(t, τ', x)` is `C^k` on the open box `I × 𝒰`
    have hg : ContDiffAt ℝ k (fun q : ℝ × ℂ => flowOf u q.1 τ' q.2) (τ, flowOf u τ' s y) := by
      have hmaps : MapsTo (fun q : ℝ × ℂ => ((q.1, τ', q.2) : ℝ × ℝ × ℂ)) (I ×ˢ 𝒰)
          (I ×ˢ I ×ˢ 𝒰) := fun q hq => ⟨hq.1, hτ'I, hq.2⟩
      have hl : ContDiff ℝ k (fun q : ℝ × ℂ => ((q.1, τ', q.2) : ℝ × ℝ × ℂ)) := by fun_prop
      have hcomp := hC.comp hl.contDiffOn hmaps
      exact hcomp.contDiffAt ((hI.prod h𝒰).mem_nhds ⟨hτI, hτ'𝒰⟩)
    -- the map `(t, s', y') ↦ (t, Φ_u(τ', s', y'))` is `C^k` near `(τ, s, y)`
    have hf : ContDiffAt ℝ k (fun p : ℝ × ℝ × ℂ => ((p.1, flowOf u τ' p.2.1 p.2.2) : ℝ × ℂ))
        (τ, s, y) := by
      refine contDiffAt_fst.prodMk ?_
      have hl : ContDiff ℝ k (fun p : ℝ × ℝ × ℂ => ((τ', p.2.1, p.2.2) : ℝ × ℝ × ℂ)) := by
        fun_prop
      have h1 : ContDiffAt ℝ k Φ ((fun p : ℝ × ℝ × ℂ => ((τ', p.2.1, p.2.2) : ℝ × ℝ × ℂ))
          (τ, s, y)) := hτ'G
      exact h1.comp (τ, s, y) hl.contDiffAt
    have hcomp := hg.comp (τ, s, y) hf
    have heq : (fun q : ℝ × ℂ => flowOf u q.1 τ' q.2) ∘
        (fun p : ℝ × ℝ × ℂ => ((p.1, flowOf u τ' p.2.1 p.2.2) : ℝ × ℂ)) = Φ := by
      funext p
      exact flowOf_cocycle hu _ _ _ _
    rw [heq] at hcomp
    exact hcomp
  have hne : G.Nonempty := ⟨s, contDiffAt_flowOf_diag hu hk s y⟩
  have huniv : G = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hne
  have ht : t ∈ G := huniv ▸ mem_univ t
  exact ht

/-- `lem:flow`(a), smoothness: `Φ_u ∈ C^∞(ℝ × ℝ × ℝ²)`. -/
theorem flowOf_contDiff (hu : IsSmoothBoundedField u) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ × ℂ => flowOf u p.1 p.2.1 p.2.2) := by
  rw [contDiff_infty]
  intro n
  have h : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × ℝ × ℂ => flowOf u p.1 p.2.1 p.2.2) :=
    contDiff_iff_contDiffAt.2 fun p => contDiffAt_flowOf hu (by omega) p.2.1 p.2.2 p.1
  exact h.of_le (by exact_mod_cast Nat.le_succ n)

private lemma flowOf_contDiff_slice (hu : IsSmoothBoundedField u) (a b : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (flowOf u a b) :=
  (flowOf_contDiff hu).comp (by fun_prop : ContDiff ℝ ∞ fun y : ℂ => ((a, b, y) : ℝ × ℝ × ℂ))

/-- `lem:flow`(b), each `Φ_u(t, s, ·)` is a `C^∞` diffeomorphism of `ℝ²` with inverse
`Φ_u(s, t, ·)`. -/
theorem flowOf_diffeo (hu : IsSmoothBoundedField u) (t s : ℝ) :
    Function.LeftInverse (flowOf u s t) (flowOf u t s) ∧
      Function.RightInverse (flowOf u s t) (flowOf u t s) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (flowOf u t s) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (flowOf u s t) := by
  refine ⟨fun y => ?_, fun x => ?_, flowOf_contDiff_slice hu t s, flowOf_contDiff_slice hu s t⟩
  · rw [flowOf_cocycle hu, flowOf_init hu]
  · rw [flowOf_cocycle hu, flowOf_init hu]

/-! ### Displacement bound (`lem:flow`(c)) -/

/-- `lem:flow`(c): `|Φ_u(t, s, y) - y| ≤ |t - s| sup_{[-T,T] × ℝ²} |u|` for `s, t ∈ [-T, T]`
(stated with any bound `M` of `|u|` on `[-T, T] × ℝ²`). -/
theorem flowOf_disp_le (hu : IsSmoothBoundedField u) {T M : ℝ}
    (hM : ∀ τ ∈ Icc (-T) T, ∀ x : ℂ, ‖u τ x‖ ≤ M) {s t : ℝ} (hs : s ∈ Icc (-T) T)
    (ht : t ∈ Icc (-T) T) (y : ℂ) :
    ‖flowOf u t s y - y‖ ≤ |t - s| * M := by
  have h := (convex_Icc (-T) T).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun r => flowOf u r s y) (f' := fun r => u r (flowOf u r s y)) (C := M)
    (fun r _ => (flowOf_hasDerivAt hu s y r).hasDerivWithinAt) (fun r hr => hM r hr _) hs ht
  rw [flowOf_init hu, Real.norm_eq_abs, mul_comm] at h
  exact h

/-! ### Variational equation and Liouville (`lem:flow`(d)) -/

/-- `lem:flow`(d), the variational equation: `Y(t) = D_y Φ_u(t, s, y)` solves
`∂_t Y = ∇u(t, Φ_u(t, s, y)) Y` with `Y(s) = I`. -/
theorem flowOf_variational (hu : IsSmoothBoundedField u) (s : ℝ) (y : ℂ) :
    (∀ t : ℝ, HasDerivAt (fun τ => fderiv ℝ (flowOf u τ s) y)
        ((fderiv ℝ (u t) (flowOf u t s y)).comp (fderiv ℝ (flowOf u t s) y)) t) ∧
      fderiv ℝ (flowOf u s s) y = ContinuousLinearMap.id ℝ ℂ := by
  refine ⟨fun t => ?_, by rw [flowOf_self hu]; exact fderiv_id⟩
  have hdiff : ∀ (a b : ℝ) (z : ℂ), DifferentiableAt ℝ (flowOf u a b) z := fun a b z =>
    ((flowOf_contDiff_slice hu a b).differentiable (by simp)) z
  set x := flowOf u t s y with hx
  set B := fderiv ℝ (flowOf u t s) y with hB
  have hfun : (fun τ => fderiv ℝ (flowOf u τ s) y) =
      fun τ => (fderiv ℝ (flowOf u τ t) x).comp B := by
    funext τ
    have hc : flowOf u τ s = flowOf u τ t ∘ flowOf u t s :=
      funext fun z => (flowOf_cocycle hu τ t s z).symm
    rw [hc, fderiv_comp y (hdiff _ _ _) (hdiff _ _ _)]
  obtain ⟨I, 𝒰, -, -, -, htI, hx𝒰, -, -, -, -, hvar⟩ :=
    ode_local_contDiff isOpen_univ (le_refl 1) (hu.contDiffOn_nat 1) (mem_univ ((t, x) : ℝ × ℂ))
  have h : HasDerivAt (fun τ => fderiv ℝ (flowOf u τ t) x)
      ((fderiv ℝ (u t) (flowOf u t t x)).comp (fderiv ℝ (flowOf u t t) x)) t :=
    (hvar t htI t htI x hx𝒰).2
  rw [flowOf_self hu t, fderiv_id, id_eq, ContinuousLinearMap.comp_id] at h
  rw [hfun]
  have h2 := h.clm_comp (hasDerivAt_const t B)
  simpa using h2

/-- The determinant of a real-linear map of `ℂ = ℝ²` in the basis `1, i`. -/
private lemma det_eq_re_im (L : ℂ →L[ℝ] ℂ) :
    L.det = (L 1).re * (L Complex.I).im - (L 1).im * (L Complex.I).re := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]
  ring

/-- A real-linear map of `ℂ` is determined by its values at `1` and `i`. -/
private lemma clm_apply_eq (L : ℂ →L[ℝ] ℂ) (z : ℂ) :
    L z = z.re • L 1 + z.im • L Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul]

/-- Liouville's formula for `2 × 2` matrices: along `Ẏ = A Y`,
`∂_t det Y = (tr A) det Y`, written with the basis `1, i`. -/
private lemma det_deriv_identity (A : ℂ →L[ℝ] ℂ) (a b : ℂ) :
    (A a).re * b.im + a.re * (A b).im - ((A a).im * b.re + a.im * (A b).re) =
      ((A 1).re + (A Complex.I).im) * (a.re * b.im - a.im * b.re) := by
  rw [clm_apply_eq A a, clm_apply_eq A b]
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

/-- `lem:flow`(d), Liouville: if `div u = 0`, then `det D_y Φ_u ≡ 1`. -/
theorem det_fderiv_flowOf (hu : IsSmoothBoundedField u)
    (hdiv : ∀ t : ℝ, ∀ x : ℂ, Prelim.divergence (u t) x = 0) (t s : ℝ) (y : ℂ) :
    (fderiv ℝ (flowOf u t s) y).det = 1 := by
  obtain ⟨hvar, hinit⟩ := flowOf_variational hu s y
  set Y : ℝ → ℂ →L[ℝ] ℂ := fun τ => fderiv ℝ (flowOf u τ s) y with hY
  set A : ℝ → ℂ →L[ℝ] ℂ := fun τ => fderiv ℝ (u τ) (flowOf u τ s y) with hA
  -- the columns `Y τ 1`, `Y τ i` and their derivatives
  have hcol : ∀ (v : ℂ) (τ : ℝ), HasDerivAt (fun r => Y r v) (A τ (Y τ v)) τ := by
    intro v τ
    have h := (hvar τ).clm_apply (hasDerivAt_const τ v)
    simpa using h
  have hre : ∀ (v : ℂ) (τ : ℝ), HasDerivAt (fun r => (Y r v).re) (A τ (Y τ v)).re τ :=
    fun v τ => by
      have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ (hcol v τ)
      exact h
  have him : ∀ (v : ℂ) (τ : ℝ), HasDerivAt (fun r => (Y r v).im) (A τ (Y τ v)).im τ :=
    fun v τ => by
      have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt τ (hcol v τ)
      exact h
  set d : ℝ → ℝ := fun r =>
    (Y r 1).re * (Y r Complex.I).im - (Y r 1).im * (Y r Complex.I).re with hd
  have hdd : ∀ τ, HasDerivAt d 0 τ := by
    intro τ
    have h := ((hre 1 τ).mul (him Complex.I τ)).sub ((him 1 τ).mul (hre Complex.I τ))
    have hzero := det_deriv_identity (A τ) (Y τ 1) (Y τ Complex.I)
    have hdivτ : (A τ 1).re + (A τ Complex.I).im = 0 := hdiv τ (flowOf u τ s y)
    rw [hdivτ, zero_mul] at hzero
    rw [hzero] at h
    exact h
  have hconst : d t = d s :=
    is_const_of_deriv_eq_zero (fun τ => (hdd τ).differentiableAt) (fun τ => (hdd τ).deriv) t s
  have hds : d s = 1 := by
    simp only [hd, hY, hinit]
    simp
  rw [det_eq_re_im]
  exact hconst.trans hds

end NonUniqueEuler.Smooth
