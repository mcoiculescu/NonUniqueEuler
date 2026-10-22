import NonUniqueEuler.Statement.Evans
import NonUniqueEuler.H.Evans.ODE.Linear
import NonUniqueEuler.H.Evans.ODE.Coeff
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Proof: the Evans ODE (existence, uniqueness, regularity)

Proof of `NonUniqueEuler/I/Evans/ODE.lean` (`def:evans` and `lem:evans-basic`, `04_ring.tex`).
Same declarations, statements copied verbatim.

Method.
* The coefficient `V = riccatiCoeff χ ℓ z G` is `C^∞` and bounded on `ℝ` for `Re z > 0`
  (`H/Evans/ODE/Coeff.lean`), so the first-order system for `(ψ, ψ')` is globally Lipschitz and
  the vendored global Picard theorem gives a global solution; it is `C^∞` by bootstrap
  (`H/Evans/ODE/Linear.lean`).
* Uniqueness, stability in `(λ, G)` and complex differentiability in `λ` all come from one
  Grönwall estimate (`EvansODE.gronwall2`, from Mathlib's
  `norm_le_gronwallBound_of_norm_deriv_right_le`). For the `λ`-derivative we compare with the
  solution `φ` of the variational equation `φ'' = V φ + (∂_λ V) ψ`, `φ(ξ_L) = φ'(ξ_L) = 0`, and
  bound the remainder by `C |λ - λ₀|²`.

Deviation from the manuscript: the manuscript states
`lem:evans-basic`(1) without proof details (holomorphy in `λ` of solutions of ODEs with
holomorphic coefficients). We prove holomorphy directly by the variational-equation estimate
above instead of an argument through Picard iterates.
-/

namespace NonUniqueEuler

open RingData Set Filter Asymptotics Topology
open scoped ContDiff

namespace EvansODE

theorem ξL_le_ξR : ξL ≤ ξR := by norm_num [ξL, ξR]

theorem ξR_mem : ξR ∈ Icc ξL ξR := ⟨ξL_le_ξR, le_rfl⟩

/-- The Grönwall constant `1 + ℓ² + ℓ M / ρ`. -/
noncomputable def Kc (ℓ : ℕ) (M ρ : ℝ) : ℝ := 1 + (ℓ : ℝ) ^ 2 + ℓ * M / ρ

theorem one_le_Kc (ℓ : ℕ) {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 < ρ) : 1 ≤ Kc ℓ M ρ := by
  unfold Kc
  have h1 : 0 ≤ (ℓ : ℝ) * M / ρ := by positivity
  have h2 : 0 ≤ (ℓ : ℝ) ^ 2 := by positivity
  linarith

theorem norm_riccatiCoeff_le_Kc {χ : ℝ → ℝ} (ℓ : ℕ) {M ρ : ℝ}
    (hM : ∀ ξ, |deriv (prof χ) ξ| ≤ M) (hρ : 0 < ρ) {z : ℂ} (hz : ρ ≤ z.re) (G ξ : ℝ) :
    ‖riccatiCoeff χ ℓ z G ξ‖ ≤ Kc ℓ M ρ := by
  have := norm_riccatiCoeff_le ℓ hM hρ hz G ξ
  unfold Kc
  linarith

theorem isEvansSolution_of_global {χ : ℝ → ℝ} {ℓ : ℕ} {z : ℂ} {G : ℝ} {ψ ψ' : ℝ → ℂ}
    (h0 : ψ ξL = 1) (h0' : ψ' ξL = (ℓ : ℂ))
    (h : ∀ t, HasDerivAt ψ (ψ' t) t ∧ HasDerivAt ψ' (riccatiCoeff χ ℓ z G t * ψ t) t) :
    IsEvansSolution χ ℓ z G ψ ψ' :=
  ⟨fun t _ => (h t).1.hasDerivWithinAt, fun t _ => (h t).2.hasDerivWithinAt, h0, h0'⟩

/-- A global solution on `ℝ` (for `Re z > 0`). -/
theorem exists_global_sol {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) :
    ∃ ψ ψ' : ℝ → ℂ, ψ ξL = 1 ∧ ψ' ξL = (ℓ : ℂ) ∧
      ∀ t, HasDerivAt ψ (ψ' t) t ∧ HasDerivAt ψ' (riccatiCoeff χ ℓ z G t * ψ t) t := by
  obtain ⟨M, -, hM⟩ := exists_bound_deriv_prof hχ
  obtain ⟨ψ, ψ', h0, h0', h⟩ := exists_sol2 (V := fun t => riccatiCoeff χ ℓ z G t)
    (F := fun _ => 0) (contDiff_riccatiCoeff' hχ ℓ hz G).continuous continuous_const
    (norm_riccatiCoeff_le ℓ hM hz le_rfl G) ξL 1 (ℓ : ℂ)
  exact ⟨ψ, ψ', h0, h0', fun t => ⟨(h t).1, by simpa using (h t).2⟩⟩

/-- A priori bound on `[ξ_L, ξ_R]` for any solution, when `ρ ≤ Re z`. -/
theorem isEvansSolution_bound {χ : ℝ → ℝ} {ℓ : ℕ} {z : ℂ} {G : ℝ} {ψ ψ' : ℝ → ℂ} {M ρ : ℝ}
    (hM : ∀ ξ, |deriv (prof χ) ξ| ≤ M) (hM0 : 0 ≤ M) (hρ : 0 < ρ) (hz : ρ ≤ z.re)
    (h : IsEvansSolution χ ℓ z G ψ ψ') :
    ∀ t ∈ Icc ξL ξR, ‖ψ t‖ ≤ (1 + ℓ) * Real.exp (Kc ℓ M ρ * (ξR - ξL)) ∧
      ‖ψ' t‖ ≤ (1 + ℓ) * Real.exp (Kc ℓ M ρ * (ξR - ξL)) := by
  have hb := sol_bound ξL_le_ξR (one_le_Kc ℓ hM0 hρ) h.hasDerivWithinAt h.hasDerivWithinAt'
    (fun t _ => norm_riccatiCoeff_le_Kc ℓ hM hρ hz G t)
  have hmax : max ‖ψ ξL‖ ‖ψ' ξL‖ ≤ 1 + ℓ := by
    rw [h.init, h.init', norm_one, Complex.norm_natCast]
    exact max_le (by linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]) (by linarith)
  have hE := (Real.exp_pos (Kc ℓ M ρ * (ξR - ξL))).le
  intro t ht
  exact ⟨(hb t ht).1.trans (mul_le_mul_of_nonneg_right hmax hE),
    (hb t ht).2.trans (mul_le_mul_of_nonneg_right hmax hE)⟩

end EvansODE

open EvansODE

/-- The chosen pair `evansSolution` is a solution on `[ξ_L, ξ_R]` (existence). -/
theorem evansSolution_spec (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) :
    IsEvansSolution χ ℓ z G (evansSolution χ ℓ z G).1 (evansSolution χ ℓ z G).2 := by
  obtain ⟨ψ, ψ', h0, h0', h⟩ := exists_global_sol hχ ℓ hz G
  have hex : ∃ p : (ℝ → ℂ) × (ℝ → ℂ), IsEvansSolution χ ℓ z G p.1 p.2 :=
    ⟨(ψ, ψ'), isEvansSolution_of_global h0 h0' h⟩
  exact Classical.epsilon_spec hex

/-- Uniqueness on `[ξ_L, ξ_R]`. -/
theorem IsEvansSolution.eqOn (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) {ψ₁ ψ₁' ψ₂ ψ₂' : ℝ → ℂ}
    (h₁ : IsEvansSolution χ ℓ z G ψ₁ ψ₁') (h₂ : IsEvansSolution χ ℓ z G ψ₂ ψ₂') :
    EqOn ψ₁ ψ₂ (Icc ξL ξR) ∧ EqOn ψ₁' ψ₂' (Icc ξL ξR) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_prof hχ
  exact sol_eqOn ξL_le_ξR (one_le_Kc ℓ hM0 hz) h₁.hasDerivWithinAt h₁.hasDerivWithinAt'
    h₂.hasDerivWithinAt h₂.hasDerivWithinAt' (h₁.init.trans h₂.init.symm)
    (h₁.init'.trans h₂.init'.symm) (fun t _ => norm_riccatiCoeff_le_Kc ℓ hM hz le_rfl G t)

/-- The Evans function computed from any solution. -/
theorem evans_eq_of_isEvansSolution (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) {ψ ψ' : ℝ → ℂ} (h : IsEvansSolution χ ℓ z G ψ ψ') :
    evans χ ℓ z G =
      ((Real.exp (-(ℓ : ℝ) * (ξR - ξL)) : ℝ) : ℂ) * (ψ' ξR + (ℓ : ℂ) * ψ ξR) := by
  have heq := IsEvansSolution.eqOn χ hχ ℓ z hz G (evansSolution_spec χ hχ ℓ z hz G) h
  simp only [evans]
  rw [heq.1 ξR_mem, heq.2 ξR_mem]

/-- `ξ ↦ riccatiCoeff χ ℓ z G ξ` is smooth on `ℝ` when `Re z > 0`. -/
theorem contDiff_riccatiCoeff (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) :
    ContDiff ℝ ∞ (fun ξ => riccatiCoeff χ ℓ z G ξ) :=
  contDiff_riccatiCoeff' hχ ℓ hz G

/-- A global smooth solution of `ψ'' = V ψ` on `ℝ`, `ψ(ξ_L) = 1`, `ψ'(ξ_L) = ℓ`, and the Evans
function is read off from it (`def:evans` solves the equation on all of `ℝ`). -/
theorem exists_global_evansSolution (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) :
    ∃ ψ : ℝ → ℂ, ContDiff ℝ ∞ ψ ∧
      (∀ ξ, deriv (deriv ψ) ξ = riccatiCoeff χ ℓ z G ξ * ψ ξ) ∧
      ψ ξL = 1 ∧ deriv ψ ξL = (ℓ : ℂ) ∧
      IsEvansSolution χ ℓ z G ψ (deriv ψ) ∧
      evans χ ℓ z G =
        ((Real.exp (-(ℓ : ℝ) * (ξR - ξL)) : ℝ) : ℂ) * (deriv ψ ξR + (ℓ : ℂ) * ψ ξR) := by
  obtain ⟨ψ, ψ', h0, h0', h⟩ := exists_global_sol hχ ℓ hz G
  have hd1 : deriv ψ = ψ' := funext fun t => (h t).1.deriv
  have hsm := contDiff_of_sol2 (V := fun t => riccatiCoeff χ ℓ z G t) (F := fun _ => 0)
    (contDiff_riccatiCoeff' hχ ℓ hz G) contDiff_const (ψ := ψ) (ψ' := ψ')
    (fun t => ⟨(h t).1, by simpa using (h t).2⟩)
  have hsol := isEvansSolution_of_global h0 h0' h
  refine ⟨ψ, hsm.1, ?_, h0, ?_, ?_, ?_⟩
  · intro ξ
    rw [hd1]
    exact (h ξ).2.deriv
  · rw [hd1]
    exact h0'
  · rw [hd1]
    exact hsol
  · rw [hd1]
    exact evans_eq_of_isEvansSolution χ hχ ℓ z hz G hsol

namespace EvansODE

/-- Local Lipschitz estimate of `E_ℓ` in `(λ, G)`. -/
theorem evans_lip {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) {M ρ : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ ξ, |deriv (prof χ) ξ| ≤ M) (hρ : 0 < ρ) {z₀ : ℂ} (hz₀ : ρ ≤ z₀.re) (G₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (G : ℝ), ρ ≤ z.re →
      ‖evans χ ℓ z G - evans χ ℓ z₀ G₀‖ ≤ C * (‖z - z₀‖ + |G - G₀|) := by
  set K := Kc ℓ M ρ with hK
  set E := Real.exp (K * (ξR - ξL)) with hE
  set Cψ := (1 + (ℓ : ℝ)) * E with hCψ
  set e := Real.exp (-(ℓ : ℝ) * (ξR - ξL)) with he
  set A := (ℓ : ℝ) * M * (1 + ℓ * Real.exp (-2 * ξL)) / (ρ * ρ) with hA
  have hA0 : 0 ≤ A := by positivity
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hCψ0 : 0 ≤ Cψ := by positivity
  refine ⟨e * (1 + ℓ) * (A * Cψ * E), by positivity, ?_⟩
  intro z G hz
  have h₀ := evansSolution_spec χ hχ ℓ z₀ (hρ.trans_le hz₀) G₀
  have h := evansSolution_spec χ hχ ℓ z (hρ.trans_le hz) G
  set Δ := ‖z - z₀‖ + |G - G₀| with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hη : ∀ t ∈ Icc ξL ξR,
      ‖riccatiCoeff χ ℓ z G t - riccatiCoeff χ ℓ z₀ G₀ t‖ ≤ A * Δ := by
    intro t ht
    refine (norm_riccatiCoeff_sub_le ℓ hM hρ hz hz₀ G G₀ t).trans ?_
    have hexp : Real.exp (-2 * t) ≤ Real.exp (-2 * ξL) := Real.exp_le_exp.2 (by linarith [ht.1])
    have h1 : ‖z - z₀‖ + ℓ * Real.exp (-2 * t) * |G - G₀| ≤
        (1 + ℓ * Real.exp (-2 * ξL)) * Δ := by
      have h2 : (ℓ : ℝ) * Real.exp (-2 * t) * |G - G₀| ≤ ℓ * Real.exp (-2 * ξL) * |G - G₀| := by
        gcongr
      have h3 : (ℓ : ℝ) * Real.exp (-2 * ξL) * |G - G₀| ≤ ℓ * Real.exp (-2 * ξL) * Δ := by
        gcongr
        rw [hΔ]
        linarith [norm_nonneg (z - z₀)]
      have h4 : ‖z - z₀‖ ≤ Δ := by rw [hΔ]; linarith [abs_nonneg (G - G₀)]
      nlinarith
    calc (ℓ : ℝ) * M * (‖z - z₀‖ + ℓ * Real.exp (-2 * t) * |G - G₀|) / (ρ * ρ)
        ≤ ℓ * M * ((1 + ℓ * Real.exp (-2 * ξL)) * Δ) / (ρ * ρ) := by gcongr
      _ = A * Δ := by rw [hA]; ring
  have hs := sol_sub_bound ξL_le_ξR (one_le_Kc ℓ hM0 hρ) (by positivity) hCψ0
    h.hasDerivWithinAt h.hasDerivWithinAt' h₀.hasDerivWithinAt h₀.hasDerivWithinAt'
    (h.init.trans h₀.init.symm) (h.init'.trans h₀.init'.symm)
    (fun t _ => norm_riccatiCoeff_le_Kc ℓ hM hρ hz₀ G₀ t) hη
    (fun t ht => (isEvansSolution_bound hM hM0 hρ hz h t ht).1) ξR ξR_mem
  have hdiff : evans χ ℓ z G - evans χ ℓ z₀ G₀ = ((e : ℝ) : ℂ) *
      (((evansSolution χ ℓ z G).2 ξR - (evansSolution χ ℓ z₀ G₀).2 ξR) +
        (ℓ : ℂ) * ((evansSolution χ ℓ z G).1 ξR - (evansSolution χ ℓ z₀ G₀).1 ξR)) := by
    simp only [evans, he]
    ring
  have hsum : ‖((evansSolution χ ℓ z G).2 ξR - (evansSolution χ ℓ z₀ G₀).2 ξR) +
        (ℓ : ℂ) * ((evansSolution χ ℓ z G).1 ξR - (evansSolution χ ℓ z₀ G₀).1 ξR)‖ ≤
      (1 + ℓ) * (A * Δ * Cψ * E) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_natCast]
    have := mul_le_mul_of_nonneg_left hs.1 (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)
    linarith [hs.2]
  rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he0]
  calc e * _ ≤ e * ((1 + ℓ) * (A * Δ * Cψ * E)) := mul_le_mul_of_nonneg_left hsum he0
    _ = e * (1 + ℓ) * (A * Cψ * E) * Δ := by ring

/-- Complex differentiability of `E_ℓ(·; G)` at a point of `{Re λ > 0}`. -/
theorem evans_hasDerivAt {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) (G : ℝ) {z₀ : ℂ}
    (hz₀ : 0 < z₀.re) : ∃ c : ℂ, HasDerivAt (fun z => evans χ ℓ z G) c z₀ := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_prof hχ
  set ρ := z₀.re / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hρz₀ : ρ ≤ z₀.re := by rw [hρdef]; linarith
  set K := Kc ℓ M ρ with hK
  set E := Real.exp (K * (ξR - ξL)) with hE
  set Cψ := (1 + (ℓ : ℝ)) * E with hCψ
  set e := Real.exp (-(ℓ : ℝ) * (ξR - ξL)) with he
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hCψ0 : 0 ≤ Cψ := by positivity
  -- the global solution at `z₀` and the variational solution `φ`
  obtain ⟨ψ₀, ψ₀', h0, h0', hg⟩ := exists_global_sol hχ ℓ hz₀ G
  have hs₀ := isEvansSolution_of_global h0 h0' hg
  have hψ₀c : Continuous ψ₀ := continuous_iff_continuousAt.2 fun t => (hg t).1.continuousAt
  obtain ⟨φ, φ', hφ0, hφ0', hφ⟩ := exists_sol2 (V := fun t => riccatiCoeff χ ℓ z₀ G t)
    (F := fun t => Vdot χ ℓ z₀ G t * ψ₀ t) (contDiff_riccatiCoeff' hχ ℓ hz₀ G).continuous
    ((continuous_Vdot hχ ℓ hz₀ G).mul hψ₀c) (norm_riccatiCoeff_le ℓ hM hz₀ le_rfl G) ξL 0 0
  set c : ℂ := ((e : ℝ) : ℂ) * (φ' ξR + (ℓ : ℂ) * φ ξR) with hc
  refine ⟨c, ?_⟩
  set B := (ℓ : ℝ) * M / (ρ * ρ) with hB
  set A := (B * (B * Cψ * E) + ℓ * M / ρ ^ 3 * Cψ) with hA
  have hB0 : 0 ≤ B := by positivity
  have hA0 : 0 ≤ A := by positivity
  have hEz₀ : evans χ ℓ z₀ G = ((e : ℝ) : ℂ) * (ψ₀' ξR + (ℓ : ℂ) * ψ₀ ξR) :=
    evans_eq_of_isEvansSolution χ hχ ℓ z₀ hz₀ G hs₀
  -- the quadratic estimate
  have key : ∀ z : ℂ, ‖z - z₀‖ < ρ →
      ‖evans χ ℓ z G - evans χ ℓ z₀ G - (z - z₀) • c‖ ≤ (e * (1 + ℓ) * (A * E)) * ‖z - z₀‖ ^ 2 := by
    intro z hzz
    have hz : ρ ≤ z.re := by
      have h1 : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re] at h1
      have h2 := (abs_le.1 h1).1
      rw [hρdef] at hzz ⊢
      linarith
    have h := evansSolution_spec χ hχ ℓ z (hρ.trans_le hz) G
    set ψ := (evansSolution χ ℓ z G).1
    set ψ' := (evansSolution χ ℓ z G).2
    have hδ0 : 0 ≤ ‖z - z₀‖ := norm_nonneg _
    have hη₁ : ∀ t ∈ Icc ξL ξR,
        ‖riccatiCoeff χ ℓ z G t - riccatiCoeff χ ℓ z₀ G t‖ ≤ B * ‖z - z₀‖ := by
      intro t _
      refine (norm_riccatiCoeff_sub_le ℓ hM hρ hz hρz₀ G G t).trans (le_of_eq ?_)
      rw [hB, sub_self, abs_zero, mul_zero, add_zero]
      ring
    have hs := sol_sub_bound ξL_le_ξR (one_le_Kc ℓ hM0 hρ) (by positivity) hCψ0
      h.hasDerivWithinAt h.hasDerivWithinAt' hs₀.hasDerivWithinAt hs₀.hasDerivWithinAt'
      (h.init.trans hs₀.init.symm) (h.init'.trans hs₀.init'.symm)
      (fun t _ => norm_riccatiCoeff_le_Kc ℓ hM hρ hρz₀ G t) hη₁
      (fun t ht => (isEvansSolution_bound hM hM0 hρ hz h t ht).1)
    have hl := sol_lin_bound (η₁ := B * ‖z - z₀‖) (D₁ := B * ‖z - z₀‖ * Cψ * E)
      (η₂ := ℓ * M * ‖z - z₀‖ ^ 2 / ρ ^ 3) (C := Cψ) ξL_le_ξR (one_le_Kc ℓ hM0 hρ)
      (by positivity) (by positivity) (by positivity) hCψ0 (z - z₀)
      h.hasDerivWithinAt h.hasDerivWithinAt' hs₀.hasDerivWithinAt hs₀.hasDerivWithinAt'
      (fun t _ => (hφ t).1.hasDerivWithinAt) (fun t _ => (hφ t).2.hasDerivWithinAt)
      (h.init.trans hs₀.init.symm) (h.init'.trans hs₀.init'.symm) hφ0 hφ0'
      (fun t _ => norm_riccatiCoeff_le_Kc ℓ hM hρ hρz₀ G t) hη₁
      (fun t ht => (hs t ht).1)
      (fun t _ => norm_riccatiCoeff_sub_sub_le ℓ hM hρ hz hρz₀ G t)
      (fun t ht => (isEvansSolution_bound hM hM0 hρ hρz₀ hs₀ t ht).1) ξR ξR_mem
    have hAeq : (B * ‖z - z₀‖ * (B * ‖z - z₀‖ * Cψ * E) + ℓ * M * ‖z - z₀‖ ^ 2 / ρ ^ 3 * Cψ) =
        A * ‖z - z₀‖ ^ 2 := by
      rw [hA]; ring
    rw [hAeq] at hl
    have hdiff : evans χ ℓ z G - evans χ ℓ z₀ G - (z - z₀) • c = ((e : ℝ) : ℂ) *
        ((ψ' ξR - ψ₀' ξR - (z - z₀) * φ' ξR) + (ℓ : ℂ) * (ψ ξR - ψ₀ ξR - (z - z₀) * φ ξR)) := by
      rw [hEz₀, hc, smul_eq_mul]
      simp only [evans, he, ψ, ψ']
      ring
    have hsum : ‖(ψ' ξR - ψ₀' ξR - (z - z₀) * φ' ξR) +
          (ℓ : ℂ) * (ψ ξR - ψ₀ ξR - (z - z₀) * φ ξR)‖ ≤
        (1 + ℓ) * (A * ‖z - z₀‖ ^ 2 * E) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_natCast]
      have := mul_le_mul_of_nonneg_left hl.1 (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)
      linarith [hl.2]
    rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he0]
    calc e * _ ≤ e * ((1 + ℓ) * (A * ‖z - z₀‖ ^ 2 * E)) := mul_le_mul_of_nonneg_left hsum he0
      _ = e * (1 + ℓ) * (A * E) * ‖z - z₀‖ ^ 2 := by ring
  rw [hasDerivAt_iff_isLittleO]
  have hO : (fun z => evans χ ℓ z G - evans χ ℓ z₀ G - (z - z₀) • c) =O[𝓝 z₀]
      (fun z => ‖z - z₀‖ ^ 2) := by
    refine IsBigO.of_bound (e * (1 + ℓ) * (A * E)) ?_
    have hball : ∀ᶠ z in 𝓝 z₀, ‖z - z₀‖ < ρ := by
      have := Metric.ball_mem_nhds z₀ hρ
      filter_upwards [this] with z hz
      rwa [Metric.mem_ball, dist_eq_norm] at hz
    filter_upwards [hball] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact key z hz
  exact hO.trans_isLittleO (isLittleO_pow_sub_sub z₀ one_lt_two)

end EvansODE

/-- `lem:evans-basic`(1): `E_ℓ(·; G)` is holomorphic on `{Re λ > 0}`. -/
theorem evans_differentiableOn (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) (G : ℝ) :
    DifferentiableOn ℂ (fun z => evans χ ℓ z G) {z : ℂ | 0 < z.re} := by
  intro z hz
  obtain ⟨c, hc⟩ := evans_hasDerivAt hχ ℓ G (z₀ := z) hz
  exact hc.differentiableAt.differentiableWithinAt

/-- Joint continuity of `E_ℓ` in `(λ, G)` on `{Re λ > 0} × ℝ`. -/
theorem evans_continuousOn (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) :
    ContinuousOn (fun p : ℂ × ℝ => evans χ ℓ p.1 p.2) {p : ℂ × ℝ | 0 < p.1.re} := by
  intro p₀ hp₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_prof hχ
  have hp₀' : 0 < p₀.1.re := hp₀
  set ρ := p₀.1.re / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  obtain ⟨C, -, hC⟩ := evans_lip hχ ℓ hM0 hM hρ (z₀ := p₀.1) (by rw [hρdef]; linarith) p₀.2
  have hev : ∀ᶠ p in 𝓝 p₀, ρ ≤ p.1.re := by
    have hopen : IsOpen {p : ℂ × ℝ | ρ < p.1.re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)
    have hmem : p₀ ∈ {p : ℂ × ℝ | ρ < p.1.re} := by
      show ρ < p₀.1.re
      rw [hρdef]; linarith
    filter_upwards [hopen.mem_nhds hmem] with p hp
    exact le_of_lt hp
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun p : ℂ × ℝ => C * (‖p.1 - p₀.1‖ + |p.2 - p₀.2|)) (𝓝 p₀) (𝓝 0) := by
    have hcont : Continuous (fun p : ℂ × ℝ => C * (‖p.1 - p₀.1‖ + |p.2 - p₀.2|)) := by
      fun_prop
    simpa using hcont.tendsto p₀
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hev.mono fun p hp => hC p.1 p.2 hp) hlim

end NonUniqueEuler
