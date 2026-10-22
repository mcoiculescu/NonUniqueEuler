import NonUniqueEuler.I.Sec6.FieldContinuity
import NonUniqueEuler.I.Sec8.Coupling.RadialSector
import NonUniqueEuler.H.Sec8.Coupling.Forcing
import NonUniqueEuler.H.Sec8.Coupling.Symmetry
import NonUniqueEuler.H.Sec8.Coupling.Sector
import NonUniqueEuler.H.Sec8.Coupling.Moment

/-!
# Helper for `lem:coupling`(1) (`08_kick.tex:66-110`)

Helper of `P/Sec8/Coupling.lean` (fully proved, modulo the interface files it imports).

* `radComp_monopole`: the monopole `G y^⊥/|y|²` is orthogonal to `e_r`;
* `radComp_hIn`: `h^in_k(τ)·e_r = (K_BS * ν^in_k)·e_r`;
* `profile_hIn`: the sector-`3` profile of `h^in_k(A_kt)·e_r` is `(i/2)pout_3[ν^in_k]r^{-4}` on
  `[a/4, 3]` (`angularSector_radComp_velocity`, `I/Sec8/Coupling/RadialSector.lean`, with
  `ρ = a/8`);
* `memCk_hIn`: `h^in_k(A_kt) ∈ C^M(N')` (`hIn_continuous` on the one-point interval);
* `coupling_one_aux`: the statement of `lem:coupling`(1).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.CouplingAux

open RingData Datum OneRing

/-- The monopole `G y^⊥/|y|²` is orthogonal to `e_r`. -/
theorem radComp_monopole (G : ℝ) (y : ℂ) :
    radComp (fun y => (G : ℂ) * (Complex.I * y) / ((‖y‖ ^ 2 : ℝ) : ℂ)) y = 0 := by
  rw [radComp_eq]
  have hc : (G : ℂ) * (Complex.I * y) / ((‖y‖ ^ 2 : ℝ) : ℂ) =
      ((G / ‖y‖ ^ 2 : ℝ) : ℂ) * (Complex.I * y) := by
    push_cast; ring
  rw [hc]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- The radial component is additive. -/
theorem radComp_sub (f g : ℂ → ℂ) (y : ℂ) :
    radComp (fun y => f y - g y) y = radComp f y - radComp g y := by
  simp only [radComp, sub_mul, Complex.sub_re]

/-- `h^in_k(τ)·e_r = (K_BS * ν^in_k(τ/A_k))·e_r` (the monopole is orthogonal to `e_r`). -/
theorem radComp_hIn (P : Approx) (k : ℕ) (τ : ℝ) (y : ℂ) :
    radComp (P.hIn k τ) y = radComp (velocity (P.nuIn k (τ / P.A k))) y := by
  have h : P.hIn k τ = fun y => velocity (P.nuIn k (τ / P.A k)) y -
      (fun y => (P.G k : ℂ) * (Complex.I * y) / ((‖y‖ ^ 2 : ℝ) : ℂ)) y := rfl
  rw [h, radComp_sub, radComp_monopole, sub_zero]

variable (P : Approx)

/-- **The sector-`3` profile of `h^in_k(A_kt)·e_r`** (`08_kick.tex:66-86`). -/
theorem profile_hIn (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < P.n) {t : ℝ} (ht : 0 ≤ t) (hin : P.HInDefined k t) :
    ∀ r ∈ Icc (a / 4) 3,
      Polar.angularSector (fun y => ((radComp (P.hIn k (P.A k * t)) y : ℝ) : ℂ)) 3 r =
        Complex.I / 2 * BS.pout 3 (fun y => ((P.nuIn k t y : ℝ) : ℂ)) * (r : ℂ) ^ (-4 : ℤ) := by
  intro r hr
  have hA : P.A k ≠ 0 := (hP.A_pos k).ne'
  have hτ : P.A k * t / P.A k = t := by field_simp
  have hfun : (fun y => ((radComp (P.hIn k (P.A k * t)) y : ℝ) : ℂ)) =
      fun y => ((radComp (velocity (P.nuIn k t)) y : ℝ) : ℂ) := by
    funext y
    rw [radComp_hIn, hτ]
  have ha := a_pos
  have hsupp : ∀ y : ℂ, a / 8 ≤ ‖y‖ → P.nuIn k t y = 0 := fun y hy =>
    nuIn_eq_zero P hP hin hy
  have h := Kick.angularSector_radComp_velocity (nuIn_contDiff P hP hN hk hkn ht)
    (by positivity : (0 : ℝ) < a / 8) hsupp (le_refl 1 |>.trans (by norm_num : (1 : ℕ) ≤ 3))
    (show a / 8 < r by linarith [hr.1])
  rw [hfun]
  have he : (-((3 : ℕ) : ℤ) - 1) = (-4 : ℤ) := by norm_num
  simpa [he] using h

/-- `h^in_k(A_kt) ∈ C^M(N')` when `D_{k+1}(t) ⊂ B_{a r_k/8}`. -/
theorem memCk_hIn (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < P.n) {t : ℝ} (ht : 0 ≤ t) (hin : P.HInDefined k t) (M : ℕ) :
    MemCk M annN' (P.hIn k (P.A k * t)) := by
  have hdef : ∀ t' ∈ Icc t t, P.HInDefined k t' := fun t' ht' => by
    rw [Icc_self, mem_singleton_iff] at ht'
    rw [ht']; exact hin
  exact (Approx.hIn_continuous P hP hN hk hkn.le ht hdef M).1 (P.A k * t) (left_mem_Icc.2 le_rfl)

/-- **`lem:coupling`(1)** (`08_kick.tex:26-33`), proved. -/
theorem coupling_one_aux (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k < P.n) {t : ℝ} (ht : 0 ≤ t) (hin : P.HInDefined k t) :
    (∀ s : ℕ, Lin.MemXFn s (OneRing.forcing P.χ (P.hIn k) (P.A k * t))) ∧
    Eig.ellFn P.χ (P.G k) (OneRing.forcing P.χ (P.hIn k) (P.A k * t)) =
      (P.μ : ℂ) * P.betaK k * P.q (k + 1) t ∧
    ∀ r ∈ Icc (a / 4) 3,
      Polar.angularSector (fun y => ((OneRing.radComp (P.hIn k (P.A k * t)) y : ℝ) : ℂ)) 3 r =
        Complex.I / 2 * BS.pout 3 (fun y => ((P.nuIn k t y : ℝ) : ℂ)) * (r : ℂ) ^ (-4 : ℤ) := by
  have hχ := hP.admissible
  have hτ0 : 0 ≤ P.A k * t := mul_nonneg (hP.A_pos k).le ht
  have hprof := profile_hIn P hP hN hk hkn ht hin
  refine ⟨fun s => ?_, ?_, hprof⟩
  · rw [forcing_eq]
    exact memXFn_neg_hGradPhi P.χ hχ hN (memCk_hIn P hP hN hk hkn ht hin s)
      (isSymFieldOn_hIn P hP hN hk hkn hτ0 annN')
  · rw [forcing_eq, ellFn_forcing hχ (P.G k) hprof, pout_nuIn P hP hk t]
    simp only [Approx.betaK]
    push_cast
    ring

end NonUniqueEuler.CouplingAux
