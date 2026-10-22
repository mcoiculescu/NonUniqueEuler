import NonUniqueEuler.H.Sec8.Coupling.PartTwo

/-!
# Helper for `lem:coupling`(3) (`08_kick.tex:139-154`)

Helper of `P/Sec8/Coupling.lean` (fully proved, modulo the interface files it imports).

* `hOut_ckPath`: `τ ↦ h^out_k(τ)` is continuous on `[0, t̄♯_k]` into every `C^M(N')`;
* `coupling_three_aux`: the statement of `lem:coupling`(3): `-h^out_k·∇Φ ∈ C([0,t̄♯_k];X^s)` and
  `wlin_{in,k} + wlin_{out,k} = wlin[h_k]` (linearity of the Duhamel integral, `wlin_add`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.CouplingAux

open RingData Datum OneRing

variable (P : Approx)

/-- `τ ↦ h^out_k(τ)` is continuous on `[0, t̄♯_k]` into every `C^M(N')`. -/
theorem hOut_ckPath (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ P.n) (hout : ∀ t ∈ Icc (0 : ℝ) (P.tsh k), P.HOutDefined k t) (M : ℕ) :
    CkPathOn M annN' (Icc 0 (P.tash k)) (P.hOut k) := by
  have h := Approx.hOut_continuous P hP hN hk hkn (le_refl 0) hout M
  rwa [mul_zero, ← Approx.tash_def] at h

/-- **`lem:coupling`(3)** (`08_kick.tex:54-63`), proved. -/
theorem coupling_three_aux (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k < P.n)
    (hdef : ∀ t ∈ Icc (0 : ℝ) (P.tsh k), P.HDefined k t) (s : ℕ) :
    OneRing.PathC s (P.tash k) (OneRing.forcing P.χ (P.hOut k)) ∧
    ∀ τ ∈ Icc (0 : ℝ) (P.tash k),
      P.wlinIn s k τ + P.wlinOut s k τ = OneRing.wlin P.χ s (P.G k) (P.hField k) τ := by
  have hχ := hP.admissible
  have hpOut : PathC s (P.tash k) (forcing P.χ (P.hOut k)) :=
    forcing_pathC P.χ hχ hN (hOut_ckPath P hP hN hk hkn.le (fun t ht => (hdef t ht).2) s)
      fun v hv => isSymFieldOn_hOut P hP hN hk hkn.le hv.1 annN'
  have hpIn : PathC s (P.tash k) (forcing P.χ (P.hIn k)) :=
    forcing_pathC P.χ hχ hN (hIn_ckPath P hP hN hk hkn (fun t ht => (hdef t ht).1) s)
      fun v hv => isSymFieldOn_hIn P hP hN hk hkn hv.1 annN'
  refine ⟨hpOut, fun τ hτ => ?_⟩
  exact wlin_add P.χ hχ hpIn hpOut hτ

end NonUniqueEuler.CouplingAux
