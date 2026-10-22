import NonUniqueEuler.Defs.Sec6.All
import NonUniqueEuler.Defs.Sec3.Criterion
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec5.Seed
import NonUniqueEuler.I.Sec6.Integrability
import NonUniqueEuler.I.SmoothB.SmoothRot
import NonUniqueEuler.I.SmoothB.SmoothWeak
import NonUniqueEuler.H.Sec6.Adm.Terms
import NonUniqueEuler.H.Sec6.Adm.Conv

/-!
# Proof: `lem:adm` (the approximate data form an admissible sequence)

Proof of `I/Sec6/Adm.lean` (`06_datum.tex:83-92`, proof `:93-136`); same declaration, statement
copied verbatim.

* Step 1 (`06_datum.tex:94-99`): `f^{(n)}` is a finite sum of nonnegative `3`-fold symmetric
  `C_c^∞` functions (`AdmH.isGoodProfile_approxDatum`, from `lem:ring-facts` and `lem:seed`);
  `thm:smooth`(6) (`Smooth.smooth_rot`) gives the symmetry of `ω^{(n)}(t)`.
* Step 2 (`06_datum.tex:101-113`): `f^{(n)} → f` in `L^q`, `q ∈ [1,∞)`
  (`AdmH.tendsto_eLpNorm_approxDatum_sub`; uses `prop:integrability` and the measure preservation
  of `Y_κ`).
* Step 3 (`06_datum.tex:114-136`): `thm:smooth`(7) (`Smooth.smooth_weak`) already gives a
  renormalized weak solution in `X_q(T)` for every `T > 0` and `q > 4/3`, so the admissibility
  is assembled directly (the manuscript's detour through `lem:bounded-adm`(i), whose content is
  this renormalization, is not needed).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Datum

open RingData

/-- **`lem:adm`** (`06_datum.tex:83-92`). Under (N1)–(N3), for an admissible `χ`, parameters as in
`def:datum` and `κ_seed ∈ (0, κ_L]`: for every `n ≥ 2`, `f^{(n)} ∈ C_c^∞`, `f^{(n)} ≥ 0`, `f^{(n)}`
and every `ω^{(n)}(t)` are `3`-fold symmetric; `f^{(n)} → f` in `L^q` for every `q ∈ [1,∞)`; and
`(f^{(n+2)}, ω^{(n+2)})_{n ≥ 0}` is `q`-admissible for `f` on `[0,∞)` for every `q ∈ (4/3,∞)`. -/
theorem adm (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {A₁ μ sbar κs : ℝ} (hp : DatumParams A₁ μ sbar) (hκ : κs ∈ Ioc 0 (OneRing.kL χ)) :
    (∀ n : ℕ, 2 ≤ n →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (approxDatum χ A₁ μ sbar κs n) ∧
      HasCompactSupport (approxDatum χ A₁ μ sbar κs n) ∧
      (∀ x, 0 ≤ approxDatum χ A₁ μ sbar κs n x) ∧
      IsMFoldSymmetric 3 (approxDatum χ A₁ μ sbar κs n) ∧
      ∀ t : ℝ, IsMFoldSymmetric 3 (Smooth.sol (approxDatum χ A₁ μ sbar κs n) t)) ∧
    (∀ q : ℝ, 1 ≤ q → Tendsto
      (fun n => eLpNorm (approxDatum χ A₁ μ sbar κs n - datum χ A₁ μ sbar) (ENNReal.ofReal q)
        volume) atTop (𝓝 0)) ∧
    ∀ q : ℝ, 4 / 3 < q → Compact.IsAdmissibleSeq q ⊤ (datum χ A₁ μ sbar)
      (fun n => approxDatum χ A₁ μ sbar κs (n + 2))
      (fun n => Smooth.sol (approxDatum χ A₁ μ sbar κs (n + 2))) := by
  -- `lem:ring-facts`, `lem:seed`, `prop:integrability`
  have hR : RingFacts χ := ringFacts_of_admissible hχ
  have hS : OneRing.IsSeedFlow χ (OneRing.seedFlow χ) (OneRing.kL χ) (OneRing.Cprime χ) :=
    OneRing.seedData_spec (OneRing.seed χ hχ hN)
  have hI := integrability χ hχ hp
  -- step 1: `f^{(n)}` is a finite sum of nonnegative `3`-fold symmetric `C_c^∞` functions
  have hgoodS : AdmH.IsGoodProfile (2 * Real.pi / 3) (OneRing.PhiSeed χ κs) :=
    ⟨hS.phi_contDiff κs hκ, hS.phi_hasCompactSupport κs hκ, hS.phi_nonneg κs hκ,
      hS.phi_sym κs hκ⟩
  have hgood : ∀ n, AdmH.IsGoodProfile (2 * Real.pi / 3) (approxDatum χ A₁ μ sbar κs n) :=
    AdmH.isGoodProfile_approxDatum hR hp hgoodS
  have h3 : (2 * Real.pi / ((3 : ℕ) : ℝ)) = 2 * Real.pi / 3 := by norm_num
  have hSD : ∀ n, ∃ R₀, Smooth.IsSmoothDatum (approxDatum χ A₁ μ sbar κs n) R₀ := by
    intro n
    obtain ⟨R₀, hR₀⟩ := (hgood n).2.1.isCompact.isBounded.subset_ball (0 : ℂ)
    exact ⟨R₀, ⟨(hgood n).1, hR₀⟩⟩
  have hmem : ∀ n (p : ENNReal), MemLp (approxDatum χ A₁ μ sbar κs n) p volume := fun n _ =>
    (hgood n).1.continuous.memLp_of_hasCompactSupport (hgood n).2.1
  -- step 2: `f^{(n)} → f` in `L^q`
  have hconv : ∀ q : ℝ, 1 ≤ q → Tendsto
      (fun n => eLpNorm (approxDatum χ A₁ μ sbar κs n - datum χ A₁ μ sbar) (ENNReal.ofReal q)
        volume) atTop (𝓝 0) := fun q hq =>
    AdmH.tendsto_eLpNorm_approxDatum_sub hR hp hI.2.1 hI.1.2.2.2.1 (hS.measurePreserving κs) hq
  refine ⟨fun n _ => ⟨(hgood n).1, (hgood n).2.1, (hgood n).2.2.1, ?_, fun t => ?_⟩, hconv,
    fun q hq => ?_⟩
  · -- `f^{(n)}` is `3`-fold symmetric
    refine Filter.Eventually.of_forall fun x => ?_
    show approxDatum χ A₁ μ sbar κs n (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x) = _
    rw [h3]
    exact (hgood n).2.2.2 x
  · -- `thm:smooth`(6): `ω^{(n)}(t)` is `3`-fold symmetric
    obtain ⟨R₀, hR₀⟩ := hSD n
    refine Filter.Eventually.of_forall fun x => ?_
    show Smooth.sol (approxDatum χ A₁ μ sbar κs n) t (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x) = _
    rw [h3]
    exact Smooth.smooth_rot hR₀ (hgood n).2.2.2 t x
  · -- step 3: admissibility (`thm:smooth`(7) gives renormalized weak solutions on `[0, T]`)
    have hF1 : MemLp (datum χ A₁ μ sbar) 1 volume := by
      simpa using hI.1.2.2.2.1 1 le_rfl
    have h1 := (hconv 1 le_rfl).comp (tendsto_add_atTop_nat 2)
    have h2 := (hconv q (by linarith)).comp (tendsto_add_atTop_nat 2)
    rw [ENNReal.ofReal_one] at h1
    exact
      { q_gt := hq
        T₀_pos := by simp
        memLp_one := hF1
        memLp_q := hI.1.2.2.2.1 q (by linarith)
        memLp_one_seq := fun n => hmem (n + 2) 1
        memLp_q_seq := fun n => hmem (n + 2) _
        tendsto := by simpa [Weak.normL1LpE, Function.comp_def] using h1.add h2
        renormalized := fun n T hT _ => by
          obtain ⟨R₀, hR₀⟩ := hSD (n + 2)
          exact (Smooth.smooth_weak hR₀ hT hq).2.2 }

end Datum

end NonUniqueEuler
