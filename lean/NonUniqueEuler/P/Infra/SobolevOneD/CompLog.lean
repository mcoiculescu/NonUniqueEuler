import NonUniqueEuler.Defs.Infra.SobolevOneD
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import NonUniqueEuler.H.Infra.SobolevOneD.CompLog.Change
import NonUniqueEuler.H.Infra.SobolevOneD.CompLog.Rev

/-!
# Proof: `u ∈ H^m(ℝ)` gives `u ∘ log ∈ H^m((a, b))` for `0 < a` (library I-SOB1)

Proof of `NonUniqueEuler/I/Infra/SobolevOneD/CompLog.lean` (used by `lem:elliptic`,
`04_ring.tex:867-898`).

* Weak derivatives (`H/.../CompLog/Rev.lean`): with `U_p` the weak derivatives of `u` on `ℝ`
  (`CompLogH.exists_seq`), the iterated weak chain rule
  `∂_r^j (u ∘ log) = r^{-j} ∑_{p ≤ j} d_{jp} U_p(log r)` holds on `(0, ∞)`
  (`CompLogH.exists_rev`), hence on `(a, b) ⊆ (0, ∞)` (`HasWeakDerivOn.mono`).
* Square integrability (`H/.../CompLog/Change.lean`, `CompLogH.memLp_comp_log_Icc`): for
  `V ∈ L²(ℝ)`, the substitution `r = e^x` turns `∫_a^{b'} |r^{-j} V(log r)|² dr` into
  `∫_{log a}^{log b'} e^{(1-2j)x} |V(x)|² dx` with a continuous weight on a compact interval;
  here `b' = max a b`, so that `(a, b) ⊆ [a, b']` also when `b ≤ a` (empty interval).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Sob

/-- `u ∈ H^m(ℝ)` gives `u ∘ log ∈ H^m((a, b))` for `0 < a`. -/
theorem memH1On_comp_log {m : ℕ} {u : ℝ → ℂ} (hu : MemH1On m univ u) {a b : ℝ} (ha : 0 < a) :
    MemH1On m (Ioo a b) (fun r => u (Real.log r)) := by
  have hsub : Ioo a b ⊆ Ioi (0 : ℝ) := fun r hr => ha.trans hr.1
  have hIcc : Ioo a b ⊆ Icc a (max a b) := fun r hr =>
    ⟨hr.1.le, hr.2.le.trans (le_max_right a b)⟩
  -- square integrability of `r ↦ r^{-q} V(log r)` on `(a, b)`
  have key : ∀ (q : ℕ) (V : ℝ → ℂ), MemLp V 2 volume →
      MemLp (fun r => (((r⁻¹ : ℝ) : ℂ)) ^ q * V (Real.log r)) 2 (volume.restrict (Ioo a b)) :=
    fun q V hV => (CompLogH.memLp_comp_log_Icc hV ha (le_max_left a b) q).mono_measure
      (Measure.restrict_mono hIcc le_rfl)
  -- the weak derivatives of `u` on the line
  obtain ⟨U, hU0, hUL2', -, hUchain⟩ := CompLogH.exists_seq isOpen_univ hu
  have hUL2 : ∀ p ≤ m, MemLp (U p) 2 volume := fun p hp => by
    have := hUL2' p hp
    rwa [Measure.restrict_univ] at this
  have hUli : ∀ p ≤ m, LocallyIntegrable (U p) := fun p hp =>
    (hUL2 p hp).locallyIntegrable (by norm_num)
  choose d hd using CompLogH.exists_rev
  refine ⟨?_, fun j hj => ⟨fun r => ((r⁻¹ : ℝ) : ℂ) ^ j *
      ∑ p ∈ Finset.range (j + 1), d j p * U p (Real.log r), ?_, ?_⟩⟩
  · -- zeroth order
    have hu0 : MemLp u 2 volume := by
      have := hu.memLp
      rwa [Measure.restrict_univ] at this
    have h := key 0 u hu0
    simp only [pow_zero, one_mul] at h
    exact h
  · -- the `j`-th weak derivative is in `L²((a, b))`
    exact key j _ (memLp_finsetSum _ fun p hp =>
      (hUL2 p (by have := Finset.mem_range.1 hp; omega)).const_mul (d j p))
  · -- the `j`-th weak derivative on `(a, b)`
    have h := hd j U (fun p hp => hUchain p (by omega)) (fun p hp => hUli p (by omega))
    rw [hU0] at h
    exact h.mono hsub

end NonUniqueEuler.Sob
