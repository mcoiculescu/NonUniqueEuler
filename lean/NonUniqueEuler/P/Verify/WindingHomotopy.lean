import NonUniqueEuler.Defs.Verify.Winding
import NonUniqueEuler.I.Verify.WindingAlgebra
import NonUniqueEuler.I.Verify.WindingLift
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Complex.Basic

/-!
# Proof: stability of winding numbers (dog on a leash) and homotopy invariance

Proof of `NonUniqueEuler/I/Verify/WindingHomotopy.lean` (same declarations, statements copied
verbatim).

**Manuscript.** Background for the argument principle and for the reading of
`wind(E_3(Γ; G), 0)` as a well-defined integer (`A_verification.tex:42-50`).

* `HasWinding.of_norm_sub_lt`: the quotient `w = c₂ / c₁` satisfies `‖w - 1‖ < 1`, so
  `Re w > 0`, `arg ∘ w` is a continuous lift and `w` has winding `0`; then `HasWinding.mul`
  (`I/Verify/WindingAlgebra.lean`) and `HasWinding.congr` (`I/Verify/WindingLift.lean`).
* `HasWinding.of_homotopy`: `m = min ‖H‖ > 0` on the compact `Icc 0 1 ×ˢ Icc a b`, uniform
  continuity gives `δ` with `‖H s t - H s' t‖ < m` for `|s - s'| < δ`; then induction on `k`
  for the parameters `s ≤ k δ / 2`.
-/

open Set Real

namespace NonUniqueEuler

/-- The quotient of two curves at distance `< ‖c₁‖` lies in the right half-plane. -/
private lemma re_div_pos {z₁ z₂ : ℂ} (hlt : ‖z₂ - z₁‖ < ‖z₁‖) : 0 < (z₂ / z₁).re := by
  have hz₁ : z₁ ≠ 0 := by
    intro h; rw [h, norm_zero] at hlt; exact (norm_nonneg _).not_gt hlt
  have hn : 0 < ‖z₁‖ := norm_pos_iff.mpr hz₁
  have hq : 1 - z₂ / z₁ = (z₁ - z₂) / z₁ := by field_simp
  have h1 : ‖1 - z₂ / z₁‖ < 1 := by
    rw [hq, norm_div, div_lt_one hn, norm_sub_rev]; exact hlt
  have h2 := Complex.re_le_norm (1 - z₂ / z₁)
  rw [Complex.sub_re, Complex.one_re] at h2
  linarith

/-- **Dog on a leash.** A closed curve uniformly closer to `c₁` than `|c₁|` has the same
winding number. -/
theorem HasWinding.of_norm_sub_lt {c₁ c₂ : ℝ → ℂ} {a b : ℝ} {n : ℤ} (h : HasWinding c₁ a b n)
    (hc₂ : ContinuousOn c₂ (Icc a b)) (hcl : c₂ a = c₂ b)
    (hlt : ∀ t ∈ Icc a b, ‖c₂ t - c₁ t‖ < ‖c₁ t‖) : HasWinding c₂ a b n := by
  have hne₁ := h.ne_zero
  have hab := h.le
  set w : ℝ → ℂ := fun t => c₂ t / c₁ t with hw
  have hslit : ∀ t ∈ Icc a b, w t ∈ Complex.slitPlane := fun t ht =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (re_div_pos (hlt t ht)))
  have hwc : ContinuousOn w (Icc a b) := hc₂.div h.continuousOn hne₁
  have hw0 : HasWinding w a b 0 := by
    have hwab : w a = w b := by
      simp only [hw]; rw [hcl, h.closed]
    refine ⟨hwab, hab, hwc, fun t ht => Complex.slitPlane_ne_zero (hslit t ht), ?_⟩
    refine ⟨fun t => Complex.arg (w t), ⟨?_, ?_⟩, ?_⟩
    · exact Complex.continuousOn_arg.comp hwc (fun t ht => hslit t ht)
    · intro t _
      exact (Complex.norm_mul_exp_arg_mul_I (w t)).symm
    · simp only [hwab, sub_self, Int.cast_zero, mul_zero]
  have hmul := h.mul hw0
  rw [add_zero] at hmul
  refine hmul.congr ?_
  intro t ht
  simp only [hw]
  field_simp [hne₁ t ht]

/-- **Homotopy invariance.** A homotopy of closed curves avoiding `0` preserves the winding
number. -/
theorem HasWinding.of_homotopy {H : ℝ → ℝ → ℂ} {a b : ℝ}
    (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ Icc a b))
    (hne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b, H s t ≠ 0)
    (hcl : ∀ s ∈ Icc (0 : ℝ) 1, H s a = H s b) {n : ℤ} (h0 : HasWinding (H 0) a b n) :
    HasWinding (H 1) a b n := by
  have hab := h0.le
  set K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc a b with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty := ⟨(0, a), ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, hab⟩⟩⟩
  -- the minimum of `‖H‖` on `K`
  obtain ⟨p₀, hp₀, hmin⟩ := hKc.exists_isMinOn hKne (continuous_norm.comp_continuousOn hH)
  set m : ℝ := ‖H p₀.1 p₀.2‖ with hm
  have hmpos : 0 < m := norm_pos_iff.mpr (hne p₀.1 hp₀.1 p₀.2 hp₀.2)
  have hmle : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b, m ≤ ‖H s t‖ := fun s hs t ht =>
    hmin (show (s, t) ∈ K from ⟨hs, ht⟩)
  -- uniform continuity
  have huc := hKc.uniformContinuousOn_of_continuous hH
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδK⟩ := huc m hmpos
  -- continuity of each slice
  have hslice : ∀ s ∈ Icc (0 : ℝ) 1, ContinuousOn (H s) (Icc a b) := by
    intro s hs
    have hcont : ContinuousOn (fun t : ℝ => ((s, t) : ℝ × ℝ)) (Icc a b) :=
      (Continuous.prodMk continuous_const continuous_id).continuousOn
    exact hH.comp hcont (fun t ht => ⟨hs, ht⟩)
  -- one step of the chain
  have hstep : ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, |s - s'| < δ →
      HasWinding (H s') a b n → HasWinding (H s) a b n := by
    intro s hs s' hs' hss' h'
    refine h'.of_norm_sub_lt (hslice s hs) (hcl s hs) ?_
    intro t ht
    have hd : dist ((s, t) : ℝ × ℝ) (s', t) < δ := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      exact max_lt hss' hδ
    have := hδK (s, t) ⟨hs, ht⟩ (s', t) ⟨hs', ht⟩ hd
    rw [dist_eq_norm] at this
    exact lt_of_lt_of_le this (hmle s' hs' t ht)
  -- induction along the chain `s ≤ k δ / 2`
  have hind : ∀ k : ℕ, ∀ s ∈ Icc (0 : ℝ) 1, s ≤ k * (δ / 2) → HasWinding (H s) a b n := by
    intro k
    induction k with
    | zero =>
      intro s hs hsk
      have : s = 0 := le_antisymm (by simpa using hsk) hs.1
      rw [this]; exact h0
    | succ k ih =>
      intro s hs hsk
      by_cases hle : s ≤ k * (δ / 2)
      · exact ih s hs hle
      · replace hle := not_le.mp hle
        have hk0 : (0 : ℝ) ≤ k * (δ / 2) := by positivity
        have hs' : (k : ℝ) * (δ / 2) ∈ Icc (0 : ℝ) 1 := ⟨hk0, le_trans hle.le hs.2⟩
        refine hstep s hs _ hs' ?_ (ih _ hs' le_rfl)
        rw [abs_lt]
        push_cast at hsk
        constructor <;> nlinarith
  obtain ⟨k, hk⟩ := exists_nat_ge (2 / δ)
  refine hind k 1 ⟨zero_le_one, le_rfl⟩ ?_
  rw [div_le_iff₀ hδ] at hk
  linarith

end NonUniqueEuler
