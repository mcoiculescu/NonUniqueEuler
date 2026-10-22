import NonUniqueEuler.Defs.Verify.Winding
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Proof: existence and uniqueness of argument lifts; additivity over concatenation

Proof of `NonUniqueEuler/I/Verify/WindingLift.lean` (same declarations, statements verbatim).

**Manuscript.** The definition of `wind(c, 0)` (`A_verification.tex:42-46`) and the proof of
Proposition A.4 (`:487-499`).

* Uniqueness: two continuous arguments differ by a function with values in `2πℤ`, which is
  continuous on the connected `Icc a b`, hence constant (`IsPreconnected.constant_of_mapsTo`
  with the discrete set `AddSubgroup.zmultiples (2π)`).
* Existence: path lifting through the covering map `exp : ℂ → ℂ \ {0}`
  (`Complex.isCoveringMap_exp`, `IsCoveringMap.exists_path_lifts`) after the affine
  reparametrization of `[a, b]` to the unit interval; the argument is the imaginary part of
  the lift, read back through `Set.projIcc`.
* Additivity: glue the first lift with the second one shifted by a multiple of `2π`
  (`ContinuousOn.union_of_isClosed`).
-/

open Set Real

namespace NonUniqueEuler

/-! ### Helper facts -/

/-- `exp w = |exp w| e^{i Im w}`. -/
private theorem exp_eq_norm_mul_exp_im (w : ℂ) :
    Complex.exp w = ((‖Complex.exp w‖ : ℝ) : ℂ) * Complex.exp ((w.im : ℂ) * Complex.I) := by
  rw [Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  exact (Complex.re_add_im w).symm

/-- If `|z| e^{iα} = |z| e^{iβ}` with `z ≠ 0`, then `α = β + 2πk`. -/
private theorem exists_int_of_eq {z : ℂ} (hz : z ≠ 0) {α β : ℝ}
    (hα : z = ((‖z‖ : ℝ) : ℂ) * Complex.exp ((α : ℂ) * Complex.I))
    (hβ : z = ((‖z‖ : ℝ) : ℂ) * Complex.exp ((β : ℂ) * Complex.I)) :
    ∃ k : ℤ, α = β + 2 * π * k := by
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  have hexp : Complex.exp ((α : ℂ) * Complex.I) = Complex.exp ((β : ℂ) * Complex.I) :=
    mul_left_cancel₀ hn (hα.symm.trans hβ)
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  refine ⟨k, ?_⟩
  have h2 := congrArg Complex.im hk
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
    Complex.I_re, mul_zero, add_zero, mul_one, Complex.add_im, Complex.intCast_re,
    Complex.intCast_im, Complex.mul_re, zero_mul, sub_zero, Complex.re_ofNat,
    Complex.im_ofNat] at h2
  linarith

/-! ### Uniqueness -/

/-- Two continuous arguments of a nonvanishing curve on `[a, b]` differ by a constant integer
multiple of `2π`. -/
theorem IsArgLift.exists_int_eq_add {c : ℝ → ℂ} {a b : ℝ} {θ₁ θ₂ : ℝ → ℝ}
    (hne : ∀ t ∈ Icc a b, c t ≠ 0) (h₁ : IsArgLift c a b θ₁) (h₂ : IsArgLift c a b θ₂) :
    ∃ k : ℤ, ∀ t ∈ Icc a b, θ₁ t = θ₂ t + 2 * π * k := by
  rcases lt_or_ge b a with hba | hab
  · refine ⟨0, fun t ht => ?_⟩
    exact absurd (ht.1.trans ht.2) (not_le.mpr hba)
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  -- the difference takes values in `2πℤ`
  have hmaps : MapsTo (fun t => θ₁ t - θ₂ t) (Icc a b)
      ((AddSubgroup.zmultiples (2 * π) : AddSubgroup ℝ) : Set ℝ) := by
    intro t ht
    obtain ⟨k, hk⟩ := exists_int_of_eq (hne t ht) (h₁.eq t ht) (h₂.eq t ht)
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨k, ?_⟩
    simp only [zsmul_eq_mul]
    linarith
  have hdisc : IsDiscrete ((AddSubgroup.zmultiples (2 * π) : AddSubgroup ℝ) : Set ℝ) :=
    isDiscrete_iff_discreteTopology.mpr (NormedSpace.discreteTopology_zmultiples (2 * π))
  have hcont : ContinuousOn (fun t => θ₁ t - θ₂ t) (Icc a b) :=
    h₁.continuousOn.sub h₂.continuousOn
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hmaps ha)
  refine ⟨k, fun t ht => ?_⟩
  have hconst := isPreconnected_Icc.constant_of_mapsTo hdisc hcont hmaps ht ha
  simp only [zsmul_eq_mul] at hk
  linarith

/-- The argument change does not depend on the lift. -/
theorem HasArgChange.unique {c : ℝ → ℂ} {a b Δ₁ Δ₂ : ℝ} (h₁ : HasArgChange c a b Δ₁)
    (h₂ : HasArgChange c a b Δ₂) : Δ₁ = Δ₂ := by
  obtain ⟨θ₁, hθ₁, hΔ₁⟩ := h₁.exists_lift
  obtain ⟨θ₂, hθ₂, hΔ₂⟩ := h₂.exists_lift
  obtain ⟨k, hk⟩ := IsArgLift.exists_int_eq_add h₁.ne_zero hθ₁ hθ₂
  have ha := hk a (left_mem_Icc.mpr h₁.le)
  have hb := hk b (right_mem_Icc.mpr h₁.le)
  rw [← hΔ₁, ← hΔ₂, ha, hb]
  ring

/-- The winding number is unique. -/
theorem HasWinding.unique {c : ℝ → ℂ} {a b : ℝ} {n m : ℤ} (h₁ : HasWinding c a b n)
    (h₂ : HasWinding c a b m) : n = m := by
  have h := h₁.argChange.unique h₂.argChange
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  have : (n : ℝ) = m := mul_left_cancel₀ hπ h
  exact_mod_cast this

theorem HasWinding.windingNumber_eq {c : ℝ → ℂ} {a b : ℝ} {n : ℤ} (h : HasWinding c a b n) :
    windingNumber c a b = n := by
  have hex : ∃ n : ℤ, HasWinding c a b n := ⟨n, h⟩
  unfold windingNumber
  split_ifs
  exact hex.choose_spec.unique h

/-! ### Existence -/

/-- **Existence of a continuous argument** with a prescribed initial value. -/
theorem exists_argLift_of_start {c : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn c (Icc a b)) (hne : ∀ t ∈ Icc a b, c t ≠ 0) {θ₀ : ℝ}
    (h₀ : c a = ((‖c a‖ : ℝ) : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)) :
    ∃ θ : ℝ → ℝ, IsArgLift c a b θ ∧ θ a = θ₀ := by
  rcases hab.eq_or_lt with rfl | hlt
  · -- degenerate interval
    refine ⟨fun _ => θ₀, ⟨continuousOn_const, fun t ht => ?_⟩, rfl⟩
    have : t = a := le_antisymm ht.2 ht.1
    subst this
    exact h₀
  -- the affine reparametrization `s ↦ a + s (b - a)` of the unit interval
  have hφ : ∀ s : unitInterval, a + (s : ℝ) * (b - a) ∈ Icc a b := by
    intro s
    have h0 := s.2.1
    have h1 := s.2.2
    constructor
    · nlinarith
    · nlinarith
  have hcont : Continuous fun s : unitInterval => c (a + (s : ℝ) * (b - a)) :=
    hc.comp_continuous (by fun_prop) hφ
  let γ : C(unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun s => ⟨c (a + (s : ℝ) * (b - a)), hne _ (hφ s)⟩, hcont.subtype_mk _⟩
  set e : ℂ := (Real.log ‖c a‖ : ℂ) + (θ₀ : ℂ) * Complex.I with he_def
  have hca : c a ≠ 0 := hne a (left_mem_Icc.mpr hab)
  have he : γ 0 = ⟨Complex.exp e, Complex.exp_ne_zero e⟩ := by
    apply Subtype.ext
    change c (a + ((0 : unitInterval) : ℝ) * (b - a)) = Complex.exp e
    rw [Set.Icc.coe_zero, zero_mul, add_zero, he_def, Complex.exp_add,
      ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr hca)]
    exact h₀
  obtain ⟨Γ, hΓ, hΓ0⟩ := Complex.isCoveringMap_exp.exists_path_lifts γ e he
  have key : ∀ s : unitInterval, Complex.exp (Γ s) = c (a + (s : ℝ) * (b - a)) := fun s =>
    congrArg Subtype.val (congrFun hΓ s)
  have hba : 0 < b - a := sub_pos.mpr hlt
  -- read the lift back on `[a, b]`
  let ψ : ℝ → unitInterval := fun t => projIcc 0 1 zero_le_one ((t - a) / (b - a))
  have hψ : Continuous ψ := continuous_projIcc.comp (by fun_prop)
  refine ⟨fun t => (Γ (ψ t)).im, ⟨?_, fun t ht => ?_⟩, ?_⟩
  · exact (Complex.continuous_im.comp (Γ.continuous.comp hψ)).continuousOn
  · have hmem : (t - a) / (b - a) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr ht.1) hba.le
      · rw [div_le_one hba]; linarith [ht.2]
    have hψt : ((ψ t : unitInterval) : ℝ) = (t - a) / (b - a) := by
      simp only [ψ, projIcc_of_mem _ hmem]
    have hct : c t = Complex.exp (Γ (ψ t)) := by
      rw [key, hψt]
      congr 1
      field_simp
      ring
    rw [hct]
    exact exp_eq_norm_mul_exp_im _
  · have hψa : ψ a = 0 := by
      apply Subtype.ext
      simp [ψ]
    simp only [hψa, hΓ0, he_def]
    simp

/-- Every continuous nonvanishing curve on `[a, b]` has a continuous argument. -/
theorem exists_hasArgChange {c : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn c (Icc a b)) (hne : ∀ t ∈ Icc a b, c t ≠ 0) :
    ∃ Δ : ℝ, HasArgChange c a b Δ := by
  obtain ⟨θ, hθ, -⟩ := exists_argLift_of_start hab hc hne (θ₀ := Complex.arg (c a))
    (Complex.norm_mul_exp_arg_mul_I (c a)).symm
  exact ⟨θ b - θ a, hab, hc, hne, θ, hθ, rfl⟩

/-- Every continuous closed curve avoiding `0` has a winding number. -/
theorem exists_hasWinding {c : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn c (Icc a b)) (hne : ∀ t ∈ Icc a b, c t ≠ 0) (hcl : c a = c b) :
    ∃ n : ℤ, HasWinding c a b n := by
  obtain ⟨θ, hθ, -⟩ := exists_argLift_of_start hab hc hne (θ₀ := Complex.arg (c a))
    (Complex.norm_mul_exp_arg_mul_I (c a)).symm
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hθb := hθ.eq b hb
  rw [← hcl] at hθb
  obtain ⟨k, hk⟩ := exists_int_of_eq (hne a ha) hθb (hθ.eq a ha)
  refine ⟨k, hcl, hab, hc, hne, θ, hθ, ?_⟩
  linarith

/-! ### Additivity and congruence -/

/-- **Additivity over concatenation** of the argument change. -/
theorem HasArgChange.append {c : ℝ → ℂ} {a b e Δ₁ Δ₂ : ℝ} (h₁ : HasArgChange c a b Δ₁)
    (h₂ : HasArgChange c b e Δ₂) : HasArgChange c a e (Δ₁ + Δ₂) := by
  obtain ⟨θ₁, hθ₁, hΔ₁⟩ := h₁.exists_lift
  obtain ⟨θ₂, hθ₂, hΔ₂⟩ := h₂.exists_lift
  have hab := h₁.le
  have hbe := h₂.le
  have hb₁ : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hb₂ : b ∈ Icc b e := left_mem_Icc.mpr hbe
  -- match the two lifts at `b`
  obtain ⟨k, hk⟩ := exists_int_of_eq (h₁.ne_zero b hb₁) (hθ₁.eq b hb₁) (hθ₂.eq b hb₂)
  have hU : Icc a b ∪ Icc b e = Icc a e := Icc_union_Icc_eq_Icc hab hbe
  let θ : ℝ → ℝ := fun t => if t ≤ b then θ₁ t else θ₂ t + 2 * π * k
  have hθ₁' : EqOn θ θ₁ (Icc a b) := fun t ht => by simp [θ, ht.2]
  have hθ₂' : EqOn θ (fun t => θ₂ t + 2 * π * k) (Icc b e) := fun t ht => by
    rcases ht.1.eq_or_lt with h | h
    · subst h
      simp only [θ, le_refl, ite_true]
      exact hk
    · simp [θ, not_le.mpr h]
  have hcont : ContinuousOn θ (Icc a e) := by
    rw [← hU]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact hθ₁.continuousOn.congr hθ₁'
    · exact (hθ₂.continuousOn.add continuousOn_const).congr hθ₂'
  have hmem : ∀ t ∈ Icc a e, t ∈ Icc a b ∨ t ∈ Icc b e := fun t ht => by
    rw [← hU] at ht
    exact ht
  refine ⟨hab.trans hbe, ?_, ?_, θ, ⟨hcont, fun t ht => ?_⟩, ?_⟩
  · rw [← hU]
    exact h₁.continuousOn.union_of_isClosed h₂.continuousOn isClosed_Icc isClosed_Icc
  · intro t ht
    rcases hmem t ht with h | h
    · exact h₁.ne_zero t h
    · exact h₂.ne_zero t h
  · rcases hmem t ht with h | h
    · rw [hθ₁' h]
      exact hθ₁.eq t h
    · rw [hθ₂' h, hθ₂.eq t h]
      have hexp : Complex.exp (((θ₂ t + 2 * π * k : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((θ₂ t : ℂ) * Complex.I) := by
        rw [Complex.exp_eq_exp_iff_exists_int]
        exact ⟨k, by push_cast; ring⟩
      rw [hexp]
      conv_lhs => rw [hθ₂.eq t h]
  · have hθa : θ a = θ₁ a := hθ₁' (left_mem_Icc.mpr hab)
    have hθe : θ e = θ₂ e + 2 * π * k := hθ₂' (right_mem_Icc.mpr hbe)
    rw [hθa, hθe, ← hΔ₁, ← hΔ₂, hk]
    ring

/-- Additivity for two closed loops with the same base point. -/
theorem HasWinding.append {c : ℝ → ℂ} {a b e : ℝ} {n m : ℤ} (h₁ : HasWinding c a b n)
    (h₂ : HasWinding c b e m) : HasWinding c a e (n + m) := by
  refine ⟨h₁.closed.trans h₂.closed, ?_⟩
  have h := h₁.argChange.append h₂.argChange
  have heq : 2 * π * (n : ℝ) + 2 * π * (m : ℝ) = 2 * π * ((n + m : ℤ) : ℝ) := by
    push_cast; ring
  rw [heq] at h
  exact h

theorem HasArgChange.congr {c c' : ℝ → ℂ} {a b Δ : ℝ} (h : HasArgChange c a b Δ)
    (heq : EqOn c c' (Icc a b)) : HasArgChange c' a b Δ := by
  obtain ⟨θ, hθ, hΔ⟩ := h.exists_lift
  refine ⟨h.le, h.continuousOn.congr heq.symm, fun t ht => ?_, θ, ⟨hθ.continuousOn,
    fun t ht => ?_⟩, hΔ⟩
  · rw [← heq ht]
    exact h.ne_zero t ht
  · rw [← heq ht]
    exact hθ.eq t ht

theorem HasWinding.congr {c c' : ℝ → ℂ} {a b : ℝ} {n : ℤ} (h : HasWinding c a b n)
    (heq : EqOn c c' (Icc a b)) : HasWinding c' a b n := by
  refine ⟨?_, h.argChange.congr heq⟩
  rw [← heq (left_mem_Icc.mpr h.le), ← heq (right_mem_Icc.mpr h.le)]
  exact h.closed

end NonUniqueEuler
