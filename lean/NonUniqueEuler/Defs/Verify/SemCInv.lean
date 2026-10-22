import NonUniqueEuler.Defs.Verify.SemOps
import NonUniqueEuler.Verify.Comp.CInv

/-!
# Containment (CP) of `Ball.meet`, `CBox.invDisk` and `CBox.invTight`

Deviation A7 (see `FORMALIZATION_NOTES.md`). Code: `Verify/Comp/CInv.lean`.
Semantics: `Defs/Verify/Sem.lean`. All lemmas are proved, without side conditions.

* `Ball.mem_meet : x ∈ X → x ∈ Y → x ∈ meet p X Y`;
* `CBox.mem_invDisk : z ∈ Z → z⁻¹ ∈ invDisk p Z` (the disk bound
  `|1/z - 1/m| = |z - m|/(|z||m|) ≤ r/(|m|(|m| - r))`, `|z| ≥ |m| - r`, and
  `|m|(|m| - r) ≥ |m|² - r·|m|ᵘ = L > 0`);
* `CBox.mem_invTight : z ∈ Z → z⁻¹ ∈ invTight p Z`.
-/

noncomputable section

namespace NonUniqueEuler.Verify

open Complex

theorem UB.isFin_of_mul {U V : UB} (h : (U.mul V).isFin = true) :
    U.isFin = true ∧ V.isFin = true := by
  cases U <;> cases V <;> simp_all [UB.mul, UB.isFin]

theorem UB.isFin_ofDyExact (x : Dy) : (UB.ofDyExact x).isFin = true := by
  unfold UB.ofDyExact; split <;> rfl

namespace Ball

theorem mem_meet {p : ℕ} {X Y : Ball} {x : ℝ} (hx : x ∈ X) (hy : x ∈ Y) : x ∈ meet p X Y := by
  unfold meet
  split
  · rename_i a b c d ha hb hc hd
    dsimp only
    split
    · apply mem_ofInterval
      · rw [Dy.toReal_max]; exact max_le (lower?_le ha hx) (lower?_le hc hy)
      · rw [Dy.toReal_min]; exact le_min (le_upper? hb hx) (le_upper? hd hy)
    · exact hx
  · exact hx
  · exact hy

end Ball

namespace CBox

/-- The real inequality behind `invDisk`. -/
theorem invDisk_aux {z m : ℂ} {r mU : UB} {rm L : Dy} (hδ : ‖z - m‖ ≤ᵤ r) (hmU : ‖m‖ ≤ᵤ mU)
    (hrm : (UB.mul r mU).toDy? = some rm) (hL : L.toReal = ‖m‖ ^ 2 - rm.toReal)
    (hLpos : 0 < L.man) : ‖z⁻¹ - m⁻¹‖ ≤ᵤ UB.div r (UB.ofDyExact L) := by
  obtain ⟨hfin, hrmv⟩ := UB.toDy?_eq_some hrm
  obtain ⟨hrf, hmf⟩ := UB.isFin_of_mul hfin
  have hR := UB.Bounds.le_toReal hrf hδ
  have hM := UB.Bounds.le_toReal hmf hmU
  have hR0 := UB.toReal_nonneg r
  have hRM : r.toReal * mU.toReal ≤ rm.toReal := by
    rw [hrmv]
    exact UB.Bounds.le_toReal hfin (UB.bounds_mul hR0 (UB.toReal_nonneg _)
      (UB.bounds_of_isFin hrf le_rfl) (UB.bounds_of_isFin hmf le_rfl))
  have hLp : 0 < L.toReal := (Dy.toReal_pos_iff L).2 hLpos
  have hm0 := norm_nonneg m
  have hmR : r.toReal < ‖m‖ := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h hm0, mul_le_mul_of_nonneg_left hM hR0]
  have hz : ‖m‖ - r.toReal ≤ ‖z‖ := by
    have := norm_sub_norm_le m z
    rw [norm_sub_rev] at this
    linarith
  have hzpos : 0 < ‖z‖ := by linarith
  have hmpos : 0 < ‖m‖ := by linarith
  have key : ‖z⁻¹ - m⁻¹‖ = ‖z - m‖ / (‖z‖ * ‖m‖) := by
    rw [inv_sub_inv (norm_pos_iff.1 hzpos) (norm_pos_iff.1 hmpos), Complex.norm_div, Complex.norm_mul,
      norm_sub_rev]
  rw [key]
  have hC : (UB.ofDyExact L).toReal = L.toReal := by
    rw [UB.toReal_ofDyExact]; exact max_eq_left hLp.le
  apply UB.bounds_div' (norm_nonneg _) hδ (UB.isFin_ofDyExact L)
  · rw [hC]; exact hLp
  · rw [hC, hL]
    nlinarith [mul_le_mul_of_nonneg_left hz hm0, mul_le_mul_of_nonneg_left hM hR0]

theorem mem_invDisk {p : ℕ} {Z : CBox} {z : ℂ} (hz : z ∈ Z) : z⁻¹ ∈ invDisk p Z := by
  unfold invDisk
  split
  · rename_i ma ea mb eb hra hrb
    dsimp only
    split
    · rename_i rm hrm
      split
      · rename_i hL
        have hm : (⟨Z.re.mid.toReal, Z.im.mid.toReal⟩ : ℂ) ∈
            (⟨Ball.ofDy Z.re.mid, Ball.ofDy Z.im.mid⟩ : CBox) :=
          mem_mk.2 ⟨Ball.mem_ofDy _, Ball.mem_ofDy _⟩
        refine mem_addDisk (mem_inv hm) (invDisk_aux ?_ ?_ hrm ?_ hL)
        · have hzr : |z.re - Z.re.mid.toReal| ≤ᵤ UB.fin ma ea := by rw [← hra]; exact hz.1
          have hzi : |z.im - Z.im.mid.toReal| ≤ᵤ UB.fin mb eb := by rw [← hrb]; exact hz.2
          have h4 := UB.bounds_sqrtUp (by positivity)
            (UB.bounds_add (UB.bounds_mul (abs_nonneg _) (abs_nonneg _) hzr hzr)
              (UB.bounds_mul (abs_nonneg _) (abs_nonneg _) hzi hzi))
          rw [Complex.norm_def, normSq_apply]
          simpa only [sub_re, sub_im, abs_mul_abs_self] using h4
        · rw [Complex.norm_def]
          refine UB.bounds_sqrtUp (normSq_nonneg _) (UB.bounds_ofDyUp ?_)
          simp [normSq_apply]
        · rw [Dy.toReal_sub, Dy.toReal_add, Dy.toReal_mul, Dy.toReal_mul, Complex.sq_norm,
            normSq_apply]
      · exact mem_top _
    · exact mem_top _
  · exact mem_top _

theorem mem_invTight {p : ℕ} {Z : CBox} {z : ℂ} (hz : z ∈ Z) : z⁻¹ ∈ invTight p Z :=
  mem_def.2 ⟨Ball.mem_meet (mem_inv hz).1 (mem_invDisk hz).1,
    Ball.mem_meet (mem_inv hz).2 (mem_invDisk hz).2⟩

end CBox

end NonUniqueEuler.Verify
