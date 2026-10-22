import NonUniqueEuler.Defs.Verify.Encl
import NonUniqueEuler.I.Verify.EndRegionCorollaries
import NonUniqueEuler.I.Evans.ODE

/-!
# Proof: Proposition A.3, steps (ii) and (iv): the boxes of the two end regions

Proof of `NonUniqueEuler/I/Verify/Sound/EndBoxes.lean` (same declarations, statements copied
verbatim). Manuscript: proof of Proposition A.3 (`prop:enclosure`), step (ii)
(`A_verification.tex:395-402`) and step (iv) (`A_verification.tex:439-450`).

Used black boxes: `leftEnd_bound`, `rightEnd_bound` (`I/Verify/EndRegionCorollaries`),
`evans_eq_of_isEvansSolution` (`I/Evans/ODE`). The containment facts of the code's operations
are the proved lemmas of `Defs/Verify/{Sem,SemOps}.lean`.

The only point that is not a direct application: the radius `W` of step (iv) is taken to be
`|Y(ξb)|_w` itself, so that the bound holds whether or not the code's `W`-bound is finite.
-/

noncomputable section

open Set

namespace NonUniqueEuler.Verify

open AppA RingData

/-- `max` of two upper bounds bounds the `max` of the bounded reals. -/
private theorem ub_bounds_max_max {U V : UB} {x y : ℝ} (hx : x ≤ᵤ U) (hy : y ≤ᵤ V) :
    max x y ≤ᵤ U.max V := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]; exact UB.bounds_max_right hy
  · rw [max_eq_left h]; exact UB.bounds_max_left hx

/-- The radius `2ε·up(e)` of the left end box bounds `2εe`. -/
private theorem endBox_radius_left {eps : UB} (hfin : eps.isFin = true) {emL1 : Ball} {e : ℝ}
    (he0 : 0 ≤ e) (he : e ∈ emL1) :
    2 * eps.toReal * e ≤ᵤ UB.mul (Ball.upperUB emL1) (UB.scale eps 1) := by
  have hε0 : 0 ≤ eps.toReal := UB.toReal_nonneg eps
  have h1 : eps.toReal * 2 ^ (1 : ℤ) ≤ᵤ UB.scale eps 1 :=
    UB.bounds_scale (UB.bounds_of_isFin hfin le_rfl) 1
  have h2 := UB.bounds_mul he0 (by positivity) (Ball.le_upperUB he) h1
  refine UB.Bounds.mono (le_of_eq ?_) h2
  rw [zpow_one]; ring

theorem leftEnd_mem {p ℓ : ℕ} (hℓ : 1 ≤ ℓ) {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {z : ℂ}
    (hz : 0 < z.re) {G : ℝ} {ψ ψ' : ℝ → ℂ} (hsol : IsEvansSolution χ ℓ z G ψ ψ') {eps : UB}
    (hfin : eps.isFin = true) (hε : epsEnd z ≤ eps.toReal) (hε1 : eps.toReal ≤ 1)
    {emL1 : Ball} (hemL1 : Real.exp (ℓ * endL) ∈ emL1) :
    ψ ξa ∈ CBox.addDisk (CBox.ofBall emL1) (UB.mul (Ball.upperUB emL1) (UB.scale eps 1)) ∧
      ψ' ξa ∈ CBox.mulNat p
        (CBox.addDisk (CBox.ofBall emL1) (UB.mul (Ball.upperUB emL1) (UB.scale eps 1))) ℓ := by
  obtain ⟨hb1, hb2⟩ := leftEnd_bound hχ hℓ hz hsol hε hε1
  set e : ℝ := Real.exp (ℓ * endL) with he_def
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hrad := endBox_radius_left hfin he0 hemL1
  have hc : ((e : ℝ) : ℂ) ∈ CBox.ofBall emL1 := CBox.mem_ofBall hemL1
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hℓ)
  refine ⟨CBox.mem_addDisk hc (hrad.mono hb1), ?_⟩
  have hdiv : ‖ψ' ξa / (ℓ : ℂ) - ((e : ℝ) : ℂ)‖ ≤ 2 * eps.toReal * e := by
    have heq : ψ' ξa / (ℓ : ℂ) - ((e : ℝ) : ℂ) =
        (ψ' ξa - (ℓ : ℂ) * ((e : ℝ) : ℂ)) / (ℓ : ℂ) := by
      field_simp
    rw [heq, norm_div, Complex.norm_natCast, div_le_iff₀ hℓ0]
    calc ‖ψ' ξa - (ℓ : ℂ) * ((e : ℝ) : ℂ)‖ ≤ 2 * ℓ * eps.toReal * e := hb2
      _ = 2 * eps.toReal * e * ℓ := by ring
  have hmem := CBox.mem_mulNat (p := p) (CBox.mem_addDisk hc (hrad.mono hdiv)) ℓ
  rwa [div_mul_cancel₀ _ hℓC] at hmem

theorem rightEnd_mem {p ℓ : ℕ} (hℓ : 1 ≤ ℓ) {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {z : ℂ}
    (hz : 0 < z.re) {G : ℝ} {ψ ψ' : ℝ → ℂ} (hsol : IsEvansSolution χ ℓ z G ψ ψ') {eps : UB}
    (hfin : eps.isFin = true) (hε : epsEnd z ≤ eps.toReal) (hε1 : eps.toReal ≤ 1)
    {emL2 nrm : Ball} (hemL2 : Real.exp (ℓ * endR) ∈ emL2)
    (hnrm : Real.exp (-(ℓ : ℝ) * (ξR - ξL)) ∈ nrm) {psi dpsi : CBox} (h1 : ψ ξb ∈ psi)
    (h2 : ψ' ξb ∈ dpsi) :
    evans χ ℓ z G ∈ CBox.mulBall p
      (CBox.addDisk (CBox.mulBall p (CBox.add p dpsi (CBox.mulNat p psi ℓ)) emL2)
        (UB.mul (UB.mul (UB.scale (Ball.upperUB emL2) 1)
          (UB.max (UB.mulNat (CBox.absUB psi) ℓ) (CBox.absUB dpsi))) (UB.scale eps 1))) nrm := by
  set W : ℝ := wnorm ℓ (ψ ξb) (ψ' ξb) with hW_def
  set e : ℝ := Real.exp (ℓ * endR) with he_def
  have hb := rightEnd_bound hχ hℓ hz hsol hε hε1 (W := W) le_rfl
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hε0 : 0 ≤ eps.toReal := UB.toReal_nonneg eps
  have hW0 : 0 ≤ W := (mul_nonneg (Nat.cast_nonneg ℓ) (norm_nonneg _)).trans (le_max_left _ _)
  -- the code's bound of `W = max(ℓ|ψ(ξb)|, |ψ'(ξb)|)`
  have hWn : W ≤ᵤ UB.max (UB.mulNat (CBox.absUB psi) ℓ) (CBox.absUB dpsi) := by
    have hu : (ℓ : ℝ) * ‖ψ ξb‖ ≤ᵤ UB.mulNat (CBox.absUB psi) ℓ := by
      rw [mul_comm]; exact UB.bounds_mulNat (norm_nonneg _) (CBox.norm_le_absUB h1) ℓ
    exact ub_bounds_max_max hu (CBox.norm_le_absUB h2)
  -- the radius `2·up(e)·W·2ε` bounds `4εWe`
  have hrad : 4 * eps.toReal * W * e ≤ᵤ
      UB.mul (UB.mul (UB.scale (Ball.upperUB emL2) 1)
        (UB.max (UB.mulNat (CBox.absUB psi) ℓ) (CBox.absUB dpsi))) (UB.scale eps 1) := by
    have hs1 : e * 2 ^ (1 : ℤ) ≤ᵤ UB.scale (Ball.upperUB emL2) 1 :=
      UB.bounds_scale (Ball.le_upperUB hemL2) 1
    have hs2 : eps.toReal * 2 ^ (1 : ℤ) ≤ᵤ UB.scale eps 1 :=
      UB.bounds_scale (UB.bounds_of_isFin hfin le_rfl) 1
    have hm1 := UB.bounds_mul (by positivity) hW0 hs1 hWn
    have hm2 := UB.bounds_mul (by positivity) (by positivity) hm1 hs2
    refine UB.Bounds.mono (le_of_eq ?_) hm2
    rw [zpow_one]; ring
  -- the center `(ψ'(ξb) + ℓψ(ξb))·e^{ℓL₂}`
  have hc : (ψ' ξb + ψ ξb * (ℓ : ℂ)) * ((e : ℝ) : ℂ) ∈
      CBox.mulBall p (CBox.add p dpsi (CBox.mulNat p psi ℓ)) emL2 :=
    CBox.mem_mulBall (CBox.mem_add h2 (CBox.mem_mulNat h1 ℓ)) hemL2
  have hd : ‖(ψ' ξR + (ℓ : ℂ) * ψ ξR) - (ψ' ξb + ψ ξb * (ℓ : ℂ)) * ((e : ℝ) : ℂ)‖ ≤
      4 * eps.toReal * W * e := by
    have heq : (ψ' ξb + ψ ξb * (ℓ : ℂ)) * ((e : ℝ) : ℂ) =
        ((e : ℝ) : ℂ) * (ψ' ξb + (ℓ : ℂ) * ψ ξb) := by ring
    rw [heq]; exact hb
  have hbox := CBox.mem_mulBall (p := p) (CBox.mem_addDisk hc (hrad.mono hd)) hnrm
  rw [evans_eq_of_isEvansSolution χ hχ ℓ z hz G hsol, mul_comm]
  exact hbox

end NonUniqueEuler.Verify
