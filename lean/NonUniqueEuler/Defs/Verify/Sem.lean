import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import NonUniqueEuler.Verify.Comp.Notation

/-!
# Semantics of the part 2 arithmetic layer

The real-number meaning of the computable arithmetic of `NonUniqueEuler/Verify/Comp/`:

* `Dy.toReal x = x.man · 2^x.exp` (zpow);
* `UB.toReal (fin m e) = m · 2^e`, `UB.toReal inf = 0` (junk), and `UB.Bounds U x`
  (notation `x ≤ᵤ U`): `U` is an upper bound of `x`, i.e. `U = inf` or `x ≤ U.toReal`;
* `Ball.mem b x` (`x ∈ b`): `|x - b.mid.toReal| ≤ᵤ b.rad` (every real if `b.rad = inf`);
* `CBox.mem B z` (`z ∈ B`): `z.re ∈ B.re ∧ z.im ∈ B.im`.

The containment property (CP) of an operation is stated as
`x ∈ X → y ∈ Y → f x y ∈ op p X Y` (no side conditions; see `Ball.mem_add`, …).
This file proves the basic lemmas: exactness of the `Dy` ring operations and comparisons, the
upper-bound lemmas of the `UB` operations used by the radius computations, and CP for the core
`Ball` operations (`roundMk`, `neg`, `add`, `sub`, `mul`, `sqr`, `mulDy`, `scale2`, `addErr`).
-/

noncomputable section

namespace NonUniqueEuler.Verify

/-! ## Helpers -/

theorem two_zpow_pos (e : ℤ) : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) e

theorem two_zpow_add (a b : ℤ) : (2 : ℝ) ^ (a + b) = 2 ^ a * 2 ^ b :=
  zpow_add₀ (by norm_num) a b

theorem two_zpow_natCast (k : ℕ) : (2 : ℝ) ^ (k : ℤ) = 2 ^ k := zpow_natCast 2 k

/-- `2^(b - a).toNat · 2^a = 2^b` for `a ≤ b`. -/
theorem two_pow_toNat_sub_mul {a b : ℤ} (h : a ≤ b) :
    (2 : ℝ) ^ (b - a).toNat * 2 ^ a = 2 ^ b := by
  rw [← two_zpow_natCast, Int.toNat_of_nonneg (by omega), ← two_zpow_add]
  congr 1; ring

theorem shl_eq (m : ℤ) (k : ℕ) : shl m k = m * 2 ^ k := by
  unfold shl
  split
  · subst_vars; simp
  · rw [Nat.one_shiftLeft]; push_cast; ring

theorem shr_eq (m : ℤ) (k : ℕ) : shr m k = m / 2 ^ k := by
  unfold shr; exact Int.shiftRight_eq_div_pow m k

theorem lt_two_pow_bitLen (n : ℕ) : n < 2 ^ bitLen n := Nat.lt_log2_self

/-! ## `Dy` -/

namespace Dy

/-- The value `man · 2^exp`. -/
def toReal (x : Dy) : ℝ := (x.man : ℝ) * (2 : ℝ) ^ x.exp

@[simp] theorem toReal_mk (m e : ℤ) : (⟨m, e⟩ : Dy).toReal = (m : ℝ) * 2 ^ e := rfl
@[simp] theorem toReal_zero : zero.toReal = 0 := by simp [zero, toReal]
@[simp] theorem toReal_one : one.toReal = 1 := by simp [one, toReal]
@[simp] theorem toReal_ofInt (n : ℤ) : (ofInt n).toReal = n := by simp [ofInt, toReal]
@[simp] theorem toReal_ofNat (n : ℕ) : (ofNat n).toReal = n := by simp [ofNat, toReal]
@[simp] theorem toReal_pow2 (e : ℤ) : (pow2 e).toReal = 2 ^ e := by simp [pow2, toReal]

@[simp] theorem toReal_neg (x : Dy) : x.neg.toReal = -x.toReal := by
  simp [neg, toReal]

@[simp] theorem toReal_scale (x : Dy) (k : ℤ) : (x.scale k).toReal = x.toReal * 2 ^ k := by
  simp only [scale, toReal, two_zpow_add]; ring

@[simp] theorem toReal_abs (x : Dy) : x.abs.toReal = |x.toReal| := by
  simp only [abs, toReal, abs_mul, abs_of_pos (two_zpow_pos _)]
  congr 1
  rw [Int.natCast_natAbs, Int.cast_abs]

@[simp] theorem toReal_mul (x y : Dy) : (x.mul y).toReal = x.toReal * y.toReal := by
  simp only [mul, toReal, two_zpow_add]; push_cast; ring

theorem toReal_eq_zero_of_man {x : Dy} (h : x.man = 0) : x.toReal = 0 := by
  simp [toReal, h]

@[simp] theorem toReal_add (x y : Dy) : (x.add y).toReal = x.toReal + y.toReal := by
  unfold add
  split
  · simp [toReal_eq_zero_of_man ‹_›]
  split
  · simp [toReal_eq_zero_of_man ‹_›]
  split
  · rename_i h
    simp only [toReal, shl_eq]; push_cast
    rw [← two_pow_toNat_sub_mul h]; ring
  · rename_i h
    simp only [toReal, shl_eq]; push_cast
    rw [← two_pow_toNat_sub_mul (le_of_lt (not_le.mp h))]; ring

@[simp] theorem toReal_sub (x y : Dy) : (x.sub y).toReal = x.toReal - y.toReal := by
  simp [sub, sub_eq_add_neg]

theorem toReal_pos_iff (x : Dy) : 0 < x.toReal ↔ 0 < x.man := by
  rw [toReal, mul_pos_iff_of_pos_right (two_zpow_pos _)]; exact_mod_cast Iff.rfl

theorem toReal_neg_iff (x : Dy) : x.toReal < 0 ↔ x.man < 0 := by
  have h := two_zpow_pos x.exp
  constructor
  · intro hx; by_contra hm
    have : (0 : ℝ) ≤ x.man := by exact_mod_cast (not_lt.mp hm)
    have := mul_nonneg this h.le; simp only [toReal] at hx; linarith
  · intro hm; have : (x.man : ℝ) < 0 := by exact_mod_cast hm
    simp only [toReal]; nlinarith

theorem toReal_nonneg_iff (x : Dy) : 0 ≤ x.toReal ↔ 0 ≤ x.man := by
  rw [← not_lt, toReal_neg_iff, not_lt]

theorem toReal_nonpos_iff (x : Dy) : x.toReal ≤ 0 ↔ x.man ≤ 0 := by
  rw [← not_lt, toReal_pos_iff, not_lt]

theorem toReal_eq_zero_iff (x : Dy) : x.toReal = 0 ↔ x.man = 0 := by
  constructor
  · intro h
    have h1 := (toReal_nonneg_iff x).1 (le_of_eq h.symm)
    have h2 := (toReal_nonpos_iff x).1 (le_of_eq h)
    omega
  · exact toReal_eq_zero_of_man


theorem isPos_iff (x : Dy) : x.isPos = true ↔ 0 < x.toReal := by
  rw [toReal_pos_iff]; simp [isPos]

theorem isNeg_iff (x : Dy) : x.isNeg = true ↔ x.toReal < 0 := by
  rw [toReal_neg_iff]; simp [isNeg]

theorem isNonneg_iff (x : Dy) : x.isNonneg = true ↔ 0 ≤ x.toReal := by
  rw [toReal_nonneg_iff]; simp [isNonneg]

theorem blt_iff (x y : Dy) : blt x y = true ↔ x.toReal < y.toReal := by
  unfold blt; rw [decide_eq_true_iff, ← toReal_neg_iff, toReal_sub, sub_neg]

theorem ble_iff (x y : Dy) : ble x y = true ↔ x.toReal ≤ y.toReal := by
  unfold ble; rw [decide_eq_true_iff, ← toReal_nonpos_iff, toReal_sub, sub_nonpos]

theorem beqv_iff (x y : Dy) : beqv x y = true ↔ x.toReal = y.toReal := by
  unfold beqv; rw [decide_eq_true_iff, ← toReal_eq_zero_iff, toReal_sub, sub_eq_zero]

@[simp] theorem toReal_min (x y : Dy) : (min x y).toReal = Min.min x.toReal y.toReal := by
  unfold min; split <;> rename_i h
  · rw [ble_iff] at h; exact (min_eq_left h).symm
  · rw [ble_iff] at h; exact (min_eq_right (le_of_lt (not_le.mp h))).symm

@[simp] theorem toReal_max (x y : Dy) : (max x y).toReal = Max.max x.toReal y.toReal := by
  unfold max; split <;> rename_i h
  · rw [ble_iff] at h; exact (max_eq_right h).symm
  · rw [ble_iff] at h; exact (max_eq_left (le_of_lt (not_le.mp h))).symm

theorem floorP_le (p : ℕ) (x : Dy) : (floorP p x).toReal ≤ x.toReal := by
  dsimp only [floorP]
  split
  · exact le_rfl
  · simp only [toReal, shr_eq, two_zpow_add, two_zpow_natCast]
    set s := bitLen x.man.natAbs - p
    have h1 : (x.man / 2 ^ s) * 2 ^ s ≤ x.man := Int.ediv_mul_le _ (by positivity)
    have h2 : ((x.man / 2 ^ s : ℤ) : ℝ) * 2 ^ s ≤ x.man := by exact_mod_cast h1
    have := two_zpow_pos x.exp
    nlinarith

theorem le_ceilP (p : ℕ) (x : Dy) : x.toReal ≤ (ceilP p x).toReal := by
  have := floorP_le p x.neg
  simp only [ceilP, toReal_neg] at *; linarith

/-- `2^(-e - t) · 2^t · 2^e = 1`. -/
theorem two_zpow_cancel (e : ℤ) (t : ℕ) :
    (2 : ℝ) ^ (-e - (t : ℤ)) * 2 ^ t * 2 ^ e = 1 := by
  rw [← two_zpow_natCast, ← two_zpow_add, ← two_zpow_add]; norm_num

/-- With `q = ⌊2^t / a⌋`: `q · 2^(-e-t) ≤ (a · 2^e)⁻¹ ≤ (q + 1) · 2^(-e-t)`. -/
theorem recip_aux (a : ℕ) (ha : 0 < a) (e : ℤ) (t : ℕ) :
    ((2 ^ t / a : ℕ) : ℝ) * 2 ^ (-e - (t : ℤ)) ≤ ((a : ℝ) * 2 ^ e)⁻¹ ∧
      ((a : ℝ) * 2 ^ e)⁻¹ ≤ (((2 ^ t / a : ℕ) : ℝ) + 1) * 2 ^ (-e - (t : ℤ)) := by
  set c : ℝ := 2 ^ (-e - (t : ℤ))
  have hc0 : 0 ≤ c := (two_zpow_pos _).le
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have hainv : (0 : ℝ) ≤ (a : ℝ)⁻¹ := inv_nonneg.2 hapos.le
  have hcm : c * 2 ^ t = ((2 : ℝ) ^ e)⁻¹ := eq_inv_of_mul_eq_one_left (two_zpow_cancel e t)
  have key : ((a : ℝ) * 2 ^ e)⁻¹ = 2 ^ t * (a : ℝ)⁻¹ * c := by
    rw [mul_inv, ← hcm]; ring
  have hq : ((2 ^ t / a : ℕ) : ℝ) * a ≤ 2 ^ t := by
    exact_mod_cast Nat.div_mul_le_self (2 ^ t) a
  have hq' : (2 : ℝ) ^ t ≤ (((2 ^ t / a : ℕ) : ℝ) + 1) * a := by
    have : 2 ^ t < (2 ^ t / a + 1) * a := by
      rw [Nat.add_mul, Nat.one_mul]; exact Nat.lt_div_mul_add ha
    exact_mod_cast this.le
  have hself : (a : ℝ) * (a : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hapos.ne'
  rw [key]
  constructor
  · calc ((2 ^ t / a : ℕ) : ℝ) * c = (((2 ^ t / a : ℕ) : ℝ) * a) * (a : ℝ)⁻¹ * c := by
          rw [mul_assoc (((2 ^ t / a : ℕ) : ℝ)), hself, mul_one]
      _ ≤ 2 ^ t * (a : ℝ)⁻¹ * c := by gcongr
  · calc 2 ^ t * (a : ℝ)⁻¹ * c ≤ ((((2 ^ t / a : ℕ) : ℝ) + 1) * a) * (a : ℝ)⁻¹ * c := by gcongr
      _ = (((2 ^ t / a : ℕ) : ℝ) + 1) * c := by rw [mul_assoc _ (a : ℝ), hself, mul_one]

theorem natAbs_cast_of_pos {m : ℤ} (h : 0 < m) : ((m.natAbs : ℕ) : ℝ) = m := by
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast h)]

theorem natAbs_cast_of_neg {m : ℤ} (h : m < 0) : ((m.natAbs : ℕ) : ℝ) = -m := by
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast h)]

theorem recipDown_le (p : ℕ) {x : Dy} (hx : x.man ≠ 0) :
    (recipDown p x).toReal ≤ (x.toReal)⁻¹ := by
  dsimp only [recipDown]
  have ha : x.man.natAbs ≠ 0 := by omega
  rw [ite_eq_right ha, Nat.one_shiftLeft]
  have h := recip_aux x.man.natAbs (Nat.pos_of_ne_zero ha) x.exp (p + bitLen x.man.natAbs)
  generalize p + bitLen x.man.natAbs = t at h ⊢
  generalize hq : 2 ^ t / x.man.natAbs = q at h ⊢
  split
  · rename_i hm
    simp only [toReal, Int.cast_natCast]; rw [← natAbs_cast_of_pos hm]; exact h.1
  · rename_i hm
    have hm' : x.man < 0 := by omega
    simp only [toReal]
    rw [show (x.man : ℝ) = -((x.man.natAbs : ℕ) : ℝ) by rw [natAbs_cast_of_neg hm']; ring]
    push_cast
    simp only [neg_mul, inv_neg]
    exact neg_le_neg h.2

theorem le_recipUp (p : ℕ) {x : Dy} (hx : x.man ≠ 0) :
    (x.toReal)⁻¹ ≤ (recipUp p x).toReal := by
  dsimp only [recipUp]
  have ha : x.man.natAbs ≠ 0 := by omega
  rw [ite_eq_right ha, Nat.one_shiftLeft]
  have h := recip_aux x.man.natAbs (Nat.pos_of_ne_zero ha) x.exp (p + bitLen x.man.natAbs)
  generalize p + bitLen x.man.natAbs = t at h ⊢
  generalize hq : 2 ^ t / x.man.natAbs = q at h ⊢
  split
  · rename_i hm
    simp only [toReal]
    rw [← natAbs_cast_of_pos hm]; push_cast; exact h.2
  · rename_i hm
    have hm' : x.man < 0 := by omega
    simp only [toReal]
    rw [show (x.man : ℝ) = -((x.man.natAbs : ℕ) : ℝ) by rw [natAbs_cast_of_neg hm']; ring]
    push_cast
    simp only [neg_mul, inv_neg]
    exact neg_le_neg h.1

end Dy

/-! ## `UB` -/

namespace UB

/-- The value of a finite bound (`0`, junk, for `inf`). -/
def toReal : UB → ℝ
  | fin m e => (m : ℝ) * 2 ^ e
  | inf => 0

/-- `U` is an upper bound of `x`: `U = inf`, or `x ≤ U.toReal`. -/
def Bounds : UB → ℝ → Prop
  | fin m e, x => x ≤ (m : ℝ) * 2 ^ e
  | inf, _ => True

end UB

/-- `x ≤ᵤ U`: the upper bound `U : UB` bounds the real `x`. -/
notation:50 x:51 " ≤ᵤ " U:51 => UB.Bounds U x

namespace UB

@[simp] theorem toReal_fin (m : ℕ) (e : ℤ) : (fin m e).toReal = (m : ℝ) * 2 ^ e := rfl
@[simp] theorem bounds_fin {x : ℝ} {m : ℕ} {e : ℤ} : (x ≤ᵤ fin m e) ↔ x ≤ (m : ℝ) * 2 ^ e :=
  Iff.rfl
@[simp] theorem bounds_inf (x : ℝ) : x ≤ᵤ inf := trivial

theorem toReal_nonneg (U : UB) : 0 ≤ U.toReal := by
  cases U with
  | fin m e => exact mul_nonneg (Nat.cast_nonneg m) (two_zpow_pos e).le
  | inf => exact le_rfl

theorem bounds_iff (U : UB) (x : ℝ) : (x ≤ᵤ U) ↔ U.isFin = false ∨ x ≤ U.toReal := by
  cases U <;> simp [Bounds, isFin, toReal]

theorem Bounds.mono {U : UB} {x y : ℝ} (hxy : x ≤ y) (h : y ≤ᵤ U) : x ≤ᵤ U := by
  cases U with
  | fin m e => exact le_trans hxy h
  | inf => trivial

theorem bounds_of_isFin {U : UB} {x : ℝ} (hU : U.isFin = true) (h : x ≤ U.toReal) : x ≤ᵤ U := by
  cases U with
  | fin m e => exact h
  | inf => trivial

theorem Bounds.le_toReal {U : UB} {x : ℝ} (hU : U.isFin = true) (h : x ≤ᵤ U) : x ≤ U.toReal := by
  cases U with
  | fin m e => exact h
  | inf => simp [isFin] at hU

theorem isFin_mkUp (m : ℕ) (e : ℤ) : (mkUp m e).isFin = true := by
  dsimp only [mkUp]; split <;> rfl

theorem le_toReal_mkUp (m : ℕ) (e : ℤ) : (m : ℝ) * 2 ^ e ≤ (mkUp m e).toReal := by
  dsimp only [mkUp]
  split
  · exact le_rfl
  · simp only [toReal, two_zpow_add, two_zpow_natCast, Nat.shiftRight_eq_div_pow]
    generalize bitLen m - radPrec = s
    have h : m < (m / 2 ^ s + 1) * 2 ^ s := by
      rw [Nat.add_mul, Nat.one_mul]; exact Nat.lt_div_mul_add (by positivity)
    have h' : (m : ℝ) ≤ (((m / 2 ^ s : ℕ) : ℝ) + 1) * 2 ^ s := by exact_mod_cast h.le
    have := two_zpow_pos e
    push_cast
    nlinarith

theorem bounds_mkUp {x : ℝ} {m : ℕ} {e : ℤ} (h : x ≤ (m : ℝ) * 2 ^ e) : x ≤ᵤ mkUp m e :=
  bounds_of_isFin (isFin_mkUp m e) (h.trans (le_toReal_mkUp m e))

@[simp] theorem toReal_zero : zero.toReal = 0 := by simp [zero, toReal]
theorem bounds_zero {x : ℝ} : (x ≤ᵤ zero) ↔ x ≤ 0 := by simp [zero]
@[simp] theorem toReal_pow2 (e : ℤ) : (pow2 e).toReal = 2 ^ e := by simp [pow2, toReal]
theorem bounds_pow2 {x : ℝ} {e : ℤ} : (x ≤ᵤ pow2 e) ↔ x ≤ 2 ^ e := by simp [pow2]

theorem bounds_ofNat (n : ℕ) : (n : ℝ) ≤ᵤ ofNat n := bounds_mkUp (by simp)

theorem bounds_absUp (x : Dy) : |x.toReal| ≤ᵤ absUp x := by
  apply bounds_mkUp
  rw [← Dy.toReal_abs]; simp [Dy.abs, Dy.toReal]

theorem bounds_ofDyUp {a : ℝ} {x : Dy} (h : a ≤ x.toReal) : a ≤ᵤ ofDyUp x := by
  unfold ofDyUp
  split
  · rename_i hm
    rw [bounds_zero]; exact h.trans ((Dy.toReal_nonpos_iff x).2 hm)
  · rename_i hm
    apply bounds_mkUp
    have : ((x.man.toNat : ℕ) : ℝ) = (x.man : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
    rw [this]; exact h

theorem toReal_ofDyExact (x : Dy) : (ofDyExact x).toReal = Max.max x.toReal 0 := by
  unfold ofDyExact
  split
  · rename_i hm; simp [max_eq_right ((Dy.toReal_nonpos_iff x).2 hm)]
  · rename_i hm
    have : 0 < x.toReal := (Dy.toReal_pos_iff x).2 (by omega)
    have h2 : ((x.man.toNat : ℕ) : ℝ) = (x.man : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega)
    rw [max_eq_left this.le]; simp [Dy.toReal, h2]

theorem isFin_add {U V : UB} (hU : U.isFin = true) (hV : V.isFin = true) : (U.add V).isFin = true := by
  cases U <;> cases V <;> simp [isFin] at hU hV
  dsimp only [add, addFin]
  split; · rfl
  split; · rfl
  split <;> (split <;> exact isFin_mkUp _ _)

theorem le_toReal_addFin {m m' : ℕ} {e e' : ℤ} (h : e' ≤ e) :
    (m : ℝ) * 2 ^ e + (m' : ℝ) * 2 ^ e' ≤ (addFin m e m' e').toReal := by
  dsimp only [addFin]
  split
  · rename_i hc
    refine le_trans ?_ (le_toReal_mkUp _ _)
    generalize (radPrec + 1) - bitLen m = k at hc ⊢
    have hb : (m' : ℝ) * 2 ^ e' ≤ 2 ^ (e - (k : ℤ)) := by
      have h1 : (m' : ℝ) < 2 ^ bitLen m' := by exact_mod_cast lt_two_pow_bitLen m'
      have h2 : (2 : ℝ) ^ (e' + (bitLen m' : ℤ)) ≤ 2 ^ (e - (k : ℤ)) :=
        zpow_le_zpow_right₀ (by norm_num) hc
      rw [two_zpow_add, two_zpow_natCast] at h2
      have := two_zpow_pos e'
      nlinarith
    have he : (2 : ℝ) ^ e = 2 ^ k * 2 ^ (e - (k : ℤ)) := by
      rw [← two_zpow_natCast, ← two_zpow_add]; congr 1; ring
    simp only [Nat.shiftLeft_eq]; push_cast
    rw [he]; nlinarith
  · refine le_trans (le_of_eq ?_) (le_toReal_mkUp _ _)
    simp only [Nat.shiftLeft_eq]; push_cast
    rw [← two_pow_toNat_sub_mul h]; ring

theorem le_toReal_add {m m' : ℕ} {e e' : ℤ} :
    (m : ℝ) * 2 ^ e + (m' : ℝ) * 2 ^ e' ≤ ((fin m e).add (fin m' e')).toReal := by
  dsimp only [add]
  split
  · subst_vars; simp
  split
  · subst_vars; simp
  split
  · exact le_toReal_addFin ‹_›
  · rw [add_comm]; exact le_toReal_addFin (le_of_lt (not_le.mp ‹_›))

theorem bounds_add {U V : UB} {a b : ℝ} (ha : a ≤ᵤ U) (hb : b ≤ᵤ V) : a + b ≤ᵤ U.add V := by
  cases U with
  | inf => trivial
  | fin m e =>
    cases V with
    | inf => trivial
    | fin m' e' =>
      exact bounds_of_isFin (isFin_add rfl rfl) ((add_le_add ha hb).trans le_toReal_add)

theorem bounds_mul {U V : UB} {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ᵤ U)
    (hb : b ≤ᵤ V) : a * b ≤ᵤ U.mul V := by
  cases U with
  | inf => trivial
  | fin m e =>
    cases V with
    | inf => trivial
    | fin m' e' =>
      apply bounds_mkUp
      have : (((m * m' : ℕ)) : ℝ) * 2 ^ (e + e') = ((m : ℝ) * 2 ^ e) * ((m' : ℝ) * 2 ^ e') := by
        rw [two_zpow_add]; push_cast; ring
      rw [this]; exact mul_le_mul ha hb hb0 (ha0.trans ha)

theorem bounds_scale {U : UB} {a : ℝ} (ha : a ≤ᵤ U) (k : ℤ) : a * 2 ^ k ≤ᵤ U.scale k := by
  cases U with
  | inf => trivial
  | fin m e =>
    show a * 2 ^ k ≤ (m : ℝ) * 2 ^ (e + k)
    rw [two_zpow_add, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right ha (two_zpow_pos k).le

theorem bounds_mulAbs {U : UB} {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ᵤ U) (x : Dy) :
    a * |x.toReal| ≤ᵤ U.mulAbs x := by
  unfold mulAbs
  split
  · rename_i e
    have : a = 0 := le_antisymm (by simpa using ha) ha0
    rw [bounds_zero, this, zero_mul]
  · exact bounds_mul ha0 (abs_nonneg _) ha (bounds_absUp x)

theorem bounds_mulNat {U : UB} {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ᵤ U) (k : ℕ) :
    a * k ≤ᵤ U.mulNat k :=
  bounds_mul ha0 (Nat.cast_nonneg k) ha (by simp)

theorem leFin_iff (m : ℕ) (e : ℤ) (m' : ℕ) (e' : ℤ) :
    leFin m e m' e' = true ↔ (m : ℝ) * 2 ^ e ≤ (m' : ℝ) * 2 ^ e' := by
  unfold leFin
  split
  · rename_i h
    rw [decide_eq_true_iff, Nat.shiftLeft_eq, ← two_pow_toNat_sub_mul h, ← mul_assoc]
    rw [mul_le_mul_iff_of_pos_right (two_zpow_pos e)]
    exact_mod_cast Iff.rfl
  · rename_i h
    rw [decide_eq_true_iff, Nat.shiftLeft_eq, ← two_pow_toNat_sub_mul (le_of_lt (not_le.mp h)),
      ← mul_assoc, mul_le_mul_iff_of_pos_right (two_zpow_pos e')]
    exact_mod_cast Iff.rfl

/-- `le U V = true` means `U ≤ V` in `[0, ∞]`. -/
theorem Bounds.of_le {U V : UB} {x : ℝ} (h : x ≤ᵤ U) (hle : le U V = true) : x ≤ᵤ V := by
  cases U with
  | inf => cases V with
    | inf => trivial
    | fin m e => simp [le] at hle
  | fin m e => cases V with
    | inf => trivial
    | fin m' e' => exact le_trans h ((leFin_iff m e m' e').1 hle)

theorem bounds_max_left {U V : UB} {x : ℝ} (h : x ≤ᵤ U) : x ≤ᵤ U.max V := by
  unfold max; split
  · exact h.of_le ‹_›
  · exact h

theorem bounds_max_right {U V : UB} {x : ℝ} (h : x ≤ᵤ V) : x ≤ᵤ U.max V := by
  unfold max; split
  · exact h
  · rename_i hle
    cases U with
    | inf => trivial
    | fin m e => cases V with
      | inf => simp [le] at hle
      | fin m' e' =>
        have hlt : ¬ ((m : ℝ) * 2 ^ e ≤ (m' : ℝ) * 2 ^ e') := fun h' =>
          hle ((leFin_iff m e m' e').2 h')
        exact le_trans h (le_of_lt (not_le.mp hlt))

theorem leDy_sound {U : UB} {c : Dy} {x : ℝ} (h : x ≤ᵤ U) (hle : U.leDy c = true) :
    x ≤ c.toReal := by
  cases U with
  | inf => simp [leDy] at hle
  | fin m e =>
    have := (Dy.ble_iff _ _).1 hle
    simp only [Dy.toReal_mk, Int.cast_natCast] at this
    exact le_trans h this

theorem bounds_div {U : UB} {x y : ℝ} {m' : ℕ} {e' : ℤ} (hx0 : 0 ≤ x) (hx : x ≤ᵤ U)
    (hm' : 0 < m') (hy : (m' : ℝ) * 2 ^ e' ≤ y) : x / y ≤ᵤ U.div (fin m' e') := by
  cases U with
  | inf => trivial
  | fin m e =>
    have hy0 : (0 : ℝ) < (m' : ℝ) * 2 ^ e' :=
      mul_pos (by exact_mod_cast hm') (two_zpow_pos e')
    have h12 : x / y ≤ (m : ℝ) * 2 ^ e / ((m' : ℝ) * 2 ^ e') :=
      (div_le_div_of_nonneg_left hx0 hy0 hy).trans (div_le_div_of_nonneg_right hx hy0.le)
    dsimp only [div]
    rw [ite_eq_right (by omega : ¬ m' = 0)]
    split
    · rename_i hm
      subst hm
      rw [bounds_zero]; simpa using h12
    · apply bounds_mkUp
      refine h12.trans ?_
      rw [div_le_iff₀ hy0]
      generalize (radPrec + bitLen m' + 1) - bitLen m = t
      have hq : m * 2 ^ t < (m * 2 ^ t / m' + 1) * m' := by
        rw [Nat.add_mul, Nat.one_mul]; exact Nat.lt_div_mul_add hm'
      have hq' : (m : ℝ) * 2 ^ t ≤ (((m * 2 ^ t / m' : ℕ) : ℝ) + 1) * m' := by
        exact_mod_cast hq.le
      have hexp : (2 : ℝ) ^ (e - e' - (t : ℤ)) * 2 ^ e' * 2 ^ t = 2 ^ e := by
        rw [← two_zpow_natCast, ← two_zpow_add, ← two_zpow_add]; congr 1; ring
      have hte : (0 : ℝ) < 2 ^ (e - e' - (t : ℤ)) := two_zpow_pos _
      simp only [Nat.shiftLeft_eq]
      push_cast
      calc (m : ℝ) * 2 ^ e = ((m : ℝ) * 2 ^ t) * (2 ^ (e - e' - (t : ℤ)) * 2 ^ e') := by
            rw [← hexp]; ring
        _ ≤ ((((m * 2 ^ t / m' : ℕ) : ℝ) + 1) * m') * (2 ^ (e - e' - (t : ℤ)) * 2 ^ e') :=
            mul_le_mul_of_nonneg_right hq' (mul_pos hte (two_zpow_pos e')).le
        _ = _ := by ring

theorem bounds_divNat {U : UB} {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ᵤ U) {k : ℕ} (hk : 0 < k) :
    x / k ≤ᵤ U.divNat k :=
  bounds_div hx0 hx hk (by simp)

theorem bounds_sqrtUp {U : UB} {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ᵤ U) : Real.sqrt x ≤ᵤ U.sqrtUp := by
  cases U with
  | inf => trivial
  | fin m e =>
    dsimp only [sqrtUp]
    split
    · rename_i hm
      subst hm
      have : x = 0 := le_antisymm (by simpa using hx) hx0
      rw [bounds_zero, this, Real.sqrt_zero]
    · generalize sqrtCand m e = cg
      split
      · rename_i _ hc
        apply bounds_mkUp
        rw [leFin_iff] at hc
        have hg : (2 : ℝ) ^ (2 * cg.2) = (2 ^ cg.2) ^ 2 := by
          rw [← zpow_natCast, ← zpow_mul]; congr 1; ring
        rw [Real.sqrt_le_left (mul_nonneg (Nat.cast_nonneg _) (two_zpow_pos _).le)]
        calc x ≤ (m : ℝ) * 2 ^ e := hx
          _ ≤ ((cg.1 * cg.1 : ℕ) : ℝ) * 2 ^ (2 * cg.2) := hc
          _ = ((cg.1 : ℝ) * 2 ^ cg.2) ^ 2 := by rw [hg]; push_cast; ring
      · have hx' : x ≤ (m : ℝ) * 2 ^ e := hx
        have hv : (0 : ℝ) ≤ (m : ℝ) * 2 ^ e := hx0.trans hx'
        have h1 : Real.sqrt x ≤ 1 + (m : ℝ) * 2 ^ e := by
          rw [Real.sqrt_le_left (by linarith)]
          nlinarith
        exact Bounds.mono h1 (bounds_add (by simp : (1 : ℝ) ≤ᵤ fin 1 0)
          (show (m : ℝ) * 2 ^ e ≤ᵤ fin m e from le_rfl))

end UB

/-! ## `Ball` -/

namespace Ball

/-- `x ∈ b`: `|x - b.mid| ≤ᵤ b.rad` (every real if `b.rad = inf`). -/
def mem (b : Ball) (x : ℝ) : Prop := |x - b.mid.toReal| ≤ᵤ b.rad

instance : Membership ℝ Ball := ⟨mem⟩

theorem mem_def {b : Ball} {x : ℝ} : x ∈ b ↔ |x - b.mid.toReal| ≤ᵤ b.rad := Iff.rfl

theorem mem_iff_le {b : Ball} {x : ℝ} (hb : b.isFinite = true) :
    x ∈ b ↔ |x - b.mid.toReal| ≤ b.rad.toReal := by
  rw [mem_def, UB.bounds_iff]; simp [isFinite] at hb; simp [hb]

@[simp] theorem mem_top (x : ℝ) : x ∈ top := trivial

theorem mem_of_rad_inf {b : Ball} (hb : b.rad = .inf) (x : ℝ) : x ∈ b := by
  rw [mem_def, hb]; trivial

theorem mem_ofDy_iff {d : Dy} {x : ℝ} : x ∈ ofDy d ↔ x = d.toReal := by
  rw [mem_def]; simp [ofDy, UB.bounds_zero, abs_nonpos_iff, sub_eq_zero]

theorem mem_ofDy (d : Dy) : d.toReal ∈ ofDy d := mem_ofDy_iff.2 rfl
@[simp] theorem mem_zero : (0 : ℝ) ∈ zero := mem_ofDy_iff.2 (by simp)
@[simp] theorem mem_one : (1 : ℝ) ∈ one := mem_ofDy_iff.2 (by simp)
@[simp] theorem mem_ofInt (n : ℤ) : (n : ℝ) ∈ ofInt n := mem_ofDy_iff.2 (by simp)
@[simp] theorem mem_ofNat (n : ℕ) : (n : ℝ) ∈ ofNat n := mem_ofDy_iff.2 (by simp)

/-- The truncation error of `roundMk`: below one unit `2^(e+s)` in the last place. -/
theorem trunc_err (man : ℤ) (s : ℕ) (e : ℤ) :
    |(man : ℝ) * 2 ^ e - ((if man < 0 then -(((man.natAbs >>> s : ℕ)) : ℤ)
      else (((man.natAbs >>> s : ℕ)) : ℤ) : ℤ) : ℝ) * 2 ^ (e + (s : ℤ))| ≤ 2 ^ (e + (s : ℤ)) := by
  rw [Nat.shiftRight_eq_div_pow]
  have hq1 : ((man.natAbs / 2 ^ s : ℕ) : ℝ) * 2 ^ s ≤ man.natAbs := by
    exact_mod_cast Nat.div_mul_le_self man.natAbs (2 ^ s)
  have hq2 : (man.natAbs : ℝ) < ((man.natAbs / 2 ^ s : ℕ) : ℝ) * 2 ^ s + 2 ^ s := by
    exact_mod_cast Nat.lt_div_mul_add (by positivity)
  generalize man.natAbs / 2 ^ s = q at hq1 hq2 ⊢
  have he := two_zpow_pos e
  rw [two_zpow_add, two_zpow_natCast]
  split
  · rename_i hm
    rw [show (man : ℝ) = -(man.natAbs : ℝ) by rw [Dy.natAbs_cast_of_neg hm]; ring]
    simp only [Int.cast_neg, Int.cast_natCast]
    rw [abs_le]; constructor <;> nlinarith
  · rename_i hm
    rw [show (man : ℝ) = (man.natAbs : ℝ) by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast not_lt.mp hm)]]
    simp only [Int.cast_natCast]
    rw [abs_le]; constructor <;> nlinarith

/-- **CP of the core normalization.** -/
theorem mem_roundMk {p : ℕ} {m : Dy} {r : UB} {x : ℝ} (h : |x - m.toReal| ≤ᵤ r) :
    x ∈ roundMk p m r := by
  dsimp only [roundMk]
  split
  · exact h
  · rw [mem_def]
    refine UB.Bounds.mono ?_ (UB.bounds_add h (UB.bounds_pow2.2 (trunc_err m.man _ m.exp)))
    simp only [Dy.toReal]
    exact abs_sub_le _ _ _

theorem mem_round {p : ℕ} {X : Ball} {x : ℝ} (hx : x ∈ X) : x ∈ X.round p := mem_roundMk hx

theorem mem_addErr {X : Ball} {r : UB} {x y : ℝ} (hx : x ∈ X) (hy : |y - x| ≤ᵤ r) :
    y ∈ X.addErr r := by
  rw [mem_def]
  refine UB.Bounds.mono ?_ (UB.bounds_add hx hy)
  calc |y - X.mid.toReal| = |(x - X.mid.toReal) + (y - x)| := by ring_nf
    _ ≤ _ := abs_add_le _ _

theorem mem_neg {X : Ball} {x : ℝ} (hx : x ∈ X) : -x ∈ X.neg := by
  rw [mem_def]; simp only [neg, Dy.toReal_neg]
  rw [show -x - -X.mid.toReal = -(x - X.mid.toReal) by ring, abs_neg]; exact hx

theorem mem_add {p : ℕ} {X Y : Ball} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) :
    x + y ∈ add p X Y := by
  apply mem_roundMk
  refine UB.Bounds.mono ?_ (UB.bounds_add hx hy)
  rw [Dy.toReal_add]
  calc |x + y - (X.mid.toReal + Y.mid.toReal)|
      = |(x - X.mid.toReal) + (y - Y.mid.toReal)| := by ring_nf
    _ ≤ _ := abs_add_le _ _

theorem mem_sub {p : ℕ} {X Y : Ball} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) :
    x - y ∈ sub p X Y := by
  apply mem_roundMk
  refine UB.Bounds.mono ?_ (UB.bounds_add hx hy)
  rw [Dy.toReal_sub]
  calc |x - y - (X.mid.toReal - Y.mid.toReal)|
      = |(x - X.mid.toReal) - (y - Y.mid.toReal)| := by ring_nf
    _ ≤ _ := abs_sub _ _

theorem mem_mul {p : ℕ} {X Y : Ball} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) :
    x * y ∈ mul p X Y := by
  apply mem_roundMk
  have h1 := UB.bounds_mulAbs (abs_nonneg _) hx Y.mid
  have h2 := UB.bounds_mulAbs (abs_nonneg _) hy X.mid
  have h3 := UB.bounds_mul (abs_nonneg _) (abs_nonneg _) hx hy
  refine UB.Bounds.mono ?_ (UB.bounds_add h1 (UB.bounds_add h2 h3))
  rw [Dy.toReal_mul]
  set a := x - X.mid.toReal
  set b := y - Y.mid.toReal
  calc |x * y - X.mid.toReal * Y.mid.toReal|
      = |a * Y.mid.toReal + (b * X.mid.toReal + a * b)| := by simp only [a, b]; ring_nf
    _ ≤ |a * Y.mid.toReal| + (|b * X.mid.toReal| + |a * b|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ = _ := by simp only [abs_mul]

theorem mem_sqr {p : ℕ} {X : Ball} {x : ℝ} (hx : x ∈ X) : x * x ∈ sqr p X := by
  apply mem_roundMk
  have h1 := UB.bounds_scale (UB.bounds_mulAbs (abs_nonneg _) hx X.mid) 1
  have h3 := UB.bounds_mul (abs_nonneg _) (abs_nonneg _) hx hx
  refine UB.Bounds.mono ?_ (UB.bounds_add h1 h3)
  rw [Dy.toReal_mul]
  set a := x - X.mid.toReal
  calc |x * x - X.mid.toReal * X.mid.toReal|
      = |(a * X.mid.toReal) * 2 + a * a| := by simp only [a]; ring_nf
    _ ≤ |(a * X.mid.toReal) * 2| + |a * a| := abs_add_le _ _
    _ = _ := by simp only [abs_mul, zpow_one]; norm_num

theorem mem_sqr' {p : ℕ} {X : Ball} {x : ℝ} (hx : x ∈ X) : x ^ 2 ∈ sqr p X := by
  rw [sq]; exact mem_sqr hx

theorem mem_mulDy {p : ℕ} {c : Dy} {X : Ball} {x : ℝ} (hx : x ∈ X) :
    c.toReal * x ∈ mulDy p c X := by
  apply mem_roundMk
  refine UB.Bounds.mono (le_of_eq ?_) (UB.bounds_mulAbs (abs_nonneg _) hx c)
  rw [Dy.toReal_mul, ← mul_sub, abs_mul, mul_comm]

theorem mem_mulNat {p : ℕ} {X : Ball} {x : ℝ} (hx : x ∈ X) (k : ℕ) :
    x * k ∈ mulNat p X k := by
  have := mem_mulDy (p := p) (c := Dy.ofNat k) hx
  rw [Dy.toReal_ofNat, mul_comm] at this; exact this

theorem mem_mulInt {p : ℕ} {X : Ball} {x : ℝ} (hx : x ∈ X) (k : ℤ) :
    x * k ∈ mulInt p X k := by
  have := mem_mulDy (p := p) (c := Dy.ofInt k) hx
  rw [Dy.toReal_ofInt, mul_comm] at this; exact this

theorem mem_scale2 {X : Ball} {x : ℝ} (hx : x ∈ X) (k : ℤ) : x * 2 ^ k ∈ X.scale2 k := by
  rw [mem_def]
  refine UB.Bounds.mono (le_of_eq ?_) (UB.bounds_scale hx k)
  simp only [scale2, Dy.toReal_scale]
  rw [← sub_mul, abs_mul, abs_of_pos (two_zpow_pos k)]

end Ball

/-! ## `CBox` -/

namespace CBox

/-- `z ∈ B`: `z.re ∈ B.re ∧ z.im ∈ B.im`. -/
def mem (B : CBox) (z : ℂ) : Prop := B.re.mem z.re ∧ B.im.mem z.im

instance : Membership ℂ CBox := ⟨mem⟩

theorem mem_def {B : CBox} {z : ℂ} : z ∈ B ↔ z.re ∈ B.re ∧ z.im ∈ B.im := Iff.rfl

theorem mem_mk {a b : Ball} {z : ℂ} : z ∈ (⟨a, b⟩ : CBox) ↔ z.re ∈ a ∧ z.im ∈ b := Iff.rfl

@[simp] theorem mem_top (z : ℂ) : z ∈ top := ⟨trivial, trivial⟩

end CBox

end NonUniqueEuler.Verify
