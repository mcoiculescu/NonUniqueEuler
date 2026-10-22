import NonUniqueEuler.Defs.Verify.Sem
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Cast.Defs

/-!
# Containment (CP) of the remaining `Ball` operations, of `CBox`, and of the series helpers

Semantics: `NonUniqueEuler/Defs/Verify/Sem.lean` (`x ∈ b`, `z ∈ B`, `x ≤ᵤ U`).

Every operation of `Verify/Comp/{Ball,CBox,Series}.lean` that is not treated in `Sem.lean`
gets its CP lemma here, without side conditions (division by a ball that may contain `0`
gives `top`, which contains Lean's `0⁻¹ = 0`). The elementary functions (`exp`, `H`,
`UB.expUp`) are in `SemElem.lean`.
-/

noncomputable section

namespace NonUniqueEuler.Verify

open Finset

/-- Floor division error: with `q = ⌊N / k⌋` (`Int.ediv`, `k > 0`),
`|N/k · c - q · c| ≤ c` for `c > 0`. -/
theorem floorDiv_err (N : ℤ) {k : ℕ} (hk : 0 < k) {c : ℝ} (hc : 0 < c) :
    |(N : ℝ) / k * c - ((N / (k : ℤ) : ℤ) : ℝ) * c| ≤ c := by
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have h1 : N / (k : ℤ) * k ≤ N := Int.ediv_mul_le N hk'.ne'
  have h2 : N < (N / (k : ℤ) + 1) * k := Int.lt_ediv_add_one_mul_self N hk'
  generalize N / (k : ℤ) = q at h1 h2 ⊢
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h1' : (q : ℝ) * k ≤ N := by exact_mod_cast h1
  have h2' : (N : ℝ) < ((q : ℝ) + 1) * k := by exact_mod_cast h2
  set u : ℝ := (N : ℝ) / k
  have hu : u * k = N := div_mul_cancel₀ _ hkR.ne'
  have hqu : (q : ℝ) ≤ u := le_of_mul_le_mul_right (by rw [hu]; exact h1') hkR
  have huq : u < (q : ℝ) + 1 := lt_of_mul_lt_mul_right (by rw [hu]; exact h2') hkR.le
  rw [← sub_mul, abs_mul, abs_of_pos hc, abs_of_nonneg (by linarith)]
  nlinarith

namespace UB

theorem toDy?_eq_some {U : UB} {d : Dy} (h : U.toDy? = some d) :
    U.isFin = true ∧ d.toReal = U.toReal := by
  cases U with
  | fin m e => simp only [toDy?, Option.some.injEq] at h; subst h; simp [isFin, Dy.toReal]
  | inf => simp [toDy?] at h

/-- `UB.div` with a divisor given as any finite `UB` with positive value `≤ y`. -/
theorem bounds_div' {U C : UB} {x y : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ᵤ U) (hC : C.isFin = true)
    (hC0 : 0 < C.toReal) (hy : C.toReal ≤ y) : x / y ≤ᵤ U.div C := by
  cases C with
  | inf => simp [isFin] at hC
  | fin m' e' =>
    have hm' : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with h | h
      · subst h; simp at hC0
      · exact h
    exact bounds_div hx0 hx hm' hy

end UB

namespace Ball

/-! ## Endpoints, intervals, hulls -/

theorem lower?_le {X : Ball} {l : Dy} (h : X.lower? = some l) {x : ℝ} (hx : x ∈ X) :
    l.toReal ≤ x := by
  unfold lower? at h
  split at h
  · rename_i m e hr
    cases h
    rw [mem_def, hr, UB.bounds_fin] at hx
    rw [Dy.toReal_sub]; simp only [Dy.toReal_mk, Int.cast_natCast]
    have := neg_abs_le (x - X.mid.toReal)
    linarith
  · simp at h

theorem le_upper? {X : Ball} {u : Dy} (h : X.upper? = some u) {x : ℝ} (hx : x ∈ X) :
    x ≤ u.toReal := by
  unfold upper? at h
  split at h
  · rename_i m e hr
    cases h
    rw [mem_def, hr, UB.bounds_fin] at hx
    rw [Dy.toReal_add]; simp only [Dy.toReal_mk, Int.cast_natCast]
    have := le_abs_self (x - X.mid.toReal)
    linarith
  · simp at h

theorem lower?_isSome {X : Ball} (h : X.isFinite = true) : ∃ l, X.lower? = some l := by
  unfold lower?; unfold isFinite at h
  split
  · exact ⟨_, rfl⟩
  · rename_i hr; rw [hr] at h; simp [UB.isFin] at h

theorem upper?_isSome {X : Ball} (h : X.isFinite = true) : ∃ u, X.upper? = some u := by
  unfold upper?; unfold isFinite at h
  split
  · exact ⟨_, rfl⟩
  · rename_i hr; rw [hr] at h; simp [UB.isFin] at h

theorem mem_ofInterval {p : ℕ} {lo hi : Dy} {x : ℝ} (h1 : lo.toReal ≤ x) (h2 : x ≤ hi.toReal) :
    x ∈ ofInterval p lo hi := by
  apply mem_roundMk
  apply UB.bounds_ofDyUp
  simp only [Dy.toReal_scale, Dy.toReal_add, Dy.toReal_sub, zpow_neg, zpow_one]
  rw [abs_le]; constructor <;> linarith

theorem mem_hull {p : ℕ} {L U : Ball} {l u z : ℝ} (hl : l ∈ L) (hu : u ∈ U) (h1 : l ≤ z)
    (h2 : z ≤ u) : z ∈ hull p L U := by
  unfold hull
  split
  · rename_i a b ha hb
    exact mem_ofInterval ((lower?_le ha hl).trans h1) (h2.trans (le_upper? hb hu))
  · exact mem_top _

theorem mem_union_of {p : ℕ} {X Y : Ball} {z : ℝ}
    (hz : ∀ a b c d : Dy, X.lower? = some a → X.upper? = some b → Y.lower? = some c →
      Y.upper? = some d → Min.min a.toReal c.toReal ≤ z ∧ z ≤ Max.max b.toReal d.toReal) :
    z ∈ union p X Y := by
  unfold union
  split
  · rename_i a b c d ha hb hc hd
    obtain ⟨h1, h2⟩ := hz a b c d ha hb hc hd
    exact mem_ofInterval (by simpa using h1) (by simpa using h2)
  · exact mem_top _

theorem mem_union_left {p : ℕ} {X Y : Ball} {x : ℝ} (hx : x ∈ X) : x ∈ union p X Y :=
  mem_union_of fun _ _ _ _ ha hb _ _ =>
    ⟨(min_le_left _ _).trans (lower?_le ha hx), (le_upper? hb hx).trans (le_max_left _ _)⟩

theorem mem_union_right {p : ℕ} {X Y : Ball} {y : ℝ} (hy : y ∈ Y) : y ∈ union p X Y :=
  mem_union_of fun _ _ _ _ _ _ hc hd =>
    ⟨(min_le_right _ _).trans (lower?_le hc hy), (le_upper? hd hy).trans (le_max_right _ _)⟩

/-- The union contains every point between a point of `X` and a point of `Y`. -/
theorem mem_union_of_between {p : ℕ} {X Y : Ball} {x y z : ℝ} (hx : x ∈ X) (hy : y ∈ Y)
    (h1 : Min.min x y ≤ z) (h2 : z ≤ Max.max x y) : z ∈ union p X Y :=
  mem_union_of fun _ _ _ _ ha hb hc hd =>
    ⟨le_trans (min_le_min (lower?_le ha hx) (lower?_le hc hy)) h1,
     le_trans h2 (max_le_max (le_upper? hb hx) (le_upper? hd hy))⟩

theorem mem_nonnegPart {p : ℕ} {X : Ball} {x : ℝ} (hx : x ∈ X) (h0 : 0 ≤ x) :
    x ∈ nonnegPart p X := by
  unfold nonnegPart
  split
  · exact mem_top _
  · rename_i m e hr
    have hx' : |x - X.mid.toReal| ≤ (m : ℝ) * 2 ^ e := by rw [mem_def, hr] at hx; exact hx
    have hab := le_abs_self (x - X.mid.toReal)
    dsimp only
    split
    · rename_i hneg
      exfalso
      have := (Dy.toReal_neg_iff _).2 hneg
      simp only [Dy.toReal_add, Dy.toReal_mk, Int.cast_natCast] at this
      linarith
    · split
      · exact hx
      · apply mem_ofInterval
        · simpa using h0
        · simp only [Dy.toReal_add, Dy.toReal_mk, Int.cast_natCast]; linarith

/-! ## Division and reciprocals -/

theorem mem_divNat {p : ℕ} {X : Ball} {x : ℝ} (hx : x ∈ X) (k : ℕ) : x / k ∈ divNat p X k := by
  unfold divNat
  split
  · exact mem_top _
  · rename_i hk
    have hk0 : 0 < k := Nat.pos_of_ne_zero hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    rw [mem_def]
    dsimp only
    generalize (p + bitLen k + 1) - bitLen X.mid.man.natAbs = t
    have hc := two_zpow_pos (X.mid.exp - (t : ℤ))
    have herr := floorDiv_err (X.mid.man * 2 ^ t) hk0 hc
    have hval : X.mid.toReal / k = ((X.mid.man * 2 ^ t : ℤ) : ℝ) / k * 2 ^ (X.mid.exp - (t : ℤ)) := by
      have : (2 : ℝ) ^ X.mid.exp = 2 ^ t * 2 ^ (X.mid.exp - (t : ℤ)) := by
        rw [← two_zpow_natCast, ← two_zpow_add]; congr 1; ring
      simp only [Dy.toReal]; rw [this]; push_cast; ring
    refine UB.Bounds.mono ?_ (UB.bounds_add (UB.bounds_divNat (abs_nonneg _) hx hk0)
      (UB.bounds_pow2.2 herr))
    rw [shl_eq, Dy.toReal_mk]
    calc |x / k - ((X.mid.man * 2 ^ t / (k : ℤ) : ℤ) : ℝ) * 2 ^ (X.mid.exp - (t : ℤ))|
        = |(x - X.mid.toReal) / k + (X.mid.toReal / k -
            ((X.mid.man * 2 ^ t / (k : ℤ) : ℤ) : ℝ) * 2 ^ (X.mid.exp - (t : ℤ)))| := by ring_nf
      _ ≤ |(x - X.mid.toReal) / k| + |X.mid.toReal / k -
            ((X.mid.man * 2 ^ t / (k : ℤ) : ℤ) : ℝ) * 2 ^ (X.mid.exp - (t : ℤ))| := abs_add_le _ _
      _ = _ := by rw [abs_div, abs_of_pos hkR, hval]

theorem mem_inv {p : ℕ} {X : Ball} {x : ℝ} (hx : x ∈ X) : x⁻¹ ∈ inv p X := by
  unfold inv
  split
  · exact mem_top _
  · rename_i m e hr
    have hx' : |x - X.mid.toReal| ≤ (m : ℝ) * 2 ^ e := by rw [mem_def, hr] at hx; exact hx
    have h1 := neg_abs_le (x - X.mid.toReal)
    have h2 := le_abs_self (x - X.mid.toReal)
    dsimp only
    split
    · rename_i hc
      set lo := X.mid.sub ⟨(m : ℤ), e⟩
      set hi := X.mid.add ⟨(m : ℤ), e⟩
      have hlo : lo.toReal ≤ x := by
        simp only [lo, Dy.toReal_sub, Dy.toReal_mk, Int.cast_natCast]; linarith
      have hhi : x ≤ hi.toReal := by
        simp only [hi, Dy.toReal_add, Dy.toReal_mk, Int.cast_natCast]; linarith
      have hlohi : lo.toReal ≤ hi.toReal := hlo.trans hhi
      have hne : ∀ d : Dy, d.toReal ≠ 0 → d.man ≠ 0 := fun d hd h =>
        hd ((Dy.toReal_eq_zero_iff d).2 h)
      rcases hc with hc | hc
      · have hlo0 : 0 < lo.toReal := (Dy.toReal_pos_iff _).2 hc
        have hx0 : 0 < x := lt_of_lt_of_le hlo0 hlo
        apply mem_ofInterval
        · exact (Dy.recipDown_le p (hne hi (by linarith))).trans (inv_anti₀ hx0 hhi)
        · exact (inv_anti₀ hlo0 hlo).trans (Dy.le_recipUp p (hne lo hlo0.ne'))
      · have hhi0 : hi.toReal < 0 := (Dy.toReal_neg_iff _).2 hc
        have hx0 : x < 0 := lt_of_le_of_lt hhi hhi0
        have hlo0 : lo.toReal < 0 := lt_of_le_of_lt hlo hx0
        apply mem_ofInterval
        · exact (Dy.recipDown_le p (hne hi hhi0.ne)).trans ((inv_le_inv_of_neg hhi0 hx0).2 hhi)
        · exact ((inv_le_inv_of_neg hx0 hlo0).2 hlo).trans (Dy.le_recipUp p (hne lo hlo0.ne))
    · exact mem_top _

theorem mem_div {p : ℕ} {X Y : Ball} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) :
    x / y ∈ div p X Y := by
  rw [div_eq_mul_inv]; exact mem_mul hx (mem_inv hy)

/-! ## Magnitudes and certified comparisons -/

theorem abs_le_absUB {X : Ball} {x : ℝ} (hx : x ∈ X) : |x| ≤ᵤ X.absUB := by
  refine UB.Bounds.mono ?_ (UB.bounds_add (UB.bounds_absUp X.mid) hx)
  calc |x| = |X.mid.toReal + (x - X.mid.toReal)| := by ring_nf
    _ ≤ _ := abs_add_le _ _

theorem le_upperUB {X : Ball} {x : ℝ} (hx : x ∈ X) : x ≤ᵤ X.upperUB := by
  refine UB.Bounds.mono ?_ (UB.bounds_add (UB.bounds_ofDyUp le_rfl) hx)
  have := le_abs_self (x - X.mid.toReal)
  linarith

theorem absLow_nonneg (X : Ball) : 0 ≤ X.absLow.toReal := by
  unfold absLow
  split
  · simp
  · dsimp only
    split
    · rename_i h; exact ((Dy.toReal_pos_iff _).2 h).le
    · simp

theorem absLow_le {X : Ball} {x : ℝ} (hx : x ∈ X) : X.absLow.toReal ≤ |x| := by
  unfold absLow
  split
  · simp
  · rename_i m e hr
    have hx' : |x - X.mid.toReal| ≤ (m : ℝ) * 2 ^ e := by rw [mem_def, hr] at hx; exact hx
    dsimp only
    split
    · simp only [Dy.toReal_sub, Dy.toReal_abs, Dy.toReal_mk, Int.cast_natCast]
      have := abs_sub_abs_le_abs_sub X.mid.toReal x
      rw [abs_sub_comm] at this
      linarith
    · simp

theorem posC_sound {X : Ball} (h : X.posC = true) {x : ℝ} (hx : x ∈ X) : 0 < x := by
  unfold posC at h
  split at h
  · rename_i l hl; exact lt_of_lt_of_le ((Dy.isPos_iff l).1 h) (lower?_le hl hx)
  · simp at h

theorem negC_sound {X : Ball} (h : X.negC = true) {x : ℝ} (hx : x ∈ X) : x < 0 := by
  unfold negC at h
  split at h
  · rename_i u hu; exact lt_of_le_of_lt (le_upper? hu hx) ((Dy.isNeg_iff u).1 h)
  · simp at h

theorem nonnegC_sound {X : Ball} (h : X.nonnegC = true) {x : ℝ} (hx : x ∈ X) : 0 ≤ x := by
  unfold nonnegC at h
  split at h
  · rename_i l hl; exact le_trans ((Dy.isNonneg_iff l).1 h) (lower?_le hl hx)
  · simp at h

theorem ltDy_sound {X : Ball} {c : Dy} (h : X.ltDy c = true) {x : ℝ} (hx : x ∈ X) :
    x < c.toReal := by
  unfold ltDy at h
  split at h
  · rename_i u hu; exact lt_of_le_of_lt (le_upper? hu hx) ((Dy.blt_iff u c).1 h)
  · simp at h

theorem leDy_sound {X : Ball} {c : Dy} (h : X.leDy c = true) {x : ℝ} (hx : x ∈ X) :
    x ≤ c.toReal := by
  unfold leDy at h
  split at h
  · rename_i u hu; exact le_trans (le_upper? hu hx) ((Dy.ble_iff u c).1 h)
  · simp at h

theorem gtDy_sound {X : Ball} {c : Dy} (h : X.gtDy c = true) {x : ℝ} (hx : x ∈ X) :
    c.toReal < x := by
  unfold gtDy at h
  split at h
  · rename_i l hl; exact lt_of_lt_of_le ((Dy.blt_iff c l).1 h) (lower?_le hl hx)
  · simp at h

theorem geDy_sound {X : Ball} {c : Dy} (h : X.geDy c = true) {x : ℝ} (hx : x ∈ X) :
    c.toReal ≤ x := by
  unfold geDy at h
  split at h
  · rename_i l hl; exact le_trans ((Dy.ble_iff c l).1 h) (lower?_le hl hx)
  · simp at h

theorem ltB_sound {X Y : Ball} (h : ltB X Y = true) {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) :
    x < y := by
  unfold ltB at h
  split at h
  · rename_i u l hu hl
    exact lt_of_le_of_lt (le_upper? hu hx) (lt_of_lt_of_le ((Dy.blt_iff u l).1 h) (lower?_le hl hy))
  · simp at h

theorem isFinite_iff (X : Ball) : X.isFinite = true ↔ X.rad.isFin = true := Iff.rfl

/-! ## Rationals -/

theorem mem_ofFrac (p : ℕ) (n : ℤ) (d : ℕ) : (n : ℝ) / d ∈ ofFrac p n d := by
  unfold ofFrac
  split
  · exact mem_top _
  · rename_i hd
    split
    · rename_i h2
      apply mem_roundMk
      rw [UB.bounds_zero, abs_nonpos_iff, sub_eq_zero, Dy.toReal_mk]
      have hd' : (d : ℝ) = 2 ^ d.log2 := by
        rw [Nat.one_shiftLeft] at h2; exact_mod_cast h2.symm
      rw [hd', zpow_neg, two_zpow_natCast, div_eq_mul_inv]
    · rename_i h2
      have hd0 : 0 < d := Nat.pos_of_ne_zero hd
      rw [mem_def]
      dsimp only
      generalize (p + bitLen d + 1) - bitLen n.natAbs = t
      rw [UB.bounds_pow2, shl_eq, Dy.toReal_mk]
      have hval : (n : ℝ) / d = ((n * 2 ^ t : ℤ) : ℝ) / d * 2 ^ (-(t : ℤ)) := by
        push_cast; rw [zpow_neg, two_zpow_natCast]; field_simp
      rw [hval]
      exact floorDiv_err (n * 2 ^ t) hd0 (two_zpow_pos _)

theorem mem_ofRat (p : ℕ) (q : ℚ) : (q : ℝ) ∈ ofRat p q := by
  rw [Rat.cast_def]; exact mem_ofFrac p q.num q.den

end Ball

/-! ## `CBox` -/

namespace CBox

open Complex

theorem mem_ofBall {b : Ball} {x : ℝ} (hx : x ∈ b) : (x : ℂ) ∈ ofBall b :=
  mem_def.2 ⟨by rw [ofReal_re]; exact hx, by rw [ofReal_im]; exact Ball.mem_zero⟩

theorem mem_ofIm {b : Ball} {y : ℝ} (hy : y ∈ b) : (y : ℂ) * I ∈ ofIm b :=
  mem_def.2 ⟨by rw [show ((y : ℂ) * I).re = 0 by simp]; exact Ball.mem_zero,
    by rw [show ((y : ℂ) * I).im = y by simp]; exact hy⟩

theorem mem_ofDy (d : Dy) : (d.toReal : ℂ) ∈ ofDy d := mem_ofBall (Ball.mem_ofDy d)

@[simp] theorem mem_zero : (0 : ℂ) ∈ zero :=
  mem_def.2 ⟨by rw [zero_re]; exact Ball.mem_zero, by rw [zero_im]; exact Ball.mem_zero⟩

@[simp] theorem mem_one : (1 : ℂ) ∈ one :=
  mem_def.2 ⟨by rw [one_re]; exact Ball.mem_one, by rw [one_im]; exact Ball.mem_zero⟩

@[simp] theorem mem_ofNat (n : ℕ) : (n : ℂ) ∈ ofNat n :=
  mem_def.2 ⟨by rw [natCast_re]; exact Ball.mem_ofNat n, by rw [natCast_im]; exact Ball.mem_zero⟩

theorem mem_ofRat (p : ℕ) (x y : ℚ) : (⟨x, y⟩ : ℂ) ∈ ofRat p x y :=
  mem_def.2 ⟨Ball.mem_ofRat p x, Ball.mem_ofRat p y⟩

theorem isFinite_iff (z : CBox) :
    z.isFinite = true ↔ z.re.isFinite = true ∧ z.im.isFinite = true := by
  simp [isFinite]

theorem mem_round {p : ℕ} {Z : CBox} {z : ℂ} (hz : z ∈ Z) : z ∈ Z.round p :=
  mem_def.2 ⟨Ball.mem_round hz.1, Ball.mem_round hz.2⟩

theorem mem_neg {Z : CBox} {z : ℂ} (hz : z ∈ Z) : -z ∈ Z.neg :=
  mem_def.2 ⟨by rw [neg_re]; exact Ball.mem_neg hz.1, by rw [neg_im]; exact Ball.mem_neg hz.2⟩

theorem mem_conj {Z : CBox} {z : ℂ} (hz : z ∈ Z) : (starRingEnd ℂ) z ∈ Z.conj :=
  mem_def.2 ⟨by rw [conj_re]; exact hz.1, by rw [conj_im]; exact Ball.mem_neg hz.2⟩

theorem mem_mulI {Z : CBox} {z : ℂ} (hz : z ∈ Z) : I * z ∈ Z.mulI :=
  mem_def.2 ⟨by rw [I_mul_re]; exact Ball.mem_neg hz.2, by rw [I_mul_im]; exact hz.1⟩

theorem mem_add {p : ℕ} {Z W : CBox} {z w : ℂ} (hz : z ∈ Z) (hw : w ∈ W) : z + w ∈ add p Z W :=
  ⟨by rw [add_re]; exact Ball.mem_add hz.1 hw.1, by rw [add_im]; exact Ball.mem_add hz.2 hw.2⟩

theorem mem_sub {p : ℕ} {Z W : CBox} {z w : ℂ} (hz : z ∈ Z) (hw : w ∈ W) : z - w ∈ sub p Z W :=
  ⟨by rw [sub_re]; exact Ball.mem_sub hz.1 hw.1, by rw [sub_im]; exact Ball.mem_sub hz.2 hw.2⟩

theorem mem_mul {p : ℕ} {Z W : CBox} {z w : ℂ} (hz : z ∈ Z) (hw : w ∈ W) : z * w ∈ mul p Z W :=
  ⟨by rw [mul_re]; exact Ball.mem_sub (Ball.mem_mul hz.1 hw.1) (Ball.mem_mul hz.2 hw.2),
   by rw [mul_im]; exact Ball.mem_add (Ball.mem_mul hz.1 hw.2) (Ball.mem_mul hz.2 hw.1)⟩

theorem mem_sqr {p : ℕ} {Z : CBox} {z : ℂ} (hz : z ∈ Z) : z * z ∈ sqr p Z :=
  ⟨by rw [mul_re]; exact Ball.mem_sub (Ball.mem_sqr hz.1) (Ball.mem_sqr hz.2),
   by
    rw [mul_im, show z.re * z.im + z.im * z.re = z.re * z.im * 2 ^ (1 : ℤ) by rw [zpow_one]; ring]
    exact Ball.mem_scale2 (Ball.mem_mul hz.1 hz.2) 1⟩

theorem mem_mulBall {p : ℕ} {Z : CBox} {b : Ball} {z : ℂ} {x : ℝ} (hz : z ∈ Z) (hx : x ∈ b) :
    z * x ∈ mulBall p Z b :=
  mem_def.2 ⟨by rw [re_mul_ofReal]; exact Ball.mem_mul hz.1 hx,
    by rw [im_mul_ofReal]; exact Ball.mem_mul hz.2 hx⟩

theorem mem_mulDy {p : ℕ} {c : Dy} {Z : CBox} {z : ℂ} (hz : z ∈ Z) :
    (c.toReal : ℂ) * z ∈ mulDy p c Z :=
  mem_def.2 ⟨by rw [re_ofReal_mul]; exact Ball.mem_mulDy hz.1,
    by rw [im_ofReal_mul]; exact Ball.mem_mulDy hz.2⟩

theorem mem_mulNat {p : ℕ} {Z : CBox} {z : ℂ} (hz : z ∈ Z) (k : ℕ) : z * k ∈ mulNat p Z k := by
  rw [show (k : ℂ) = ((k : ℝ) : ℂ) by norm_cast]
  exact mem_def.2 ⟨by rw [re_mul_ofReal]; exact Ball.mem_mulNat hz.1 k,
    by rw [im_mul_ofReal]; exact Ball.mem_mulNat hz.2 k⟩

theorem mem_scale2 {Z : CBox} {z : ℂ} (hz : z ∈ Z) (k : ℤ) :
    z * (((2 : ℝ) ^ k : ℝ) : ℂ) ∈ Z.scale2 k :=
  mem_def.2 ⟨by rw [re_mul_ofReal]; exact Ball.mem_scale2 hz.1 k,
    by rw [im_mul_ofReal]; exact Ball.mem_scale2 hz.2 k⟩

theorem mem_divNat {p : ℕ} {Z : CBox} {z : ℂ} (hz : z ∈ Z) (k : ℕ) : z / k ∈ divNat p Z k :=
  mem_def.2 ⟨by rw [div_natCast_re]; exact Ball.mem_divNat hz.1 k,
    by rw [div_natCast_im]; exact Ball.mem_divNat hz.2 k⟩

theorem mem_divBall {p : ℕ} {Z : CBox} {b : Ball} {z : ℂ} {x : ℝ} (hz : z ∈ Z) (hx : x ∈ b) :
    z / x ∈ divBall p Z b :=
  mem_def.2 ⟨by rw [div_ofReal_re, div_eq_mul_inv]; exact Ball.mem_mul hz.1 (Ball.mem_inv hx),
    by rw [div_ofReal_im, div_eq_mul_inv]; exact Ball.mem_mul hz.2 (Ball.mem_inv hx)⟩

theorem mem_addBall {p : ℕ} {Z : CBox} {b : Ball} {z : ℂ} {x : ℝ} (hz : z ∈ Z) (hx : x ∈ b) :
    z + x ∈ addBall p Z b :=
  mem_def.2 ⟨by rw [add_re, ofReal_re]; exact Ball.mem_add hz.1 hx,
    by rw [add_im, ofReal_im, add_zero]; exact hz.2⟩

theorem mem_inv {p : ℕ} {Z : CBox} {z : ℂ} (hz : z ∈ Z) : z⁻¹ ∈ inv p Z := by
  have ht : normSq z ∈ Ball.add p (Ball.sqr p Z.re) (Ball.sqr p Z.im) := by
    rw [normSq_apply]; exact Ball.mem_add (Ball.mem_sqr hz.1) (Ball.mem_sqr hz.2)
  have hu := Ball.mem_inv (p := p) ht
  constructor
  · rw [inv_re, div_eq_mul_inv]; exact Ball.mem_mul hz.1 hu
  · rw [inv_im, neg_div, div_eq_mul_inv]; exact Ball.mem_neg (Ball.mem_mul hz.2 hu)

theorem mem_div {p : ℕ} {Z W : CBox} {z w : ℂ} (hz : z ∈ Z) (hw : w ∈ W) : z / w ∈ div p Z W := by
  rw [div_eq_mul_inv]; exact mem_mul hz (mem_inv hw)

theorem norm_le_absUB {Z : CBox} {z : ℂ} (hz : z ∈ Z) : ‖z‖ ≤ᵤ Z.absUB := by
  have ha := Ball.abs_le_absUB hz.1
  have hb := Ball.abs_le_absUB hz.2
  have h := UB.bounds_add (UB.bounds_mul (abs_nonneg _) (abs_nonneg _) ha ha)
    (UB.bounds_mul (abs_nonneg _) (abs_nonneg _) hb hb)
  have h2 := UB.bounds_sqrtUp (by positivity) h
  rw [norm_def, normSq_apply]
  dsimp only [absUB]
  simpa only [abs_mul_abs_self] using h2

theorem absLow_le_norm {Z : CBox} {z : ℂ} (hz : z ∈ Z) : Z.absLow.toReal ≤ ‖z‖ := by
  simp only [absLow, Dy.toReal_max]
  exact max_le ((Ball.absLow_le hz.1).trans (abs_re_le_norm z))
    ((Ball.absLow_le hz.2).trans (abs_im_le_norm z))

theorem mem_diskBox {r : UB} {w : ℂ} (h : ‖w‖ ≤ᵤ r) : w ∈ diskBox r :=
  mem_def.2 ⟨show |w.re - Dy.zero.toReal| ≤ᵤ r by simpa using h.mono (abs_re_le_norm w),
    show |w.im - Dy.zero.toReal| ≤ᵤ r by simpa using h.mono (abs_im_le_norm w)⟩

theorem mem_addDisk {Z : CBox} {r : UB} {z w : ℂ} (hz : z ∈ Z) (h : ‖w - z‖ ≤ᵤ r) :
    w ∈ Z.addDisk r :=
  ⟨Ball.mem_addErr hz.1 (h.mono (by simpa using abs_re_le_norm (w - z))),
   Ball.mem_addErr hz.2 (h.mono (by simpa using abs_im_le_norm (w - z)))⟩

theorem mem_union_left {p : ℕ} {Z W : CBox} {z : ℂ} (hz : z ∈ Z) : z ∈ union p Z W :=
  ⟨Ball.mem_union_left hz.1, Ball.mem_union_left hz.2⟩

theorem mem_union_right {p : ℕ} {Z W : CBox} {w : ℂ} (hw : w ∈ W) : w ∈ union p Z W :=
  ⟨Ball.mem_union_right hw.1, Ball.mem_union_right hw.2⟩

end CBox

/-! ## Series helpers -/

namespace Ball

theorem mem_foldSum {p : ℕ} {f : ℕ → Ball} {y : ℕ → ℝ} {acc : Ball} {a : ℝ} {j n : ℕ}
    (hacc : a ∈ acc) (hf : ∀ i < n, y (j + i) ∈ f (j + i)) :
    a + ∑ i ∈ range n, y (j + i) ∈ foldSum p f acc j n := by
  induction n generalizing acc a j with
  | zero => simp only [foldSum, range_zero, sum_empty, add_zero]; exact hacc
  | succ n ih =>
    have h := ih (acc := add p acc (f j)) (a := a + y j) (j := j + 1)
      (mem_add hacc (by simpa using hf 0 (by omega)))
      (fun i hi => by rw [show j + 1 + i = j + (i + 1) by omega]; exact hf (i + 1) (by omega))
    simp only [foldSum]
    rw [sum_range_succ']
    convert h using 1
    simp only [add_zero, show ∀ i, j + 1 + i = j + (i + 1) from fun i => by omega]
    ring

theorem mem_cauchy {p : ℕ} {a b : ℕ → Ball} {x y : ℕ → ℝ} {k : ℕ}
    (ha : ∀ i ≤ k, x i ∈ a i) (hb : ∀ i ≤ k, y i ∈ b i) :
    ∑ i ∈ range (k + 1), x i * y (k - i) ∈ cauchy p a b k := by
  have h := mem_foldSum (p := p) (f := fun j => mul p (a j) (b (k - j)))
    (y := fun i => x i * y (k - i)) (acc := mul p (a 0) (b k)) (j := 1) (n := k)
    (mem_mul (ha 0 (by omega)) (hb k le_rfl))
    (fun i hi => mem_mul (ha _ (by omega)) (hb _ (by omega)))
  rw [sum_range_succ', add_comm]
  convert h using 2
  all_goals first
    | rfl
    | exact sum_congr rfl fun i _ => by rw [Nat.add_comm i 1]

end Ball

namespace CBox

theorem mem_foldSum {p : ℕ} {f : ℕ → CBox} {y : ℕ → ℂ} {acc : CBox} {a : ℂ} {j n : ℕ}
    (hacc : a ∈ acc) (hf : ∀ i < n, y (j + i) ∈ f (j + i)) :
    a + ∑ i ∈ range n, y (j + i) ∈ foldSum p f acc j n := by
  induction n generalizing acc a j with
  | zero => simp only [foldSum, range_zero, sum_empty, add_zero]; exact hacc
  | succ n ih =>
    have h := ih (acc := add p acc (f j)) (a := a + y j) (j := j + 1)
      (mem_add hacc (by simpa using hf 0 (by omega)))
      (fun i hi => by rw [show j + 1 + i = j + (i + 1) by omega]; exact hf (i + 1) (by omega))
    simp only [foldSum]
    rw [sum_range_succ']
    convert h using 1
    simp only [add_zero, show ∀ i, j + 1 + i = j + (i + 1) from fun i => by omega]
    ring

theorem mem_cauchy {p : ℕ} {a b : ℕ → CBox} {x y : ℕ → ℂ} {k : ℕ}
    (ha : ∀ i ≤ k, x i ∈ a i) (hb : ∀ i ≤ k, y i ∈ b i) :
    ∑ i ∈ range (k + 1), x i * y (k - i) ∈ cauchy p a b k := by
  have h := mem_foldSum (p := p) (f := fun j => mul p (a j) (b (k - j)))
    (y := fun i => x i * y (k - i)) (acc := mul p (a 0) (b k)) (j := 1) (n := k)
    (mem_mul (ha 0 (by omega)) (hb k le_rfl))
    (fun i hi => mem_mul (ha _ (by omega)) (hb _ (by omega)))
  rw [sum_range_succ', add_comm]
  convert h using 2
  all_goals first
    | rfl
    | exact sum_congr rfl fun i _ => by rw [Nat.add_comm i 1]

/-- Mixed Cauchy sum, real `a`: `Σ_{i ≤ k} x_i · w_{k-i}` with `x_i ∈ a i`, `w_j ∈ b j`. -/
theorem mem_cauchyBC {p : ℕ} {a : ℕ → Ball} {b : ℕ → CBox} {x : ℕ → ℝ} {w : ℕ → ℂ} {k : ℕ}
    (ha : ∀ i ≤ k, x i ∈ a i) (hb : ∀ i ≤ k, w i ∈ b i) :
    ∑ i ∈ range (k + 1), (x i : ℂ) * w (k - i) ∈ cauchyBC p a b k := by
  have h := mem_foldSum (p := p) (f := fun j => mulBall p (b (k - j)) (a j))
    (y := fun i => w (k - i) * x i) (acc := mulBall p (b k) (a 0)) (j := 1) (n := k)
    (mem_mulBall (hb k le_rfl) (ha 0 (by omega)))
    (fun i hi => mem_mulBall (hb _ (by omega)) (ha _ (by omega)))
  rw [sum_range_succ', add_comm]
  convert h using 2
  all_goals first
    | rfl
    | rw [Nat.sub_zero, mul_comm]
    | exact sum_congr rfl fun i _ => by rw [Nat.add_comm i 1, mul_comm]

/-- Mixed Cauchy sum, real `b`: `Σ_{i ≤ k} z_i · y_{k-i}` with `z_i ∈ a i`, `y_j ∈ b j`. -/
theorem mem_cauchyCB {p : ℕ} {a : ℕ → CBox} {b : ℕ → Ball} {z : ℕ → ℂ} {y : ℕ → ℝ} {k : ℕ}
    (ha : ∀ i ≤ k, z i ∈ a i) (hb : ∀ i ≤ k, y i ∈ b i) :
    ∑ i ∈ range (k + 1), z i * y (k - i) ∈ cauchyCB p a b k := by
  have h := mem_foldSum (p := p) (f := fun j => mulBall p (a j) (b (k - j)))
    (y := fun i => z i * y (k - i)) (acc := mulBall p (a 0) (b k)) (j := 1) (n := k)
    (mem_mulBall (ha 0 (by omega)) (hb k le_rfl))
    (fun i hi => mem_mulBall (ha _ (by omega)) (hb _ (by omega)))
  rw [sum_range_succ', add_comm]
  convert h using 2
  all_goals first
    | rfl
    | exact sum_congr rfl fun i _ => by rw [Nat.add_comm i 1]

end CBox

/-! ## `buildArray` -/

theorem size_buildArray {α : Type} (step : Array α → α) (arr : Array α) (n : ℕ) :
    (buildArray step arr n).size = arr.size + n := by
  induction n generalizing arr with
  | zero => rfl
  | succ n ih => simp only [buildArray, ih, Array.size_push]; omega

/-- The prefix is kept. -/
theorem buildArray_getElem_of_lt {α : Type} (step : Array α → α) (arr : Array α) (n : ℕ)
    {i : ℕ} (hi : i < arr.size) :
    (buildArray step arr n)[i]'(by rw [size_buildArray]; omega) = arr[i] := by
  induction n generalizing arr with
  | zero => rfl
  | succ n ih =>
    simp only [buildArray]
    rw [ih (arr.push (step arr)) (by simp; omega)]
    exact Array.getElem_push_lt hi

/-- Entry `arr.size + i` is `step` applied to the array built after `i` pushes. -/
theorem buildArray_getElem {α : Type} (step : Array α → α) (arr : Array α) (n : ℕ)
    {i : ℕ} (hi : i < n) :
    (buildArray step arr n)[arr.size + i]'(by rw [size_buildArray]; omega) =
      step (buildArray step arr i) := by
  induction n generalizing arr i with
  | zero => omega
  | succ n ih =>
    simp only [buildArray]
    rcases i with _ | i
    · rw [buildArray_getElem_of_lt step (arr.push (step arr)) n (by simp)]
      simp [buildArray]
    · have h := ih (arr.push (step arr)) (i := i) (by omega)
      simp only [Array.size_push] at h
      simp only [buildArray]
      rw [← h]
      congr 1
      omega

/-! ## Operator notation (`Verify/Comp/Notation.lean`) -/

theorem Ball.neg_def (x : Ball) : -x = Ball.neg x := rfl
theorem CBox.neg_def (x : CBox) : -x = CBox.neg x := rfl

section Notation
variable [Prec]
theorem Ball.add_def (x y : Ball) : x + y = Ball.add Prec.prec x y := rfl
theorem Ball.sub_def (x y : Ball) : x - y = Ball.sub Prec.prec x y := rfl
theorem Ball.mul_def (x y : Ball) : x * y = Ball.mul Prec.prec x y := rfl
theorem Ball.inv_def (x : Ball) : x⁻¹ = Ball.inv Prec.prec x := rfl
theorem Ball.div_def (x y : Ball) : x / y = Ball.div Prec.prec x y := rfl
theorem CBox.add_def (x y : CBox) : x + y = CBox.add Prec.prec x y := rfl
theorem CBox.sub_def (x y : CBox) : x - y = CBox.sub Prec.prec x y := rfl
theorem CBox.mul_def (x y : CBox) : x * y = CBox.mul Prec.prec x y := rfl
theorem CBox.inv_def (x : CBox) : x⁻¹ = CBox.inv Prec.prec x := rfl
theorem CBox.div_def (x y : CBox) : x / y = CBox.div Prec.prec x y := rfl
end Notation

end NonUniqueEuler.Verify
