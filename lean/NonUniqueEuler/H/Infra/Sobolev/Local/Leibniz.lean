import NonUniqueEuler.H.Infra.Sobolev.Local.Basic

/-!
# Helper for `P/Infra/Sobolev/Local`: the Leibniz rule on an open set

For `V ⊆ ℂ` open, a smooth compactly supported multiplier `χ` maps `H^k(V)` boundedly into
`H^k(V)` (`LocalAux.memHOn_mul_testFn`). This is the local Leibniz rule used in the extension
lemma (`02_prelim.tex:687-692`). Instead of the explicit Leibniz formula we induct on `k`:

* first order (`hasWeakDerivOn_mul_single`): `∂_v(χF) = (∂_vχ) F + χ ∂_vF` weakly on `V`
  (test with `χφ`, which is a test function supported in `V`);
* `U ∈ H^{k+1}(V)` gives `∂_i U ∈ H^k(V)` (`memHOn_weakPartialOn`);
* conversely `U ∈ L²(V)` with `∂_1U, ∂_2U ∈ H^k(V)` gives `U ∈ H^{k+1}(V)`
  (`memHOn_succ_of_grad`), with `∂^γ U = ∂^β ∂_i U` for `γ = β + e_i`;
* sums (`memHOn_add`).
The constants are crude (`#multiIdx k ≤ (k+1)²` on each sum); they are existential.

Uses `weakDerivOn_ae_eq`, `HasWeakDerivOn.add`, `HasWeakDerivOn.perm`, `HasWeakDerivOn.trans`
(`I/Infra/Sobolev/WeakDeriv.lean`) as black boxes.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob.LocalAux

/-! ### Calculus -/

theorem contDiff_dirDeriv {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (v : ℂ) :
    ContDiff ℝ ∞ (dirDeriv v φ) :=
  (ContDiff.fderiv_right (m := ∞) h (by simp)).clm_apply contDiff_const

theorem dirDeriv_mul {χ φ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hφ : ContDiff ℝ ∞ φ) (v x : ℂ) :
    dirDeriv v (fun y => χ y * φ y) x = dirDeriv v χ x * φ x + χ x * dirDeriv v φ x := by
  unfold dirDeriv
  rw [fderiv_fun_mul ((hχ.differentiable (by simp)) x) ((hφ.differentiable (by simp)) x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- A locally integrable function on `V` times a test function supported in `V` is
integrable. -/
theorem integrable_mul_testFn {V : Set ℂ} {g φ : ℂ → ℂ} (hg : LocallyIntegrableOn g V)
    (hφ : IsTestFn V φ) : Integrable (fun x => g x * φ x) := by
  have hK : IsCompact (tsupport φ) := hφ.compact
  have h1 : IntegrableOn g (tsupport φ) := hg.integrableOn_compact_subset hφ.subset hK
  have h2 : IntegrableOn (fun x => g x * φ x) (tsupport φ) :=
    h1.mul_continuousOn hφ.continuous.continuousOn hK
  refine h2.integrable_of_forall_notMem_eq_zero (fun x hx => ?_)
  simp [image_eq_zero_of_notMem_tsupport hx]

/-! ### First-order product rule -/

/-- `∂_v(χF) = (∂_vχ) F + χ ∂_vF` weakly on `V`, for smooth `χ`. -/
theorem hasWeakDerivOn_mul_single {V : Set ℂ} {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ) {v : ℂ}
    {F G : ℂ → ℂ} (hF : LocallyIntegrableOn F V) (hG : LocallyIntegrableOn G V)
    (h : HasWeakDerivOn V [v] F G) :
    HasWeakDerivOn V [v] (fun x => χ x * F x) (fun x => dirDeriv v χ x * F x + χ x * G x) := by
  intro φ hφ
  have hχφ : IsTestFn V (fun x => χ x * φ x) := isTestFn_mul hχ hφ
  have hχ'φ : IsTestFn V (fun x => dirDeriv v χ x * φ x) :=
    isTestFn_mul (contDiff_dirDeriv hχ v) hφ
  have h1 : ∫ x, F x * dirDeriv v (fun y => χ y * φ y) x =
      (-1 : ℂ) ^ 1 * ∫ x, G x * (χ x * φ x) := h _ hχφ
  show ∫ x, χ x * F x * dirDeriv v φ x =
    (-1 : ℂ) ^ 1 * ∫ x, (dirDeriv v χ x * F x + χ x * G x) * φ x
  have hpt : ∀ x, χ x * F x * dirDeriv v φ x =
      F x * dirDeriv v (fun y => χ y * φ y) x - F x * (dirDeriv v χ x * φ x) := by
    intro x
    rw [dirDeriv_mul hχ hφ.smooth]
    ring
  have i1 := integrable_mul_testFn hF (hχφ.dirDeriv v)
  have i2 := integrable_mul_testFn hF hχ'φ
  have i3 := integrable_mul_testFn hG hχφ
  have e1 : ∫ x, χ x * F x * dirDeriv v φ x =
      (∫ x, F x * dirDeriv v (fun y => χ y * φ y) x) - ∫ x, F x * (dirDeriv v χ x * φ x) := by
    rw [← integral_sub i1 i2]
    exact integral_congr_ae (Eventually.of_forall hpt)
  have e2 : ∫ x, (dirDeriv v χ x * F x + χ x * G x) * φ x =
      (∫ x, F x * (dirDeriv v χ x * φ x)) + ∫ x, G x * (χ x * φ x) := by
    rw [← integral_add i2 i3]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [e1, e2, h1]
  ring

/-! ### Derivatives of `H^{k+1}(V)` functions -/

/-- The directions of `∂^{β+γ}` are a permutation of those of `∂^γ ∂^β`. -/
theorem pdList_add_perm (β γ : ℕ × ℕ) :
    (pdList (β + γ)).Perm (pdList γ ++ pdList β) := by
  simp only [pdList, Prod.fst_add, Prod.snd_add, List.replicate_add]
  set A := List.replicate β.1 (1 : ℂ)
  set B := List.replicate β.2 Complex.I
  set C := List.replicate γ.1 (1 : ℂ)
  set D := List.replicate γ.2 Complex.I
  have h1 : (C ++ (B ++ D)).Perm (B ++ (C ++ D)) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := C) (l₂ := B)).append_right D
  have h2 : (A ++ C ++ (B ++ D)).Perm (A ++ B ++ (C ++ D)) := by
    simpa only [List.append_assoc] using h1.append_left A
  exact h2.trans List.perm_append_comm

/-- `∂^β (∂^γ f) = ∂^{β+γ} f` weakly on `V`. -/
theorem hasWeakDerivOn_comp {V : Set ℂ} {β γ : ℕ × ℕ} {f g h : ℂ → ℂ}
    (hg : HasWeakDerivOn V (pdList γ) f g) (hh : HasWeakDerivOn V (pdList (β + γ)) f h) :
    HasWeakDerivOn V (pdList β) g h := by
  intro φ hφ
  have hh' := hh.perm (pdList_add_perm β γ) φ hφ
  have hg' := hg _ (hφ.iterDirDeriv (pdList β))
  rw [iterDirDeriv_append, hg'] at hh'
  simp only [List.length_append, pdList_length] at hh'
  simp only [pdList_length]
  have hs : ((-1 : ℂ) ^ (γ.1 + γ.2)) * (-1 : ℂ) ^ (γ.1 + γ.2) = 1 := by
    rw [← mul_pow]; simp
  calc ∫ x, g x * iterDirDeriv (pdList β) φ x
      = ((-1 : ℂ) ^ (γ.1 + γ.2)) * ((-1 : ℂ) ^ (γ.1 + γ.2) *
          ∫ x, g x * iterDirDeriv (pdList β) φ x) := by rw [← mul_assoc, hs, one_mul]
    _ = ((-1 : ℂ) ^ (γ.1 + γ.2)) * ((-1 : ℂ) ^ (γ.1 + γ.2 + (β.1 + β.2)) * ∫ x, h x * φ x) := by
        rw [hh']
    _ = (-1 : ℂ) ^ (β.1 + β.2) * ∫ x, h x * φ x := by
        rw [pow_add (-1 : ℂ) (γ.1 + γ.2) (β.1 + β.2), ← mul_assoc, ← mul_assoc, hs, one_mul]

/-- Derivatives of `H^{k+|γ|}(V)` functions lie in `H^k(V)`. -/
theorem memHOn_weakPartialOn {k : ℕ} {V : Set ℂ} (hV : IsOpen V) {γ : ℕ × ℕ} {f : ℂ → ℂ}
    (hf : MemHOn (k + (γ.1 + γ.2)) V f) :
    MemHOn k V (weakPartialOn V γ f) ∧
      normHOn k V (weakPartialOn V γ f) ≤ (k + 1) * normHOn (k + (γ.1 + γ.2)) V f := by
  have hγ : γ ∈ multiIdx (k + (γ.1 + γ.2)) := mem_multiIdx.2 (by omega)
  obtain ⟨hg2, hg⟩ := memHOn_spec hV hf hγ
  have hβγ : ∀ β ∈ multiIdx k, β + γ ∈ multiIdx (k + (γ.1 + γ.2)) := by
    intro β hβ
    rw [mem_multiIdx] at hβ ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hder : ∀ β ∈ multiIdx k, MemLp (weakPartialOn V (β + γ) f) 2 (volume.restrict V) ∧
      HasWeakDerivOn V (pdList β) (weakPartialOn V γ f) (weakPartialOn V (β + γ) f) := by
    intro β hβ
    obtain ⟨h1, h2⟩ := memHOn_spec hV hf (hβγ β hβ)
    exact ⟨h1, hasWeakDerivOn_comp hg h2⟩
  have hmem : MemHOn k V (weakPartialOn V γ f) := ⟨hg2, fun β hβ => ⟨_, hder β hβ⟩⟩
  refine ⟨hmem, normHOn_le_of_forall (normHOn_nonneg _ _ _) fun β hβ => ?_⟩
  have hae := weakDerivOn_ae_eq hV (locInt_of_memLp one_le_two (hder β hβ).1) (hder β hβ).2
  have e : l2On V (weakPartialOn V β (weakPartialOn V γ f)) =
      l2On V (weakPartialOn V (β + γ) f) := l2On_congr_ae hV.measurableSet hae
  rw [e]
  exact l2On_weakPartialOn_le_normHOn (hβγ β hβ)

/-! ### Sums -/

theorem memHOn_add {k : ℕ} {V : Set ℂ} (hV : IsOpen V) {F G : ℂ → ℂ} (hF : MemHOn k V F)
    (hG : MemHOn k V G) :
    MemHOn k V (fun x => F x + G x) ∧
      normHOn k V (fun x => F x + G x) ≤ (k + 1) * (normHOn k V F + normHOn k V G) := by
  have hd : ∀ γ ∈ multiIdx k,
      MemLp (fun x => weakPartialOn V γ F x + weakPartialOn V γ G x) 2 (volume.restrict V) ∧
      HasWeakDerivOn V (pdList γ) (fun x => F x + G x)
        (fun x => weakPartialOn V γ F x + weakPartialOn V γ G x) := by
    intro γ hγ
    obtain ⟨a2, ad⟩ := memHOn_spec hV hF hγ
    obtain ⟨b2, bd⟩ := memHOn_spec hV hG hγ
    exact ⟨a2.add b2, HasWeakDerivOn.add hV (locInt_of_memLp one_le_two hF.memLp)
      (locInt_of_memLp one_le_two hG.memLp) (locInt_of_memLp one_le_two a2)
      (locInt_of_memLp one_le_two b2) ad bd⟩
  refine ⟨⟨hF.memLp.add hG.memLp, fun γ hγ => ⟨_, hd γ hγ⟩⟩,
    normHOn_le_of_forall (add_nonneg (normHOn_nonneg _ _ _) (normHOn_nonneg _ _ _))
      fun γ hγ => ?_⟩
  have hae := weakDerivOn_ae_eq hV (locInt_of_memLp one_le_two (hd γ hγ).1) (hd γ hγ).2
  have e : l2On V (weakPartialOn V γ (fun x => F x + G x)) =
      l2On V (fun x => weakPartialOn V γ F x + weakPartialOn V γ G x) :=
    l2On_congr_ae hV.measurableSet hae
  obtain ⟨a2, -⟩ := memHOn_spec hV hF hγ
  obtain ⟨b2, -⟩ := memHOn_spec hV hG hγ
  rw [e]
  exact (l2On_add_le a2 b2).trans
    (add_le_add (l2On_weakPartialOn_le_normHOn hγ) (l2On_weakPartialOn_le_normHOn hγ))

/-! ### From first derivatives to `H^{k+1}(V)` -/

theorem hasWeakDerivOn_succ {V : Set ℂ} {e : ℕ × ℕ} {v : ℂ} (he : pdList e = [v])
    {β γ : ℕ × ℕ} (hγ : γ = β + e) {U G H : ℂ → ℂ} (h₁ : HasWeakDerivOn V [v] U G)
    (hβ : HasWeakDerivOn V (pdList β) G H) : HasWeakDerivOn V (pdList γ) U H := by
  subst hγ
  refine (h₁.trans hβ).perm ?_
  have p := pdList_add_perm β e
  rw [he] at p
  exact List.perm_append_comm.trans p.symm

/-- `U ∈ L²(V)` with weak derivatives `∂₁U = G₁`, `∂₂U = G₂` in `H^k(V)` lies in
`H^{k+1}(V)`. -/
theorem memHOn_succ_of_grad {k : ℕ} {V : Set ℂ} (hV : IsOpen V) {U G₁ G₂ : ℂ → ℂ}
    (hU : MemLp U 2 (volume.restrict V)) (h₁ : HasWeakDerivOn V [1] U G₁)
    (h₂ : HasWeakDerivOn V [Complex.I] U G₂) (hG₁ : MemHOn k V G₁) (hG₂ : MemHOn k V G₂) :
    MemHOn (k + 1) V U ∧
      normHOn (k + 1) V U ≤ (k + 2) * (l2On V U + normHOn k V G₁ + normHOn k V G₂) := by
  set S := l2On V U + normHOn k V G₁ + normHOn k V G₂ with hS
  have n0 := l2On_nonneg V U
  have n1 := normHOn_nonneg k V G₁
  have n2 := normHOn_nonneg k V G₂
  have hd : ∀ γ ∈ multiIdx (k + 1), ∃ g : ℂ → ℂ, MemLp g 2 (volume.restrict V) ∧
      HasWeakDerivOn V (pdList γ) U g ∧ l2On V g ≤ S := by
    intro γ hγ
    have hγ' := mem_multiIdx.1 hγ
    rcases Nat.eq_zero_or_pos γ.1 with h0 | h0
    · rcases Nat.eq_zero_or_pos γ.2 with h0' | h0'
      · have hγ0 : γ = (0, 0) := Prod.ext h0 h0'
        subst hγ0
        exact ⟨U, hU, hasWeakDerivOn_zero V U, by linarith⟩
      · set β : ℕ × ℕ := (0, γ.2 - 1) with hβdef
        have hβ : β ∈ multiIdx k := mem_multiIdx.2 (by simp only [hβdef]; omega)
        obtain ⟨b2, bd⟩ := memHOn_spec hV hG₂ hβ
        have hγβ : γ = β + (0, 1) := Prod.ext (by simp [hβdef, h0]) (by simp [hβdef]; omega)
        refine ⟨_, b2, hasWeakDerivOn_succ (e := (0, 1)) rfl hγβ h₂ bd, ?_⟩
        have := l2On_weakPartialOn_le_normHOn (f := G₂) (V := V) hβ
        linarith
    · set β : ℕ × ℕ := (γ.1 - 1, γ.2) with hβdef
      have hβ : β ∈ multiIdx k := mem_multiIdx.2 (by simp only [hβdef]; omega)
      obtain ⟨b1, bd⟩ := memHOn_spec hV hG₁ hβ
      have hγβ : γ = β + (1, 0) := Prod.ext (by simp [hβdef]; omega) (by simp [hβdef])
      refine ⟨_, b1, hasWeakDerivOn_succ (e := (1, 0)) rfl hγβ h₁ bd, ?_⟩
      have := l2On_weakPartialOn_le_normHOn (f := G₁) (V := V) hβ
      linarith
  have hmem : MemHOn (k + 1) V U := ⟨hU, fun γ hγ => by
    obtain ⟨g, a, b, -⟩ := hd γ hγ
    exact ⟨g, a, b⟩⟩
  refine ⟨hmem, ?_⟩
  have hb : normHOn (k + 1) V U ≤ ((k + 1 : ℕ) + 1) * S := by
    refine normHOn_le_of_forall (by positivity) fun γ hγ => ?_
    obtain ⟨g, a, b, c⟩ := hd γ hγ
    have hae := weakDerivOn_ae_eq hV (locInt_of_memLp one_le_two a) b
    have e : l2On V (weakPartialOn V γ U) = l2On V g := l2On_congr_ae hV.measurableSet hae
    rw [e]
    exact c
  calc normHOn (k + 1) V U ≤ ((k + 1 : ℕ) + 1) * S := hb
    _ = (k + 2) * S := by push_cast; ring

/-! ### The local Leibniz rule -/

/-- A smooth compactly supported multiplier maps `H^k(V)` boundedly into `H^k(V)`. -/
theorem memHOn_mul_testFn {V : Set ℂ} (hV : IsOpen V) (k : ℕ) :
    ∀ χ : ℂ → ℂ, IsTestFn univ χ → ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℂ → ℂ, MemHOn k V U →
      MemHOn k V (fun x => χ x * U x) ∧ normHOn k V (fun x => χ x * U x) ≤ C * normHOn k V U := by
  induction k with
  | zero =>
    intro χ hχ
    obtain ⟨B, hB⟩ := hχ.continuous.bounded_above_of_compact_support hχ.compact
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    refine ⟨B, hB0, fun U hU => ?_⟩
    have hm := memLp_mul_of_bound hχ.continuous hB hU.memLp
    have h00 : ∀ γ ∈ multiIdx 0, γ = (0, 0) := fun γ hγ => by
      have := mem_multiIdx.1 hγ
      exact Prod.ext (by omega) (by omega)
    have hmem : MemHOn 0 V (fun x => χ x * U x) := ⟨hm, fun γ hγ => by
      rw [h00 γ hγ]
      exact ⟨_, hm, hasWeakDerivOn_zero V _⟩⟩
    refine ⟨hmem, ?_⟩
    have hb : normHOn 0 V (fun x => χ x * U x) ≤ ((0 : ℕ) + 1) * (B * l2On V U) := by
      refine normHOn_le_of_forall (mul_nonneg hB0 (l2On_nonneg _ _)) fun γ hγ => ?_
      rw [h00 γ hγ]
      have hae := weakDerivOn_ae_eq hV (locInt_of_memLp one_le_two hm) (hasWeakDerivOn_zero V _)
      have e : l2On V (weakPartialOn V (0, 0) (fun x => χ x * U x)) =
          l2On V (fun x => χ x * U x) := l2On_congr_ae hV.measurableSet hae
      rw [e]
      exact l2On_mul_le hB hU.memLp
    calc normHOn 0 V (fun x => χ x * U x) ≤ ((0 : ℕ) + 1) * (B * l2On V U) := hb
      _ = B * l2On V U := by push_cast; ring
      _ ≤ B * normHOn 0 V U := mul_le_mul_of_nonneg_left (l2On_le_normHOn hV hU.memLp) hB0
  | succ k ih =>
    intro χ hχ
    obtain ⟨B, hB⟩ := hχ.continuous.bounded_above_of_compact_support hχ.compact
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    obtain ⟨C₀, hC₀, h₀⟩ := ih χ hχ
    obtain ⟨C₁, hC₁, h₁⟩ := ih (dirDeriv 1 χ) (hχ.dirDeriv 1)
    obtain ⟨C₂, hC₂, h₂⟩ := ih (dirDeriv Complex.I χ) (hχ.dirDeriv Complex.I)
    refine ⟨(k + 2) * (B + (k + 1) * (C₁ + C₀ * (k + 1)) + (k + 1) * (C₂ + C₀ * (k + 1))),
      by positivity, fun U hU => ?_⟩
    set N := normHOn (k + 1) V U with hN
    have hN0 : 0 ≤ N := normHOn_nonneg _ _ _
    have hUk : MemHOn k V U := hU.mono_order (Nat.le_succ k)
    have nUk : normHOn k V U ≤ N := normHOn_mono_order (Nat.le_succ k) V U
    obtain ⟨hD₁, nD₁⟩ := memHOn_weakPartialOn (k := k) (γ := (1, 0)) hV hU
    obtain ⟨hD₂, nD₂⟩ := memHOn_weakPartialOn (k := k) (γ := (0, 1)) hV hU
    have hw₁ : HasWeakDerivOn V [1] U (weakPartialOn V (1, 0) U) :=
      (memHOn_spec hV hU (γ := (1, 0)) (mem_multiIdx.2 (by norm_num))).2
    have hw₂ : HasWeakDerivOn V [Complex.I] U (weakPartialOn V (0, 1) U) :=
      (memHOn_spec hV hU (γ := (0, 1)) (mem_multiIdx.2 (by norm_num))).2
    have lU := locInt_of_memLp one_le_two hU.memLp
    have hL₁ := hasWeakDerivOn_mul_single hχ.smooth lU (locInt_of_memLp one_le_two hD₁.memLp) hw₁
    have hL₂ := hasWeakDerivOn_mul_single hχ.smooth lU (locInt_of_memLp one_le_two hD₂.memLp) hw₂
    obtain ⟨m11, n11⟩ := h₁ U hUk
    obtain ⟨m12, n12⟩ := h₀ _ hD₁
    obtain ⟨m21, n21⟩ := h₂ U hUk
    obtain ⟨m22, n22⟩ := h₀ _ hD₂
    obtain ⟨mG₁, nG₁⟩ := memHOn_add hV m11 m12
    obtain ⟨mG₂, nG₂⟩ := memHOn_add hV m21 m22
    have hχU := memLp_mul_of_bound hχ.continuous hB hU.memLp
    obtain ⟨hres, nres⟩ := memHOn_succ_of_grad hV hχU hL₁ hL₂ mG₁ mG₂
    refine ⟨hres, nres.trans ?_⟩
    have l0 : l2On V (fun x => χ x * U x) ≤ B * N :=
      (l2On_mul_le hB hU.memLp).trans
        (mul_le_mul_of_nonneg_left (l2On_le_normHOn hV hU.memLp) hB0)
    have nD₁' : normHOn k V (weakPartialOn V (1, 0) U) ≤ (k + 1) * N := nD₁
    have nD₂' : normHOn k V (weakPartialOn V (0, 1) U) ≤ (k + 1) * N := nD₂
    have g1 : normHOn k V (fun x => dirDeriv 1 χ x * U x + χ x * weakPartialOn V (1, 0) U x) ≤
        (k + 1) * (C₁ + C₀ * (k + 1)) * N := by
      calc _ ≤ (k + 1) * (normHOn k V (fun x => dirDeriv 1 χ x * U x) +
            normHOn k V (fun x => χ x * weakPartialOn V (1, 0) U x)) := nG₁
        _ ≤ (k + 1) * (C₁ * N + C₀ * ((k + 1) * N)) := by
          gcongr
          · exact n11.trans (mul_le_mul_of_nonneg_left nUk hC₁)
          · exact n12.trans (mul_le_mul_of_nonneg_left nD₁' hC₀)
        _ = (k + 1) * (C₁ + C₀ * (k + 1)) * N := by ring
    have g2 : normHOn k V (fun x => dirDeriv Complex.I χ x * U x +
          χ x * weakPartialOn V (0, 1) U x) ≤ (k + 1) * (C₂ + C₀ * (k + 1)) * N := by
      calc _ ≤ (k + 1) * (normHOn k V (fun x => dirDeriv Complex.I χ x * U x) +
            normHOn k V (fun x => χ x * weakPartialOn V (0, 1) U x)) := nG₂
        _ ≤ (k + 1) * (C₂ * N + C₀ * ((k + 1) * N)) := by
          gcongr
          · exact n21.trans (mul_le_mul_of_nonneg_left nUk hC₂)
          · exact n22.trans (mul_le_mul_of_nonneg_left nD₂' hC₀)
        _ = (k + 1) * (C₂ + C₀ * (k + 1)) * N := by ring
    calc (k + 2 : ℝ) * (l2On V (fun x => χ x * U x) + _ + _)
        ≤ (k + 2) * (B * N + (k + 1) * (C₁ + C₀ * (k + 1)) * N +
            (k + 1) * (C₂ + C₀ * (k + 1)) * N) := by gcongr
      _ = _ := by ring

end NonUniqueEuler.Sob.LocalAux
