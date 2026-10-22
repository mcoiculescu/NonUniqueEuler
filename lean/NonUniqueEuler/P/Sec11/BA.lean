import NonUniqueEuler.Defs.Sec11.All
import NonUniqueEuler.I.Sec4.Annuli
import NonUniqueEuler.I.Sec10.ConstantsPos

/-!
# Proof: the remarks after `def:BA` ((BA*) implies (BA), with room to spare)

Proof of `I/Sec11/BA.lean` (`11_bootstrap.tex:87-92`): same declarations, same statements.

* `pertDefined_of_BA1`: `S_j(t') ⊂ N♭_j = r_j N♭ ⊂ r_j N = N_j` (`lem:annuli`, `annuli_chain`).
* `BA_of_BAstar`: `BA1At.mono` with `𝒩_j ⊂ int N♭_j ⊂ N♭_j`, `BA2At.mono` with `Ā ≤ 2Ā`
  (`Ā > 0`, `constants_pos`) and `ε_j > 0` (`Valid.eps_pos`), `BA3At.mono` with `C₂ ≤ 2C₂`
  (`C₂ ≥ 1`, `constants_pos`) and `1 + ρ̂_k ≥ 1` (`ρ̂_k ≥ 0` from its formula, `C₀ ≥ 1`).
* `BAstar_room`: `𝒩_j ⊂ int N♭_j` (the dilation `x ↦ r_j⁻¹x` is continuous, so the preimage of
  an interior lies in the interior of the preimage); `x < 2x` for `x = Āε_j > 0` and for
  `x = C₂â_k(u)(1 + ρ̂_k(u)) > 0` (`â_k(u) = κ♯_k e^{σ_k u}`, `κ♯_k > 0` by `ClockUpTo.ksh_mem`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- The dilation `scaleSet r` is monotone. -/
private theorem scaleSet_mono_BA {r : ℝ} {U V : Set ℂ} (h : U ⊆ V) :
    scaleSet r U ⊆ scaleSet r V :=
  fun _ hx => h hx

/-- `r · int U ⊆ int (r · U)` (the map `x ↦ r⁻¹ x` is continuous). -/
private theorem scaleSet_interior_subset_BA (r : ℝ) (U : Set ℂ) :
    scaleSet r (interior U) ⊆ interior (scaleSet r U) :=
  preimage_interior_subset_interior_preimage (f := fun x : ℂ => (r : ℂ)⁻¹ * x)
    (continuous_const.mul continuous_id)

/-- `𝒩_j ⊂ int N♭_j` (`lem:annuli`, scaled by `r_j`). -/
private theorem Nnk_subset_interior_Nflatk_BA (P : Approx) (j : ℕ) :
    P.Nnk j ⊆ interior (P.Nflatk j) :=
  (scaleSet_mono_BA annuli_chain.2.2.1).trans (scaleSet_interior_subset_BA _ _)

/-- `ρ̂ ≥ 0` for `C₀ ≥ 0` (from the formula, `thm:active`, `05_single_ring.tex:876-880`). -/
private theorem rhoHatOf_nonneg_BA {σ σ' C₀ : ℝ} (hC : 0 ≤ C₀) (u : ℝ) :
    0 ≤ OneRing.rhoHatOf σ σ' C₀ u := by
  unfold OneRing.rhoHatOf
  split_ifs
  · exact mul_nonneg (mul_nonneg hC (pow_nonneg (Prelim.jap_nonneg _) _)) (Real.exp_pos _).le
  · exact mul_nonneg (pow_nonneg (Prelim.jap_nonneg _) _) (Real.exp_pos _).le

/-- `1 + ρ̂_k(u) > 0` (with `C₀ = S.C0 ≥ 1`). -/
private theorem one_add_rhoHatK_pos_BA (S : Standing) (k : ℕ) (u : ℝ) :
    0 < 1 + S.rhoHatK S.C0 k u := by
  have h : 0 ≤ S.rhoHatK S.C0 k u :=
    rhoHatOf_nonneg_BA (le_trans zero_le_one S.one_le_C0) u
  linarith

/-- **`w_k(t')` is defined under (BA1)** (`11_bootstrap.tex:87-88`): if (BA1) holds at `t'` (with
`N♭_j`), then `S_j(t') ⊂ N_j` for every ring `j ∈ [1, n]` that is not debris at `t'`. -/
theorem pertDefined_of_BA1 (S : Standing) {t' : ℝ} (h : S.BA1At S.P.Nflatk t') :
    ∀ j ∈ Finset.Icc 1 S.P.n, ¬ S.P.DebrisAt j t' → S.P.PertDefined j t' := by
  intro j hj hd
  exact (h j hj hd).trans (scaleSet_mono_BA annuli_chain.2.2.2.1)

/-- **(BA*)(t) implies (BA)(t)** (`11_bootstrap.tex:88-90`). -/
theorem BA_of_BAstar (S : Standing) (hS : S.Holds) (hL : S.ParamLists) {t : ℝ}
    (h : S.BAstar t) : S.BA t := by
  have hpos := constants_pos S hS.admissible hS.hN hS.σ'_gt hS.σ'_lt_sigma hS.δ₀_pos
    hS.one_lt_μ hS.Tpin_pos
  have hA : S.Abar ≤ 2 * S.Abar := by linarith [hpos.Abar_pos]
  have hC : S.C2 ≤ 2 * S.C2 := by linarith [hpos.one_le_C2]
  refine ⟨fun t' ht' => (h.ba1 t' ht').mono ?_, fun t' ht' => (h.ba2 t' ht').mono hA ?_,
    fun t' ht' k hk => (h.ba3 t' ht' k hk).mono hC (one_add_rhoHatK_pos_BA S k _).le⟩
  · exact fun j _ => (Nnk_subset_interior_Nflatk_BA S.P j).trans interior_subset
  · exact fun j _ => (hS.valid.eps_pos j).le

/-- **The room to spare between (BA*) and (BA)** (`11_bootstrap.tex:88-90`; used in Step 7,
`:582-591`): `𝒩_j ⊂ int N♭_j` for every ring `j`; `Āε_j < 2Āε_j` for every ring `j < n`; and, for
every ring `k` with `κ♯_k` defined (clock defined up to level `k`) and every `u ≥ 0`,
`C₂â_k(u)(1 + ρ̂_k(u)) < 2C₂â_k(u)(1 + ρ̂_k(u))` (`ρ̂_k` with `C₀ = S.C0`). -/
theorem BAstar_room (S : Standing) (hS : S.Holds) (hL : S.ParamLists) :
    (∀ j ∈ Finset.Icc 1 S.P.n, S.P.Nnk j ⊆ interior (S.P.Nflatk j)) ∧
    (∀ j ∈ Finset.Ico 1 S.P.n, S.Abar * S.P.eps j < 2 * S.Abar * S.P.eps j) ∧
    ∀ k ∈ Finset.Icc 1 S.P.n, S.P.ClockUpTo k → ∀ u : ℝ, 0 ≤ u →
      S.C2 * S.ahatK k u * (1 + S.rhoHatK S.C0 k u) <
        2 * S.C2 * S.ahatK k u * (1 + S.rhoHatK S.C0 k u) := by
  have hpos := constants_pos S hS.admissible hS.hN hS.σ'_gt hS.σ'_lt_sigma hS.δ₀_pos
    hS.one_lt_μ hS.Tpin_pos
  refine ⟨fun j _ => Nnk_subset_interior_Nflatk_BA S.P j, ?_, ?_⟩
  · intro j _
    have hp : 0 < S.Abar * S.P.eps j := mul_pos hpos.Abar_pos (hS.valid.eps_pos j)
    have he : 2 * S.Abar * S.P.eps j = 2 * (S.Abar * S.P.eps j) := by ring
    rw [he]
    linarith
  · intro k hk hclock u _
    have hkn : k ≤ S.P.n := (Finset.mem_Icc.1 hk).2
    have hksh : 0 < S.P.ksh k := (hclock.ksh_mem le_rfl hkn).1
    have ha : 0 < S.ahatK k u := mul_pos hksh (Real.exp_pos _)
    have hC2 : 0 < S.C2 := lt_of_lt_of_le one_pos hpos.one_le_C2
    have hp : 0 < S.C2 * S.ahatK k u * (1 + S.rhoHatK S.C0 k u) :=
      mul_pos (mul_pos hC2 ha) (one_add_rhoHatK_pos_BA S k u)
    have he : 2 * S.C2 * S.ahatK k u * (1 + S.rhoHatK S.C0 k u) =
        2 * (S.C2 * S.ahatK k u * (1 + S.rhoHatK S.C0 k u)) := by ring
    rw [he]
    linarith

end Relay

end NonUniqueEuler
