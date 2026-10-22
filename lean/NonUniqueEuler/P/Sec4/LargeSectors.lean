import NonUniqueEuler.Defs.Sec4.Operators
import NonUniqueEuler.H.Sec4.LargeSectors.Bootstrap
import NonUniqueEuler.H.Sec4.LargeSectors.Norms

/-!
# Proof: `prop:large-sectors` and the uniform exponential bounds `ExpBounded`

Proof of `I/Sec4/LargeSectors.lean` (`04_ring.tex:1014-1040`).

Structure (deviation): the manuscript runs the
bootstrap `Y_T ≤ C_s c_s(γ) + Y_T/2` in the profile norm `‖·‖_{s,ℓ}`; here it is run in the
operator norm of `Y^s_ℓ` (a Banach algebra, so the Duhamel integral is estimated with
`‖∫‖ ≤ ∫‖·‖`), with the constants `C_s`, `C_K` of `lem:semigroup-construct`(1) and
`cor:K-bound` transported to the operator norm by the norm equivalence uniform in `ℓ`
(`H/Sec4/LargeSectors/Norms.lean`). The profile-norm statement `largeSectors` then follows from
the operator-norm one by the same norm equivalence (both constants are existential, D11). The
abstract bootstrap is `LargeSectorsH.norm_exp_add_le` (`H/Sec4/LargeSectors/Bootstrap.lean`).

`ExpBounded`: for `|ℓ| ≥ M_1` the bound of `prop:large-sectors` with `γ = 1`; for each of the
finitely many `|ℓ| < M_1` the same bootstrap with `κ = ‖k_ℓ𝒢_ℓ‖` and a `γ_ℓ` with
`C_s κ I_s(γ_ℓ) ≤ 1/2` (instead of the manuscript's sketch `‖exp(tL_ℓ)‖ ≤ e^{t‖L_ℓ‖}`, which would
need a bound of `‖-iℓΩ(·;G)‖` uniform in `|G| ≤ G₊`; the bootstrap only uses the transport bound,
which is already uniform in `G`, and `k_ℓ𝒢_ℓ`, which does not depend on `G`).
-/

noncomputable section

open MeasureTheory Set
open scoped Nat

namespace NonUniqueEuler

namespace LargeSectorsH

open SectorSetting Sect

/-- `prop:large-sectors` in the operator norm of `Y^s_ℓ` (the core of the proof). -/
theorem largeSectors_opNorm_aux (S : SectorSetting) (hS : S.Valid) (s : ℕ) {γ Gp : ℝ}
    (hγ : 0 < γ) (hGp : 0 ≤ Gp) :
    ∃ M C : ℝ, 1 ≤ M ∧ 0 < C ∧ ∀ ℓ : ℤ, M ≤ |(ℓ : ℝ)| → ∀ G : ℝ, |G| ≤ Gp →
      ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G)‖ ≤ C * Real.exp (γ * t) := by
  obtain ⟨Ct, hCt, hT⟩ := exists_norm_exp_transSec_le S hS s hGp
  obtain ⟨K, hK, hKb⟩ := exists_norm_Ksec_le S hS s
  have hIp : 0 < Ip s γ := Ip_pos s hγ
  refine ⟨max 1 (2 * Ct * K * Ip s γ), 2 * Ct * (s ! * Real.exp γ / γ ^ s), le_max_left _ _,
    by positivity, fun ℓ hℓ G hG t ht => ?_⟩
  have hM1 : (1 : ℝ) ≤ |(ℓ : ℝ)| := (le_max_left _ _).trans hℓ
  have hM2 : 2 * Ct * K * Ip s γ ≤ |(ℓ : ℝ)| := (le_max_right _ _).trans hℓ
  have habs : 0 < |(ℓ : ℝ)| := lt_of_lt_of_le one_pos hM1
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    simp at habs
  rw [Lsec_def]
  refine norm_exp_add_le (S.transSec s ℓ G) (S.Ksec s ℓ) s (κ := K / |(ℓ : ℝ)|) hCt.le
    (by positivity) hγ (fun u hu => ?_) (hKb ℓ hℓ0)
    (fun u hu => one_add_pow_mul_exp_neg_le s hγ hu) ?_ ht
  · have h := hT ℓ G hG u
    rwa [abs_of_nonneg hu] at h
  · have : Ct * (K / |(ℓ : ℝ)|) * Ip s γ = (Ct * K * Ip s γ) / |(ℓ : ℝ)| := by ring
    rw [this, div_le_iff₀ habs]
    linarith

end LargeSectorsH

namespace SectorSetting

open Sect

/-- **`prop:large-sectors`** (`04_ring.tex:1014-1022`): for `γ > 0` and `G₊ ≥ 0` there are
`M_γ ≥ 1` and `C` (the manuscript's `2C_s c_s(γ)`) such that
`‖e^{tL_ℓ(G)}‖_{s,ℓ → s,ℓ} ≤ C e^{γt}` for every `ℓ ∈ ℤ` with `|ℓ| ≥ M_γ`, every `|G| ≤ G₊` and
every `t ≥ 0`. -/
theorem largeSectors (S : SectorSetting) (hS : S.Valid) (s : ℕ) {γ Gp : ℝ} (hγ : 0 < γ)
    (hGp : 0 ≤ Gp) :
    ∃ M C : ℝ, 1 ≤ M ∧ 0 < C ∧ ∀ ℓ : ℤ, M ≤ |(ℓ : ℝ)| → ∀ G : ℝ, |G| ≤ Gp →
      ∀ t : ℝ, 0 ≤ t → ∀ g : Ysec s S.Nstar ℓ,
        S.secNormY s (NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G) g) ≤
          C * Real.exp (γ * t) * S.secNormY s g := by
  obtain ⟨M, C, hM, hC, h⟩ := LargeSectorsH.largeSectors_opNorm_aux S hS s hγ hGp
  obtain ⟨a, b, ha, hb, hab⟩ := LargeSectorsH.exists_secNormY_equiv S hS s
  refine ⟨M, a * C * b, hM, by positivity, fun ℓ hℓ G hG t ht g => ?_⟩
  have hE := h ℓ hℓ G hG t ht
  have hexp := Real.exp_pos (γ * t)
  calc S.secNormY s (NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G) g)
      ≤ a * ‖NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G) g‖ := (hab ℓ _).1
    _ ≤ a * (‖NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G)‖ * ‖g‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) ha.le
    _ ≤ a * ((C * Real.exp (γ * t)) * (b * S.secNormY s g)) := by
        gcongr
        exact (hab ℓ g).2
    _ = a * C * b * Real.exp (γ * t) * S.secNormY s g := by ring

/-- `prop:large-sectors` in the operator norm of `Y^s_ℓ` (equivalent up to constants, uniformly
in `ℓ`). -/
theorem largeSectors_opNorm (S : SectorSetting) (hS : S.Valid) (s : ℕ) {γ Gp : ℝ} (hγ : 0 < γ)
    (hGp : 0 ≤ Gp) :
    ∃ M C : ℝ, 1 ≤ M ∧ 0 < C ∧ ∀ ℓ : ℤ, M ≤ |(ℓ : ℝ)| → ∀ G : ℝ, |G| ≤ Gp →
      ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G)‖ ≤ C * Real.exp (γ * t) :=
  LargeSectorsH.largeSectors_opNorm_aux S hS s hγ hGp

/-- The sector exponentials `exp(tL_ℓ(G))` are bounded uniformly in `ℓ ∈ ℤ`, `|G| ≤ G₊` and
`t ∈ [0, T]` (from `prop:large-sectors` and the finitely many small sectors). -/
theorem largeSectors_expBounded_uniform (S : SectorSetting) (hS : S.Valid) (s : ℕ) {Gp : ℝ}
    (hGp : 0 ≤ Gp) (T : ℝ) :
    ∃ B : ℝ, ∀ G : ℝ, |G| ≤ Gp → ∀ t ∈ Icc (0 : ℝ) T, ∀ ℓ : ℤ,
      ‖NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G)‖ ≤ B := by
  obtain ⟨M, C, hM, hC, hlarge⟩ :=
    LargeSectorsH.largeSectors_opNorm_aux S hS s (γ := 1) one_pos hGp
  obtain ⟨Ct, hCt, hT⟩ := LargeSectorsH.exists_norm_exp_transSec_le S hS s hGp
  have hsmall : ∀ ℓ : ℤ, ∃ γ : ℝ, 1 ≤ γ ∧ Ct * ‖S.Ksec s ℓ‖ * Ip s γ ≤ 1 / 2 := fun ℓ =>
    LargeSectorsH.exists_Ip_small s (K := Ct * ‖S.Ksec s ℓ‖) (by positivity)
  choose γf hγf1 hγf using hsmall
  set T' : ℝ := max T 0 with hT'
  set bnd : ℤ → ℝ := fun ℓ =>
    2 * Ct * (s ! * Real.exp (γf ℓ) / γf ℓ ^ s) * Real.exp (γf ℓ * T') with hbnd
  have hγf0 : ∀ ℓ, 0 < γf ℓ := fun ℓ => lt_of_lt_of_le one_pos (hγf1 ℓ)
  have hbnd_nonneg : ∀ ℓ, 0 ≤ bnd ℓ := fun ℓ => by
    have := hγf0 ℓ
    simp only [hbnd]
    positivity
  set N : ℕ := ⌈M⌉₊ with hN
  refine ⟨C * Real.exp (1 * T') + ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) N, bnd ℓ, ?_⟩
  intro G hG t ht ℓ
  have ht0 : 0 ≤ t := ht.1
  have htT : t ≤ T' := ht.2.trans (le_max_left _ _)
  have hsum_nonneg : 0 ≤ ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) N, bnd ℓ :=
    Finset.sum_nonneg fun ℓ _ => hbnd_nonneg ℓ
  by_cases hℓ : M ≤ |(ℓ : ℝ)|
  · calc ‖NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G)‖ ≤ C * Real.exp (1 * t) :=
          hlarge ℓ hℓ G hG t ht0
      _ ≤ C * Real.exp (1 * T') := by gcongr
      _ ≤ C * Real.exp (1 * T') + ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) N, bnd ℓ :=
          le_add_of_nonneg_right hsum_nonneg
  · replace hℓ : |(ℓ : ℝ)| < M := not_le.1 hℓ
    have hmem : ℓ ∈ Finset.Icc (-(N : ℤ)) N := by
      rw [Finset.mem_Icc]
      have h1 : |(ℓ : ℝ)| ≤ (N : ℝ) := hℓ.le.trans (Nat.le_ceil M)
      have h2 : ((|ℓ| : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) := by
        rw [Int.cast_abs]
        exact_mod_cast h1
      exact abs_le.1 (by exact_mod_cast h2)
    have hb : ‖NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G)‖ ≤ bnd ℓ := by
      rw [Lsec_def]
      have hA : ∀ u : ℝ, 0 ≤ u →
          ‖NormedSpace.exp ((u : ℂ) • S.transSec s ℓ G)‖ ≤ Ct * (1 + u) ^ s := fun u hu => by
        have h := hT ℓ G hG u
        rwa [abs_of_nonneg hu] at h
      have h := LargeSectorsH.norm_exp_add_le (S.transSec s ℓ G) (S.Ksec s ℓ) s
        (κ := ‖S.Ksec s ℓ‖) hCt.le (by positivity) (hγf0 ℓ) hA le_rfl
        (fun u hu => LargeSectorsH.one_add_pow_mul_exp_neg_le s (hγf0 ℓ) hu) (hγf ℓ) ht0
      have := hγf0 ℓ
      calc _ ≤ 2 * Ct * (s ! * Real.exp (γf ℓ) / γf ℓ ^ s) * Real.exp (γf ℓ * t) := h
        _ ≤ bnd ℓ := by
            simp only [hbnd]
            gcongr
    calc ‖NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G)‖ ≤ bnd ℓ := hb
      _ ≤ ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) N, bnd ℓ :=
          Finset.single_le_sum (fun ℓ' _ => hbnd_nonneg ℓ') hmem
      _ ≤ C * Real.exp (1 * T') + ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) N, bnd ℓ :=
          le_add_of_nonneg_left (by positivity)

/-- `Sect.ExpBounded` for the sector operators of a setting: the hypothesis under which
`S.semigroup s G = ⊕_ℓ exp(tL_ℓ(G))` is a strongly continuous semigroup
(`I/Infra/SectorSpace/Semigroup.lean`). -/
theorem largeSectors_expBounded (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ) :
    ExpBounded s S.Nstar (fun ℓ => S.Lsec s ℓ G) := by
  intro T
  obtain ⟨B, hB⟩ := largeSectors_expBounded_uniform S hS s (abs_nonneg G) T
  exact ⟨B, fun t ht ℓ => hB G le_rfl t ht ℓ⟩

end SectorSetting

end NonUniqueEuler
