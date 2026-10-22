import NonUniqueEuler.Defs.Sec4.Operators
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import NonUniqueEuler.H.Sec4.SemigroupLaw.Basic
import NonUniqueEuler.H.Sec4.SemigroupLaw.Conj
import NonUniqueEuler.H.Sec4.SemigroupLaw.Operators
import NonUniqueEuler.I.Sec4.LargeSectors
import NonUniqueEuler.I.Infra.SectorSpace.Semigroup
import NonUniqueEuler.I.Infra.SectorSpace.DirectSum
import NonUniqueEuler.I.Infra.SectorSpace.Lower
import NonUniqueEuler.I.Infra.SectorSpace.Projection
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition
import NonUniqueEuler.I.Infra.SectorSpace.BanachExp

/-!
# Proof: `lem:semigroup-construct` (2) and (3) in the form of restructuring R1

Proof of `I/Sec4/SemigroupLaw.lean` (same declarations, statements copied verbatim).
Manuscript: `04_ring.tex:924-1012` (`lem:semigroup-construct`), `:1042-1044` (`Y^s_𝒵`),
`05_single_ring.tex:45-47` (real functions).

The linear evolution is the sector-wise exponential `S.semigroup s G t = ⊕_ℓ exp(tL_ℓ(G))`
(D8, R1), so everything reduces to the I-SECT library with `hb := largeSectors_expBounded`:
* `e^{0L} = 1`, semigroup law, strong continuity, `P_ℓ e^{tL} = exp(tL_ℓ)P_ℓ`, `Y^s_𝒵`:
  `sectorExp_zero`, `sectorExp_add`, `continuousOn_sectorExp`, `secProj_sectorExp`,
  `sectorExp_mem_YZSub`; the restriction to a sector by comparing sector projections
  (`secProj_inclSec`, `hasSum_secProj`);
* bound on `[0, T]`: `exists_sectorSum_spec` with `largeSectors_expBounded_uniform`;
* Duhamel formulas: `BanachExp.exp_add_eq_duhamel(')` with `A = transSec`, `B = Ksec`;
* `lowerY`: `exp(tL_ℓ)` commutes with `lowerSec` (`SgLaw_exp_Lsec_lowerSec`), then
  `sectorSum_lowerY`;
* derivative: `P_ℓ L(G)w = L_ℓ(G)P_ℓ w` (`SgLaw_secProj_LinY`, from `lem:sector`(2)), so
  `L(G)w = ∑_ℓ L_ℓ P_ℓ w` and `hasDerivWithinAt_sectorExp` applies; `L(G)e^{tL}w = e^{tL}L(G)w`
  sector by sector (`L_ℓ` commutes with `exp(tL_ℓ)`, and the compatibility with `lowerY`);
* real functions: `P_{-ℓ}w = conj(P_ℓ w)` for real `w`, and
  `exp(tL_{-ℓ}) conj = conj exp(tL_ℓ)` (`SgLaw_exp_Lsec_conjSec`, from `LsecFn_neg_conj`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace SectorSetting

open Sect

/-! ### Two facts about `secProj` on a sector -/

private theorem secProj_inclSec_self (S : SectorSetting) {s : ℕ} {ℓ : ℤ}
    (g : Ysec s S.Nstar ℓ) : secProj s S.Nstar ℓ (inclSec s S.Nstar ℓ g) = g := by
  apply Subtype.ext
  rw [secProj_inclSec S.isRotInvariant_Nstar]
  simp

private theorem secProj_inclSec_ne (S : SectorSetting) {s : ℕ} {ℓ m : ℤ} (hm : m ≠ ℓ)
    (g : Ysec s S.Nstar ℓ) : secProj s S.Nstar m (inclSec s S.Nstar ℓ g) = 0 := by
  apply Subtype.ext
  rw [secProj_inclSec S.isRotInvariant_Nstar]
  simp [hm]

/-! ### The I-SECT facts on `S.Nstar` (stated syntactically on `S.Nstar` for rewriting) -/

private theorem Y_ext_Nstar (S : SectorSetting) (hS : S.Valid) {s : ℕ} {a b : Y s S.Nstar}
    (h : ∀ ℓ, secProj s S.Nstar ℓ a = secProj s S.Nstar ℓ b) : a = b :=
  SgLawH.Y_ext_of_secProj hS.ρm_pos hS.ρm_lt_ρp h

private theorem hasSum_secProj_Nstar (S : SectorSetting) (hS : S.Valid) {s : ℕ}
    (w : Y s S.Nstar) :
    HasSum (fun ℓ : ℤ => inclSec s S.Nstar ℓ (secProj s S.Nstar ℓ w)) w :=
  hasSum_secProj hS.ρm_pos hS.ρm_lt_ρp w

private theorem isReal_Nstar (S : SectorSetting) (hS : S.Valid) {s : ℕ} {u : Y s S.Nstar}
    (h : ∀ ℓ, secProj s S.Nstar (-ℓ) u =
      SgLawH.conjSec s S.Nstar ℓ (secProj s S.Nstar ℓ u)) : u.IsReal :=
  SgLawH.isReal_of_secProj_neg hS.ρm_pos hS.ρm_lt_ρp h

/-! ### The interface statements -/

/-- `e^{0·L(G)} = 1`. -/
theorem semigroup_zero (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ) :
    S.semigroup s G 0 = ContinuousLinearMap.id ℂ _ := by
  rw [semigroup_def]
  exact sectorExp_zero hS.ρm_pos hS.ρm_lt_ρp _

/-- **R1 form of `lem:semigroup-construct`(2): the semigroup law** for `t, t' ≥ 0`. -/
theorem semigroup_add (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ) {t t' : ℝ}
    (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    S.semigroup s G (t + t') = (S.semigroup s G t).comp (S.semigroup s G t') := by
  simp only [semigroup_def]
  exact sectorExp_add hS.ρm_pos hS.ρm_lt_ρp (largeSectors_expBounded S hS s G) ht ht'

/-- Local uniform bounds: `sup_{0 ≤ t ≤ T, |G| ≤ G₊} ‖e^{tL(G)}‖_{Y^s → Y^s} < ∞` (this replaces
the uniform boundedness principle in the proof of `lem:duhamel`, `05_single_ring.tex:60-62`). -/
theorem semigroup_bound (S : SectorSetting) (hS : S.Valid) (s : ℕ) {Gp : ℝ} (hGp : 0 ≤ Gp)
    (T : ℝ) :
    ∃ B : ℝ, ∀ G : ℝ, |G| ≤ Gp → ∀ t ∈ Icc (0 : ℝ) T, ‖S.semigroup s G t‖ ≤ B := by
  obtain ⟨B, hB⟩ := largeSectors_expBounded_uniform S hS s hGp T
  obtain ⟨C, -, hC⟩ := exists_sectorSum_spec s hS.ρm_pos hS.ρm_lt_ρp
  refine ⟨C * B, fun G hG t ht => ?_⟩
  exact (hC (fun ℓ => NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G)) B (hB G hG t ht)).2

/-- **R1 form of `lem:semigroup-construct`(2): strong continuity** on `[0, ∞)`. -/
theorem semigroup_continuousOn (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ)
    (w : Y s S.Nstar) :
    ContinuousOn (fun t => S.semigroup s G t w) (Ici 0) := by
  simp only [semigroup_def]
  exact continuousOn_sectorExp hS.ρm_pos hS.ρm_lt_ρp (largeSectors_expBounded S hS s G) w

/-- **`lem:semigroup-construct`(3)** (`04_ring.tex:940-941`): `P_ℓ e^{tL(G)} = exp(tL_ℓ(G)) P_ℓ`
and `e^{tL(G)}` restricted to the sector `ℓ` is `exp(tL_ℓ(G))`; in particular `e^{tL}` preserves
each sector (part (2)). -/
theorem semigroup_sector (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (ℓ : ℤ) :
    (∀ w : Y s S.Nstar, secProj s S.Nstar ℓ (S.semigroup s G t w) =
        NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G) (secProj s S.Nstar ℓ w)) ∧
      ∀ g : Ysec s S.Nstar ℓ, S.semigroup s G t (inclSec s S.Nstar ℓ g) =
        inclSec s S.Nstar ℓ (NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G) g) := by
  have hb := largeSectors_expBounded S hS s G
  have h1 : ∀ (m : ℤ) (w : Y s S.Nstar), secProj s S.Nstar m (S.semigroup s G t w) =
      NormedSpace.exp ((t : ℂ) • S.Lsec s m G) (secProj s S.Nstar m w) := fun m w => by
    rw [semigroup_def]
    exact secProj_sectorExp hS.ρm_pos hS.ρm_lt_ρp hb ht m w
  refine ⟨h1 ℓ, fun g => ?_⟩
  refine Y_ext_Nstar S hS fun m => ?_
  rw [h1 m]
  by_cases hm : m = ℓ
  · subst hm
    rw [secProj_inclSec_self, secProj_inclSec_self]
  · rw [secProj_inclSec_ne S hm, secProj_inclSec_ne S hm, map_zero]

/-- **R1 form of `lem:semigroup-construct`(2): both Duhamel formulas, sector-wise**
(`04_ring.tex:936-937`), with `e^{tL^tr} = exp(t(-iℓΩ))` and `𝒦 = k_ℓ𝒢_ℓ` on the sector. -/
theorem semigroup_duhamel_sector (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ) (G t : ℝ) :
    NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G) =
        NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G) +
          ∫ τ in (0 : ℝ)..t, NormedSpace.exp (((t - τ : ℝ) : ℂ) • S.transSec s ℓ G) *
            S.Ksec s ℓ * NormedSpace.exp ((τ : ℂ) • S.Lsec s ℓ G) ∧
      NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G) =
        NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G) +
          ∫ τ in (0 : ℝ)..t, NormedSpace.exp (((t - τ : ℝ) : ℂ) • S.Lsec s ℓ G) *
            S.Ksec s ℓ * NormedSpace.exp ((τ : ℂ) • S.transSec s ℓ G) := by
  simp only [Lsec_def]
  exact ⟨BanachExp.exp_add_eq_duhamel (S.transSec s ℓ G) (S.Ksec s ℓ) t,
    BanachExp.exp_add_eq_duhamel' (S.transSec s ℓ G) (S.Ksec s ℓ) t⟩

/-- The invariance of `Y^s_𝒵` (`04_ring.tex:1042-1044`). -/
theorem semigroup_mem_YZSub (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (Z : Set ℤ) {w : Y s S.Nstar} (hw : (w : Sob.SobTuple s) ∈ YZSub s S.Nstar Z) :
    ((S.semigroup s G t w : Y s S.Nstar) : Sob.SobTuple s) ∈ YZSub s S.Nstar Z := by
  simp only [semigroup_def]
  exact sectorExp_mem_YZSub hS.ρm_pos hS.ρm_lt_ρp (largeSectors_expBounded S hS s G) ht Z hw

/-- The semigroups on `Y^{s'}` and `Y^s` (`s ≤ s'`) are compatible with the inclusion
`Y^{s'} → Y^s` (implicit in the manuscript: one operator `e^{tL}` acting on every `Y^s`). -/
theorem semigroup_lowerY (S : SectorSetting) (hS : S.Valid) {s s' : ℕ} (hss' : s ≤ s') (G : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (w : Y s' S.Nstar) :
    lowerY s s' S.Nstar (S.semigroup s' G t w) = S.semigroup s G t (lowerY s s' S.Nstar w) := by
  obtain ⟨M, hM⟩ := largeSectors_expBounded S hS s G t
  obtain ⟨M', hM'⟩ := largeSectors_expBounded S hS s' G t
  simp only [semigroup_def]
  exact (sectorSum_lowerY hss' hS.ρm_pos hS.ρm_lt_ρp (fun ℓ => hM t ⟨ht, le_rfl⟩ ℓ)
    (fun ℓ => hM' t ⟨ht, le_rfl⟩ ℓ) (fun ℓ g => SgLaw_exp_Lsec_lowerSec S hS hss' ℓ G t g)
    w).symm

/-- **R1 form of `lem:semigroup-construct`(2): the generator extends `L(G)` on `Y^{s+1}`**
(`04_ring.tex:937-939`): for `w ∈ Y^{s+1}` and `t ≥ 0`,
`d/dt e^{tL}w = L(G) e^{tL}w = e^{tL} L(G)w` in `Y^s` (one-sided at `t = 0`). -/
theorem semigroup_hasDerivWithinAt (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ)
    (w : Y (s + 1) S.Nstar) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun τ => S.semigroup s G τ (lowerY s (s + 1) S.Nstar w))
        (S.LinY s G (S.semigroup (s + 1) G t w)) (Ici 0) t ∧
      S.LinY s G (S.semigroup (s + 1) G t w) = S.semigroup s G t (S.LinY s G w) := by
  have hb := largeSectors_expBounded S hS s G
  have hP : ∀ (ℓ : ℤ) (v : Y s S.Nstar), secProj s S.Nstar ℓ (S.semigroup s G t v) =
      NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G) (secProj s S.Nstar ℓ v) :=
    fun ℓ v => (semigroup_sector S hS s G ht ℓ).1 v
  have hcomm : S.LinY s G (S.semigroup (s + 1) G t w) = S.semigroup s G t (S.LinY s G w) := by
    refine Y_ext_Nstar S hS fun ℓ => ?_
    rw [SgLaw_secProj_LinY S hS s G _ ℓ, semigroup_lowerY S hS (Nat.le_succ s) G ht w, hP, hP,
      SgLaw_secProj_LinY S hS s G w ℓ]
    exact SgLaw_exp_comm (S.Lsec s ℓ G) t _
  refine ⟨?_, hcomm⟩
  rw [hcomm]
  have hv : HasSum (fun ℓ : ℤ => inclSec s S.Nstar ℓ
      (S.Lsec s ℓ G (secProj s S.Nstar ℓ (lowerY s (s + 1) S.Nstar w)))) (S.LinY s G w) := by
    have := hasSum_secProj_Nstar S hS (S.LinY s G w)
    simpa only [SgLaw_secProj_LinY S hS s G w] using this
  simp only [semigroup_def]
  exact hasDerivWithinAt_sectorExp hS.ρm_pos hS.ρm_lt_ρp hb hv ht

/-- `e^{tL(G)}` maps real-valued functions to real-valued functions (`05_single_ring.tex:45-47`). -/
theorem semigroup_isReal (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ) {t : ℝ}
    (ht : 0 ≤ t) {w : Y s S.Nstar} (hw : w.IsReal) : (S.semigroup s G t w).IsReal := by
  have hP : ∀ (ℓ : ℤ) (v : Y s S.Nstar), secProj s S.Nstar ℓ (S.semigroup s G t v) =
      NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G) (secProj s S.Nstar ℓ v) :=
    fun ℓ v => (semigroup_sector S hS s G ht ℓ).1 v
  refine isReal_Nstar S hS fun ℓ => ?_
  rw [hP, hP, SgLawH.secProj_neg_of_isReal S.isRotInvariant_Nstar hw ℓ]
  exact (SgLaw_exp_Lsec_conjSec S hS s ℓ G t _).symm

end SectorSetting

end NonUniqueEuler
