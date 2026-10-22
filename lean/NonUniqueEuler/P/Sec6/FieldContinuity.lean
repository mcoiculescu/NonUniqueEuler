import NonUniqueEuler.Defs.Sec6.All
import NonUniqueEuler.H.Sec6.FieldContinuity.Generic
import NonUniqueEuler.H.Sec6.FieldContinuity.Ext

/-!
# Proof: continuity in time of the fields, of their norms and of the moments

Proof of the interface `NonUniqueEuler/I/Sec6/FieldContinuity.lean` (the paragraph after
`lem:regions-basic`, `06_datum.tex:294-321`, and `08_kick.tex:125-127`).

**Route.** By `eq:omega-ge` (`regions_basic_three`), for `t ≥ 0`,
`ω_{≥k+1}(t) = g_in ∘ Φ_t⁻¹` and `ω(t)1_{S_1(t)∪…∪S_{k-1}(t)} = g_out ∘ Φ_t⁻¹` with
`g_in = Σ_{i>k} f^{(n)}_i`, `g_out = Σ_{i<k} f^{(n)}_i ∈ C_c^∞`. Since `(t, x) ↦ Φ_t⁻¹(x)` is `C^∞`
(`thm:smooth`(4)), the space–time vorticities `(τ, y) ↦ A_k⁻¹ g(Φ_{τ/A_k}⁻¹(r_k y))` are `C^∞` with
supports bounded locally uniformly in time, so their Biot–Savart velocities are `C^∞` on
`ℝ × ℝ²` (`I/Infra/BSParam/ContDiff.lean`). Hence `h^in_k`, `h^out_k`, `h_k` agree for `τ ≥ 0`
with fields that are `C^∞` on `ℝ × (ℂ ∖ {0})` (the monopole `G_k y^⊥/|y|²` is smooth off `0`), and
`I/Infra/CkNorm/Continuity.lean` gives the continuity into `C^M(N')` and of the norms. The
majorants are `e^{στ} ∫₀^τ e^{-σv} η(v) dv` (`continuousOn_primitive_interval`). The moment
`Q_3[ω_{≥k+1}(t)] = ∫ g_in(Φ_t⁻¹ x) x³ dx` is continuous by dominated convergence on a ball.

**Deviation.** The confinement hypotheses (`HInDefined`, `HOutDefined`) are not
used: the vorticity is jointly `C_c^∞`, so the velocity is smooth everywhere. They remain in the
statements, where they make the fields the manuscript's objects.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Datum

namespace Approx

open RingData FieldContinuityAux

/-- `[A t₁, A t₂] ⊆ [0, ∞)` for `A > 0`, `t₁ ≥ 0`. -/
private theorem Icc_mul_subset_Ici {A t₁ t₂ : ℝ} (hA : 0 < A) (h0 : 0 ≤ t₁) :
    Icc (A * t₁) (A * t₂) ⊆ Ici 0 :=
  fun _ hτ => le_trans (mul_nonneg hA.le h0) hτ.1

/-- **Continuity of the inner field** (`06_datum.tex:294-315`): if `D_{k+1}(t) ⊂ B_{a r_k/8}` for
every `t ∈ [t₁, t₂] ⊂ [0, ∞)`, then for every integer `M ≥ 0`, `τ ↦ h^in_k(τ)` is continuous from
`[A_k t₁, A_k t₂]` into `C^M(N')`. -/
theorem hIn_continuous (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ P.n) {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁)
    (hdef : ∀ t ∈ Icc t₁ t₂, P.HInDefined k t) (M : ℕ) :
    OneRing.CkPathOn M annN' (Icc (P.A k * t₁) (P.A k * t₂)) (P.hIn k) :=
  ckPathOn_of_ext (Icc_mul_subset_Ici (hP.A_pos k) h0) (hIn_ext hP hN hk hkn)

/-- **Continuity of the outer field** (`06_datum.tex:315-318`): if the rings `i < k` lie outside
`B_{6r_k}` at every `t ∈ [t₁, t₂] ⊂ [0, ∞)`, then for every integer `M ≥ 0`, `τ ↦ h^out_k(τ)` is
continuous from `[A_k t₁, A_k t₂]` into `C^M(N')`. -/
theorem hOut_continuous (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ P.n) {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁)
    (hdef : ∀ t ∈ Icc t₁ t₂, P.HOutDefined k t) (M : ℕ) :
    OneRing.CkPathOn M annN' (Icc (P.A k * t₁) (P.A k * t₂)) (P.hOut k) :=
  ckPathOn_of_ext (Icc_mul_subset_Ici (hP.A_pos k) h0) (hOut_ext hP hN hk hkn)

/-- **Continuity of the external field** `h_k = h^in_k + h^out_k` (`06_datum.tex:294-318`): if both
fields are defined at every `t ∈ [t₁, t₂] ⊂ [0, ∞)`, then for every integer `M ≥ 0`,
`τ ↦ h_k(τ)` is continuous from `[A_k t₁, A_k t₂]` into `C^M(N')`. -/
theorem hField_continuous (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ P.n) {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁)
    (hdef : ∀ t ∈ Icc t₁ t₂, P.HDefined k t) (M : ℕ) :
    OneRing.CkPathOn M annN' (Icc (P.A k * t₁) (P.A k * t₂)) (P.hField k) :=
  ckPathOn_of_ext (Icc_mul_subset_Ici (hP.A_pos k) h0) (hField_ext hP hN hk hkn)

/-- `η^in_k`, `η^out_k`, `η_k` are continuous on every `J ⊆ [0, ∞)` (no definedness needed). -/
private theorem eta_continuousOn_aux (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ P.n) (Mh : ℕ) {J : Set ℝ} (hJ : J ⊆ Ici 0) :
    ContinuousOn (P.etaIn Mh k) J ∧ ContinuousOn (P.etaOut Mh k) J ∧
      ContinuousOn (P.eta Mh k) J := by
  have h1 : ContinuousOn (P.etaIn Mh k) J :=
    continuousOn_normCk_of_ext (M := Mh) hJ (hIn_ext hP hN hk hkn)
  have h2 : ContinuousOn (P.etaOut Mh k) J :=
    continuousOn_normCk_of_ext (M := Mh) hJ (hOut_ext hP hN hk hkn)
  exact ⟨h1, h2, h1.add h2⟩

/-- **Continuity of the field norms** (`06_datum.tex:319-320`): `η^in_k`, `η^out_k` and `η_k` are
continuous on `[A_k t₁, A_k t₂]` whenever the corresponding fields are defined on `[t₁, t₂]`. -/
theorem eta_continuous (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ P.n) {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (Mh : ℕ) :
    ((∀ t ∈ Icc t₁ t₂, P.HInDefined k t) →
      ContinuousOn (P.etaIn Mh k) (Icc (P.A k * t₁) (P.A k * t₂))) ∧
    ((∀ t ∈ Icc t₁ t₂, P.HOutDefined k t) →
      ContinuousOn (P.etaOut Mh k) (Icc (P.A k * t₁) (P.A k * t₂))) ∧
    ((∀ t ∈ Icc t₁ t₂, P.HDefined k t) →
      ContinuousOn (P.eta Mh k) (Icc (P.A k * t₁) (P.A k * t₂))) := by
  obtain ⟨h1, h2, h3⟩ :=
    eta_continuousOn_aux P hP hN hk hkn Mh (Icc_mul_subset_Ici (t₂ := t₂) (hP.A_pos k) h0)
  exact ⟨fun _ => h1, fun _ => h2, fun _ => h3⟩

/-- **Continuity of the Duhamel majorants** (`06_datum.tex:202-209`, `:319-321`): if `h_k` is
defined on `[0, t₂]`, then `maj_k` is continuous on `[0, A_k t₂]`; if `h^in_k` is defined on
`[0, t₂]`, then `maj^in_k` is continuous on `[0, A_k t₂]`. -/
theorem maj_continuous (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ P.n) {t₂ : ℝ} (h0 : 0 ≤ t₂) (Mh : ℕ) :
    ((∀ t ∈ Icc (0 : ℝ) t₂, P.HDefined k t) →
      ContinuousOn (P.majK Mh k) (Icc 0 (P.A k * t₂))) ∧
    ((∀ t ∈ Icc (0 : ℝ) t₂, P.HInDefined k t) →
      ContinuousOn (P.majIn Mh k) (Icc 0 (P.A k * t₂))) := by
  have hB : 0 ≤ P.A k * t₂ := mul_nonneg (hP.A_pos k).le h0
  obtain ⟨h1, -, h3⟩ :=
    eta_continuousOn_aux P hP hN hk hkn Mh (J := Icc 0 (P.A k * t₂)) fun _ hτ => hτ.1
  exact ⟨fun _ => maj_continuousOn hB h3, fun _ => maj_continuousOn hB h1⟩

/-- **Continuity of the normalized moment** (`08_kick.tex:125-127`): for `1 ≤ k < n`,
`t ↦ q_{k+1}(t)` is continuous on `[0, ∞)`. -/
theorem q_continuous (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k < P.n) :
    ContinuousOn (P.q (k + 1)) (Ici 0) := by
  obtain ⟨I, hI, heq⟩ := omegaGe_moment_continuous hP hN hk hkn.le
  have hc : Continuous fun t => (starRingEnd ℂ) (I t) /
      (((P.A (k + 1) * P.r (k + 1) ^ (3 + 2) : ℝ)) : ℂ) :=
    (Complex.continuous_conj.comp hI).div_const _
  refine hc.continuousOn.congr fun t ht => ?_
  simp only [q, heq t ht]

end Approx

end Datum

end NonUniqueEuler
