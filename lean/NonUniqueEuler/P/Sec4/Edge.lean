import NonUniqueEuler.Defs.Sec4.Operators
import NonUniqueEuler.I.Sec4.Sector
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition
import NonUniqueEuler.H.Sec4.Edge.Profile

/-!
# Proof of `I/Sec4/Edge.lean`: `lem:edge` (a priori bound for the eigenvalues of large sectors)

Manuscript `04_ring.tex:718-769`.

* `edge_bound`: the typed eigen-equation `L_ℓ(G) g = λ g` on `Y^0_ℓ` is transferred to the
  profile `g_ℓ = Polar.angularSector g.fn ℓ` (`Lsec_zero_spec`, `Sect.Ysec.fn_ae_eq_ofProfile`,
  polar coordinates `EdgeH.ae_eq_of_ofProfile_ae_eq'`); `g ≠ 0` gives `g_ℓ ≠ 0` a.e. through
  `‖g‖² = 2π ∫ |g_ℓ|² r dr` (`isProfileL2_angularSector`). The profile statement is
  `EdgeH.edge_profile` (`H/Sec4/Edge/Profile.lean`), the manuscript's energy argument.
* `Zedge_antitone`: `r/ρ < 1` on `𝒰₊ × 𝒰₋`, so the integrand decreases in `ℓ`.

**Deviation (harmless).** The manuscript reduces to the sign `+` by conjugation
(`lem:resolvent`); the energy argument works verbatim for any `ℓ ≠ 0` (with `n = |ℓ|` in the
kernel and the factor `ℓ` in `k_ℓ`), so no reduction is made. The manuscript's splitting
`g = g_a + g_b` and "diagonal terms are real" is replaced by the equivalent identity
`T - T̄ = -c (B(ω̄'e r, |ω̄'|e r) - B(|ω̄'|e r, ω̄'e r))` (one use of the Hermitian symmetry of the
kernel), in which only the cross terms on `𝒰₊ × 𝒰₋` and `𝒰₋ × 𝒰₊` survive pointwise
(`EdgeH.K0_mul_cross`); there the kernel factorizes, so `Im T = -2c Im(αβ̄)` with one-dimensional
integrals `α`, `β`, and the two-dimensional Cauchy–Schwarz becomes two one-dimensional ones
(`Z_n = Z₊ Z₋`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace SectorSetting

open Sect

/-- `lem:edge`: under `S.EdgeSplit`, every eigenvalue `λ` of `L_{ℓ'}(G)` on `Y^0_{ℓ'}`
(`ℓ' ≠ 0`, any `G ∈ ℝ`) with `Re λ > 0` satisfies `Re λ ≤ ½ Z_{|ℓ'|}^{1/2}`. -/
theorem edge_bound (S : SectorSetting) (hS : S.Valid) (hsplit : S.EdgeSplit) {ℓ : ℤ}
    (hℓ : ℓ ≠ 0) (G : ℝ) (z : ℂ) (hz : 0 < z.re) (g : Ysec 0 S.Nstar ℓ) (hg : g ≠ 0)
    (hgz : S.Lsec 0 ℓ G g = z • g) :
    z.re ≤ 1 / 2 * Real.sqrt (S.Zedge ℓ.natAbs) := by
  obtain ⟨hprof, hnorm⟩ := isProfileL2_angularSector S hS ℓ g
  refine EdgeH.edge_profile hS hsplit hℓ G hz hprof ?_ ?_
  · intro h0
    apply hg
    have hae : (fun r => ‖Polar.angularSector g.fn ℓ r‖ ^ 2 * r) =ᵐ[volume.restrict (Ioi 0)]
        0 := by
      filter_upwards [h0] with r hr
      simp [hr]
    have hint0 : ∫ r in Ioi (0 : ℝ), ‖Polar.angularSector g.fn ℓ r‖ ^ 2 * r = 0 := by
      rw [integral_congr_ae hae]
      simp
    have h2 : ‖g‖ ^ 2 = 0 := by rw [hnorm, hint0, mul_zero]
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
  · have h1 := Lsec_zero_spec S hS ℓ G g
    rw [hgz] at h1
    have h2 : (z • g).fn =ᵐ[volume] z • g.fn :=
      Lp.coeFn_smul z ((g : Sob.SobTuple 0).ofLp (Sob.idx0 0))
    have h3 : g.fn =ᵐ[volume] Ang.ofProfile ℓ (Polar.angularSector g.fn ℓ) :=
      Sect.Ysec.fn_ae_eq_ofProfile hS.ρm_pos g
    have h4 : Ang.ofProfile ℓ (S.LsecFn ℓ G (Polar.angularSector g.fn ℓ)) =ᵐ[volume]
        Ang.ofProfile ℓ (fun r => z * Polar.angularSector g.fn ℓ r) := by
      filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
      rw [← hx1, hx2, Pi.smul_apply, hx3, smul_eq_mul]
      simp only [Ang.ofProfile]
      ring
    exact EdgeH.ae_eq_of_ofProfile_ae_eq' h4

/-- `lem:edge`, last assertion: `Z_ℓ` is nonincreasing in `ℓ ≥ 1`. -/
theorem Zedge_antitone (S : SectorSetting) (hS : S.Valid) (hsplit : S.EdgeSplit) {ℓ m : ℕ}
    (hℓ : 1 ≤ ℓ) (hℓm : ℓ ≤ m) : S.Zedge m ≤ S.Zedge ℓ := by
  have hd := EdgeH.continuous_dom hS
  have hUp := EdgeH.measurableSet_Up hS
  have hUn := EdgeH.measurableSet_Un hS
  have hnn : ∀ (k : ℕ) (r ρ : ℝ), 0 ≤ (r / ρ) ^ (2 * k) * |S.dom r| * |S.dom ρ| := by
    intro k r ρ
    refine mul_nonneg (mul_nonneg ?_ (abs_nonneg _)) (abs_nonneg _)
    rw [pow_mul]
    positivity
  have hinner : ∀ r : ℝ, IntegrableOn (fun ρ => (r / ρ) ^ (2 * ℓ) * |S.dom r| * |S.dom ρ|)
      {ρ : ℝ | 0 < ρ ∧ S.dom ρ < 0} := by
    intro r
    have hc : ContinuousOn (fun ρ => (r / ρ) ^ (2 * ℓ) * |S.dom r| * |S.dom ρ|)
        (Icc S.r₁ S.r₂) :=
      (((continuousOn_const.div continuousOn_id
        fun ρ hρ => (EdgeH.pos_of_mem_Icc hS hρ).ne').pow _).mul continuousOn_const).mul
        hd.abs.continuousOn
    exact (hc.integrableOn_compact isCompact_Icc).mono_set (EdgeH.Un_subset hS)
  have houter : (fun r => ∫ ρ in {ρ : ℝ | 0 < ρ ∧ S.dom ρ < 0},
      (r / ρ) ^ (2 * ℓ) * |S.dom r| * |S.dom ρ|) =
      fun r => (r ^ ℓ) ^ 2 * |S.dom r| *
        ∫ ρ in {ρ : ℝ | 0 < ρ ∧ S.dom ρ < 0}, ((ρ ^ ℓ)⁻¹) ^ 2 * |S.dom ρ| := by
    funext r
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
    simp only
    rw [pow_mul', div_pow, div_eq_mul_inv, mul_pow]
    ring
  have hout : Integrable (fun r => ∫ ρ in {ρ : ℝ | 0 < ρ ∧ S.dom ρ < 0},
      (r / ρ) ^ (2 * ℓ) * |S.dom r| * |S.dom ρ|)
      (volume.restrict {r : ℝ | 0 < r ∧ 0 < S.dom r}) := by
    rw [houter]
    exact ((((((continuous_pow ℓ).pow 2).mul hd.abs).mul
      continuous_const).continuousOn).integrableOn_compact isCompact_Icc).mono_set
      (EdgeH.Up_subset hS)
  unfold Zedge
  refine integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun r => integral_nonneg fun ρ => hnn m r ρ) hout ?_
  refine ae_restrict_of_forall_mem hUp fun r hr => ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ρ => hnn m r ρ)
    (hinner r) ?_
  refine ae_restrict_of_forall_mem hUn fun ρ hρ => ?_
  have hlt : r < ρ := hsplit r ρ hr.1 hρ.1 hr.2 hρ.2
  have h0 : 0 ≤ r / ρ := div_nonneg hr.1.le hρ.1.le
  have h1 : r / ρ ≤ 1 := (div_le_one hρ.1).2 hlt.le
  have hpow := pow_le_pow_of_le_one h0 h1 (Nat.mul_le_mul_left 2 hℓm)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow (abs_nonneg _))
    (abs_nonneg _)

end SectorSetting

end NonUniqueEuler
