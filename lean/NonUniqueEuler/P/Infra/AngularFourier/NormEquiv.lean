import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.Lower
import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.Synthesis

/-!
# Proof: the norm equivalence on an annulus (`I/Infra/AngularFourier/NormEquiv.lean`)

Manuscript `lem:norm-equiv` (`04_ring.tex:843-864`).

Structure of the proof (deviation from the manuscript):
* **Lower bound** `c ∑_ℓ ‖g_ℓ‖²_{k,ℓ} ≤ ‖w‖²_{H^k}`, with summability: as in the manuscript, via
  the polar derivatives `∂_θ^n ∂_r^i w` (bounded by `‖w‖_{H^k}`, Leibniz with the coefficients
  `cos θ, sin θ, x₁, x₂`), Parseval in `θ`, `∂_θ = iℓ` and `∂_r` commuting with sectors, and the
  weights `2^{-p}(1+x)^p ≤ ∑_{n≤p} x^n` (`NormEquivAux.lower_bound`).
* **Upper bound**: instead of the converse polar formulas `∂₁ = cos θ ∂_r - (sin θ/r)∂_θ`, …
  (which need weak commutation of `∂_r` and `∂_θ`), we use the finite-sum bound
  `‖∑_{ℓ∈S} h_ℓ e^{iℓθ}‖²_{H^k} ≤ C ∑_{ℓ∈S} ‖h_ℓ‖²_{k,ℓ}`
  (`I/Infra/AngularFourier/NormEquiv/FiniteSum.lean`), pass to infinite sums by completeness of
  `Sob.Hk k` (synthesis, `NormEquivAux.synthesis`), and identify `w` with the synthesis of its
  own sectors (uniqueness of sector decompositions, `ae_eq_zero_of_sectorProj`).
-/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Ang

open NormEquivAux

/-- `lem:norm-equiv` on the annulus `{ρ₋ ≤ |x| ≤ ρ₊}`. -/
theorem exists_norm_equiv (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w : ℂ → ℂ, Sob.MemH k w →
      (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → w x = 0) →
      Summable (fun ℓ : ℤ => Sob.secNormSq k ℓ (Icc ρm ρp) (Polar.angularSector w ℓ)) ∧
        c * ∑' ℓ : ℤ, Sob.secNormSq k ℓ (Icc ρm ρp) (Polar.angularSector w ℓ) ≤
          Sob.normH k w ^ 2 ∧
        Sob.normH k w ^ 2 ≤
          C * ∑' ℓ : ℤ, Sob.secNormSq k ℓ (Icc ρm ρp) (Polar.angularSector w ℓ) := by
  obtain ⟨c, hc, hLow⟩ := lower_bound k (ρp := ρp) hρm
  obtain ⟨C, hC, hSyn⟩ := synthesis k hρm hρ
  refine ⟨c, C, hc, hC, fun w hw hwK => ?_⟩
  obtain ⟨hsum, hlow⟩ := hLow w hw hwK
  refine ⟨hsum, hlow, ?_⟩
  obtain ⟨w', hw', -, hsec, -, hbound⟩ := hSyn (fun ℓ => Polar.angularSector w ℓ)
    (fun ℓ => (memH1On_angularSector hρm hw hwK ℓ).1)
    (fun ℓ => (memH1On_angularSector hρm hw hwK ℓ).2) hsum
  have hwL2 : MemLp w 2 volume := (Sob.memH_iff.1 hw).1
  have hw'L2 : MemLp w' 2 volume := (Sob.memH_iff.1 hw').1
  have hzero : ∀ ℓ : ℤ, sectorProj ℓ (w - w') =ᵐ[volume] 0 := by
    intro ℓ
    filter_upwards [sectorProj_sub_ae ℓ hwL2 hw'L2, sectorProj_ae_eq_ofProfile ℓ w,
      sectorProj_ae_eq_ofProfile ℓ w', ofProfile_congr_ae (ℓ := ℓ) (hsec ℓ)] with x h1 h2 h3 h4
    simp only [h1, Pi.sub_apply, h2, h3, h4, sub_self, Pi.zero_apply]
  have hae : w - w' =ᵐ[volume] 0 := ae_eq_zero_of_sectorProj (hwL2.sub hw'L2) hzero
  have hww' : w' =ᵐ[volume] w := by
    filter_upwards [hae] with x hx
    have : w x - w' x = 0 := hx
    exact (sub_eq_zero.1 this).symm
  rw [(Sob.MemH.congr_ae hw' hww').2]
  exact hbound

/-- Single sector, both directions: for a profile `h ∈ H^k((0,∞))` supported in `[ρ₋, ρ₊]`,
`h(r) e^{iℓθ} ∈ H^k` with `c ‖h‖²_{k,ℓ} ≤ ‖h(r)e^{iℓθ}‖²_{H^k} ≤ C ‖h‖²_{k,ℓ}`, uniformly in `ℓ`. -/
theorem exists_norm_equiv_ofProfile (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ℓ : ℤ) (h : ℝ → ℂ), Sob.MemH1On k (Ioi 0) h →
      (∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0) →
      Sob.MemH k (ofProfile ℓ h) ∧
        c * Sob.secNormSq k ℓ (Icc ρm ρp) h ≤ Sob.normH k (ofProfile ℓ h) ^ 2 ∧
        Sob.normH k (ofProfile ℓ h) ^ 2 ≤ C * Sob.secNormSq k ℓ (Icc ρm ρp) h := by
  obtain ⟨c, hc, hLow⟩ := lower_bound k (ρp := ρp) hρm
  obtain ⟨C, hC, hFS⟩ := exists_normH_sum_ofProfile_le k hρm hρ
  refine ⟨c, C, hc, hC, fun ℓ h hh hhI => ?_⟩
  obtain ⟨hmem, hup⟩ := hFS {ℓ} (fun _ => h) (fun _ _ => hh) (fun _ _ => hhI)
  simp only [Finset.sum_singleton] at hmem hup
  have hIcc : Icc ρm ρp ⊆ Ioi (0 : ℝ) := fun r hr => lt_of_lt_of_le hρm hr.1
  obtain ⟨-, hlow⟩ := hLow (ofProfile ℓ h) hmem (ofProfile_eq_zero_outside hhI)
  have htsum : ∑' m : ℤ, Sob.secNormSq k m (Icc ρm ρp) (Polar.angularSector (ofProfile ℓ h) m) =
      Sob.secNormSq k ℓ (Icc ρm ρp) h := by
    simp_rw [secNormSq_angularSector_ofProfile measurableSet_Icc hIcc ℓ _ h]
    exact tsum_ite_eq ℓ (fun _ => Sob.secNormSq k ℓ (Icc ρm ρp) h)
  rw [htsum] at hlow
  exact ⟨hmem, hlow, hup⟩

/-- Synthesis: profiles with `∑_ℓ ‖h_ℓ‖²_{k,ℓ} < ∞` are the sectors of a `w ∈ H^k` supported in
the annulus, `w = ∑_ℓ h_ℓ(r) e^{iℓθ}` in `L²`. -/
theorem exists_memH_of_summable (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℤ → ℝ → ℂ, (∀ ℓ, Sob.MemH1On k (Ioi 0) (h ℓ)) →
      (∀ ℓ, ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h ℓ r = 0) →
      Summable (fun ℓ : ℤ => Sob.secNormSq k ℓ (Icc ρm ρp) (h ℓ)) →
      ∃ w : ℂ → ℂ, Sob.MemH k w ∧ (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → w x = 0) ∧
        (∀ ℓ, Polar.angularSector w ℓ =ᵐ[volume.restrict (Ioi 0)] h ℓ) ∧
        Tendsto (fun N : ℕ => Sob.l2 (w - ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) N, ofProfile ℓ (h ℓ)))
          atTop (𝓝 0) ∧
        Sob.normH k w ^ 2 ≤ C * ∑' ℓ : ℤ, Sob.secNormSq k ℓ (Icc ρm ρp) (h ℓ) :=
  synthesis k hρm hρ

end NonUniqueEuler.Ang
