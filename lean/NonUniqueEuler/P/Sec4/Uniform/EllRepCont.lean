import NonUniqueEuler.H.Sec4.Uniform.EllRepCont.Cont

/-!
# Proof: the representer of `ℓ_*(G)` is continuous in `L²(N)` (step of `lem:uniform`)

Proof of `I/Sec4/Uniform/EllRepCont.lean` (`04_ring.tex:1540-1543`). Same declaration, statement
copied verbatim.

**Proof.** By `ellRep_eq`, `ellRep(G) = h_G(|x|) e^{3iθ}` with the profile
`h_G = 1_{[a/2,2]} · A(G, ·)`, `A(G, r) = (n_*/(2π conj J)) conj(ψ_*(log r) M_*(r))`. So
`ellRep(G) - ellRep(G₀)` is the sector function with profile `h_G - h_{G₀}`, and the polar
formula `memLp_ofProfile_iff` gives
`‖ellRep(G) - ellRep(G₀)‖_{L²} = D(G) := (2π ∫_{a/2}^2 |A(G,r) - A(G₀,r)|² r dr)^{1/2}`.
`A` is jointly continuous on `[0,G₁] × [a/2,2]` (`cRep_continuousOn`: `n_*`, `J` continuous and
`J ≠ 0`; `adjEig_path_continuousOn`: `ψ_*`, `M_*` continuous), so `D` is continuous on
`[0,G₁]` (parametric integral over a compact interval), and `D(G₀) = 0`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology ComplexConjugate

namespace NonUniqueEuler

namespace Eig

open RingData

namespace EllRepContH

variable {χ : ℝ → ℝ}

/-- The profile `A(G, r) = (n_*/(2π conj J)) conj(ψ_*(log r) M_*(r))` of the representer. -/
def repProf (χ : ℝ → ℝ) (G r : ℝ) : ℂ := cRep χ G * (ringPhiSetting χ).adjEig 3 (lam χ G) G r

theorem repProf_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (fun p : ℝ × ℝ => repProf χ p.1 p.2) (Icc 0 Gbar ×ˢ Ioi 0) :=
  ((cRep_continuousOn hχ hN).comp continuousOn_fst fun _ hp => hp.1).mul
    (adjEig_path_continuousOn hχ hN)

/-- The difference of the representers is the sector function with profile the difference of
the profiles. -/
theorem ellRep_sub_eq (χ : ℝ → ℝ) (G G₀ : ℝ) :
    (fun x => ellRep χ G x - ellRep χ G₀ x) =
      Ang.ofProfile 3 ((Icc (a / 2) 2).indicator fun r => repProf χ G r - repProf χ G₀ r) := by
  classical
  funext x
  rw [ellRep_eq, ellRep_eq]
  simp only [Ang.ofProfile, Set.indicator_apply, repProf]
  split_ifs
  · ring
  · ring

/-- `‖ellRep(G) - ellRep(G₀)‖_{L²} = (2π ∫_{a/2}^2 |A(G,r) - A(G₀,r)|² r dr)^{1/2}`. -/
theorem l2_ellRep_sub_eq (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G G₀ : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) (hG₀ : G₀ ∈ Icc (0 : ℝ) Gbar) :
    Sob.l2 (fun x => ellRep χ G x - ellRep χ G₀ x) =
      Real.sqrt (2 * π * ∫ r in (a / 2)..2, ‖repProf χ G r - repProf χ G₀ r‖ ^ 2 * r) := by
  rw [ellRep_sub_eq]
  set h : ℝ → ℂ := (Icc (a / 2) 2).indicator fun r => repProf χ G r - repProf χ G₀ r with hhdef
  have hslice : ∀ G' ∈ Icc (0 : ℝ) Gbar, ContinuousOn (repProf χ G') (Ioi 0) := by
    intro G' hG'
    have hpath : ContinuousOn (fun r : ℝ => ((G', r) : ℝ × ℝ)) (Ioi 0) :=
      continuousOn_const.prodMk continuousOn_id
    exact ((repProf_continuousOn hχ hN).comp hpath fun r hr => ⟨hG', hr⟩).congr fun _ _ => rfl
  have hm : AEStronglyMeasurable h (volume.restrict (Ioi 0)) :=
    (((hslice G hG).sub (hslice G₀ hG₀)).aestronglyMeasurable measurableSet_Ioi).indicator
      measurableSet_Icc
  have h2 := (Ang.memLp_ofProfile_iff (ℓ := 3) hm).2
  have ha2 : a / 2 ≤ 2 := by linarith [a_pos_lt_one.2]
  have hint : ∫ r in Ioi (0 : ℝ), ‖h r‖ ^ 2 * r =
      ∫ r in (a / 2)..2, ‖repProf χ G r - repProf χ G₀ r‖ ^ 2 * r := by
    rw [setIntegral_Ioi_eq_intervalIntegral (by linarith [a_pos_lt_one.1]) ha2
      fun r _ hr' => by simp [hhdef, Set.indicator_of_notMem hr']]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ha2] at hr
    simp only [hhdef, Set.indicator_of_mem hr]
  have hnn : 0 ≤ Sob.l2 (Ang.ofProfile 3 h) := ENNReal.toReal_nonneg
  rw [← hint, ← h2, Real.sqrt_sq hnn]

end EllRepContH

open EllRepContH in
/-- **`lem:uniform`, continuity of the representer of `ℓ_*`** (`04_ring.tex:1540-1543`):
`ellRep(G) → ellRep(G₀)` in `L²` as `G → G₀` in `[0,G₁]`. -/
theorem ellRep_tendsto_l2 (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G₀ : ℝ} (hG₀ : G₀ ∈ Icc (0 : ℝ) Gbar) :
    Tendsto (fun G => Sob.l2 (fun x => ellRep χ G x - ellRep χ G₀ x)) (𝓝[Icc 0 Gbar] G₀)
      (𝓝 0) := by
  have hsub := prod_mono (subset_refl (Icc (0 : ℝ) Gbar)) Icc_a_two_subset
  have hA := (repProf_continuousOn hχ hN).mono hsub
  have hA₀ : ContinuousOn (fun p : ℝ × ℝ => repProf χ G₀ p.2) (Icc 0 Gbar ×ˢ Icc (a / 2) 2) := by
    have hpath : ContinuousOn (fun p : ℝ × ℝ => ((G₀, p.2) : ℝ × ℝ))
        (Icc 0 Gbar ×ˢ Icc (a / 2) 2) :=
      continuousOn_const.prodMk continuousOn_snd
    exact (hA.comp hpath fun p hp => ⟨hG₀, hp.2⟩).congr fun _ _ => rfl
  have hF : ContinuousOn (fun p : ℝ × ℝ => ‖repProf χ p.1 p.2 - repProf χ G₀ p.2‖ ^ 2 * p.2)
      (Icc 0 Gbar ×ˢ Icc (a / 2) 2) :=
    ((hA.sub hA₀).norm.pow 2).mul continuousOn_snd
  have hI := continuousOn_intervalIntegral_rect
    (F := fun G r => ‖repProf χ G r - repProf χ G₀ r‖ ^ 2 * r) (c := a / 2) (d := 2)
    Gbar_nonneg (by linarith [a_pos_lt_one.2]) hF
  have hD := Real.continuous_sqrt.comp_continuousOn ((continuousOn_const (c := 2 * π)).mul hI)
  have ht : Tendsto
      (fun G => Real.sqrt (2 * π * ∫ r in (a / 2)..2, ‖repProf χ G r - repProf χ G₀ r‖ ^ 2 * r))
      (𝓝[Icc 0 Gbar] G₀)
      (𝓝 (Real.sqrt (2 * π * ∫ r in (a / 2)..2, ‖repProf χ G₀ r - repProf χ G₀ r‖ ^ 2 * r))) :=
    (hD G₀ hG₀).tendsto
  have hD0 : Real.sqrt (2 * π * ∫ r in (a / 2)..2, ‖repProf χ G₀ r - repProf χ G₀ r‖ ^ 2 * r) =
      0 := by
    simp
  rw [hD0] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with G hG
  exact (l2_ellRep_sub_eq hχ hN hG hG₀).symm

end Eig

end NonUniqueEuler
