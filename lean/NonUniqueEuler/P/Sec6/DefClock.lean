import NonUniqueEuler.Defs.Sec6.All
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec6.Adm
import NonUniqueEuler.I.SmoothB.Smooth

/-!
# Proof: the facts stated inside `def:clock` and right after it

Proof of the interface `NonUniqueEuler/I/Sec6/DefClock.lean` (`def:clock`, `06_datum.tex:399-430`).

* `kickTime_eq`: algebra with `tsh_eq_T_add` (`t♯_k = T_{k+1} + T_pin/A_{k+1}`) and `amp_succ`
  (`A_{k+1} = μ A_k`).
* `clock_start`: `Φ_0 = id` holds for the maximal-flow construction itself
  (`maxFlow F U s s y = y`, both when a maximal solution exists — its initial value — and in the
  junk case); `ω(0) = f^{(n)}` from `thm:smooth` (`sol_isSmoothSol`, the datum being `C_c^∞` by
  `lem:adm`); `f^{(n)} 1_{S_n} = f^{(n)}_n` and `S_n ⊂ 𝒩₋_n` from `lem:regions-basic`(1);
  `𝒩₋ ⊂ N` from the radii (`a/2 ≤ 7a/8`, `5/4 ≤ 2`); the ring part of ring `n` in ring-`n` units
  is `Φ^{κ_seed}` (`Valid.ringConfig_ring0_n`); `t♯_n = 0`, `G_n = 0` (`tsh_n`, `G_n`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Datum

namespace Approx

open RingData

/-- The maximal flow at its own initial time is the identity (also in the junk case). -/
private theorem maxFlow_self_eq {F : ℝ → ℂ → ℂ} {U : Set (ℝ × ℂ)} {s : ℝ} {y : ℂ} :
    Smooth.maxFlow F U s s y = y := by
  classical
  by_cases h : ∃ (J : Set ℝ) (γ : ℝ → ℂ), Smooth.IsMaxSol F U s y J γ
  · exact (Smooth.isMaxSol_maxFlow h).init
  · rw [Smooth.maxFlow, dite_eq_right h]

/-- `Φ_0 = id`. -/
private theorem flow_zero_eq (P : Approx) (y : ℂ) : P.flow 0 y = y := by
  simp only [flow, Smooth.flowOf]
  exact maxFlow_self_eq

/-- `S_k(0) = S_k`. -/
private theorem St_zero_eq (P : Approx) (k : ℕ) : P.St k 0 = P.S k := by
  have h : P.flow 0 = id := funext (flow_zero_eq P)
  simp only [St, h, Set.image_id]

/-- `ω^{(n)}(0) = f^{(n)}`. -/
private theorem om_zero_eq (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) :
    P.om 0 = P.f := by
  obtain ⟨hcd, hcs, -⟩ :=
    (adm P.χ hP.admissible hN hP.datumParams ⟨hP.kseed_pos, hP.kseed_le⟩).1 P.n hP.two_le_n
  obtain ⟨R₀, hR₀⟩ := hcs.isCompact.isBounded.subset_ball 0
  have hD : Smooth.IsSmoothDatum P.f R₀ := ⟨hcd, hR₀⟩
  rw [hP.om_eq]
  exact (Smooth.sol_isSmoothSol hD).init

/-- `𝒩₋ ⊂ N`. -/
private theorem annNm_subset_annN : annNm ⊆ annN := by
  intro x hx
  have ha : 0 < a := Real.exp_pos _
  obtain ⟨hx1, hx2⟩ : 7 / 8 * a ≤ ‖x‖ ∧ ‖x‖ ≤ 5 / 4 := hx
  exact (⟨by linarith, by linarith⟩ : a / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2)

/-- `r U ⊂ r V` for `U ⊂ V`. -/
private theorem scaleSet_mono {r : ℝ} {U V : Set ℂ} (h : U ⊆ V) : scaleSet r U ⊆ scaleSet r V :=
  fun _ hx => h hx

/-- **The kick time on the active phase** (`def:clock`, `06_datum.tex:424-426`): for `1 ≤ k < n`
and every `t`, `A_{k+1}(t - T_{k+1}) = T_pin + μ A_k(t - t♯_k)`; in particular the kick time of
`t♯_k` is `T_pin`. -/
theorem kickTime_eq (P : Approx) (hP : P.Valid) {k : ℕ} (hk : 1 ≤ k) (hkn : k < P.n) :
    (∀ t : ℝ, P.kickTime k t = P.Tpin + P.μ * P.activeTime k t) ∧
    P.kickTime k (P.tsh k) = P.Tpin := by
  have hA : P.A (k + 1) ≠ 0 := (hP.A_pos (k + 1)).ne'
  have hAs : P.A (k + 1) = P.μ * P.A k := amp_succ P.A₁ P.μ hk
  have hT : P.T (k + 1) = P.tsh k - P.Tpin / P.A (k + 1) := by
    rw [tsh_eq_T_add P hkn]; ring
  have key : ∀ t : ℝ, P.kickTime k t = P.Tpin + P.μ * P.activeTime k t := by
    intro t
    simp only [kickTime, activeTime]
    rw [hT, mul_sub, mul_sub, mul_div_cancel₀ _ hA, hAs]
    ring
  refine ⟨key, ?_⟩
  rw [key, activeTime_tsh, mul_zero, add_zero]

/-- **The start of the clock** (`06_datum.tex:429-430`): `S_k(0) = S_k` for every `k`;
`S_n(0) ⊂ N_n`; `w_n(0) = Φ^{κ_seed} - Φ`; and `c_n(0) = ℓ_*(0)(Φ^{κ_seed} - Φ)`. -/
theorem clock_start (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) :
    (∀ k : ℕ, P.St k 0 = P.S k) ∧ P.PertDefined P.n 0 ∧
    P.w P.n 0 = (fun y => ((OneRing.PhiSeed P.χ P.κs y - ringPhi P.χ y : ℝ) : ℂ)) ∧
    P.c0 P.n =
      Eig.ellFn P.χ 0 (fun y => ((OneRing.PhiSeed P.χ P.κs y - ringPhi P.χ y : ℝ) : ℂ)) := by
  obtain ⟨h1, -, -, hSn⟩ := regions_basic_one P hP hN
  have hnmem : P.n ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨hP.one_le_n, le_rfl⟩
  have hind : (P.S P.n).indicator P.f = P.term P.n := (h1 P.n hnmem).2.2.2
  -- `ω(0) 1_{S_n(0)} = f^{(n)}_n`
  have hring : P.omegaRing P.n 0 = P.term P.n := by
    rw [omegaRing, St_zero_eq, om_zero_eq P hP hN, hind]
  -- `w_n(0) = Φ^{κ_seed} - Φ`
  have hw : P.w P.n 0 = (fun y => ((OneRing.PhiSeed P.χ P.κs y - ringPhi P.χ y : ℝ) : ℂ)) := by
    funext y
    have h0 : P.unitsVort P.n (P.term P.n) = OneRing.PhiSeed P.χ P.κs :=
      hP.ringConfig_ring0_n
    rw [w_apply, hring, h0]
  refine ⟨St_zero_eq P, ?_, hw, ?_⟩
  · -- `S_n(0) = S_n ⊂ 𝒩₋_n ⊂ N_n`
    show P.St P.n 0 ⊆ P.Nk P.n
    rw [St_zero_eq]
    exact hSn.trans (scaleSet_mono annNm_subset_annN)
  · rw [c0, tsh_n, G_n, hw]

end Approx

end Datum

end NonUniqueEuler
