import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import NonUniqueEuler.Defs.Sec4.RingSetting
import NonUniqueEuler.Defs.Sec4.Operators
import NonUniqueEuler.I.Sec4.Edge
import NonUniqueEuler.I.Sec4.ClosedForm
import NonUniqueEuler.I.Sec4.RingFacts

/-!
# Proof: `cor:sectors-9` (no unstable eigenvalue with `Re λ ≥ 9/200` in sectors `|ℓ| ≥ 9`)

Proof of `I/Sec4/Sectors9.lean` (`04_ring.tex:1173-1178`, proof `:1179-1190`). Same
declarations, statements copied verbatim.

Proof (as in the manuscript).
* For any setting `S` and `R > 0`, the dilated setting has `ω̄_R'(r) = R ω̄'(Rr)`
  (`dom_dilate`, from `deriv_comp_mul_left`; no regularity is needed). Hence `EdgeSplit` passes
  to the dilation (`edgeSplit_dilate`), and the substitution `u = Rr`, `v = Rρ` shows
  `Z_ℓ(S.dilate R) = Z_ℓ(S)` (`Zedge_dilate`; the Jacobian `R⁻²` cancels the factor `R²` of
  `|ω̄_R'(r)||ω̄_R'(ρ)|`, and `(r/ρ) = (Rr)/(Rρ)`). The change of variables is
  `Measure.integral_comp_mul_left` applied to indicator functions (the sets `{ω̄' > 0}`,
  `{ω̄' < 0}` are measurable since `deriv` is measurable).
* `ringPhiSetting χ = (ringRefSetting χ).dilate R_c` (`ringPhiSetting_eq_dilate`), which gives
  `ringPhiSetting_edgeSplit` (from `ringRefSetting_edgeSplit`) and `Zedge_ringPhi`.
* `sectors_ge9`: by `edge_bound`, `Zedge_antitone` (`|ℓ| ≥ 9`) and `closedForm_Zedge` with
  `ℓ = 9` (`9d < 1` by `ringData_order`):
  `Re λ ≤ ½Z_{|ℓ|}^{1/2} ≤ ½Z_9^{1/2} = ½(Z^a_9Z^b_9)^{1/2} ≤ ½(e^{9a₀}Θ_9 + ε_*) < 9/200`
  by (N3). The step `(Z^a_9Z^b_9)^{1/2} ≤ e^{9a₀}Θ_9 + ε_*` uses `Z^a_9, Z^b_9 ≥ 0`.
-/

noncomputable section

open Set MeasureTheory

namespace NonUniqueEuler

open RingData Sect

/-! ### Dilations: the derivative of the profile, `EdgeSplit` and `Z_ℓ` -/

/-- `ω̄_R(r) = ω̄(Rr)` as a function of `r`. -/
private lemma omR_dilate (S : SectorSetting) (R r : ℝ) :
    (S.dilate R).omR r = S.omR (R * r) := by
  simp only [SectorSetting.omR, SectorSetting.dilate, Complex.ofReal_mul]

/-- `ω̄_R'(r) = R ω̄'(Rr)` (no regularity needed: `deriv_comp_mul_left`). -/
private lemma dom_dilate (S : SectorSetting) (R r : ℝ) :
    (S.dilate R).dom r = R * S.dom (R * r) := by
  have h : (S.dilate R).omR = fun x => S.omR (R * x) := funext (omR_dilate S R)
  simp only [SectorSetting.dom, h]
  rw [deriv_comp_mul_left R S.omR r, smul_eq_mul]

/-- `EdgeSplit` passes to the dilation by `R > 0`. -/
private lemma edgeSplit_dilate {S : SectorSetting} (h : S.EdgeSplit) {R : ℝ} (hR : 0 < R) :
    (S.dilate R).EdgeSplit := by
  intro r ρ hr hρ h1 h2
  rw [dom_dilate] at h1 h2
  have h1' : 0 < S.dom (R * r) := pos_of_mul_pos_right h1 hR.le
  have h2' : S.dom (R * ρ) < 0 := neg_of_mul_neg_right h2 hR.le
  have := h (R * r) (R * ρ) (mul_pos hR hr) (mul_pos hR hρ) h1' h2'
  exact lt_of_mul_lt_mul_left this hR.le

/-- Substitution `u = Rr` in a set integral over a preimage. -/
private lemma setIntegral_comp_mul_left_preimage {A : Set ℝ} (hA : MeasurableSet A)
    (f : ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    ∫ r in (fun r => R * r) ⁻¹' A, f (R * r) = R⁻¹ * ∫ u in A, f u := by
  have hpre : MeasurableSet ((fun r => R * r) ⁻¹' A) := (measurable_const_mul R) hA
  rw [← integral_indicator hpre, ← integral_indicator hA]
  have hind : ((fun r => R * r) ⁻¹' A).indicator (fun r => f (R * r)) =
      fun r => A.indicator f (R * r) := by
    funext r
    rfl
  rw [hind, Measure.integral_comp_mul_left (A.indicator f) R, abs_of_pos (inv_pos.mpr hR),
    smul_eq_mul]

/-- `Z_ℓ` is invariant under dilation by `R > 0` (substitution `u = Rr`, `v = Rρ`). -/
private lemma Zedge_dilate (S : SectorSetting) {R : ℝ} (hR : 0 < R) (ℓ : ℕ) :
    (S.dilate R).Zedge ℓ = S.Zedge ℓ := by
  have hR0 : R ≠ 0 := hR.ne'
  have hmd : Measurable S.dom := measurable_deriv _
  have hA : MeasurableSet {u : ℝ | 0 < u ∧ 0 < S.dom u} :=
    (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_const hmd)
  have hB : MeasurableSet {v : ℝ | 0 < v ∧ S.dom v < 0} :=
    (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt hmd measurable_const)
  have hA' : {r : ℝ | 0 < r ∧ 0 < (S.dilate R).dom r} =
      (fun r => R * r) ⁻¹' {u : ℝ | 0 < u ∧ 0 < S.dom u} := by
    ext r
    simp only [dom_dilate, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos hR h1, pos_of_mul_pos_right h2 hR.le⟩
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 hR.le, mul_pos hR h2⟩
  have hB' : {ρ : ℝ | 0 < ρ ∧ (S.dilate R).dom ρ < 0} =
      (fun r => R * r) ⁻¹' {v : ℝ | 0 < v ∧ S.dom v < 0} := by
    ext ρ
    simp only [dom_dilate, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos hR h1, neg_of_mul_neg_right h2 hR.le⟩
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 hR.le, mul_neg_of_pos_of_neg hR h2⟩
  have hint : ∀ r ρ : ℝ,
      (r / ρ) ^ (2 * ℓ) * |(S.dilate R).dom r| * |(S.dilate R).dom ρ| =
        R ^ 2 * (((R * r) / (R * ρ)) ^ (2 * ℓ) * |S.dom (R * r)| * |S.dom (R * ρ)|) := by
    intro r ρ
    rw [dom_dilate, dom_dilate, mul_div_mul_left r ρ hR0, abs_mul, abs_mul, abs_of_pos hR]
    ring
  have inner : ∀ r : ℝ,
      ∫ ρ in (fun r => R * r) ⁻¹' {v : ℝ | 0 < v ∧ S.dom v < 0},
          R ^ 2 * (((R * r) / (R * ρ)) ^ (2 * ℓ) * |S.dom (R * r)| * |S.dom (R * ρ)|) =
        R⁻¹ * ∫ v in {v : ℝ | 0 < v ∧ S.dom v < 0},
          R ^ 2 * (((R * r) / v) ^ (2 * ℓ) * |S.dom (R * r)| * |S.dom v|) := fun r =>
    setIntegral_comp_mul_left_preimage hB
      (fun v => R ^ 2 * (((R * r) / v) ^ (2 * ℓ) * |S.dom (R * r)| * |S.dom v|)) hR
  calc (S.dilate R).Zedge ℓ
      = ∫ r in (fun r => R * r) ⁻¹' {u : ℝ | 0 < u ∧ 0 < S.dom u},
          ∫ ρ in (fun r => R * r) ⁻¹' {v : ℝ | 0 < v ∧ S.dom v < 0},
            R ^ 2 * (((R * r) / (R * ρ)) ^ (2 * ℓ) * |S.dom (R * r)| * |S.dom (R * ρ)|) := by
        unfold SectorSetting.Zedge
        rw [hA', hB']
        simp_rw [hint]
    _ = ∫ r in (fun r => R * r) ⁻¹' {u : ℝ | 0 < u ∧ 0 < S.dom u},
          R⁻¹ * ∫ v in {v : ℝ | 0 < v ∧ S.dom v < 0},
            R ^ 2 * (((R * r) / v) ^ (2 * ℓ) * |S.dom (R * r)| * |S.dom v|) := by
        congr 1
        funext r
        exact inner r
    _ = R⁻¹ * ∫ u in {u : ℝ | 0 < u ∧ 0 < S.dom u},
          R⁻¹ * ∫ v in {v : ℝ | 0 < v ∧ S.dom v < 0},
            R ^ 2 * ((u / v) ^ (2 * ℓ) * |S.dom u| * |S.dom v|) :=
        setIntegral_comp_mul_left_preimage hA
          (fun u => R⁻¹ * ∫ v in {v : ℝ | 0 < v ∧ S.dom v < 0},
            R ^ 2 * ((u / v) ^ (2 * ℓ) * |S.dom u| * |S.dom v|)) hR
    _ = S.Zedge ℓ := by
        simp only [integral_const_mul]
        unfold SectorSetting.Zedge
        field_simp

private lemma Rc_pos : 0 < Rc := Real.exp_pos ξR

/-! ### The three declarations of `I/Sec4/Sectors9.lean` -/

/-- Proof of `cor:sectors-9` (`04_ring.tex:1180-1181`): the ring `Φ` satisfies the hypothesis of
`lem:edge`. -/
theorem ringPhiSetting_edgeSplit {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    (ringPhiSetting χ).EdgeSplit := by
  rw [ringPhiSetting_eq_dilate]
  exact edgeSplit_dilate (ringRefSetting_edgeSplit hχ) Rc_pos

/-- Proof of `cor:sectors-9` (`04_ring.tex:1181-1182`): `Z_ℓ` is the same for `Φ` and for
`ω̄_c`. -/
theorem Zedge_ringPhi {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) :
    (ringPhiSetting χ).Zedge ℓ = (ringRefSetting χ).Zedge ℓ := by
  rw [ringPhiSetting_eq_dilate]
  exact Zedge_dilate _ Rc_pos ℓ

/-- `Z^a_ℓ ≥ 0`: the integrand `e^{2ℓ(ξ-ξ_c)}ϖ'(ξ)` is positive on `{ϖ' > 0}`. -/
private lemma zedgeA_nonneg (χ : ℝ → ℝ) (ℓ : ℕ) : 0 ≤ ZedgeA χ ℓ := by
  unfold ZedgeA
  have hmeas : MeasurableSet {ξ : ℝ | 0 < deriv (prof χ) ξ} :=
    measurableSet_lt measurable_const (measurable_deriv (prof χ))
  refine setIntegral_nonneg hmeas fun ξ hξ => ?_
  exact mul_nonneg (Real.exp_pos _).le (le_of_lt hξ)

/-- `Z^b_ℓ ≥ 0`: the integrand `e^{-2ℓ(ξ-ξ_c)}|ϖ'(ξ)|` is nonnegative. -/
private lemma zedgeB_nonneg (χ : ℝ → ℝ) (ℓ : ℕ) : 0 ≤ ZedgeB χ ℓ := by
  unfold ZedgeB
  exact integral_nonneg fun ξ => mul_nonneg (Real.exp_pos _).le (abs_nonneg _)

/-- `½ Z_9^{1/2} < 9/200` for the ring in reference units, under (N3). -/
private lemma half_sqrt_Zedge9_lt {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (h3 : N3) :
    1 / 2 * Real.sqrt ((ringRefSetting χ).Zedge 9) < 9 / 200 := by
  have hd : ((9 : ℕ) : ℝ) * d < 1 :=
    (ringData_order).2.2.2.2.2.2.1 9 (by norm_num) (by norm_num)
  obtain ⟨hZ, hA, hB⟩ := closedForm_Zedge hχ (ℓ := 9) (by norm_num) hd
  set M : ℝ := Real.exp ((9 : ℕ) * a₀) * Θ 9 + εstar with hM
  have hN3 : M < 9 / 100 := h3 9 (by simp)
  have hA0 : 0 ≤ ZedgeA χ 9 := zedgeA_nonneg χ 9
  have hB0 : 0 ≤ ZedgeB χ 9 := zedgeB_nonneg χ 9
  have hM0 : 0 ≤ M := le_trans hA0 hA
  have hprod : ZedgeA χ 9 * ZedgeB χ 9 ≤ M * M := mul_le_mul hA hB hB0 hM0
  have hsqrt : Real.sqrt ((ringRefSetting χ).Zedge 9) ≤ M := by
    rw [hZ]
    calc Real.sqrt (ZedgeA χ 9 * ZedgeB χ 9) ≤ Real.sqrt (M * M) := Real.sqrt_le_sqrt hprod
      _ = M := Real.sqrt_mul_self hM0
  linarith

/-- `cor:sectors-9`: assume (N3). For the ring in reference or ring units, every `G ∈ ℝ`, every
`ℓ ∈ ℤ` with `|ℓ| ≥ 9`, every eigenvalue `λ` of `L_ℓ(G)` on `Y^0_ℓ` with `Re λ > 0` satisfies
`Re λ < 9/200`. -/
theorem sectors_ge9 {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (h3 : N3) (S : SectorSetting)
    (hS : S = ringRefSetting χ ∨ S = ringPhiSetting χ) (G : ℝ) (ℓ : ℤ) (hℓ : 9 ≤ |ℓ|)
    (g : Ysec 0 S.Nstar ℓ) (z : ℂ) (hg : g ≠ 0) (hgz : S.Lsec 0 ℓ G g = z • g)
    (hz : 0 < z.re) : z.re < 9 / 200 := by
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    norm_num at hℓ
  have hnat : 9 ≤ ℓ.natAbs := by
    have h1 : ((9 : ℕ) : ℤ) ≤ (ℓ.natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      exact_mod_cast hℓ
    exact_mod_cast h1
  -- the setting is valid, satisfies `EdgeSplit`, and has the `Z_ℓ` of `ω̄_c`
  have hdata : S.Valid ∧ S.EdgeSplit ∧ S.Zedge 9 = (ringRefSetting χ).Zedge 9 := by
    rcases hS with rfl | rfl
    · exact ⟨ringRefSetting_valid hχ, ringRefSetting_edgeSplit hχ, rfl⟩
    · exact ⟨ringPhiSetting_valid hχ, ringPhiSetting_edgeSplit hχ, Zedge_ringPhi hχ 9⟩
  obtain ⟨hV, hsplit, hZ⟩ := hdata
  have hedge := SectorSetting.edge_bound S hV hsplit hℓ0 G z hz g hg hgz
  have hmono : S.Zedge ℓ.natAbs ≤ S.Zedge 9 :=
    SectorSetting.Zedge_antitone S hV hsplit (by norm_num) hnat
  have hsq : Real.sqrt (S.Zedge ℓ.natAbs) ≤ Real.sqrt (S.Zedge 9) := Real.sqrt_le_sqrt hmono
  rw [hZ] at hsq
  have h9 := half_sqrt_Zedge9_lt hχ h3
  linarith

end NonUniqueEuler
