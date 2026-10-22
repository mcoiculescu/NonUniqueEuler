import NonUniqueEuler.Defs.Sec4.RingSetting
import NonUniqueEuler.I.Ring.ChiStd
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Proof: `lem:ring-facts` (the ring is admissible and gives two sector settings)

Proof of `I/Sec4/RingFacts.lean`, following `04_ring.tex:70-99`.

* `exists_isAdmissibleCutoff`: the explicit cutoff `chiStd` (`I/Ring/ChiStd.lean`).
* `ringData_order`: `norm_num` on the dyadic data.
* `ringRef_facts`: `ϖ` is smooth with `0 ≤ ϖ < 1` and vanishes off `tsupport χ ⊆ [ξL, ξR]`;
  hence `ω̄_c = ϖ ∘ log ∘ |·|` vanishes off the annulus `{e^{ξL} ≤ |x| ≤ e^{ξR}}`, is smooth
  on `x ≠ 0` and is `0` on the disk `|x| < e^{ξL}`.
* `ringFacts_of_admissible`: `Φ = ω̄_c(R_c ·)`, with `e^{ξL}/R_c = a`, and `Φ ≢ 0` at
  `y = e^{ξa}/R_c` since `ϖ(ξa) = H((ξa - a₀)/d) H(-ξa/d) > 0`.
* `ringRefSetting_valid`, `ringPhiSetting_valid`: from the general criterion
  `RingFactsProof.valid_of_tsupport_subset` (a profile whose topological support lies in
  `{r₁ ≤ |x| ≤ r₂}` has `ω̄' = 0` off `[r₁, r₂]`).

The helper lemmas live in the namespace `NonUniqueEuler.RingFactsProof` to avoid name clashes
in the full library.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler

open RingData

namespace RingFactsProof

/-! ### The annulus `{r₁ ≤ |x| ≤ r₂}` -/

/-- The closed annulus `{r₁ ≤ |x| ≤ r₂}` as it appears in the statements. -/
theorem isClosed_annulusSet (r₁ r₂ : ℝ) :
    IsClosed {x : ℂ | r₁ ≤ ‖x‖ ∧ ‖x‖ ≤ r₂} :=
  (isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)

theorem isCompact_annulusSet (r₁ r₂ : ℝ) :
    IsCompact {x : ℂ | r₁ ≤ ‖x‖ ∧ ‖x‖ ≤ r₂} :=
  (isCompact_closedBall (0 : ℂ) r₂).of_isClosed_subset (isClosed_annulusSet r₁ r₂)
    (fun x hx => by simpa [Metric.mem_closedBall, dist_zero_right] using hx.2)

/-- If a function vanishes off the annulus, its topological support lies in it. -/
theorem tsupport_subset_annulusSet {f : ℂ → ℝ} {r₁ r₂ : ℝ}
    (h : ∀ x : ℂ, ¬(r₁ ≤ ‖x‖ ∧ ‖x‖ ≤ r₂) → f x = 0) :
    tsupport f ⊆ {x : ℂ | r₁ ≤ ‖x‖ ∧ ‖x‖ ≤ r₂} := by
  refine closure_minimal (fun x hx => ?_) (isClosed_annulusSet r₁ r₂)
  by_contra hn
  exact hx (h x hn)

/-- A function vanishing off the annulus has compact support. -/
theorem hasCompactSupport_of_annulusSet {f : ℂ → ℝ} {r₁ r₂ : ℝ}
    (h : ∀ x : ℂ, ¬(r₁ ≤ ‖x‖ ∧ ‖x‖ ≤ r₂) → f x = 0) : HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_annulusSet r₁ r₂) h

/-- `‖rot θ x‖ = ‖x‖`. -/
theorem norm_rot (θ : ℝ) (x : ℂ) : ‖rot θ x‖ = ‖x‖ := by
  simp [rot, Complex.norm_exp_ofReal_mul_I]

theorem rot_eq_zero_iff (θ : ℝ) (x : ℂ) : rot θ x = 0 ↔ x = 0 := by
  simp [rot, Complex.exp_ne_zero]

/-! ### The general validity criterion -/

/-- A sector setting whose profile is smooth, compactly supported, radial and has topological
support in `{r₁ ≤ |x| ≤ r₂}` is valid as soon as the radii are ordered. -/
theorem valid_of_tsupport_subset (S : SectorSetting) (h1 : ContDiff ℝ ∞ S.om)
    (h2 : HasCompactSupport S.om) (h3 : IsRadialPointwise S.om)
    (h4 : tsupport S.om ⊆ {x : ℂ | S.r₁ ≤ ‖x‖ ∧ ‖x‖ ≤ S.r₂})
    (h5 : 0 < S.ρm) (h6 : S.ρm < S.r₁) (h7 : S.r₁ ≤ S.r₂) (h8 : S.r₂ < S.ρp) :
    S.Valid where
  contDiff := h1
  hasCompactSupport := h2
  radial := h3
  r₁_pos := h5.trans h6
  r₁_le_r₂ := h7
  dom_eq_zero := by
    intro r hr hnot
    have hnorm : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
    have hns : (r : ℂ) ∉ tsupport S.om := by
      intro hm
      have hm' : S.r₁ ≤ ‖(r : ℂ)‖ ∧ ‖(r : ℂ)‖ ≤ S.r₂ := h4 hm
      rw [hnorm] at hm'
      exact hnot hm'
    have hev : S.om =ᶠ[𝓝 (r : ℂ)] 0 := (notMem_tsupport_iff_eventuallyEq).1 hns
    have hev' : S.omR =ᶠ[𝓝 r] fun _ => (0 : ℝ) :=
      (Complex.continuous_ofReal.tendsto r).eventually hev
    simp only [SectorSetting.dom]
    rw [hev'.deriv_eq, deriv_const]
  ρm_pos := h5
  ρm_lt_r₁ := h6
  r₂_lt_ρp := h8

/-! ### The function `H` and the profile `ϖ` -/

theorem contDiff_H : ContDiff ℝ ∞ H := by
  have hne : ∀ x : ℝ, 1 + Real.exp (-2 * x) ≠ 0 := fun x => by positivity
  have hc : ContDiff ℝ ∞ (fun x : ℝ => 1 + Real.exp (-2 * x)) :=
    contDiff_const.add (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  exact hc.inv hne

theorem H_pos (x : ℝ) : 0 < H x := by
  unfold H
  positivity

theorem H_lt_one (x : ℝ) : H x < 1 := by
  unfold H
  apply inv_lt_one_of_one_lt₀
  have := Real.exp_pos (-2 * x)
  linarith

theorem contDiff_prof {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) : ContDiff ℝ ∞ (prof χ) := by
  have h1 : ContDiff ℝ ∞ (fun ξ : ℝ => H ((ξ - a₀) / d)) :=
    contDiff_H.comp ((contDiff_id.sub contDiff_const).div_const d)
  have h2 : ContDiff ℝ ∞ (fun ξ : ℝ => H (-ξ / d)) :=
    contDiff_H.comp (contDiff_id.neg.div_const d)
  exact (hχ.contDiff.mul h1).mul h2

theorem prof_nonneg {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) : 0 ≤ prof χ ξ := by
  have hc := (hχ.mem_Icc ξ).1
  have := H_pos ((ξ - a₀) / d)
  have := H_pos (-ξ / d)
  unfold prof
  positivity

theorem prof_lt_one {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) : prof χ ξ < 1 := by
  have hc0 := (hχ.mem_Icc ξ).1
  have hc1 := (hχ.mem_Icc ξ).2
  have p1 := H_pos ((ξ - a₀) / d)
  have p2 := H_pos (-ξ / d)
  have l1 := H_lt_one ((ξ - a₀) / d)
  have l2 := H_lt_one (-ξ / d)
  have hHH : H ((ξ - a₀) / d) * H (-ξ / d) < 1 := by
    calc H ((ξ - a₀) / d) * H (-ξ / d) < 1 * 1 :=
          mul_lt_mul'' l1 l2 p1.le p2.le
      _ = 1 := one_mul 1
  unfold prof
  rw [mul_assoc]
  calc χ ξ * (H ((ξ - a₀) / d) * H (-ξ / d)) ≤ 1 * (H ((ξ - a₀) / d) * H (-ξ / d)) :=
        mul_le_mul_of_nonneg_right hc1 (mul_pos p1 p2).le
    _ < 1 := by rw [one_mul]; exact hHH

theorem prof_eq_zero_of_notMem {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ξ : ℝ}
    (hξ : ξ ∉ Icc ξL ξR) : prof χ ξ = 0 := by
  have : χ ξ = 0 := image_eq_zero_of_notMem_tsupport (fun h => hξ (hχ.tsupport_subset h))
  simp [prof, this]

/-! ### The ring in reference units `ω̄_c` -/

theorem ringRef_of_ne {χ : ℝ → ℝ} {x : ℂ} (hx : x ≠ 0) :
    ringRef χ x = prof χ (Real.log ‖x‖) := by
  simp [ringRef, hx]

theorem ringRef_eq_zero_of_not {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {x : ℂ}
    (hx : ¬(Real.exp ξL ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp ξR)) : ringRef χ x = 0 := by
  by_cases h0 : x = 0
  · simp [ringRef, h0]
  rw [ringRef_of_ne h0]
  apply prof_eq_zero_of_notMem hχ
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 h0
  rintro ⟨hL, hR⟩
  exact hx ⟨(Real.le_log_iff_exp_le hpos).1 hL, (Real.log_le_iff_le_exp hpos).1 hR⟩

theorem ringRef_nonneg {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (x : ℂ) : 0 ≤ ringRef χ x := by
  unfold ringRef
  split_ifs
  · exact le_rfl
  · exact prof_nonneg hχ _

theorem ringRef_lt_one {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (x : ℂ) : ringRef χ x < 1 := by
  unfold ringRef
  split_ifs
  · exact one_pos
  · exact prof_lt_one hχ _

theorem contDiffAt_ringRef {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (x : ℂ) :
    ContDiffAt ℝ ∞ (ringRef χ) x := by
  by_cases hx : x = 0
  · -- `ω̄_c = 0` on the disk `|y| < e^{ξL}`
    subst hx
    have hev : ringRef χ =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      have hb : Metric.ball (0 : ℂ) (Real.exp ξL) ∈ 𝓝 (0 : ℂ) :=
        Metric.ball_mem_nhds 0 (Real.exp_pos ξL)
      filter_upwards [hb] with y hy
      apply ringRef_eq_zero_of_not hχ
      rw [Metric.mem_ball, dist_zero_right] at hy
      rintro ⟨h, -⟩
      linarith
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hev : ringRef χ =ᶠ[𝓝 x] fun y => prof χ (Real.log ‖y‖) := by
      filter_upwards [eventually_ne_nhds hx] with y hy
      exact ringRef_of_ne hy
    have hn : ContDiffAt ℝ ∞ (fun y : ℂ => ‖y‖) x := contDiffAt_norm ℝ hx
    have hl : ContDiffAt ℝ ∞ Real.log ‖x‖ :=
      Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hx)
    have hc : ContDiffAt ℝ ∞ (fun y : ℂ => prof χ (Real.log ‖y‖)) x :=
      (contDiff_prof hχ).contDiffAt.comp x (hl.comp x hn)
    exact hc.congr_of_eventuallyEq hev

theorem ringRef_rot {χ : ℝ → ℝ} (θ : ℝ) (x : ℂ) : ringRef χ (rot θ x) = ringRef χ x := by
  by_cases hx : x = 0
  · have : rot θ x = 0 := (rot_eq_zero_iff θ x).2 hx
    rw [this, hx]
  · have : rot θ x ≠ 0 := fun h => hx ((rot_eq_zero_iff θ x).1 h)
    rw [ringRef_of_ne this, ringRef_of_ne hx, norm_rot]

/-- `ω̄_c(r) = ϖ(log r)` for `r > 0`. -/
theorem ringRef_ofReal {χ : ℝ → ℝ} {r : ℝ} (hr : 0 < r) :
    ringRef χ (r : ℂ) = prof χ (Real.log r) := by
  have hne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  rw [ringRef_of_ne hne, Complex.norm_real, Real.norm_of_nonneg hr.le]

/-! ### The ring `Φ` in ring units -/

theorem Rc_pos : 0 < Rc := Real.exp_pos ξR

theorem norm_Rc_mul (y : ℂ) : ‖(Rc : ℂ) * y‖ = Rc * ‖y‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Rc_pos.le]

theorem a_eq_div : a = Real.exp ξL / Rc := by
  rw [a, Real.exp_sub, Rc]

theorem ringPhi_eq_zero_of_not {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {y : ℂ}
    (hy : ¬(a ≤ ‖y‖ ∧ ‖y‖ ≤ 1)) : ringPhi χ y = 0 := by
  apply ringRef_eq_zero_of_not hχ
  rw [norm_Rc_mul]
  rintro ⟨hL, hR⟩
  apply hy
  constructor
  · rw [a_eq_div, div_le_iff₀ Rc_pos, mul_comm]
    exact hL
  · have hR' : Rc * ‖y‖ ≤ Rc * 1 := by rw [mul_one]; exact hR
    exact le_of_mul_le_mul_left hR' Rc_pos

theorem prof_ξa_pos {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) : 0 < prof χ ξa := by
  have hab : ξa ≤ ξb := by norm_num [ξa, ξb]
  have h1 : χ ξa = 1 := hχ.eq_one ξa ⟨le_rfl, hab⟩
  have p1 := H_pos ((ξa - a₀) / d)
  have p2 := H_pos (-ξa / d)
  unfold prof
  rw [h1, one_mul]
  exact mul_pos p1 p2

end RingFactsProof

open RingFactsProof

/-- `lem:ring-facts`, first sentence: an admissible cutoff `χ` as in `def:ring` exists. -/
theorem exists_isAdmissibleCutoff : ∃ χ : ℝ → ℝ, IsAdmissibleCutoff χ :=
  ⟨chiStd, chiStd_admissible⟩

/-- `lem:ring-facts`, the order of the data: `a₀ < 0 < d`, `ξL < ξa ≤ a₀/2 ≤ ξb < ξR`,
`ℓ d < 1` for every integer `1 ≤ ℓ ≤ 49`, and `0 < a < 1`. -/
theorem ringData_order :
    a₀ < 0 ∧ 0 < d ∧ ξL < ξa ∧ ξa ≤ a₀ / 2 ∧ a₀ / 2 ≤ ξb ∧ ξb < ξR ∧
      (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ 49 → (ℓ : ℝ) * d < 1) ∧ 0 < a ∧ a < 1 := by
  have hd : 0 < d := by norm_num [d]
  have h49 : (49 : ℝ) * d < 1 := by norm_num [d]
  have hLR : ξL - ξR < 0 := by norm_num [ξL, ξR]
  refine ⟨by norm_num [a₀], hd, by norm_num [ξL, ξa], by norm_num [ξa, a₀],
    by norm_num [a₀, ξb], by norm_num [ξb, ξR], ?_, Real.exp_pos _, ?_⟩
  · intro ℓ _ hℓ
    have hℓ' : (ℓ : ℝ) ≤ 49 := by exact_mod_cast hℓ
    calc (ℓ : ℝ) * d ≤ 49 * d := mul_le_mul_of_nonneg_right hℓ' hd.le
      _ < 1 := h49
  · exact Real.exp_lt_one_iff.2 hLR

/-- `lem:ring-facts` for `ω̄_c`: `ω̄_c ∈ C_c^∞(ℝ²)`, radial, `0 ≤ ω̄_c < 1`, and
`supp ω̄_c ⊆ {e^{ξL} ≤ |x| ≤ e^{ξR}}`. -/
theorem ringRef_facts {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    ContDiff ℝ ∞ (ringRef χ) ∧ HasCompactSupport (ringRef χ) ∧ IsRadialPointwise (ringRef χ) ∧
      (∀ x : ℂ, 0 ≤ ringRef χ x ∧ ringRef χ x < 1) ∧
      tsupport (ringRef χ) ⊆ {x : ℂ | Real.exp ξL ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp ξR} :=
  ⟨contDiff_iff_contDiffAt.2 (contDiffAt_ringRef hχ),
    hasCompactSupport_of_annulusSet (fun _ hx => ringRef_eq_zero_of_not hχ hx),
    fun θ x => ringRef_rot θ x,
    fun x => ⟨ringRef_nonneg hχ x, ringRef_lt_one hχ x⟩,
    tsupport_subset_annulusSet (fun _ hx => ringRef_eq_zero_of_not hχ hx)⟩

/-- `lem:ring-facts` for the ring `Φ`: the statement-layer proposition `RingFacts χ`
(`Φ ∈ C_c^∞(ℝ²)`, radial, `0 ≤ Φ < 1`, `Φ ≢ 0`, `supp Φ ⊆ {a ≤ |y| ≤ 1}`, `0 < a < 1`). -/
theorem ringFacts_of_admissible {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) : RingFacts χ := by
  obtain ⟨hcd, -, -, -, -⟩ := ringRef_facts hχ
  have hord := ringData_order
  refine ⟨?_, hasCompactSupport_of_annulusSet (fun _ hy => ringPhi_eq_zero_of_not hχ hy),
    ?_, fun y => ⟨ringRef_nonneg hχ _, ringRef_lt_one hχ _⟩, ?_,
    tsupport_subset_annulusSet (fun _ hy => ringPhi_eq_zero_of_not hχ hy),
    hord.2.2.2.2.2.2.2.1, hord.2.2.2.2.2.2.2.2⟩
  · show ContDiff ℝ ∞ (fun y : ℂ => ringRef χ ((Rc : ℂ) * y))
    exact hcd.comp (contDiff_const.mul contDiff_id)
  · intro θ y
    show ringRef χ ((Rc : ℂ) * rot θ y) = ringRef χ ((Rc : ℂ) * y)
    have : (Rc : ℂ) * rot θ y = rot θ ((Rc : ℂ) * y) := by
      simp only [rot]
      ring
    rw [this, ringRef_rot]
  · refine ⟨((Real.exp (ξa - ξR) : ℝ) : ℂ), ?_⟩
    show ringRef χ ((Rc : ℂ) * ((Real.exp (ξa - ξR) : ℝ) : ℂ)) ≠ 0
    have hmul : (Rc : ℂ) * ((Real.exp (ξa - ξR) : ℝ) : ℂ) = ((Real.exp ξa : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Rc, ← Real.exp_add]
      congr 2
      ring
    rw [hmul, ringRef_ofReal (Real.exp_pos ξa), Real.log_exp]
    exact (prof_ξa_pos hχ).ne'

/-- The ring in reference units is a sector setting (`04_ring.tex:345-347`, `:1160-1163`). -/
theorem ringRefSetting_valid {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    (ringRefSetting χ).Valid := by
  obtain ⟨h1, h2, h3, -, h5⟩ := ringRef_facts hχ
  have hLR : ξL ≤ ξR := by norm_num [ξL, ξR]
  have eL := Real.exp_pos ξL
  have eR := Real.exp_pos ξR
  exact valid_of_tsupport_subset (ringRefSetting χ) h1 h2 h3 h5
    (by simp only [ringRefSetting]; linarith)
    (by simp only [ringRefSetting]; linarith) (Real.exp_le_exp.2 hLR)
    (by simp only [ringRefSetting]; linarith)

/-- The ring in ring units is a sector setting (`04_ring.tex:1160-1163`). -/
theorem ringPhiSetting_valid {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    (ringPhiSetting χ).Valid := by
  obtain ⟨h1, h2, h3, -, -, h5, ha0, ha1⟩ := ringFacts_of_admissible hχ
  exact valid_of_tsupport_subset (ringPhiSetting χ) h1 h2 h3 h5
    (by simp only [ringPhiSetting]; linarith) (by simp only [ringPhiSetting]; linarith)
    (by simp only [ringPhiSetting]; linarith) (by simp only [ringPhiSetting]; norm_num)

end NonUniqueEuler
