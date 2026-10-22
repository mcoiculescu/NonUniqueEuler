import NonUniqueEuler.Defs.Sec4.Ring
import NonUniqueEuler.Defs.Sec4.Setting

/-!
# Section 4.5: the two sector settings of the ring (definitions)

Manuscript `04_ring.tex:1160-1171`
(and `lem:evans-basic`, last assertion, `04_ring.tex:300-302`, `:345-352`):

* **reference units** `ringRefSetting χ`: `ω̄ = ω̄_c = ringRef χ`, `(r₁, r₂) = (e^{ξL}, e^{ξR})`,
  so `(ξ₁, ξ₂) = (ξL, ξR)`, and `N_* = {½e^{ξL} ≤ |x| ≤ 2e^{ξR}}` (`RingData.annRef`);
* **ring units** `ringPhiSetting χ`: `ω̄ = Φ = ringPhi χ`, `(r₁, r₂) = (a, 1)`, so
  `(ξ₁, ξ₂) = (ξL - ξR, 0)`, and `N_* = N = {a/2 ≤ |y| ≤ 2}` (`RingData.annN`).

They are plain data; that they are valid sector settings for an admissible cutoff
(`(ringRefSetting χ).Valid`, `(ringPhiSetting χ).Valid`) is a consequence of `lem:ring-facts`
and belongs to an interface file. `Φ = ω̄_c(R_c ·)`, so the ring units are the dilation of the
reference units by `R_c` (`ringPhiSetting_eq_dilate`, proved here), and `lem:dilation` relates
the two (`eq:evans-units`).

All lemmas here are fully proved.
-/

noncomputable section

open Set

namespace NonUniqueEuler

open RingData

/-- The sector setting of the ring in **reference units** (`04_ring.tex:345-346`, `:1161-1162`). -/
def ringRefSetting (χ : ℝ → ℝ) : SectorSetting where
  om := ringRef χ
  r₁ := Real.exp ξL
  r₂ := Real.exp ξR
  ρm := Real.exp ξL / 2
  ρp := 2 * Real.exp ξR

/-- The sector setting of the ring in **ring units** (`04_ring.tex:1162-1163`): `ω̄ = Φ`,
`(ξ₁, ξ₂) = (ξL - ξR, 0)`, `N_* = N`. -/
def ringPhiSetting (χ : ℝ → ℝ) : SectorSetting where
  om := ringPhi χ
  r₁ := a
  r₂ := 1
  ρm := a / 2
  ρp := 2

/-! ### Basic lemmas (fully proved) -/

@[simp] theorem ringRefSetting_om (χ : ℝ → ℝ) : (ringRefSetting χ).om = ringRef χ := rfl

@[simp] theorem ringPhiSetting_om (χ : ℝ → ℝ) : (ringPhiSetting χ).om = ringPhi χ := rfl

theorem ringRefSetting_Nstar (χ : ℝ → ℝ) : (ringRefSetting χ).Nstar = annRef := rfl

theorem ringPhiSetting_Nstar (χ : ℝ → ℝ) : (ringPhiSetting χ).Nstar = annN := rfl

theorem ringRefSetting_ξ₁ (χ : ℝ → ℝ) : (ringRefSetting χ).ξ₁ = ξL :=
  Real.log_exp ξL

theorem ringRefSetting_ξ₂ (χ : ℝ → ℝ) : (ringRefSetting χ).ξ₂ = ξR :=
  Real.log_exp ξR

theorem ringPhiSetting_ξ₁ (χ : ℝ → ℝ) : (ringPhiSetting χ).ξ₁ = ξL - ξR :=
  Real.log_exp (ξL - ξR)

theorem ringPhiSetting_ξ₂ (χ : ℝ → ℝ) : (ringPhiSetting χ).ξ₂ = 0 :=
  Real.log_one

/-- `Φ = ω̄_c(R_c ·)`: the ring units are the reference units dilated by `R_c`
(`04_ring.tex:1164-1165`). -/
theorem ringPhiSetting_eq_dilate (χ : ℝ → ℝ) :
    ringPhiSetting χ = (ringRefSetting χ).dilate Rc := by
  have hR : Real.exp ξR ≠ 0 := Real.exp_ne_zero ξR
  have ha : Real.exp ξL / Real.exp ξR = a := by
    rw [a, Real.exp_sub]
  simp only [ringPhiSetting, SectorSetting.dilate, ringRefSetting, Rc]
  congr 1
  · rw [ha]
  · exact (div_self hR).symm
  · rw [div_right_comm, ha]
  · rw [mul_div_assoc, div_self hR, mul_one]

end NonUniqueEuler
