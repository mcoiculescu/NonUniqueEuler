import NonUniqueEuler.Defs.Sec4.Setting
import NonUniqueEuler.I.Infra.SobolevOneD.Energy
import NonUniqueEuler.I.Infra.SobolevOneD.LogVariable
import NonUniqueEuler.I.Infra.SobolevOneD.Multiplier
import NonUniqueEuler.H.Sec4.Elliptic.GreenLog
import NonUniqueEuler.H.Sec4.Elliptic.Membership

/-!
# Proof: `lem:elliptic` (elliptic estimate for `𝒢_ℓ`, uniform in `ℓ`)

Proof of `NonUniqueEuler/I/Sec4/Elliptic.lean` (`04_ring.tex:867-898`), with restructuring R4
(energy identity in place of the Fourier transform).

With `x = log r`, `g̃ = g ∘ exp`, `f = e^{2x} g̃`, `ψ̃ = yukawa ℓ f`:
* `𝒢_ℓ g = ψ̃ ∘ log` on `(0, ∞)` (`EllipticH.green_eq_yukawa_log`);
* `|g̃|²_{k,ℓ} ≤ C₁ ‖g‖²_{k,ℓ}` (`exists_logNormSq_comp_exp_le`), `|f|²_{k,ℓ} ≤ 4^{k+1}M²|g̃|²_{k,ℓ}`
  with `M = 2^k ρ₊²` (`logNormSq_mul_le`, `∂^i e^{2x} = 2^i e^{2x}`), `|ψ̃|²_{k+2,ℓ} ≤ 6|f|²_{k,ℓ}`
  (`yukawa_higher`), `‖ψ̃ ∘ log‖²_{k+2,ℓ;[α,β]} ≤ C₃ |ψ̃|²_{k+2,ℓ}`
  (`exists_secNormSq_comp_log_le`, `logNormSqOn_le_logNormSq`);
* membership `𝒢_ℓ g ∈ H^{k+2}((0,∞))`: `𝒢_ℓ g = A rⁿ` on `(0, ρ₋)`, `B r^{-n}` on `(ρ₊, ∞)`
  (`EllipticH.green_eq_of_lt`, `green_eq_of_gt`), and `ψ̃ ∘ log ∈ H^{k+2}` on `(ρ₋/2, 2ρ₊)`
  (`memH1On_comp_log`), glued by uniqueness of weak derivatives
  (`EllipticH.memH1On_of_pieces`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace SectorSetting

/-- `lem:elliptic`: for `k ≥ 0`, radii `0 < ρ₋ < ρ₊` and a compact interval `[α, β] ⊂ (0,∞)`
there is `C` such that for every `ℓ ≠ 0` and every `g ∈ H^k((0,∞))` supported in `[ρ₋, ρ₊]`,
`𝒢_ℓ g ∈ H^{k+2}((0,∞))` and `‖𝒢_ℓ g‖²_{k+2,ℓ;[α,β]} ≤ C ‖g‖²_{k,ℓ}`. -/
theorem elliptic (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℤ, ℓ ≠ 0 → ∀ g : ℝ → ℂ, Sob.MemH1On k (Ioi 0) g →
      (∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ Icc ρm ρp → g r = 0) →
        Sob.MemH1On (k + 2) (Ioi 0) (green ℓ g) ∧
          Sob.secNormSq (k + 2) ℓ (Icc α β) (green ℓ g) ≤
            C * Sob.secNormSq k ℓ (Icc ρm ρp) g := by
  obtain ⟨C₁, hC₁, h₁⟩ := Sob.exists_logNormSq_comp_exp_le k hρm hρ.le
  obtain ⟨C₃, hC₃, h₃⟩ := Sob.exists_secNormSq_comp_log_le (k + 2) hα hαβ
  have hρp : 0 < ρp := hρm.trans hρ
  set M : ℝ := 2 ^ k * ρp ^ 2 with hM
  refine ⟨C₃ * (6 * (4 ^ (k + 1) * M ^ 2 * C₁)), by positivity, fun ℓ hℓ g hg hsupp => ?_⟩
  -- the log variable: `g̃ = g ∘ exp`
  obtain ⟨hgt, hgtb⟩ := h₁ ℓ g hg hsupp
  have hgtI : ∀ᵐ x, x ∉ Icc (Real.log ρm) (Real.log ρp) → g (Real.exp x) = 0 := by
    filter_upwards [Sob.EllipticH.ae_comp_exp hsupp] with x hx hxI
    refine hx fun hI => hxI ⟨?_, ?_⟩
    · have h := Real.log_le_log hρm hI.1
      rwa [Real.log_exp] at h
    · have h := Real.log_le_log (Real.exp_pos x) hI.2
      rwa [Real.log_exp] at h
  -- `f = e^{2x} g̃`
  obtain ⟨hf, hfb⟩ := Sob.logNormSq_mul_le (a := Sob.EllipticH.expTwo) (a₀ := Real.log ρm)
    (b₀ := Real.log ρp) Sob.EllipticH.contDiff_expTwo (M := M)
    (fun i hi x hx => Sob.EllipticH.norm_iteratedDeriv_expTwo_le hi hρp hx.2) hgt hgtI ℓ
  have hfI : ∀ᵐ x, x ∉ Icc (Real.log ρm) (Real.log ρp) →
      Sob.EllipticH.expTwo x * g (Real.exp x) = 0 := by
    filter_upwards [hgtI] with x hx hxI
    rw [hx hxI, mul_zero]
  -- `ψ̃ = yukawa ℓ f`
  obtain ⟨hu, -, hub⟩ := Sob.yukawa_higher hℓ hf hfI
  have hgreen : ∀ r ∈ Ioi (0 : ℝ), green ℓ g r =
      Sob.yukawa ℓ (fun x => Sob.EllipticH.expTwo x * g (Real.exp x)) (Real.log r) :=
    fun r hr => Sob.EllipticH.green_eq_yukawa_log ℓ g hr
  obtain ⟨hwd, hb⟩ := h₃ ℓ _ hu
  have hn : 1 ≤ ℓ.natAbs := Int.natAbs_pos.2 hℓ
  refine ⟨Sob.EllipticH.memH1On_of_pieces hρm hρ hn _ _
    (fun r hr => Sob.EllipticH.green_eq_of_lt hsupp hr.2)
    (fun r hr => Sob.EllipticH.green_eq_of_gt hsupp hr) hgreen hu hwd, ?_⟩
  rw [Sob.EllipticH.secNormSq_congr hgreen]
  have hlog := Sob.logNormSqOn_le_logNormSq (k + 2) ℓ (Icc (Real.log α) (Real.log β)) hu
  have h6 : (0 : ℝ) ≤ 6 := by norm_num
  have h4 : (0 : ℝ) ≤ 4 ^ (k + 1) * M ^ 2 := by positivity
  calc _ ≤ C₃ * Sob.logNormSqOn (k + 2) ℓ (Icc (Real.log α) (Real.log β))
          (Sob.yukawa ℓ (fun x => Sob.EllipticH.expTwo x * g (Real.exp x))) := hb
    _ ≤ C₃ * Sob.logNormSq (k + 2) ℓ
          (Sob.yukawa ℓ (fun x => Sob.EllipticH.expTwo x * g (Real.exp x))) :=
        mul_le_mul_of_nonneg_left hlog hC₃.le
    _ ≤ C₃ * (6 * Sob.logNormSq k ℓ (fun x => Sob.EllipticH.expTwo x * g (Real.exp x))) :=
        mul_le_mul_of_nonneg_left hub hC₃.le
    _ ≤ C₃ * (6 * (4 ^ (k + 1) * M ^ 2 * Sob.logNormSq k ℓ (fun x => g (Real.exp x)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfb h6) hC₃.le
    _ ≤ C₃ * (6 * (4 ^ (k + 1) * M ^ 2 * (C₁ * Sob.secNormSq k ℓ (Icc ρm ρp) g))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hgtb h4) h6) hC₃.le
    _ = C₃ * (6 * (4 ^ (k + 1) * M ^ 2 * C₁)) * Sob.secNormSq k ℓ (Icc ρm ρp) g := by ring

end SectorSetting

end NonUniqueEuler
