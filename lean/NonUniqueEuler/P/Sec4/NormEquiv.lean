import NonUniqueEuler.Defs.Sec4.Setting
import NonUniqueEuler.I.Infra.AngularFourier.NormEquiv
import NonUniqueEuler.I.Infra.Sobolev.Space

/-!
# Proof of `lem:norm-equiv` in the sector setting (`I/Sec4/NormEquiv.lean`)

Manuscript `04_ring.tex:843-864`. The statement is the generic annulus norm equivalence
`Ang.exists_norm_equiv` (`I/Infra/AngularFourier/NormEquiv.lean`) applied to the function
`w.fn` of `w ∈ Y^k(N_*)`:
* `w.fn ∈ H^k` and `‖w‖ = ‖w.fn‖_{H^k}` (`Sob.Hk.memH_fn`, `I/Infra/Sobolev/Space.lean`; the
  norm of `w : Y k K` is the norm of the underlying tuple, as is that of `w.toHk : Hk k`);
* `w.fn = 0` a.e. off `N_*` (the kernel condition of `suppCLM` in `Sect.YSub`);
* `S.secNormSq k ℓ = Sob.secNormSq k ℓ (Icc ρ₋ ρ₊)` by definition.

The constants come from `Ang.exists_norm_equiv k hρm hρ` before the setting `S` is chosen, so
they depend only on `k, ρ₋, ρ₊`.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace SectorSetting

/-- `F_0|_{Kᶜ} = 0` in `L²(Kᶜ)` iff `F_0 = 0` a.e. off `K` (local copy of the helper of
`H/Infra/SectorSpace/Decomposition/Basic.lean`, which this file may not import). -/
private theorem suppCLM_eq_zero_iff' {s : ℕ} {K : Set ℂ} (F : Sob.SobTuple s) :
    Sect.suppCLM s K F = 0 ↔ ∀ᵐ x ∂volume, x ∉ K → Sob.tupleFn F x = 0 := by
  have hc := LpToLpRestrictCLM_coeFn ℂ (μ := (volume : Measure ℂ)) (p := 2) Kᶜ (Sect.proj0 s F)
  have hmeas : MeasurableSet {x | Sob.tupleFn F x = 0} :=
    (Lp.stronglyMeasurable _).measurable (measurableSet_singleton 0)
  rw [Sect.suppCLM, ContinuousLinearMap.comp_apply, Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h
    have h2 : Sob.tupleFn F =ᵐ[volume.restrict Kᶜ] 0 := hc.symm.trans h
    exact (ae_restrict_iff hmeas).1 h2
  · intro h
    have h2 : ∀ᵐ x ∂volume.restrict Kᶜ, Sob.tupleFn F x = 0 := (ae_restrict_iff hmeas).2 h
    filter_upwards [hc, h2] with x hx h2x
    rw [hx]
    exact h2x

/-- The function of `w ∈ Y^s(K)` vanishes a.e. outside `K`. -/
private theorem Y_fn_supp {s : ℕ} {K : Set ℂ} (w : Sect.Y s K) :
    ∀ᵐ x ∂volume, x ∉ K → w.fn x = 0 := by
  have h := (Submodule.mem_inf.1 w.2).2
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, suppCLM_eq_zero_iff'] at h
  exact h

/-- `lem:norm-equiv`: for `k ≥ 0` and radii `0 < ρ₋ < ρ₊` there are `c, C > 0` such that in every
sector setting with these radii, every `w ∈ Y^k` satisfies
`c ∑_ℓ ‖g_ℓ‖²_{k,ℓ} ≤ ‖w‖²_{H^k} ≤ C ∑_ℓ ‖g_ℓ‖²_{k,ℓ}`, `g_ℓ` the sector profiles of `w`. -/
theorem norm_equiv (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ S : SectorSetting, S.Valid → S.ρm = ρm → S.ρp = ρp → ∀ w : Sect.Y k S.Nstar,
        Summable (fun ℓ : ℤ => S.secNormSq k ℓ (Polar.angularSector w.fn ℓ)) ∧
          c * ∑' ℓ : ℤ, S.secNormSq k ℓ (Polar.angularSector w.fn ℓ) ≤ ‖w‖ ^ 2 ∧
          ‖w‖ ^ 2 ≤ C * ∑' ℓ : ℤ, S.secNormSq k ℓ (Polar.angularSector w.fn ℓ) := by
  obtain ⟨c, C, hc, hC, hmain⟩ := Ang.exists_norm_equiv k hρm hρ
  refine ⟨c, C, hc, hC, ?_⟩
  intro S _hS hSm hSp w
  subst hSm hSp
  have hH := Sob.Hk.memH_fn w.toHk
  have hmem : Sob.MemH k w.fn := hH.1
  have hnorm : Sob.normH k w.fn = ‖w‖ := hH.2
  have hsupp : ∀ᵐ x ∂volume, ¬ (S.ρm ≤ ‖x‖ ∧ ‖x‖ ≤ S.ρp) → w.fn x = 0 := by
    filter_upwards [Y_fn_supp w] with x hx hnx
    exact hx hnx
  obtain ⟨h1, h2, h3⟩ := hmain w.fn hmem hsupp
  rw [← hnorm]
  exact ⟨h1, h2, h3⟩

end SectorSetting

end NonUniqueEuler
