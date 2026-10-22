import NonUniqueEuler.H.Sec5.Seed.Basic
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Infra.Sobolev.ReIm
import NonUniqueEuler.Defs.Sec5.RingEq

/-!
# Helpers for `lem:seed`: the functional `ℓ_*(0)` on functions

Helper of `P/Sec5/Seed.lean` (`05_single_ring.tex:1210-1219`).

* `SeedH.ellFn_bound`: `|ℓ_*(0)(f)| ≤ ‖ℓ_*(0)‖_{(X^0)^*} ‖f‖_{L²}` for `f ∈ L²` vanishing a.e.
  off `N` (`‖ℓ_*(0)‖` is the norm of `Eig.ell χ 0 0` on `Y^0(N)`);
* `SeedH.ellFn_sub`: `ℓ_*(0)` is additive on such functions;
* `SeedH.modeFn_eq`, `SeedH.modeFn_memH`, `SeedH.modeFn_zero_outside`, `SeedH.normH_modeFn`:
  `2Re(κφ_*(0)) = 2κ Re φ_*(0)` lies in every `H^k` with norm `2|κ| ‖Re φ_*(0)‖_{H^k}`, and
  vanishes a.e. off `N`;
* `SeedH.ellFn_modeFn`: `ℓ_*(0)(2Re(κφ_*(0))) = κ` (`ℓ_*(0)(φ_*(0)) = 1`,
  `ℓ_*(0)(conj φ_*(0)) = 0`, `def:eigendata`).
-/

noncomputable section

open MeasureTheory Set Real Filter ComplexConjugate

namespace NonUniqueEuler.OneRing.SeedH

open RingData Sect Sob

variable {χ : ℝ → ℝ}

theorem zero_mem_Icc_Gbar : (0 : ℝ) ∈ Icc (0 : ℝ) Gbar := by
  refine ⟨le_rfl, ?_⟩
  unfold Gbar
  positivity

theorem ell_apply (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) (w : Y 0 annN) :
    Eig.ell χ 0 0 w = Eig.ellFn χ 0 w.fn :=
  Eig.ell_spec_of_exists (Eig.exists_ell χ hχ hN zero_mem_Icc_Gbar 0) w

/-- `|ℓ_*(0)(f)| ≤ ‖ℓ_*(0)‖ ‖f‖_{L²}` for `f ∈ L²(N)`. -/
theorem ellFn_bound (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {f : ℂ → ℂ}
    (hf : MemH 0 f) (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → f x = 0) :
    ‖Eig.ellFn χ 0 f‖ ≤ ‖Eig.ell χ 0 0‖ * normH 0 f := by
  obtain ⟨w, hw⟩ := exists_Y_of_memH (K := annN) hf hK
  have h1 : Eig.ellFn χ 0 f = Eig.ell χ 0 0 w := by
    rw [ell_apply hχ hN, ellFn_congr_ae χ 0 hw]
  have h2 : ‖w‖ = normH 0 f := by
    rw [← (Y_memH_fn w).2]
    exact ((Y_memH_fn w).1.congr_ae hw).2.symm
  rw [h1, ← h2]
  exact (Eig.ell χ 0 0).le_opNorm w

/-- `ℓ_*(0)` is additive on `L²(N)`. -/
theorem ellFn_sub (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {f g : ℂ → ℂ}
    (hf : MemH 0 f) (hfK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → f x = 0)
    (hg : MemH 0 g) (hgK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → g x = 0) :
    Eig.ellFn χ 0 (fun x => f x - g x) = Eig.ellFn χ 0 f - Eig.ellFn χ 0 g := by
  obtain ⟨v, hv⟩ := exists_Y_of_memH (K := annN) hf hfK
  obtain ⟨w, hw⟩ := exists_Y_of_memH (K := annN) hg hgK
  have hvw : (v - w).fn =ᵐ[volume] fun x => f x - g x := by
    filter_upwards [Y_fn_sub v w, hv, hw] with x h1 h2 h3
    rw [h1, h2, h3]
  rw [← ellFn_congr_ae χ 0 hvw, ← ell_apply hχ hN, map_sub, ell_apply hχ hN, ell_apply hχ hN,
    ellFn_congr_ae χ 0 hv, ellFn_congr_ae χ 0 hw]

/-! ### The mode `2Re(κ φ_*(0))` -/

theorem modeFn_eq (κ : ℝ) (x : ℂ) :
    modeFn χ 0 κ x = ((2 * κ : ℝ) : ℂ) * (((Eig.phi χ 0 x).re : ℝ) : ℂ) := by
  unfold modeFn
  have : ((κ : ℂ) * Eig.phi χ 0 x).re = κ * (Eig.phi χ 0 x).re := by
    simp [Complex.mul_re]
  rw [this]
  push_cast
  ring

theorem modeFn_eq_smul (κ : ℝ) :
    modeFn χ 0 κ = ((2 * κ : ℝ) : ℂ) • fun x => (((Eig.phi χ 0 x).re : ℝ) : ℂ) := by
  funext x
  rw [modeFn_eq]
  rfl

theorem rePhi_memH (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) (k : ℕ) :
    MemH k fun x => (((Eig.phi χ 0 x).re : ℝ) : ℂ) :=
  ((Eig.eigendata_phi χ hχ hN zero_mem_Icc_Gbar).2.1 k).1.re_im.1

theorem modeFn_memH (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) (κ : ℝ) (k : ℕ) :
    MemH k (modeFn χ 0 κ) := by
  rw [modeFn_eq_smul]
  exact ((rePhi_memH hχ hN k).const_smul _).1

theorem normH_modeFn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {κ : ℝ}
    (hκ : 0 ≤ κ) (k : ℕ) :
    normH k (modeFn χ 0 κ) = 2 * κ * normH k fun x => (((Eig.phi χ 0 x).re : ℝ) : ℂ) := by
  rw [modeFn_eq_smul, ((rePhi_memH hχ hN k).const_smul _).2, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

theorem phi_zero_outside (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → Eig.phi χ 0 x = 0 :=
  ((Eig.eigendata_phi χ hχ hN zero_mem_Icc_Gbar).2.1 0).2.1

theorem modeFn_zero_outside (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) (κ : ℝ) :
    ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → modeFn χ 0 κ x = 0 := by
  filter_upwards [phi_zero_outside hχ hN] with x hx hxK
  rw [modeFn_eq, hx hxK]
  simp

/-- `ℓ_*(0)(2Re(κφ_*(0))) = κ` (`05_single_ring.tex:1214-1215`). -/
theorem ellFn_modeFn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) (κ : ℝ) :
    Eig.ellFn χ 0 (modeFn χ 0 κ) = κ := by
  obtain ⟨-, hX, hY, h1, h0⟩ := Eig.eigendata_phi χ hχ hN zero_mem_Icc_Gbar
  have hphi0 : MemH 0 (Eig.phi χ 0) := (hX 0).1
  have hphiL : MemLp (Eig.phi χ 0) 2 volume := by
    have := hphi0.memLp
    rwa [Measure.restrict_univ] at this
  have hcL : MemLp (fun x => conj (Eig.phi χ 0 x)) 2 volume :=
    hphiL.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hphiL.1)
      (Eventually.of_forall fun x => (Complex.norm_conj _).symm)
  have hc0 : MemH 0 fun x => conj (Eig.phi χ 0 x) := (normH_zero hcL).1
  have hcK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → conj (Eig.phi χ 0 x) = 0 := by
    filter_upwards [phi_zero_outside hχ hN] with x hx hxK
    rw [hx hxK, map_zero]
  obtain ⟨w₂, hw₂⟩ := exists_Y_of_memH (K := annN) hc0 hcK
  set w₁ : Y 0 annN := Eig.phiY χ 0 0
  have hw₁ : w₁.fn =ᵐ[volume] Eig.phi χ 0 := (hY 0).1
  set w : Y 0 annN := (κ : ℂ) • w₁ + (κ : ℂ) • w₂
  have hw : w.fn =ᵐ[volume] modeFn χ 0 κ := by
    filter_upwards [Y_fn_add ((κ : ℂ) • w₁) ((κ : ℂ) • w₂), Y_fn_smul (κ : ℂ) w₁,
      Y_fn_smul (κ : ℂ) w₂, hw₁, hw₂] with x h1 h2 h3 h4 h5
    rw [h1, h2, h3, h4, h5]
    unfold modeFn
    apply Complex.ext
    · simp [Complex.mul_re]
      ring
    · simp [Complex.mul_im]
  rw [← ellFn_congr_ae χ 0 hw, ← ell_apply hχ hN, map_add, map_smul, map_smul,
    ell_apply hχ hN, ell_apply hχ hN, ellFn_congr_ae χ 0 hw₁, ellFn_congr_ae χ 0 hw₂, h1, h0]
  simp

end NonUniqueEuler.OneRing.SeedH
