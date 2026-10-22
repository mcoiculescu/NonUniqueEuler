import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.I.Infra.Sobolev.Leibniz
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.CkNorm.Basic
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives.ProfileDeriv
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives.ProfileL2

/-!
# Helpers for `P/Infra/AngularFourier/Derivatives`: profiles of `H^k` functions on an annulus

Induction on `k` (`memH1On_angularSector_aux`):
* `∂_r g = (x/|x|)·∇g` (`radDeriv_eq_dotGrad`) lies in `H^{k}` and vanishes outside the annulus
  when `g ∈ H^{k+1}` does (`Sob.MemH.dotGrad_of_memCk`, `Sob.MemH.weakPartial_eq_zero_outside`,
  `I/Infra/Sobolev/Leibniz.lean`; `x/|x|` is smooth near the annulus since `ρ₋ > 0`);
* `(g_ℓ)' = (∂_r g)_ℓ` weakly on `(0, ∞)` (`hasWeakDerivOn_angularSector`,
  `I/Infra/AngularFourier/Derivatives/ProfileDeriv.lean`), and weak derivatives compose
  (`Sob.HasWeakDerivOn.trans`);
* the `L²` part and the support (`memLp_angularSector_of_support`,
  `I/Infra/AngularFourier/Derivatives/ProfileL2.lean`).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Ang

namespace DerivAux

theorem radDeriv_eq_dotGrad (g : ℂ → ℂ) :
    radDeriv g = Sob.dotGrad (fun x => x / (‖x‖ : ℂ)) g := by
  funext x
  simp [radDeriv, Sob.dotGrad, Complex.div_ofReal_re, Complex.div_ofReal_im]

theorem isClosed_annulus' (ρm ρp : ℝ) : IsClosed {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp} :=
  (isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)

theorem isCompact_annulus' (ρm ρp : ℝ) : IsCompact {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp} :=
  (isCompact_closedBall (0 : ℂ) ρp).of_isClosed_subset (isClosed_annulus' ρm ρp)
    (fun x hx => by simpa using hx.2)

/-- The unit radial field `x/|x|` is `C^k` on the annulus. -/
theorem memCk_unit (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) :
    MemCk k {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp} (fun x => x / (‖x‖ : ℂ)) := by
  refine IsCkNear.memCk_of_isCompact ⟨{0}ᶜ, isOpen_compl_singleton, ?_, ?_⟩
    (isCompact_annulus' ρm ρp)
  · intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    simp only [Set.mem_ofPred_eq, norm_zero] at hx
    linarith [hx.1]
  · intro x hx
    have hx0 : x ≠ 0 := hx
    have h : ContDiffAt ℝ k (fun y : ℂ => (‖y‖⁻¹ : ℝ) • y) x :=
      ((contDiffAt_norm ℝ hx0).inv (norm_ne_zero_iff.2 hx0)).smul contDiffAt_id
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).contDiffWithinAt
    simp only
    rw [Complex.real_smul, div_eq_inv_mul, Complex.ofReal_inv]

/-- `∂_r g ∈ H^k`, supported in the annulus, for `g ∈ H^{k+1}` supported in the annulus. -/
theorem memH_radDeriv {k : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) {g : ℂ → ℂ}
    (hg : Sob.MemH (k + 1) g) (hgK : ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → g x = 0) :
    Sob.MemH k (radDeriv g) ∧ ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → radDeriv g x = 0 := by
  have hgK' : ∀ᵐ x, x ∉ {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp} → g x = 0 := hgK
  rw [radDeriv_eq_dotGrad]
  refine ⟨(Sob.MemH.dotGrad_of_memCk (isClosed_annulus' ρm ρp) hg hgK' (memCk_unit k hρm)).1,
    ?_⟩
  have h1 := Sob.MemH.weakPartial_eq_zero_outside (isClosed_annulus' ρm ρp) hg hgK'
    (γ := (1, 0)) (Sob.mem_multiIdx.2 (by omega))
  have h2 := Sob.MemH.weakPartial_eq_zero_outside (isClosed_annulus' ρm ρp) hg hgK'
    (γ := (0, 1)) (Sob.mem_multiIdx.2 (by omega))
  filter_upwards [h1, h2] with x hx1 hx2 hx
  simp [Sob.dotGrad, hx1 hx, hx2 hx]

theorem hasWeakDerivOn_nil_self (V : Set ℝ) (u : ℝ → ℂ) :
    Sob.HasWeakDerivOn V (Sob.derivList 0) u u := by
  intro φ _
  simp [Sob.derivList]

theorem derivList_append_one (i : ℕ) :
    Sob.derivList i ++ Sob.derivList 1 = Sob.derivList (i + 1) := by
  simp only [Sob.derivList, List.replicate_add]

/-- The profile of an `H^k` function supported in the annulus is in `H^k((0, ∞))`. -/
theorem memH1On_angularSector_aux {ρm ρp : ℝ} (hρm : 0 < ρm) (ℓ : ℤ) :
    ∀ (k : ℕ) {g : ℂ → ℂ}, Sob.MemH k g → (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → g x = 0) →
      Sob.MemH1On k (Ioi 0) (Polar.angularSector g ℓ)
  | 0, g, hg, hgK => by
    have hL := (memLp_angularSector_of_support hρm (Sob.memH_iff.1 hg).1 hgK ℓ).1
    refine ⟨hL, fun j hj => ⟨_, hL, ?_⟩⟩
    obtain rfl : j = 0 := by omega
    exact hasWeakDerivOn_nil_self _ _
  | k + 1, g, hg, hgK => by
    have hL := (memLp_angularSector_of_support hρm (Sob.memH_iff.1 hg).1 hgK ℓ).1
    obtain ⟨hr, hrK⟩ := memH_radDeriv hρm hg hgK
    have IH := memH1On_angularSector_aux hρm ℓ k hr hrK
    have h1 := hasWeakDerivOn_angularSector (hg.mono_order (by omega)) ℓ
    refine ⟨hL, fun j hj => ?_⟩
    rcases j with _ | i
    · exact ⟨_, hL, hasWeakDerivOn_nil_self _ _⟩
    · obtain ⟨hfun, hm, hd⟩ := IH.deriv i (by omega)
      refine ⟨hfun, hm, ?_⟩
      have := h1.trans hd
      rwa [derivList_append_one] at this

end DerivAux

end NonUniqueEuler.Ang
