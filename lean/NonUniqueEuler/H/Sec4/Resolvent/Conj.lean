import NonUniqueEuler.H.Sec4.Resolvent.Basic
import NonUniqueEuler.Defs.Sec4.Bridge
import NonUniqueEuler.I.Infra.Sobolev.Symmetry

/-!
# Helpers for `P/Sec4/Resolvent`: complex conjugation `Y^s_ℓ → Y^s_{-ℓ}`

* `exists_Ysec_conj`: `conj g ∈ Y^s_{ℓ'}(K)` for `g ∈ Y^s_ℓ(K)` and `ℓ' = -ℓ` (`Sob.MemH.conj`);
* `conjY`: the conjugation map, additive, conjugate-homogeneous, isometric, involutive;
* `conjLIE`: conjugation as a real-linear isometric equivalence `Y^s_ℓ ≃ Y^s_{-ℓ}`.

Adapted from `H/Sec4/SemigroupLaw/Conj.lean` (which this proof may not import
(import rules, `README.md`)), with the target sector `ℓ'` given by an equation `ℓ' = -ℓ`, so that
the inverse map `Y^s_{-ℓ} → Y^s_ℓ` needs no cast.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal ComplexConjugate

namespace NonUniqueEuler.ResolventAux

open Sect Sob Ang

variable {s : ℕ} {K : Set ℂ}

/-- `conj g ∈ Y^s_{ℓ'}(K)` for `g ∈ Y^s_ℓ(K)`, `ℓ' = -ℓ`. -/
theorem exists_Ysec_conj {ℓ ℓ' : ℤ} (hℓ : ℓ' = -ℓ) (g : Ysec s K ℓ) :
    ∃ g' : Ysec s K ℓ', g'.fn =ᵐ[volume] fun x => conj (g.fn x) := by
  subst hℓ
  obtain ⟨hmem, -⟩ := (Ysec_memH_fn g).conj
  obtain ⟨F, hF⟩ := memH_iff_exists_Hk.1 hmem
  have hY : (F : SobTuple s) ∈ YSub s K := by
    rw [mem_YSub_iff]
    refine ⟨F.2, ?_⟩
    filter_upwards [hF, Ysec_supp g] with x hx hsupp hxK
    change F.fn x = 0
    rw [hx, hsupp hxK, map_zero]
  have hsec : IsSectorFn (-ℓ) (tupleFn (F : SobTuple s)) := by
    intro θ
    have h1 := Ysec_isSectorFn g θ
    have h2 : (fun x => F.fn (rot θ x)) =ᵐ[volume] fun x => conj (g.fn (rot θ x)) :=
      (Polar.measurePreserving_rot θ).quasiMeasurePreserving.ae_eq_comp hF
    filter_upwards [h1, h2, hF] with x h1x h2x hwx
    change F.fn (rot θ x) = _ * F.fn x
    rw [h2x, h1x, map_mul, hwx, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, Int.cast_neg]
    ring
  exact ⟨⟨F, (mem_YsecSub_iff' _ _).2 ⟨hY, hsec⟩⟩, hF⟩

/-- Complex conjugation `Y^s_ℓ(K) → Y^s_{ℓ'}(K)`, `ℓ' = -ℓ`. -/
def conjY {ℓ ℓ' : ℤ} (_hℓ : ℓ' = -ℓ) (g : Ysec s K ℓ) : Ysec s K ℓ' :=
  toYsec s K ℓ' fun x => conj (g.fn x)

theorem conjY_fn {ℓ ℓ' : ℤ} (hℓ : ℓ' = -ℓ) (g : Ysec s K ℓ) :
    (conjY hℓ g).fn =ᵐ[volume] fun x => conj (g.fn x) :=
  toYsec_spec (exists_Ysec_conj hℓ g)

theorem conjY_add {ℓ ℓ' : ℤ} (hℓ : ℓ' = -ℓ) (g h : Ysec s K ℓ) :
    conjY hℓ (g + h) = conjY hℓ g + conjY hℓ h := by
  refine Ysec_ext_fn ?_
  filter_upwards [conjY_fn hℓ (g + h), Ysec_fn_add g h, conjY_fn hℓ g, conjY_fn hℓ h,
    Ysec_fn_add (conjY hℓ g) (conjY hℓ h)] with x h1 h2 h3 h4 h5
  rw [h1, h5, h2, Pi.add_apply, map_add, Pi.add_apply, h3, h4]

theorem conjY_smul {ℓ ℓ' : ℤ} (hℓ : ℓ' = -ℓ) (c : ℂ) (g : Ysec s K ℓ) :
    conjY hℓ (c • g) = conj c • conjY hℓ g := by
  refine Ysec_ext_fn ?_
  filter_upwards [conjY_fn hℓ (c • g), Ysec_fn_smul c g, conjY_fn hℓ g,
    Ysec_fn_smul (conj c) (conjY hℓ g)] with x h1 h2 h3 h4
  rw [h1, h4, h2, Pi.smul_apply, Pi.smul_apply, h3, smul_eq_mul, smul_eq_mul, map_mul]

theorem conjY_conjY {ℓ ℓ' : ℤ} (hℓ : ℓ' = -ℓ) (hℓ' : ℓ = -ℓ') (g : Ysec s K ℓ) :
    conjY hℓ' (conjY hℓ g) = g := by
  refine Ysec_ext_fn ?_
  filter_upwards [conjY_fn hℓ' (conjY hℓ g), conjY_fn hℓ g] with x h1 h2
  rw [h1, h2, Complex.conj_conj]

theorem norm_conjY {ℓ ℓ' : ℤ} (hℓ : ℓ' = -ℓ) (g : Ysec s K ℓ) : ‖conjY hℓ g‖ = ‖g‖ := by
  obtain ⟨hmem, hnorm⟩ := (Ysec_memH_fn g).conj
  rw [Ysec_norm_eq_normH_of_ae hmem (conjY_fn hℓ g), hnorm,
    ← Ysec_norm_eq_normH_of_ae (Ysec_memH_fn g) (Filter.EventuallyEq.refl _ _)]

/-- Complex conjugation as a real-linear isometric equivalence `Y^s_ℓ(K) ≃ Y^s_{-ℓ}(K)`. -/
def conjLIE (s : ℕ) (K : Set ℂ) (ℓ : ℤ) : Ysec s K ℓ ≃ₗᵢ[ℝ] Ysec s K (-ℓ) :=
  { toFun := conjY rfl
    invFun := conjY (neg_neg ℓ).symm
    map_add' := conjY_add rfl
    map_smul' := fun r g => by
      simp only [RingHom.id_apply]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r g, conjY_smul, RCLike.conj_ofReal,
        ← RCLike.real_smul_eq_coe_smul (K := ℂ) r]
    left_inv := fun g => conjY_conjY rfl (neg_neg ℓ).symm g
    right_inv := fun g => conjY_conjY (neg_neg ℓ).symm rfl g
    norm_map' := fun g => norm_conjY rfl g }

theorem conjLIE_apply (ℓ : ℤ) (g : Ysec s K ℓ) : conjLIE s K ℓ g = conjY rfl g := rfl

theorem conjLIE_fn (ℓ : ℤ) (g : Ysec s K ℓ) :
    (conjLIE s K ℓ g).fn =ᵐ[volume] fun x => conj (g.fn x) :=
  conjY_fn rfl g

theorem conjLIE_smul (ℓ : ℤ) (c : ℂ) (g : Ysec s K ℓ) :
    conjLIE s K ℓ (c • g) = conj c • conjLIE s K ℓ g :=
  conjY_smul rfl c g

/-! ### Conjugation of profiles -/

/-- `angPhase (-ℓ) x = conj (angPhase ℓ x)` for `x ≠ 0`. -/
theorem angPhase_neg {x : ℂ} (hx : x ≠ 0) (ℓ : ℤ) :
    angPhase (-ℓ) x = conj (angPhase ℓ x) := by
  have h1 : ‖angPhase ℓ x‖ = 1 := norm_angPhase hx ℓ
  have hne : angPhase ℓ x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hinv : angPhase (-ℓ) x = (angPhase ℓ x)⁻¹ := by
    simp only [angPhase, zpow_neg]
  rw [hinv, Complex.inv_def, Complex.normSq_eq_norm_sq, h1]
  simp

/-- `(conj h)(|x|) e^{-iℓθ} = conj (h(|x|) e^{iℓθ})` for `x ≠ 0`. -/
theorem ofProfile_neg_conj {x : ℂ} (hx : x ≠ 0) (ℓ : ℤ) (h : ℝ → ℂ) :
    ofProfile (-ℓ) (fun r => conj (h r)) x = conj (ofProfile ℓ h x) := by
  simp only [ofProfile, map_mul, angPhase_neg hx]

theorem ofProfile_neg_conj_ae (ℓ : ℤ) (h : ℝ → ℂ) :
    ofProfile (-ℓ) (fun r => conj (h r)) =ᵐ[volume] fun x => conj (ofProfile ℓ h x) := by
  have h0 : ∀ᵐ x : ℂ ∂volume, x ≠ 0 := by
    have : (volume : Measure ℂ) {0} = 0 := measure_singleton 0
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with x hx
    exact hx
  filter_upwards [h0] with x hx
  exact ofProfile_neg_conj hx ℓ h

end NonUniqueEuler.ResolventAux
