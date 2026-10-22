import NonUniqueEuler.Defs.Sec4.Linear
import NonUniqueEuler.I.Sec4.SemigroupLaw
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.SectorSpace.Projection
import NonUniqueEuler.I.Infra.SectorSpace.BanachExp
import NonUniqueEuler.H.Sec4.Duhamel.Basic
import NonUniqueEuler.H.Sec4.Duhamel.Sector
import NonUniqueEuler.H.Sec4.Duhamel.Deriv

/-!
# Proof: `lem:duhamel`, its converse, and the semigroup on `X^k` in ring units

Proof of `I/Sec4/Duhamel.lean` (same declarations, statements copied verbatim). Manuscript
`05_single_ring.tex:41-80`. Restructuring R1: the proof is sector-wise with bounded operators
(no generator, no `lem:mild`).

* `S_memX`: `X^k = Y^k_{3ℤ}` (`YsymSub_eq_YZSub`) is invariant (`semigroup_mem_YZSub`).
* `S_isReal`: `semigroup_isReal`.
* `duhamel_spec`: continuity from the joint continuity of `(t, w) ↦ e^{tL}w` on `[0,T] × Y`
  (`DuhamelAux.duhamel_continuousOn`); `X^k` and real elements are closed under integrals
  (kernel / equalizer of continuous maps, `DuhamelAux.intervalIntegral_memX`,
  `DuhamelAux.intervalIntegral_isReal`); the derivative is
  `DuhamelAux.hasDerivWithinAt_lower_duhamel` (sector-wise bounded-operator Duhamel formula
  `BanachExp.hasDerivWithinAt_duhamel`, the identity `P_ℓ L(G) = L_ℓ(G) P_ℓ`, the fundamental
  theorem of calculus, and the sector decomposition).
* `eq_duhamel_of_hasDerivWithinAt`: sector-wise variation of constants
  (`BanachExp.eq_duhamel_of_hasDerivWithinAt`), then the sector decomposition.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Lin

open RingData Sect

/-- `05_single_ring.tex:41-45`: `e^{tL(G)}` preserves `X^k` (it preserves each sector). -/
theorem S_memX (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (k : ℕ) (G : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {w : Y k annN} (hw : MemX w) : MemX (S χ k G t w) := by
  have hK : IsRotInvariant annN := isRotInvariant_closedAnnulus (a / 2) 2
  have e : YsymSub k annN 3 = YZSub k annN {ℓ | ((3 : ℕ) : ℤ) ∣ ℓ} :=
    YsymSub_eq_YZSub hK (by norm_num)
  rw [memX_iff, e] at hw ⊢
  exact SectorSetting.semigroup_mem_YZSub (ringPhiSetting χ) (ringPhiSetting_valid hχ) k G ht _ hw

/-- `05_single_ring.tex:45-47`: `e^{tL(G)}` maps real-valued functions to real-valued functions. -/
theorem S_isReal (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (k : ℕ) (G : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {w : Y k annN} (hw : w.IsReal) : (S χ k G t w).IsReal :=
  SectorSetting.semigroup_isReal (ringPhiSetting χ) (ringPhiSetting_valid hχ) k G ht hw

set_option linter.unusedVariables false in
/-- **`lem:duhamel`** (`05_single_ring.tex:52-57`), with the manuscript's `k ≥ 1` written `k + 1`:
for `G ∈ [0,G₁]`, `T > 0`, `f₀ ∈ X^{k+1}` and `g ∈ C([0,T];X^{k+1})`, the Duhamel integral
`u(t) = e^{tL(G)}f₀ + ∫₀ᵗ e^{(t-τ)L(G)}g(τ)dτ` lies in `C([0,T];X^{k+1}) ∩ C¹([0,T];X^k)`,
`∂_t u = L(G)u + g` on `[0,T]` (one-sided at the ends), and `u` is real if `f₀` and `g` are. -/
theorem duhamel_spec (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar)
    {T : ℝ} (hT : 0 < T) (k : ℕ) {f₀ : Y (k + 1) annN} (hf₀ : MemX f₀)
    {g : ℝ → Y (k + 1) annN} (hg : ContinuousOn g (Icc 0 T))
    (hgX : ∀ t ∈ Icc (0 : ℝ) T, MemX (g t)) :
    ContinuousOn (duhamel χ (k + 1) G f₀ g) (Icc 0 T) ∧
      (∀ t ∈ Icc (0 : ℝ) T, MemX (duhamel χ (k + 1) G f₀ g t)) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (fun τ => lowerY k (k + 1) annN (duhamel χ (k + 1) G f₀ g τ))
          (L χ k G (duhamel χ (k + 1) G f₀ g t) + lowerY k (k + 1) annN (g t)) (Icc 0 T) t) ∧
      ContinuousOn
        (fun t => L χ k G (duhamel χ (k + 1) G f₀ g t) + lowerY k (k + 1) annN (g t))
        (Icc 0 T) ∧
      (f₀.IsReal → (∀ t ∈ Icc (0 : ℝ) T, (g t).IsReal) →
        ∀ t ∈ Icc (0 : ℝ) T, (duhamel χ (k + 1) G f₀ g t).IsReal) := by
  have hu : ContinuousOn (duhamel χ (k + 1) G f₀ g) (Icc 0 T) :=
    DuhamelAux.duhamel_continuousOn hχ hT.le f₀ hg
  refine ⟨hu, fun t ht => ?_, fun t ht => DuhamelAux.hasDerivWithinAt_lower_duhamel hχ hT.le k hg ht,
    ((L χ k G).continuous.comp_continuousOn hu).add
      ((lowerY k (k + 1) annN).continuous.comp_continuousOn hg), ?_⟩
  · exact DuhamelAux.memX_add (S_memX χ hχ (k + 1) G ht.1 hf₀)
      (DuhamelAux.intervalIntegral_memX ht.1 (DuhamelAux.integrand_intervalIntegrable hχ hg ht)
        fun τ hτ => S_memX χ hχ (k + 1) G (sub_nonneg.2 hτ.2) (hgX τ ⟨hτ.1, hτ.2.trans ht.2⟩))
  · intro hf₀R hgR t ht
    exact DuhamelAux.isReal_add (S_isReal χ hχ (k + 1) G ht.1 hf₀R)
      (DuhamelAux.intervalIntegral_isReal ht.1 (DuhamelAux.integrand_intervalIntegrable hχ hg ht)
        fun τ hτ => S_isReal χ hχ (k + 1) G (sub_nonneg.2 hτ.2) (hgR τ ⟨hτ.1, hτ.2.trans ht.2⟩))

set_option linter.unusedVariables false in
/-- **The converse of `lem:duhamel`**: if
`w ∈ C([0,T];Y^{k+1}(N))`, `F ∈ C([0,T];Y^k(N))` and `∂_t w = L(G)w + F` in `Y^k(N)` on `[0,T]`,
then `w(t) = e^{tL(G)}w(0) + ∫₀ᵗ e^{(t-τ)L(G)}F(τ)dτ` in `Y^k(N)`. -/
theorem eq_duhamel_of_hasDerivWithinAt (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) {T : ℝ} (hT : 0 < T) (k : ℕ) {w : ℝ → Y (k + 1) annN}
    {F : ℝ → Y k annN} (hw : ContinuousOn w (Icc 0 T)) (hF : ContinuousOn F (Icc 0 T))
    (hder : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun τ => lowerY k (k + 1) annN (w τ)) (L χ k G (w t) + F t) (Icc 0 T) t) :
    ∀ t ∈ Icc (0 : ℝ) T,
      lowerY k (k + 1) annN (w t) = duhamel χ k G (lowerY k (k + 1) annN (w 0)) F t := by
  intro t ht
  apply DuhamelAux.ext_secProj hχ k
  intro ℓ
  have hb : ContinuousOn (fun τ => secProj k annN ℓ (F τ)) (Icc 0 T) :=
    (secProj k annN ℓ).continuous.comp_continuousOn hF
  have hφ : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun τ => secProj k annN ℓ (lowerY k (k + 1) annN (w τ)))
        (Lsec χ k ℓ G (secProj k annN ℓ (lowerY k (k + 1) annN (w τ))) + secProj k annN ℓ (F τ))
        (Icc 0 T) τ := by
    intro τ hτ
    have h := ((secProj k annN ℓ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt τ
      (hder τ hτ)
    have e : ((secProj k annN ℓ).restrictScalars ℝ) (L χ k G (w τ) + F τ) =
        Lsec χ k ℓ G (secProj k annN ℓ (lowerY k (k + 1) annN (w τ))) +
          secProj k annN ℓ (F τ) := by
      rw [ContinuousLinearMap.coe_restrictScalars', map_add, DuhamelAux.secProj_L hχ k G (w τ) ℓ]
    rw [e] at h
    exact h
  rw [BanachExp.eq_duhamel_of_hasDerivWithinAt (Lsec χ k ℓ G) hb hφ t ht,
    DuhamelAux.secProj_duhamel hχ k hF ht ℓ]
  rfl

end Lin

end NonUniqueEuler
