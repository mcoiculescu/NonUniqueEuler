import NonUniqueEuler.H.Sec4.Duhamel.Sector

/-!
# Helper for `lem:duhamel`: the time derivative of the Duhamel integral

Helper of `P/Sec4/Duhamel.lean` (restructuring R1). For `f₀ ∈ Y^{k+1}(N)` and
`g ∈ C([0,T]; Y^{k+1}(N))`, let `u(t) = e^{tL}f₀ + ∫₀ᵗ e^{(t-τ)L}g(τ)dτ` and
`D(t) = L(G)u(t) + g(t) ∈ Y^k(N)`.

* `lower_duhamel_eq_integral`: `u(t) = u(0) + ∫₀ᵗ D(s) ds` in `Y^k(N)` for `t ∈ [0,T]`. Proof:
  apply `P_ℓ`; by `secProj_duhamel` the sector component is the bounded-operator Duhamel integral
  `φ_ℓ(t) = exp(tL_ℓ)a_ℓ + ∫₀ᵗ exp((t-τ)L_ℓ)b_ℓ(τ)dτ`, which solves `φ_ℓ' = L_ℓφ_ℓ + b_ℓ`
  (`BanachExp.hasDerivWithinAt_duhamel`); `L_ℓφ_ℓ + b_ℓ = P_ℓ D` (`secProj_L`), so the
  fundamental theorem of calculus gives `φ_ℓ(t) - φ_ℓ(0) = P_ℓ ∫₀ᵗ D`; conclude by
  `ext_secProj`.
* `hasDerivWithinAt_lower_duhamel`: hence `∂_t u = D` on `[0,T]` (one-sided at the ends), by the
  fundamental theorem of calculus for the continuous `D`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.Lin.DuhamelAux

open Sect RingData SectorSetting

variable {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ)

include hχ

/-- The integral form of `∂_t u = L(G)u + g` in `Y^k(N)`. -/
theorem lower_duhamel_eq_integral {G T : ℝ} (hT : 0 ≤ T) (k : ℕ) {f₀ : Y (k + 1) annN}
    {g : ℝ → Y (k + 1) annN} (hg : ContinuousOn g (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    lowerY k (k + 1) annN (duhamel χ (k + 1) G f₀ g t) =
      lowerY k (k + 1) annN (duhamel χ (k + 1) G f₀ g 0) +
        ∫ s in (0 : ℝ)..t,
          (L χ k G (duhamel χ (k + 1) G f₀ g s) + lowerY k (k + 1) annN (g s)) := by
  set u := duhamel χ (k + 1) G f₀ g with hu_def
  have hu : ContinuousOn u (Icc 0 T) := duhamel_continuousOn hχ hT f₀ hg
  set D : ℝ → Y k annN := fun s => L χ k G (u s) + lowerY k (k + 1) annN (g s) with hD_def
  have hD : ContinuousOn D (Icc 0 T) :=
    ((L χ k G).continuous.comp_continuousOn hu).add
      ((lowerY k (k + 1) annN).continuous.comp_continuousOn hg)
  have hlg : ContinuousOn (fun τ => lowerY k (k + 1) annN (g τ)) (Icc 0 T) :=
    (lowerY k (k + 1) annN).continuous.comp_continuousOn hg
  have h0T : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  apply ext_secProj hχ k
  intro ℓ
  set A := Lsec χ k ℓ G with hA
  set a0 := secProj k annN ℓ (lowerY k (k + 1) annN f₀) with ha0
  set b : ℝ → Ysec k annN ℓ := fun τ => secProj k annN ℓ (lowerY k (k + 1) annN (g τ)) with hb_def
  set φ : ℝ → Ysec k annN ℓ := fun t => NormedSpace.exp ((t : ℂ) • A) a0 +
    ∫ τ in (0 : ℝ)..t, NormedSpace.exp (((t - τ : ℝ) : ℂ) • A) (b τ) with hφ_def
  have hb : ContinuousOn b (Icc 0 T) := (secProj k annN ℓ).continuous.comp_continuousOn hlg
  have h1 : ∀ t ∈ Icc (0 : ℝ) T, secProj k annN ℓ (lowerY k (k + 1) annN (u t)) = φ t := by
    intro t ht
    rw [hu_def, lower_duhamel hχ k hg ht, secProj_duhamel hχ k hlg ht ℓ]
  have h2 : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt φ (A (φ t) + b t) (Icc 0 T) t :=
    BanachExp.hasDerivWithinAt_duhamel A hb a0
  have h3 : ∀ t ∈ Icc (0 : ℝ) T, A (φ t) + b t = secProj k annN ℓ (D t) := by
    intro t ht
    rw [← h1 t ht, hD_def]
    simp only
    rw [map_add, secProj_L hχ k G (u t) ℓ]
  have hDℓ : ContinuousOn (fun s => secProj k annN ℓ (D s)) (Icc 0 T) :=
    (secProj k annN ℓ).continuous.comp_continuousOn hD
  have hFTC : (∫ s in (0 : ℝ)..t, secProj k annN ℓ (D s)) = φ t - φ 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    · intro x hx
      have hxT : x ∈ Icc (0 : ℝ) T := ⟨hx.1, hx.2.trans ht.2⟩
      exact (h2 x hxT).continuousWithinAt.mono (Icc_subset_Icc_right ht.2)
    · intro x hx
      have hxT : x ∈ Icc (0 : ℝ) T := ⟨hx.1.le, hx.2.le.trans ht.2⟩
      have := (h2 x hxT).hasDerivAt (Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 ht.2))
      rw [h3 x hxT] at this
      exact this
    · exact (hDℓ.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hDint : IntervalIntegrable D volume 0 t :=
    (hD.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  rw [map_add, ← (secProj k annN ℓ).intervalIntegral_comp_comm hDint, hFTC, h1 t ht, h1 0 h0T]
  abel

/-- **The main step of `lem:duhamel`**: `∂_t u = L(G)u + g` in `Y^k(N)` on `[0, T]`. -/
theorem hasDerivWithinAt_lower_duhamel {G T : ℝ} (hT : 0 ≤ T) (k : ℕ) {f₀ : Y (k + 1) annN}
    {g : ℝ → Y (k + 1) annN} (hg : ContinuousOn g (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun τ => lowerY k (k + 1) annN (duhamel χ (k + 1) G f₀ g τ))
      (L χ k G (duhamel χ (k + 1) G f₀ g t) + lowerY k (k + 1) annN (g t)) (Icc 0 T) t := by
  set u := duhamel χ (k + 1) G f₀ g with hu_def
  have hu : ContinuousOn u (Icc 0 T) := duhamel_continuousOn hχ hT f₀ hg
  set D : ℝ → Y k annN := fun s => L χ k G (u s) + lowerY k (k + 1) annN (g s) with hD_def
  have hD : ContinuousOn D (Icc 0 T) :=
    ((L χ k G).continuous.comp_continuousOn hu).add
      ((lowerY k (k + 1) annN).continuous.comp_continuousOn hg)
  have hp : Continuous fun σ : ℝ => (projIcc 0 T hT σ : ℝ) :=
    continuous_subtype_val.comp continuous_projIcc
  have hDp : Continuous fun σ => D (projIcc 0 T hT σ : ℝ) :=
    hD.comp_continuous hp fun σ => (projIcc 0 T hT σ).2
  have hint : HasDerivAt (fun τ => ∫ s in (0 : ℝ)..τ, D (projIcc 0 T hT s : ℝ))
      (D (projIcc 0 T hT t : ℝ)) t := (hDp.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hpt : (projIcc 0 T hT t : ℝ) = t := by rw [projIcc_of_mem hT ht]
  rw [hpt] at hint
  have hfin := (hint.const_add (lowerY k (k + 1) annN (u 0))).hasDerivWithinAt (s := Icc 0 T)
  refine hfin.congr_of_mem (fun τ hτ => ?_) ht
  rw [lower_duhamel_eq_integral hχ hT k hg hτ]
  congr 1
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  rw [uIcc_of_le hτ.1] at hσ
  have hσ' : (projIcc 0 T hT σ : ℝ) = σ := by
    rw [projIcc_of_mem hT ⟨hσ.1, hσ.2.trans hτ.2⟩]
  simp only [hσ', hD_def, hu_def]

end NonUniqueEuler.Lin.DuhamelAux
