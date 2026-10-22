import NonUniqueEuler.H.Sec5.Energy.Transport
import NonUniqueEuler.I.Sec5.Lambda
import NonUniqueEuler.I.Sec5.ReductionEq
import NonUniqueEuler.I.Sec5.ReductionField
import NonUniqueEuler.I.Sec5.Energy.VEquation
import NonUniqueEuler.I.Sec5.Energy.FieldBounds
import NonUniqueEuler.I.Sec5.Energy.RappPath
import NonUniqueEuler.I.Infra.Sobolev.Norm

/-!
# Helper for `lem:energy`: the energy inequality at a fixed time

Helper of `P/Sec5/Energy.lean` (`05_single_ring.tex:356-365`). Under the hypotheses of
`lem:energy`, for `τ ∈ [0,t]`, with `V = toY s N (w - w_app)` and
`V' = toY s N (∂_t w) - toY s N (∂_t w_app)` (the derivative of `V` in `Y^s(N)`),
`Re ⟪V, V'⟫_{H^s} ≤ Λ(s)‖v‖²_{H^s} + ‖R_app‖_{H^s}‖v‖_{H^s}`, i.e.
`½ d/dτ ‖v‖²_{H^s} ≤ Λ(s)‖v‖²_{H^s} + ‖R_app‖_{H^s}‖v‖_{H^s}`.

The ingredients are the interface files of the steps (`energy_vEquation`, `energy_field`,
`rapp_pathC`), `lem:bilinear`(1) for `(K_BS*v)·∇(Φ + w_app)` (`bilinear_B`, with
`C_B(s) = 2C_HK C^el_{s-1}`), and the transport bound `EnergyH.abs_re_inner_dotGrad_le`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.EnergyH

open Sect Sob RingData

/-- **The energy inequality at a fixed time** (`05_single_ring.tex:356-365`). -/
theorem energy_pointwise (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 3 ≤ s) {c : RingConfig} {t : ℝ} (hc : c.Hyp t)
    (hG : c.G ∈ Icc (0 : ℝ) Gbar) (hsupp : c.RingSupportedIn t annN)
    {wapp wapp' : ℝ → ℂ → ℂ} (happ : PathC (s + 1) t wapp) (happ' : PathC1 s t wapp wapp')
    (hw : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH s (c.w χ τ) ≤ 1)
    (hwapp : ∀ τ ∈ Icc (0 : ℝ) t, Sob.normH (s + 1) (wapp τ) ≤ 1)
    (hh : ∀ τ ∈ Icc (0 : ℝ) t, normCk (s + 1) annN' (c.h τ) ≤ 1)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) :
    (inner ℂ (toY s annN (c.w χ τ - wapp τ))
        (toY s annN (ringRHS χ c.G (c.h τ) (c.w χ τ)) - toY s annN (wapp' τ))).re ≤
      Lam χ s * normH s (c.w χ τ - wapp τ) ^ 2 +
        normH s (Rapp χ c.G c.h wapp wapp' τ) * normH s (c.w χ τ - wapp τ) := by
  have hKm : MeasurableSet annN := (isClosed_closedAnnulus _ _).measurableSet
  obtain ⟨-, hpert⟩ := reduction_eq χ hχ hc hsupp
  obtain ⟨hfield, hpath⟩ := reduction_field hc
  -- the objects at time `τ`
  set v : ℂ → ℂ := c.w χ τ - wapp τ with hvdef
  set U : ℂ → ℂ := omegaField χ c.G + c.h τ + BS.velocityRe (c.w χ τ) with hUdef
  set D : ℂ → ℂ := Sob.dotGrad U v with hDdef
  set B : ℂ → ℂ := Bfn v (PhiC χ + wapp τ) with hBdef
  set R : ℂ → ℂ := Rapp χ c.G c.h wapp wapp' τ with hRdef
  set X : ℂ → ℂ := ringRHS χ c.G (c.h τ) (c.w χ τ) with hXdef
  -- memberships
  have hwX1 : Lin.MemXFn (s + 1) (c.w χ τ) := (hpert (s + 1)).1.1 τ hτ
  have hwX : Lin.MemXFn s (c.w χ τ) := (hpert s).1.1 τ hτ
  have hXX : Lin.MemXFn s X := (hpert s).2.1.1 τ hτ
  have hw'X : Lin.MemXFn s (wapp' τ) := happ'.2.1.1 τ hτ
  have hv1 : Lin.MemXFn (s + 1) v := MemXFn.sub hwX1 (happ.1 τ hτ)
  have hv : Lin.MemXFn s v := MemXFn.mono hv1 (Nat.le_succ s)
  have hPw : Lin.MemXFn (s + 1) (PhiC χ + wapp τ) :=
    MemXFn.add (memXFn_PhiC hχ (s + 1)) (happ.1 τ hτ)
  obtain ⟨hBX, hBb⟩ := bilinear_B (k := s) (by omega) hv1 hPw
  have hRX : Lin.MemXFn s R := (rapp_pathC χ hχ hN hs hc happ happ').1 τ hτ
  -- the equation of `v`
  have heq : X - wapp' τ =ᵐ[volume] -D + B - R := energy_vEquation χ hχ hc hsupp happ τ hτ
  have hE : Lin.MemXFn s (B - R - (X - wapp' τ)) := MemXFn.sub (MemXFn.sub hBX hRX)
    (MemXFn.sub hXX hw'X)
  have hDeq : B - R - (X - wapp' τ) =ᵐ[volume] D := by
    filter_upwards [heq] with x hx
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply] at hx ⊢
    linear_combination -hx
  have hDH : MemH s D := (hE.1.congr_ae hDeq).1
  have hDN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → D x = 0 := by
    filter_upwards [hDeq, hE.2.1] with x h1 h2 hx
    rw [← h1, h2 hx]
  have hnD : MemH s (-D) := by
    have h := (hDH.const_smul (-1)).1
    have hneg : (-1 : ℂ) • D = -D := by funext x; simp
    rwa [hneg] at h
  have hnDN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → (-D) x = 0 := by
    filter_upwards [hDN] with x h hx
    simp [h hx]
  have hnDB : MemH s (-D + B) := (hnD.add hBX.1).1
  have hnDBN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → (-D + B) x = 0 := by
    filter_upwards [hnDN, hBX.2.1] with x h1 h2 hx
    rw [Pi.add_apply, h1 hx, zero_add]
    exact h2 hx
  -- the derivative `V'` in terms of `D`, `B`, `R`
  have hV' : toY s annN X - toY s annN (wapp' τ) =
      -toY s annN D + toY s annN B - toY s annN R := by
    rw [← toY_sub hKm hXX.1 hXX.2.1 hw'X.1 hw'X.2.1, toY_congr_ae heq,
      toY_sub hKm hnDB hnDBN hRX.1 hRX.2.1, toY_add hKm hnD hnDN hBX.1 hBX.2.1,
      toY_neg hKm hDH hDN]
  rw [hV', inner_sub_right, inner_add_right, inner_neg_right]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re]
  -- norms
  have hnv : ‖toY s annN v‖ = normH s v := MemXFn.norm_toY hv
  have hnB : ‖toY s annN B‖ = normH s B := MemXFn.norm_toY hBX
  have hnR : ‖toY s annN R‖ = normH s R := MemXFn.norm_toY hRX
  have hv0 := normH_nonneg s v
  have hR0 := normH_nonneg s R
  -- the transport term
  obtain ⟨O, hO, hNO, hsm, hdiv, -, -, -, -⟩ := hfield τ hτ
  have hck1 : MemCk (s + 1) annN' (c.h τ) := (hpath (s + 1)).1 τ hτ
  have hck : MemCk s annN' (c.h τ) := hck1.mono_order (Nat.le_succ s)
  have hck1' : normCk s annN' (c.h τ) ≤ 1 :=
    (normCk_mono_order hck1 (Nat.le_succ s)).trans (hh τ hτ)
  obtain ⟨hU1, hU2, hUdiv, hUb⟩ :=
    energy_field χ hχ hN hs hG hO hNO hsm hdiv hck hck1' hwX.1 hwX.2.1 (hw τ hτ)
  have htr := abs_re_inner_dotGrad_le hs hv1.1 hv1.2.1 hU1 hU2 hUdiv hDH hDN
  have hnc : 0 ≤ (nIdx s : ℝ) * CHK s := mul_nonneg (Nat.cast_nonneg _) (CP_pos s).le
  have htr' : -(inner ℂ (toY s annN v) (toY s annN D)).re ≤
      nIdx s * CHK s * As χ s * normH s v ^ 2 := by
    have h1 := neg_le_abs (inner ℂ (toY s annN v) (toY s annN D)).re
    have h2 : (nIdx s : ℝ) * CHK s * (normW1infOn annN1 U + normHOn s annN1 U) * normH s v ^ 2 ≤
        nIdx s * CHK s * As χ s * normH s v ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUb hnc) (sq_nonneg _)
    linarith
  -- the term `(K_BS*v)·∇(Φ + w_app)`
  have hB' : (inner ℂ (toY s annN v) (toY s annN B)).re ≤
      CB s * (normH (s + 1) (PhiC χ) + 1) * normH s v ^ 2 := by
    have h1 : (inner ℂ (toY s annN v) (toY s annN B)).re ≤ normH s v * normH s B := by
      rw [← hnv, ← hnB]
      exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    have h2 : normH (s + 1) (PhiC χ + wapp τ) ≤ normH (s + 1) (PhiC χ) + 1 := by
      have h21 := ((memXFn_PhiC hχ (s + 1)).1.add (happ.1 τ hτ).1).2
      have h22 := hwapp τ hτ
      linarith
    have hCB := (CB_pos s).le
    have h3 : normH s B ≤ CB s * normH s v * (normH (s + 1) (PhiC χ) + 1) :=
      hBb.trans (mul_le_mul_of_nonneg_left h2 (mul_nonneg hCB hv0))
    calc (inner ℂ (toY s annN v) (toY s annN B)).re ≤ normH s v * normH s B := h1
      _ ≤ normH s v * (CB s * normH s v * (normH (s + 1) (PhiC χ) + 1)) :=
          mul_le_mul_of_nonneg_left h3 hv0
      _ = CB s * (normH (s + 1) (PhiC χ) + 1) * normH s v ^ 2 := by ring
  -- the residual
  have hR' : -(inner ℂ (toY s annN v) (toY s annN R)).re ≤ normH s R * normH s v := by
    have h1 := neg_le_abs (inner ℂ (toY s annN v) (toY s annN R)).re
    have h2 : |(inner ℂ (toY s annN v) (toY s annN R)).re| ≤ normH s v * normH s R := by
      rw [← hnv, ← hnR]
      exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
    linarith
  -- `Λ(s)` dominates the two rates
  have hΛ : nIdx s * CHK s * As χ s + CB s * (normH (s + 1) (PhiC χ) + 1) ≤ Lam χ s := by
    have h := le_max_right (2 * sigmaMax χ)
      (nIdx s * CHK s * As χ s + 2 * CHK s * Cel (s - 1) * (Sob.normH (s + 1) (PhiC χ) + 1))
    have hCB : CB s = 2 * CHK s * Cel (s - 1) := by rw [CB, CHK_eq]
    rw [hCB]
    unfold Lam
    linarith
  have hv2 := sq_nonneg (normH s v)
  have hfin := mul_le_mul_of_nonneg_right hΛ hv2
  linarith

end NonUniqueEuler.OneRing.EnergyH
