import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec4.PropSU
import NonUniqueEuler.I.Sec5.Bilinear
import NonUniqueEuler.H.Sec5.LinearPart.Bridge
import NonUniqueEuler.H.Sec5.LinearPart.Integrals

/-!
# Helpers for `lem:linear-part`: the bound on `(1 - R) wlin₀(u)`

Helper of `P/Sec5/LinearPart.lean` (fully proved modulo the interface files it uses).
Namespace `NonUniqueEuler.OneRing.LinearPartH`. Manuscript `05_single_ring.tex:634-649`.

* `sigb_le_sigma`: `σ_b ≤ σ(G)` on `[0,G₁]` once `σ_b > 9/200` (the infimum defining `σ_b` is
  then over a set bounded below, since `sInf` of an unbounded set is `0`);
* `forcing_memX_norm`: `F(v) = -h(v)·∇Φ ∈ X^k` with `‖F(v)‖_{H^k} ≤ C_∇(k)‖h(v)‖_{C^k(N')}`
  (`lem:bilinear`(3), i.e. `lem:uniform`);
* `complement_bound`: `‖(1-R)wlin₀(u)‖_{H^k} ≤ C_lin(k)(A⟨u⟩^pe^{σ'u} + η_bκe^{σu})`.

The commutation `(1-R)∫₀ᵘ e^{(u-v)L}F(v)dv = ∫₀ᵘ e^{(u-v)L}(1-R)F(v)dv` needs the integrand to be
interval integrable; when it is not, the Bochner integral is `0` and the bound is immediate, so
no continuity of the integrand is needed (the manuscript's `F ∈ C([0,ū];X^k)` is not used).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.LinearPartH

open RingData

/-- `σ_b ≤ σ(G)` for `G ∈ [0,G₁]`, as soon as `σ_b > 9/200`. -/
theorem sigb_le_sigma {χ : ℝ → ℝ} {σ' : ℝ} (hσ' : σ' ∈ Ioo (9 / 200 : ℝ) (Eig.sigb χ)) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) : Eig.sigb χ ≤ Eig.sigma χ G := by
  have hdef : Eig.sigb χ = sInf (Eig.sigma χ '' Icc 0 Gbar) := rfl
  have hpos : 0 < Eig.sigb χ := lt_trans (lt_trans (by norm_num) hσ'.1) hσ'.2
  have hbdd : BddBelow (Eig.sigma χ '' Icc 0 Gbar) := by
    by_contra hb
    have h0 : Eig.sigb χ = 0 := by rw [hdef]; exact Real.sInf_of_not_bddBelow hb
    linarith
  rw [hdef]
  exact csInf_le hbdd (mem_image_of_mem _ hG)

/-- `C_∇(k) ≥ 0`. -/
theorem Cnab_nonneg (χ : ℝ → ℝ) (k : ℕ) : 0 ≤ Eig.Cnab χ k := by
  unfold Eig.Cnab
  have := Sob.normH_nonneg (k + 1) fun y => ((ringPhi χ y : ℝ) : ℂ)
  positivity

/-- The forcing `F(v) = -h(v)·∇Φ` lies in `X^k`, with `‖F(v)‖_{H^k} ≤ C_∇(k)‖h(v)‖_{C^k(N')}`
(`lem:bilinear`(3)). -/
theorem forcing_memX_norm (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {k : ℕ} (hk : 2 ≤ k) {hf : ℂ → ℂ} (hhf : MemCk k annN' hf) (hsym : IsSymFieldOn annN' hf) :
    Lin.MemX (Sect.toY k annN (fun x => -hGrad hf (PhiC χ) x)) ∧
      ‖Sect.toY k annN (fun x => -hGrad hf (PhiC χ) x)‖ ≤ Eig.Cnab χ k * normCk k annN' hf := by
  obtain ⟨-, -, hnorm, hX⟩ := bilinear_Phi χ hχ hN hk hhf
  have hXf := hX hsym
  rw [toY_neg hXf]
  refine ⟨?_, ?_⟩
  · show -((Sect.toY k annN (hGrad hf (PhiC χ)) : Sob.SobTuple k)) ∈ Lin.Xsub k
    exact neg_mem (memX_toY hXf)
  · rw [norm_neg, norm_toY hXf]
    exact hnorm

/-- **The bound of `lem:linear-part`** (`05_single_ring.tex:634-649`):
`‖(1-R)wlin₀(u)‖_{H^k} ≤ C_lin(k)(A⟨u⟩^pe^{σ'u} + η_bκe^{σ(G)u})` for `u ∈ [0,ū]`. -/
theorem complement_bound (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {σ' : ℝ} (hσ' : σ' ∈ Ioo (9 / 200 : ℝ) (Eig.sigb χ)) (p : ℕ) {k : ℕ} (hk : 2 ≤ k)
    {CS : ℝ} (hCS0 : 0 ≤ CS) (hCS : IsSemigroupConst χ k σ' CS)
    {G ubar A κ ηb : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) (hA : 0 ≤ A) (hκ : 0 ≤ κ)
    (hηb : 0 ≤ ηb) {w₀ : ℂ → ℂ} (hw₀ : Lin.MemXFn k w₀) (hw₀A : Sob.normH k w₀ ≤ A)
    {h : ℝ → ℂ → ℂ} (hh : CkPathOn k annN' (Icc 0 ubar) h)
    (hsym : ∀ u ∈ Icc (0 : ℝ) ubar, IsSymFieldOn annN' (h u))
    (hbd : ∀ u ∈ Icc (0 : ℝ) ubar,
      normCk k annN' (h u) ≤ A * Prelim.jap u ^ p + ηb * κ * Real.exp (Eig.sigma χ G * u))
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) ubar) :
    ‖wlin0 χ k G w₀ h u - Eig.R χ k G (wlin0 χ k G w₀ h u)‖ ≤
      Clin χ k σ' CS * (A * Prelim.jap u ^ p * Real.exp (σ' * u) +
        ηb * κ * Real.exp (Eig.sigma χ G * u)) := by
  obtain ⟨hu0, huu⟩ := hu
  -- constants
  have hσ'pos : 0 < σ' := lt_trans (by norm_num) hσ'.1
  have hσb : σ' < Eig.sigb χ := hσ'.2
  have hσbσ : Eig.sigb χ ≤ Eig.sigma χ G := sigb_le_sigma hσ' hG
  have hgap : 0 < Eig.sigb χ - σ' := by linarith
  have hCn : 0 ≤ Eig.Cnab χ k := Cnab_nonneg χ k
  have hE : 0 ≤ ηb * κ := mul_nonneg hηb hκ
  -- `R` commutes with the semigroup
  have hcomm : ∀ t : ℝ, 0 ≤ t → ∀ w : Sect.Y k annN,
      Eig.R χ k G (Lin.S χ k G t w) = Lin.S χ k G t (Eig.R χ k G w) := by
    intro t ht w
    have h1 := congrArg (fun T : Sect.Y k annN →L[ℂ] Sect.Y k annN => T w)
      ((Eig.R_sector χ hχ hN hG k).2.2.2.2 t ht)
    exact h1.symm
  -- the forcing
  have hF : ∀ v ∈ Icc (0 : ℝ) ubar,
      Lin.MemX (Sect.toY k annN (forcing χ h v)) ∧
        ‖Sect.toY k annN (forcing χ h v)‖ ≤
          Eig.Cnab χ k * (A * Prelim.jap v ^ p + ηb * κ * Real.exp (Eig.sigma χ G * v)) := by
    intro v hv
    obtain ⟨hX, hn⟩ := forcing_memX_norm χ hχ hN hk (hh.1 v hv) (hsym v hv)
    exact ⟨hX, hn.trans (mul_le_mul_of_nonneg_left (hbd v hv) hCn)⟩
  -- the decomposition
  set w0Y : Sect.Y k annN := Sect.toY k annN w₀ with hw0Y
  set I : Sect.Y k annN :=
    ∫ v in (0 : ℝ)..u, Lin.S χ k G (u - v) (Sect.toY k annN (forcing χ h v)) with hIdef
  have hW : wlin0 χ k G w₀ h u = Lin.S χ k G u w0Y + I := rfl
  have hdec : wlin0 χ k G w₀ h u - Eig.R χ k G (wlin0 χ k G w₀ h u) =
      Lin.S χ k G u (w0Y - Eig.R χ k G w0Y) + (I - Eig.R χ k G I) := by
    rw [hW, map_add, map_sub, hcomm u hu0]
    abel
  -- the first term
  have h1 : ‖Lin.S χ k G u (w0Y - Eig.R χ k G w0Y)‖ ≤ CS * Real.exp (σ' * u) * A := by
    have hc : 0 ≤ CS * Real.exp (σ' * u) := mul_nonneg hCS0 (Real.exp_pos _).le
    calc ‖Lin.S χ k G u (w0Y - Eig.R χ k G w0Y)‖ ≤ CS * Real.exp (σ' * u) * ‖w0Y‖ :=
          (hCS G hG u hu0).1 _ (memX_toY hw₀)
      _ ≤ CS * Real.exp (σ' * u) * A := by
          rw [hw0Y, norm_toY hw₀]
          exact mul_le_mul_of_nonneg_left hw₀A hc
  -- the second term
  have h2 : ‖I - Eig.R χ k G I‖ ≤ CS * Eig.Cnab χ k *
      (A * Prelim.jap u ^ p * Real.exp (σ' * u) / σ' +
        ηb * κ * Real.exp (Eig.sigma χ G * u) / (Eig.sigb χ - σ')) := by
    have hRHS : 0 ≤ CS * Eig.Cnab χ k *
        (A * Prelim.jap u ^ p * Real.exp (σ' * u) / σ' +
          ηb * κ * Real.exp (Eig.sigma χ G * u) / (Eig.sigb χ - σ')) := by
      have : 0 ≤ Prelim.jap u ^ p := pow_nonneg (Prelim.jap_nonneg u) p
      have := (Real.exp_pos (σ' * u)).le
      have := (Real.exp_pos (Eig.sigma χ G * u)).le
      have := mul_nonneg hCS0 hCn
      positivity
    by_cases hint : IntervalIntegrable
        (fun v => Lin.S χ k G (u - v) (Sect.toY k annN (forcing χ h v))) volume 0 u
    · set P : Sect.Y k annN →L[ℂ] Sect.Y k annN :=
        ContinuousLinearMap.id ℂ (Sect.Y k annN) - Eig.R χ k G with hPdef
      have hP : I - Eig.R χ k G I = P I := by
        rw [hPdef, sub_apply, ContinuousLinearMap.id_apply]
      have hPI : P I = ∫ v in (0 : ℝ)..u,
          P (Lin.S χ k G (u - v) (Sect.toY k annN (forcing χ h v))) :=
        (P.intervalIntegral_comp_comm hint).symm
      obtain ⟨hgi, hgle⟩ := scalar_bound (σ := Eig.sigma χ G) p hσ'pos hσb hσbσ hu0 hA hE
      rw [hP, hPI]
      calc ‖∫ v in (0 : ℝ)..u, P (Lin.S χ k G (u - v) (Sect.toY k annN (forcing χ h v)))‖
          ≤ ∫ v in (0 : ℝ)..u, CS * Eig.Cnab χ k *
              (A * Prelim.jap u ^ p * Real.exp (σ' * (u - v)) +
                ηb * κ * Real.exp (σ' * u) * Real.exp ((Eig.sigma χ G - σ') * v)) := by
            refine intervalIntegral.norm_integral_le_of_norm_le hu0
              (Eventually.of_forall ?_) (hgi.const_mul _)
            intro v hv
            have hvI : v ∈ Icc (0 : ℝ) ubar := ⟨hv.1.le, hv.2.trans huu⟩
            have huv : 0 ≤ u - v := sub_nonneg.2 hv.2
            obtain ⟨hFX, hFn⟩ := hF v hvI
            have e1 : P (Lin.S χ k G (u - v) (Sect.toY k annN (forcing χ h v))) =
                Lin.S χ k G (u - v) (Sect.toY k annN (forcing χ h v) -
                  Eig.R χ k G (Sect.toY k annN (forcing χ h v))) := by
              rw [hPdef, sub_apply, ContinuousLinearMap.id_apply, map_sub, hcomm (u - v) huv]
            rw [e1]
            have hc : 0 ≤ CS * Real.exp (σ' * (u - v)) :=
              mul_nonneg hCS0 (Real.exp_pos _).le
            have hpt := pointwise_bound (σ := Eig.sigma χ G) (σ' := σ') (E := ηb * κ) p
              hv.1.le hv.2 hA
            calc ‖Lin.S χ k G (u - v) (Sect.toY k annN (forcing χ h v) -
                  Eig.R χ k G (Sect.toY k annN (forcing χ h v)))‖
                ≤ CS * Real.exp (σ' * (u - v)) * ‖Sect.toY k annN (forcing χ h v)‖ :=
                  (hCS G hG (u - v) huv).1 _ hFX
              _ ≤ CS * Real.exp (σ' * (u - v)) * (Eig.Cnab χ k *
                    (A * Prelim.jap v ^ p + ηb * κ * Real.exp (Eig.sigma χ G * v))) :=
                  mul_le_mul_of_nonneg_left hFn hc
              _ = CS * Eig.Cnab χ k * (Real.exp (σ' * (u - v)) *
                    (A * Prelim.jap v ^ p + ηb * κ * Real.exp (Eig.sigma χ G * v))) := by ring
              _ ≤ CS * Eig.Cnab χ k *
                  (A * Prelim.jap u ^ p * Real.exp (σ' * (u - v)) +
                    ηb * κ * Real.exp (σ' * u) * Real.exp ((Eig.sigma χ G - σ') * v)) :=
                  mul_le_mul_of_nonneg_left hpt (mul_nonneg hCS0 hCn)
        _ = CS * Eig.Cnab χ k * ∫ v in (0 : ℝ)..u,
              (A * Prelim.jap u ^ p * Real.exp (σ' * (u - v)) +
                ηb * κ * Real.exp (σ' * u) * Real.exp ((Eig.sigma χ G - σ') * v)) :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ CS * Eig.Cnab χ k *
              (A * Prelim.jap u ^ p * Real.exp (σ' * u) / σ' +
                ηb * κ * Real.exp (Eig.sigma χ G * u) / (Eig.sigb χ - σ')) :=
            mul_le_mul_of_nonneg_left hgle (mul_nonneg hCS0 hCn)
    · have h0 : I = 0 := intervalIntegral.integral_undef hint
      rw [h0, map_zero, sub_zero, norm_zero]
      exact hRHS
  -- the final algebra
  rw [hdec]
  set J := Prelim.jap u ^ p with hJ
  set e' := Real.exp (σ' * u) with he'
  set e := Real.exp (Eig.sigma χ G * u) with he
  set Cn := Eig.Cnab χ k with hCndef
  have hJ1 : 1 ≤ J := one_le_pow₀ (Prelim.one_le_jap u)
  have he'0 : 0 ≤ e' := (Real.exp_pos _).le
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hAJe : 0 ≤ A * J * e' := by positivity
  have hEe : 0 ≤ ηb * κ * e := by positivity
  have ha : 0 ≤ Cn / σ' := div_nonneg hCn hσ'pos.le
  have hb : 0 ≤ Cn / (Eig.sigb χ - σ') := div_nonneg hCn hgap.le
  have hsplit : CS * Cn * (A * J * e' / σ' + ηb * κ * e / (Eig.sigb χ - σ')) =
      CS * (Cn / σ') * (A * J * e') + CS * (Cn / (Eig.sigb χ - σ')) * (ηb * κ * e) := by
    ring
  have i1 : CS * e' * A ≤ CS * (A * J * e' + ηb * κ * e) := by
    have : e' * A ≤ A * J * e' + ηb * κ * e := by
      have : e' * A ≤ A * J * e' := by
        have := mul_le_mul_of_nonneg_left hJ1 (mul_nonneg hA he'0)
        nlinarith
      linarith
    calc CS * e' * A = CS * (e' * A) := by ring
      _ ≤ CS * (A * J * e' + ηb * κ * e) := mul_le_mul_of_nonneg_left this hCS0
  have i2 : CS * (Cn / σ') * (A * J * e') ≤ CS * (Cn / σ') * (A * J * e' + ηb * κ * e) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hEe) (mul_nonneg hCS0 ha)
  have i3 : CS * (Cn / (Eig.sigb χ - σ')) * (ηb * κ * e) ≤
      CS * (Cn / (Eig.sigb χ - σ')) * (A * J * e' + ηb * κ * e) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hAJe) (mul_nonneg hCS0 hb)
  have hClin : Clin χ k σ' CS * (A * J * e' + ηb * κ * e) =
      CS * (A * J * e' + ηb * κ * e) + CS * (Cn / σ') * (A * J * e' + ηb * κ * e) +
        CS * (Cn / (Eig.sigb χ - σ')) * (A * J * e' + ηb * κ * e) := by
    unfold Clin
    ring
  calc ‖Lin.S χ k G u (w0Y - Eig.R χ k G w0Y) + (I - Eig.R χ k G I)‖
      ≤ ‖Lin.S χ k G u (w0Y - Eig.R χ k G w0Y)‖ + ‖I - Eig.R χ k G I‖ := norm_add_le _ _
    _ ≤ CS * e' * A + CS * Cn * (A * J * e' / σ' + ηb * κ * e / (Eig.sigb χ - σ')) :=
        add_le_add h1 h2
    _ ≤ Clin χ k σ' CS * (A * J * e' + ηb * κ * e) := by
        rw [hsplit, hClin]
        linarith

end NonUniqueEuler.OneRing.LinearPartH
