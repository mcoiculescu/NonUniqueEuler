import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec5.Quiet
import NonUniqueEuler.I.Sec6.RingConfig
import NonUniqueEuler.I.Sec6.FieldContinuity
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.CkNorm.Basic
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Norm

/-!
# Proof: `thm:quiet` applied to ring `i` in ring-`i` units (bridge)

Proof of `I/Sec9/QuietRing.lean` (`quiet_ring`), following its proof sketch
(`09_relay.tex:71-84`, `06_datum.tex:138-156`, `:323-330`).

* `T < 0`: nothing to prove.
* `T = 0`: only `τ = 0`. `Φ_0 = id` (`maxFlow` at its own initial time is the identity, also in
  the junk case), `w_i(0) = Φ - Φ = 0` (through the configuration `P.ringConfig i`, whose
  `Φ̃_0⁻¹ = id` and `ω_r(0) = Φ`), `wlin_i(0) = 0` (`toY 0 = 0`), `maj_i(0) = 0`; the support
  statement follows from `supp Φ ⊂ {a ≤ |y| ≤ 1}` (`lem:ring-facts`).
* `T > 0`: `thm:quiet` (`OneRing.quiet`, `quietConsts_spec`) applied to `c = P.ringConfig i` on
  `[0,T]` (`ringConfig_hyp` with `T' = T/A_i`), with the measurable majorant
  `η = 1_{[0,T]} η_i` (continuity of `η_i` on `[0,T]`, `eta_continuous`), and
  `‖h_i(τ)‖_{C^{M_h}(N')} ≤ η^in_i(τ) + η^out_i(τ)` (`C^{M_h}` membership from
  `hIn_continuous`, `hOut_continuous`, and `MemCk.add`). The conclusions are translated with
  `ringConfig_units`; the support statement `S_i(t) ⊂ r_i𝒩₋` is derived from the radial bound
  (`C_Δ maj_i ≤ C_Δ maj_* ≤ a/16`) and `supp Φ ⊂ {a ≤ |y| ≤ 1}`, exactly as `lem:annuli`.

Helper lemmas are in the namespace `Relay.QuietRingAux` (to avoid clashes);
the generic facts on `Y^s(K)` are copied from `H/Sec9/Handoff/Bridge.lean` (which cannot be
imported here (import rules, `README.md`)).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace QuietRingAux

open Sect Sob

/-! ### Flows at time `0` -/

/-- The maximal flow at its own initial time is the identity (also in the junk case). -/
theorem maxFlow_self {F : ℝ → ℂ → ℂ} {U : Set (ℝ × ℂ)} {s : ℝ} {y : ℂ} :
    Smooth.maxFlow F U s s y = y := by
  classical
  by_cases h : ∃ (J : Set ℝ) (γ : ℝ → ℂ), Smooth.IsMaxSol F U s y J γ
  · exact (Smooth.isMaxSol_maxFlow h).init
  · rw [Smooth.maxFlow, dite_eq_right h]

/-- `Φ_0 = id` for the flow of an approximation. -/
theorem approx_flow_zero (P : Approx) (x : ℂ) : P.flow 0 x = x := by
  simp only [Approx.flow, Smooth.flowOf]
  exact maxFlow_self

/-- `Φ_0⁻¹ = id` for the flow of a configuration. -/
theorem config_flowInv_zero (c : OneRing.RingConfig) (x : ℂ) : c.flowInv 0 x = x := by
  simp only [OneRing.RingConfig.flowInv, Smooth.flowInv, Smooth.flowOf]
  exact maxFlow_self

/-! ### Elements of `Y^s(K)` (copied from `H/Sec9/Handoff/Bridge.lean`) -/

/-- An element of `Y^s(K)` is determined by its function. -/
theorem Y_ext_fn {s : ℕ} {K : Set ℂ} {w₁ w₂ : Y s K} (h : w₁.fn =ᵐ[volume] w₂.fn) : w₁ = w₂ := by
  have : Y.toHk w₁ = Y.toHk w₂ := Hk.ext_fn h
  exact Subtype.ext (show (w₁ : SobTuple s) = w₂ from
    congrArg (fun F : Hk s => (F : SobTuple s)) this)

/-- The function of `0`. -/
theorem Y_fn_zero {s : ℕ} {K : Set ℂ} : (0 : Y s K).fn =ᵐ[volume] (0 : ℂ → ℂ) := by
  have h : (((0 : Y s K) : SobTuple s)).ofLp (idx0 s) = 0 := rfl
  have h2 : (0 : Y s K).fn = ((((0 : Y s K) : SobTuple s)).ofLp (idx0 s) : ℂ → ℂ) := rfl
  rw [h2, h]
  exact Lp.coeFn_zero _ _ _

/-- `toY s K 0 = 0`. -/
theorem toY_zero (s : ℕ) (K : Set ℂ) : toY s K (0 : ℂ → ℂ) = 0 :=
  Y_ext_fn ((toY_spec ⟨0, Y_fn_zero⟩).trans Y_fn_zero.symm)

/-- The zero function lies in every `H^s`. -/
theorem memH_zero (s : ℕ) : MemH s (0 : ℂ → ℂ) := by
  refine ⟨MemLp.zero, fun γ _ => ⟨0, MemLp.zero, fun φ _ => ?_⟩⟩
  simp

/-- `‖0‖_{H^k} = 0`. -/
theorem normH_zero_fn (k : ℕ) : normH k (0 : ℂ → ℂ) = 0 := by
  have h := ((memH_zero k).const_smul (0 : ℂ)).2
  rw [zero_smul, norm_zero, zero_mul] at h
  exact h

/-- A function that vanishes a.e. has zero `H^k` norm. -/
theorem normH_eq_zero_of_ae {k : ℕ} {f : ℂ → ℂ} (hf : f =ᵐ[volume] 0) : normH k f = 0 := by
  rw [((memH_zero k).congr_ae hf.symm).2, normH_zero_fn]

/-! ### The linear response only sees the field on `[0,τ]` -/

/-- `wlin(τ)` depends only on `h` on `[0,τ]`. -/
theorem wlin_congr {χ : ℝ → ℝ} {s : ℕ} {G : ℝ} {h h' : ℝ → ℂ → ℂ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hh : ∀ v ∈ Icc (0 : ℝ) τ, h v = h' v) :
    OneRing.wlin χ s G h τ = OneRing.wlin χ s G h' τ := by
  simp only [OneRing.wlin_def, OneRing.wlin0_def]
  congr 1
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [uIcc_of_le hτ] at hv
  simp only [OneRing.forcing_eq, hh v hv]

/-- `wlin(0) = 0`. -/
theorem wlin_zero (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) (h : ℝ → ℂ → ℂ) :
    OneRing.wlin χ s G h 0 = 0 := by
  simp only [OneRing.wlin_def, OneRing.wlin0_def, toY_zero, map_zero, zero_add,
    intervalIntegral.integral_same]

/-! ### Supports in ring-`i` units -/

/-- `‖r⁻¹ w‖ = r⁻¹ ‖w‖` for `r > 0`. -/
theorem norm_inv_mul {r : ℝ} (hr : 0 < r) (w : ℂ) :
    ‖((r : ℝ) : ℂ)⁻¹ * w‖ = r⁻¹ * ‖w‖ := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

/-- For `1 ≤ i < n`, a point of `S_i = supp f^{(n)}_i = supp A_iΦ(·/r_i)` is `r_i y` with
`y ∈ supp Φ`. -/
theorem mem_tsupport_phi {P : Approx} {i : ℕ} (hi : 1 ≤ i) (hin : i < P.n) {x : ℂ}
    (hx : x ∈ P.S i) : ((P.r i : ℝ) : ℂ)⁻¹ * x ∈ tsupport (ringPhi P.χ) := by
  have hterm : P.term i = fun x => P.A i * ringPhi P.χ (x / ((P.r i : ℝ) : ℂ)) := by
    funext x
    exact approxTerm_of_lt hi hin x
  have h1 : x ∈ tsupport (fun x => P.A i * ringPhi P.χ (x / ((P.r i : ℝ) : ℂ))) := by
    rw [← hterm]
    exact hx
  have h2 : x ∈ tsupport (fun x => ringPhi P.χ (x / ((P.r i : ℝ) : ℂ))) :=
    tsupport_mul_subset_right (f := fun _ => P.A i)
      (g := fun x => ringPhi P.χ (x / ((P.r i : ℝ) : ℂ))) h1
  have h3 := tsupport_comp_subset_preimage (ringPhi P.χ)
    (f := fun x : ℂ => x / ((P.r i : ℝ) : ℂ)) (by fun_prop) h2
  simpa only [mem_preimage, div_eq_inv_mul] using h3

/-- **Support from the radial bound** (`lem:annuli` in ring-`i` units): if every trajectory of
ring `i` moves radially by at most `r_i δ` up to time `t`, with `δ ≤ a/16`, then
`S_i(t) ⊂ r_i 𝒩₋`. -/
theorem supp_of_radial {P : Approx} (hP : P.Valid) {i : ℕ} (hi : 1 ≤ i) (hin : i < P.n)
    {t δ : ℝ} (hδ : δ ≤ a / 16)
    (hrad : ∀ x ∈ P.S i, |‖P.flow t x‖ - ‖x‖| ≤ P.r i * δ) :
    P.St i t ⊆ P.Nmk i := by
  rintro z ⟨x, hx, rfl⟩
  have hr := hP.r_pos i
  obtain ⟨-, -, -, -, -, hsupp, ha0, ha1⟩ := ringFacts_of_admissible hP.admissible
  have hy := hsupp (mem_tsupport_phi hi hin hx)
  simp only [mem_ofPred_eq, norm_inv_mul hr] at hy
  have h' : |(P.r i)⁻¹ * ‖P.flow t x‖ - (P.r i)⁻¹ * ‖x‖| ≤ δ := by
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hr), inv_mul_le_iff₀ hr]
    exact hrad x hx
  rw [abs_le] at h'
  rw [Approx.Nmk, mem_scaleSet, annNm, Sect.closedAnnulus, mem_ofPred_eq, norm_inv_mul hr]
  constructor <;> linarith [h'.1, h'.2, hy.1, hy.2]

/-- **The radial bound in ring-`i` units**: "`ω_r` moves radially by at most `δ` on `[0,τ]`" for
`c = P.ringConfig i` gives `||Φ_{t'}(x)| - |x|| ≤ r_i δ` for `x ∈ S_i`, `t' ∈ [0, τ/A_i]`. -/
theorem radial_of_moves {P : Approx} (hP : P.Valid) (hN : NumericalHypothesis P.χ) {i : ℕ}
    (hi : 1 ≤ i) (hin : i < P.n) {τ δ : ℝ} (hmov : (P.ringConfig i).MovesRadially τ δ) :
    ∀ x ∈ P.S i, ∀ t' ∈ Icc (0 : ℝ) (τ / P.A i), |‖P.flow t' x‖ - ‖x‖| ≤ P.r i * δ := by
  intro x hx t' ht'
  obtain ⟨-, -, hflow, -⟩ := Approx.ringConfig_units P hP hN hi hin.le
  have hA := hP.A_pos i
  have hr := hP.r_pos i
  have hy : ((P.r i : ℝ) : ℂ)⁻¹ * x ∈ tsupport (P.ringConfig i).ring0 := by
    rw [hP.ringConfig_ring0 hi hin]
    exact mem_tsupport_phi hi hin hx
  have hτ' : P.A i * t' ∈ Icc (0 : ℝ) τ := by
    refine ⟨mul_nonneg hA.le ht'.1, ?_⟩
    have := ht'.2
    rw [le_div_iff₀ hA] at this
    linarith
  have h := hmov _ hy _ hτ'
  rw [hflow] at h
  have e1 : P.A i * t' / P.A i = t' := by field_simp
  have hrC : ((P.r i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have e2 : ((P.r i : ℝ) : ℂ) * (((P.r i : ℝ) : ℂ)⁻¹ * x) = x := by
    rw [← mul_assoc, mul_inv_cancel₀ hrC, one_mul]
  rw [e1, e2, norm_inv_mul hr, norm_inv_mul hr, ← mul_sub, abs_mul,
    abs_of_pos (inv_pos.2 hr), inv_mul_le_iff₀ hr] at h
  exact h

end QuietRingAux

open QuietRingAux

/-- **`thm:quiet` for ring `i`** (`09_relay.tex:71-84`): if the hypotheses of `thm:quiet` hold for
ring `i` on the ring-`i` time interval `[0,T]` (with `G = G_i`, `h = h_i`, `η = η_i`,
`maj = maj_i`), then so do its conclusions (a)–(c), with the constants of (SA2). -/
theorem quiet_ring (S : Standing) (hS : S.Holds) {i : ℕ} {T : ℝ} (h : S.QuietHyp i T) :
    S.QuietConcl i T := by
  have hP := hS.valid
  have hN := hS.hN
  have hsigb : 0 < Eig.sigb S.P.χ := by linarith [hS.σ'_gt, hS.σ'_lt_sigb]
  obtain ⟨-, hCQ, hCΔ, hCΔm, hmain⟩ := OneRing.quietConsts_spec
    (OneRing.quiet S.P.χ hP.admissible hN hS.three_le_sh S.two_le_NQ (S.Lam_le_NQ_mul hsigb))
  have hδ : ∀ τ ∈ Icc (0 : ℝ) T, S.CDelta * S.maj i τ ≤ a / 16 := fun τ hτ =>
    (mul_le_mul_of_nonneg_left (h.maj_le τ hτ) hCΔ).trans hCΔm
  have hA := hP.A_pos i
  rcases lt_trichotomy T 0 with hT | hT | hT
  · -- `T < 0`: `[0,T]` is empty.
    have hE : ∀ τ ∈ Icc (0 : ℝ) T, False := fun τ hτ => absurd (hτ.1.trans hτ.2) (not_le.2 hT)
    exact ⟨fun τ hτ => (hE τ hτ).elim, fun τ hτ => (hE τ hτ).elim, fun τ hτ => (hE τ hτ).elim,
      fun τ hτ => (hE τ hτ).elim⟩
  · -- `T = 0`: only `τ = 0`.
    subst hT
    have hτ0 : ∀ τ ∈ Icc (0 : ℝ) 0, τ = 0 := fun τ hτ => le_antisymm hτ.2 hτ.1
    have hrad0 : ∀ x ∈ S.P.S i, ∀ t' ∈ Icc (0 : ℝ) (0 / S.P.A i),
        |‖S.P.flow t' x‖ - ‖x‖| ≤ S.P.r i * (S.CDelta * S.maj i 0) := by
      intro x hx t' ht'
      rw [zero_div] at ht'
      rw [hτ0 t' ht', approx_flow_zero, sub_self, abs_zero, S.maj_zero, mul_zero, mul_zero]
    have hw0 : S.P.w i 0 = 0 := by
      obtain ⟨-, -, -, -, -, -, hw, -⟩ := Approx.ringConfig_units S.P hP hN h.one_le h.lt_n.le
      have hw' := hw 0 le_rfl
      rw [zero_div] at hw'
      rw [← hw', OneRing.RingConfig.w_zero_of_flowInv_zero _ _ (config_flowInv_zero _)]
      funext x
      simp [OneRing.RingConfig.pert0, hP.ringConfig_ring0 h.one_le h.lt_n]
    have hwlin0 : S.wlinK i 0 = 0 := wlin_zero _ _ _ _
    refine ⟨fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_⟩
    · obtain rfl := hτ0 τ hτ
      exact hrad0
    · obtain rfl := hτ0 τ hτ
      exact supp_of_radial hP h.one_le h.lt_n (hδ 0 ⟨le_rfl, le_rfl⟩)
        fun x hx => hrad0 x hx (0 / S.P.A i) ⟨by rw [zero_div], le_rfl⟩
    · obtain rfl := hτ0 τ hτ
      rw [zero_div, hw0, hwlin0, S.maj_zero]
      have hae : ((0 : ℂ → ℂ) - (0 : Sect.Y S.sh annN).fn) =ᵐ[volume] 0 := by
        filter_upwards [Y_fn_zero (s := S.sh) (K := annN)] with x hx
        simp [hx]
      rw [normH_eq_zero_of_ae hae]
      simp
    · obtain rfl := hτ0 τ hτ
      rw [zero_div, hw0, S.maj_zero, mul_zero, normH_zero_fn]
  · -- `T > 0`: apply `thm:quiet` to `P.ringConfig i` on `[0,T]`.
    obtain ⟨-, -, -, -, -, -, hw, hGc, hh⟩ :=
      Approx.ringConfig_units S.P hP hN h.one_le h.lt_n.le
    have hTA : 0 < T / S.P.A i := div_pos hT hA
    have hHyp : (S.P.ringConfig i).Hyp T := by
      have := Approx.ringConfig_hyp S.P hP hN h.one_le h.lt_n.le hTA h.hdef
      rwa [mul_div_cancel₀ T hA.ne'] at this
    have hring0 := hP.ringConfig_ring0 h.one_le h.lt_n
    have hGmem : (S.P.ringConfig i).G ∈ Icc (0 : ℝ) Gbar := by
      rw [hGc]
      exact h.G_mem
    have hIcc : Icc (S.P.A i * 0) (S.P.A i * (T / S.P.A i)) = Icc 0 T := by
      rw [mul_zero, mul_div_cancel₀ T hA.ne']
    -- the measurable majorant `η = 1_{[0,T]} η_i`
    have hcont : ContinuousOn (S.eta i) (Icc 0 T) := by
      have := (Approx.eta_continuous S.P hP hN h.one_le h.lt_n.le le_rfl S.Mh).2.2 h.hdef
      rwa [hIcc] at this
    classical
    let η : ℝ → ℝ := (Icc (0 : ℝ) T).piecewise (S.eta i) 0
    have hηmeas : Measurable η :=
      hcont.measurable_piecewise continuousOn_const measurableSet_Icc
    have hηeq : ∀ v ∈ Icc (0 : ℝ) T, η v = S.eta i v := fun v hv =>
      Set.piecewise_eq_of_mem _ _ _ hv
    have hmajeq : ∀ τ ∈ Icc (0 : ℝ) T,
        OneRing.maj (Eig.sigma S.P.χ (S.P.ringConfig i).G) η τ = S.maj i τ := by
      intro τ hτ
      rw [hGc]
      show _ = OneRing.maj (S.P.sigma i) (S.P.eta S.Mh i) τ
      unfold OneRing.maj
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [uIcc_of_le hτ.1] at hv
      show Real.exp (Eig.sigma S.P.χ (S.P.G i) * (τ - v)) * η v =
        Real.exp (S.P.sigma i * (τ - v)) * S.P.eta S.Mh i v
      rw [hηeq v ⟨hv.1, hv.2.trans hτ.2⟩]
      rfl
    -- `‖h_i(t)‖_{C^{M_h}(N')} ≤ η^in_i(t) + η^out_i(t) = η(t) ≤ 1`
    have hfield : ∀ t ∈ Icc (0 : ℝ) T,
        normCk S.Mh annN' ((S.P.ringConfig i).h t) ≤ η t ∧ η t ≤ 1 := by
      intro t ht
      have hcf : (S.P.ringConfig i).h t = S.P.hField i t := funext (hh t ht.1)
      have ht' : t ∈ Icc (S.P.A i * 0) (S.P.A i * (T / S.P.A i)) := by
        rw [hIcc]
        exact ht
      have hin := (Approx.hIn_continuous S.P hP hN h.one_le h.lt_n.le le_rfl
        (fun t ht => (h.hdef t ht).1) S.Mh).1 t ht'
      have hout := (Approx.hOut_continuous S.P hP hN h.one_le h.lt_n.le le_rfl
        (fun t ht => (h.hdef t ht).2) S.Mh).1 t ht'
      have hsum : S.P.hField i t = S.P.hIn i t + S.P.hOut i t := rfl
      rw [hηeq t ht, hcf, hsum]
      exact ⟨(hin.add hout).2, h.eta_le t ht⟩
    have hmajbd : ∀ t ∈ Icc (0 : ℝ) T,
        OneRing.maj (Eig.sigma S.P.χ (S.P.ringConfig i).G) η t ≤ S.majst := by
      intro t ht
      rw [hmajeq t ht]
      exact h.maj_le t ht
    obtain ⟨-, hconc⟩ := hmain (S.P.ringConfig i) T hHyp hring0 hGmem η hηmeas hfield hmajbd
    refine ⟨fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_⟩
    · obtain ⟨hmov, -, -, -⟩ := hconc τ hτ
      rw [hmajeq τ hτ] at hmov
      exact radial_of_moves hP hN h.one_le h.lt_n hmov
    · obtain ⟨hmov, -, -, -⟩ := hconc τ hτ
      rw [hmajeq τ hτ] at hmov
      exact supp_of_radial hP h.one_le h.lt_n (hδ τ hτ) fun x hx =>
        radial_of_moves hP hN h.one_le h.lt_n hmov x hx _ ⟨div_nonneg hτ.1 hA.le, le_rfl⟩
    · obtain ⟨-, -, hlin, -⟩ := hconc τ hτ
      rw [hmajeq τ hτ, hw τ hτ.1, hGc,
        wlin_congr hτ.1 fun v hv => funext (hh v hv.1)] at hlin
      exact hlin
    · obtain ⟨-, -, -, hb⟩ := hconc τ hτ
      rw [hmajeq τ hτ, hw τ hτ.1] at hb
      exact hb

end Relay

end NonUniqueEuler
