import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec9.QuietRing
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec8.Coupling
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec6.FieldContinuity
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec5.Majorant
import NonUniqueEuler.I.Sec5.Quiet
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.H.Sec9.Handoff.Bridge

/-!
# Proof: `lem:handoff` and `eq:handoff` (the hand-off of a quiet ring at `t♯_k`)

Proof of `I/Sec9/Handoff.lean` (same declaration, statement copied verbatim). Manuscript
`09_relay.tex:863-924`. Write `τ♯ = t̄♯_k`, `maj = maj_k`, `c = c^in_k`, `G = G_k`.

1. `t♯_k > 0` (`lem:clock`(1) at level `k+1`), so `τ♯ ≥ 0` and `τ♯/A_k = t♯_k`. By (i) and
   `thm:quiet` for ring `k` (`quiet_ring`): `S_k(t♯_k) ⊂ 𝒩₋_k`, `‖w_k(t♯_k)‖_{H^{s_h}} ≤ C_Q maj(τ♯)`
   and `‖w_k(t♯_k) - wlin(τ♯)‖_{H^{s_h}} ≤ C_Q maj(τ♯)²`. In particular `S_k(t♯_k) ⊂ N_k`, so
   `w_k(t♯_k) ∈ X^{s_h}` (`lem:regions-basic`(4)), and `|ℓ_*(w_k(t♯_k)) - ℓ_*(wlin(τ♯))| ≤
   ‖ℓ_*‖C_Q maj(τ♯)²` (`HandoffAux.norm_ellFn_sub_le`, `lem:uniform`); this is
   `cor:quiet-handoff` for ring `k`.
2. `lem:coupling`(2),(3): `-h^in_k·∇Φ`, `-h^out_k·∇Φ ∈ C([0,τ♯];X^s)` and
   `wlin = wlin_{in,k} + wlin_{out,k}` (at level `s_h`); `ℓ_*(G)` is additive on `Y^{s_h}(N)`.
   `ℓ_*(G)(wlin_{in,k}(τ♯))` is the same at levels `s_h` and `0` (`HandoffAux.ellFn_wlin_level`),
   i.e. it is `c`. So `ℓ_*(wlin(τ♯)) = c + ℓ_*(wlin_{out,k}(τ♯))`.
3. `ℓ_*(wlin_{out,k}(τ♯)) = ∫₀^{τ♯} e^{λ_k(τ♯-v)}ℓ_*(-h^out_k(v)·∇Φ)dv` (`HandoffAux.ellFn_wlin_eq`:
   `ℓ_*` commutes with the Duhamel integral, `prop:semigroup`). By `lem:uniform`,
   `‖h^out_k‖_{C^0} ≤ η^out_k ≤ θ maj` ((ii)) and (M1) (`lem:majorant`, `σ_k > 0`), the integrand is
   at most `C_lsθ maj(τ♯)`, so the term is `≤ C_lsθτ♯maj(τ♯) ≤ |c|/8` ((ii), (iii)).
4. (iv), (iii): `‖ℓ_*‖C_Q maj² ≤ maj/(2K₁) ≤ |c|/4`. Hence `|κ♯_k - |c|| ≤ 3|c|/8`, which gives the
   first two claims; then `maj(τ♯) ≤ ½K₁|c| ≤ K₁κ♯_k` and `‖w_k(t♯_k)‖_{H^{s_h}} ≤ C_Q K₁κ♯_k`.

Deviation (none of substance): the manuscript's step 1 cites `cor:quiet-handoff`; here the same
inequality is derived directly from `thm:quiet`(b) for ring `k` (`QuietConcl.lin`), as in the
proof of `cor:quiet-handoff`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped Interval

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace HandoffAux

/-- `t♯_k > 0` for `k < n` when the clock is defined up to level `k+1` (`lem:clock`(1)). -/
theorem tsh_pos (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall)
    {k : ℕ} (hkn : k < P.n) (hc : P.ClockUpTo (k + 1)) : 0 < P.tsh k := by
  have hmem : k + 1 ∈ Finset.Icc (k + 1) P.n := Finset.mem_Icc.mpr ⟨le_rfl, hkn⟩
  have hord := Approx.clock_order P hP hN hG (Nat.le_add_left 1 k) hc
  have hT : 0 < P.T (k + 1) := lt_of_le_of_lt (hord.2.2.2 (k + 1) hmem) (hord.1 (k + 1) hmem)
  rw [P.tsh_eq_T_add hkn]
  have := hP.Tpin_pos
  have := hP.A_pos (k + 1)
  positivity

/-- `𝒩₋_k ⊂ N_k`. -/
theorem Nmk_subset_Nk (P : Approx) (k : ℕ) : P.Nmk k ⊆ P.Nk k := by
  intro x hx
  have ha := zero_lt_a
  have hx' : (P.r k : ℂ)⁻¹ * x ∈ annNm := hx
  show (P.r k : ℂ)⁻¹ * x ∈ annN
  obtain ⟨h1, h2⟩ := hx'
  exact ⟨by linarith, by linarith⟩

/-- The final arithmetic of `lem:handoff` (`09_relay.tex:917-921`): from
`|E - L| ≤ X m²`, `L = c + O`, `|O| ≤ Y m`, `X K₁ m ≤ ½`, `Y K₁ ≤ ¼`, `m ≤ ½K₁|c|` (`m ≥ 0`,
`K₁ > 0`), `|E - c| ≤ 3|c|/8`. -/
theorem norm_sub_le_aux {E c O L : ℂ} {m K₁ X Y : ℝ} (hK₁ : 0 < K₁) (hm : 0 ≤ m)
    (hEL : ‖E - L‖ ≤ X * m ^ 2) (hL : L = c + O) (hO : ‖O‖ ≤ Y * m)
    (hiv : X * K₁ * m ≤ 1 / 2) (hii : Y * K₁ ≤ 1 / 4) (hiii : m ≤ 1 / 2 * K₁ * ‖c‖) :
    ‖E - c‖ ≤ 3 / 8 * ‖c‖ := by
  have h1 : X * m ^ 2 ≤ 1 / 4 * ‖c‖ := by
    have h2 : X * m ^ 2 * K₁ ≤ m / 2 := by
      have := mul_le_mul_of_nonneg_right hiv hm
      nlinarith
    have h3 : X * m ^ 2 * K₁ ≤ 1 / 4 * ‖c‖ * K₁ := by nlinarith
    exact le_of_mul_le_mul_right h3 hK₁
  have h4 : Y * m ≤ 1 / 8 * ‖c‖ := by
    have h5 : Y * m * K₁ ≤ m / 4 := by
      have := mul_le_mul_of_nonneg_right hii hm
      nlinarith
    have h6 : Y * m * K₁ ≤ 1 / 8 * ‖c‖ * K₁ := by nlinarith
    exact le_of_mul_le_mul_right h6 hK₁
  have hsplit : E - c = (E - L) + O := by rw [hL]; ring
  rw [hsplit]
  calc ‖(E - L) + O‖ ≤ ‖E - L‖ + ‖O‖ := norm_add_le _ _
    _ ≤ X * m ^ 2 + Y * m := add_le_add hEL hO
    _ ≤ 1 / 4 * ‖c‖ + 1 / 8 * ‖c‖ := add_le_add h1 h4
    _ = 3 / 8 * ‖c‖ := by ring

/-- **The outer term** (`09_relay.tex:900-912`): under the hypotheses of `lem:handoff`,
`|ℓ_*(G_k)(wlin_{out,k}(τ♯))| ≤ C_lsθτ♯maj_k(τ♯)` (at level `s_h`). -/
theorem ellFn_wlinOut_le (S : Standing) (hS : S.Holds) {θ K₁ : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hkn : k < S.P.n) (hc : S.P.ClockUpTo (k + 1)) (h : S.HandoffHyp θ K₁ k)
    (hτ0 : 0 ≤ S.P.tash k)
    (hdef : ∀ t ∈ Icc (0 : ℝ) (S.P.tsh k), S.P.HDefined k t) :
    ‖Eig.ellFn S.P.χ (S.P.G k) (S.P.wlinOut S.sh k (S.P.tash k)).fn‖ ≤
      Eig.Cls S.P.χ * θ * S.maj k (S.P.tash k) * S.P.tash k := by
  have hP := hS.valid
  have hN := hS.hN
  have hχ := hS.admissible
  obtain ⟨hsigb, -, hGs, hlev⟩ := standing_levels S hS
  have hkmem : k ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hk, hkn.le⟩
  obtain ⟨-, hG, hσb⟩ := hlev k hkmem
  have hσ : 0 < S.P.sigma k := lt_of_lt_of_le hsigb hσb
  set τ := S.P.tash k with hτdef
  have hτmem : τ ∈ Icc (0 : ℝ) τ := ⟨hτ0, le_rfl⟩
  -- the forcing of the outer field is continuous into `X^{s_h}` (`lem:coupling`(3))
  have hc3 := Kick.coupling_three S.P hP hN hGs hk hkn hc hdef S.sh
  have heq := HandoffAux.ellFn_wlin_eq S.P.χ hχ hN hG hc3.1 hτmem
  have hW : S.P.wlinOut S.sh k τ = OneRing.wlin S.P.χ S.sh (S.P.G k) (S.P.hOut k) τ := rfl
  rw [hW, heq]
  -- the integrand
  have hout : OneRing.CkPathOn S.Mh annN' (Icc 0 τ) (S.P.hOut k) := by
    have := Approx.hOut_continuous S.P hP hN hk hkn.le (le_refl 0)
      (fun t ht => (hdef t ht).2) S.Mh
    rwa [mul_zero, ← Approx.tash_def] at this
  have hηint : IntegrableOn (S.P.eta S.Mh k) (Icc 0 τ) := by
    have := (Approx.eta_continuous S.P hP hN hk hkn.le (le_refl 0) S.Mh).2.2 hdef
    rw [mul_zero, ← Approx.tash_def] at this
    exact this.integrableOn_Icc
  have hM1 := (OneRing.majorant_of_pos hσ hηint fun t _ => S.P.eta_nonneg _ _ _).1
  have hellle : ‖Eig.ell S.P.χ 0 (S.P.G k)‖ ≤ Eig.ellNorm S.P.χ :=
    ((Eig.uniform_constants S.P.χ hχ hN).2.2.2.2.2.2.2.2 (S.P.G k) hG).2.2.2.1
  have hEN : 0 ≤ Eig.ellNorm S.P.χ := (ContinuousLinearMap.opNorm_nonneg _).trans hellle
  have hCls : 0 ≤ Eig.Cls S.P.χ :=
    mul_nonneg hEN ENNReal.toReal_nonneg
  have hCθ : 0 ≤ Eig.Cls S.P.χ * θ := mul_nonneg hCls h.θ_nonneg
  have hptw : ∀ v ∈ Ι (0 : ℝ) τ,
      ‖Complex.exp (Eig.lam S.P.χ (S.P.G k) * ((τ - v : ℝ) : ℂ)) *
          Eig.ellFn S.P.χ (S.P.G k) (OneRing.forcing S.P.χ (S.P.hOut k) v)‖ ≤
        Eig.Cls S.P.χ * θ * S.maj k τ := by
    intro v hv
    rw [uIoc_of_le hτ0] at hv
    have hvI : v ∈ Icc (0 : ℝ) τ := ⟨hv.1.le, hv.2⟩
    have hmem : MemCk S.Mh annN' (S.P.hOut k v) := hout.1 v hvI
    have hls : ‖Eig.ellFn S.P.χ (S.P.G k) (OneRing.forcing S.P.χ (S.P.hOut k) v)‖ ≤
        Eig.Cls S.P.χ * normCk 0 annN' (S.P.hOut k v) :=
      (Eig.uniform_inequalities S.P.χ hχ hN).1 (S.P.G k) hG (S.P.hOut k v)
        (hmem.mono_order (Nat.zero_le _))
    have hC0 : normCk 0 annN' (S.P.hOut k v) ≤ S.etaOut k v :=
      normCk_mono_order hmem (Nat.zero_le _)
    have hθv : S.etaOut k v ≤ θ * S.maj k v := h.etaOut_le v hvI
    have hexp : ‖Complex.exp (Eig.lam S.P.χ (S.P.G k) * ((τ - v : ℝ) : ℂ))‖ =
        Real.exp (S.P.sigma k * (τ - v)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Approx.sigma, Eig.sigma]
    have hM := (hM1 v τ hvI.1 hvI.2 le_rfl).1
    have hM' : Real.exp (S.P.sigma k * (τ - v)) * S.maj k v ≤ S.maj k τ := hM
    rw [norm_mul, hexp]
    calc Real.exp (S.P.sigma k * (τ - v)) *
          ‖Eig.ellFn S.P.χ (S.P.G k) (OneRing.forcing S.P.χ (S.P.hOut k) v)‖
        ≤ Real.exp (S.P.sigma k * (τ - v)) * (Eig.Cls S.P.χ * (θ * S.maj k v)) := by
          refine mul_le_mul_of_nonneg_left (hls.trans ?_) (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left (hC0.trans hθv) hCls
      _ = Eig.Cls S.P.χ * θ * (Real.exp (S.P.sigma k * (τ - v)) * S.maj k v) := by ring
      _ ≤ Eig.Cls S.P.χ * θ * S.maj k τ := mul_le_mul_of_nonneg_left hM' hCθ
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hptw
  rwa [sub_zero, abs_of_nonneg hτ0] at hint

end HandoffAux

/-- **`lem:handoff`** (`09_relay.tex:863-885`). Assume (SA), (Det), `K₁ > 0`, `1 ≤ k < n`, the clock
defined up to level `k+1`, and (i)–(iv) (`S.HandoffHyp θ K₁ k`). Then `eq:handoff` holds with
`C_hand = K₁C_Q`: `½|c^in_k| ≤ κ♯_k ≤ (3/2)|c^in_k|`, `maj_k(t̄♯_k) ≤ K₁κ♯_k`,
`‖w_k(t♯_k)‖_{H^{s_h}} ≤ K₁C_Qκ♯_k` and `S_k(t♯_k) ⊆ 𝒩₋_k` (`supp(Φ + w_k(t♯_k)) ⊂ 𝒩₋`). -/
theorem handoff (S : Standing) (hS : S.Holds) (hDet : S.Det) {θ K₁ : ℝ} (hK₁ : 0 < K₁) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k < S.P.n) (hc : S.P.ClockUpTo (k + 1)) (h : S.HandoffHyp θ K₁ k) :
    1 / 2 * ‖S.P.cinK k‖ ≤ S.P.ksh k ∧ S.P.ksh k ≤ 3 / 2 * ‖S.P.cinK k‖ ∧
      S.maj k (S.P.tash k) ≤ K₁ * S.P.ksh k ∧
      Sob.normH S.sh (S.P.w k (S.P.tsh k)) ≤ K₁ * S.CQ * S.P.ksh k ∧
      S.P.St k (S.P.tsh k) ⊆ S.P.Nmk k := by
  -- (Det) is a standing assumption of the lemma; the proof does not use it.
  have _ := hDet
  have hP := hS.valid
  have hN := hS.hN
  have hχ := hS.admissible
  obtain ⟨hsigb, -, hGs, hlev⟩ := standing_levels S hS
  have hkmem : k ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hk, hkn.le⟩
  obtain ⟨-, hG, -⟩ := hlev k hkmem
  have hA : 0 < S.P.A k := hP.A_pos k
  have htsh : 0 < S.P.tsh k := HandoffAux.tsh_pos S.P hP hN hGs hkn hc
  have hτ0 : 0 ≤ S.P.tash k := (mul_pos hA htsh).le
  have hτA : S.P.tash k / S.P.A k = S.P.tsh k := by
    rw [Approx.tash_def]
    field_simp
  have hdef : ∀ t ∈ Icc (0 : ℝ) (S.P.tsh k), S.P.HDefined k t := by
    intro t ht
    exact h.quiet.hdef t (by rwa [hτA])
  have hτmem : S.P.tash k ∈ Icc (0 : ℝ) (S.P.tash k) := ⟨hτ0, le_rfl⟩
  -- Step 1: `thm:quiet` for ring `k` at `τ♯`
  have hQC := quiet_ring S hS h.quiet
  have hsupp := hQC.supp _ hτmem
  have hlin := hQC.lin _ hτmem
  have hbd := hQC.bound _ hτmem
  rw [hτA] at hsupp hlin hbd
  have hCQ : 0 ≤ S.CQ :=
    (OneRing.quietConsts_spec (OneRing.quiet S.P.χ hχ hN hS.three_le_sh S.two_le_NQ
      (S.Lam_le_NQ_mul hsigb))).2.1
  have hmaj0 : 0 ≤ S.maj k (S.P.tash k) := by
    show 0 ≤ OneRing.maj (S.P.sigma k) (S.P.eta S.Mh k) (S.P.tash k)
    unfold OneRing.maj
    exact intervalIntegral.integral_nonneg hτ0 fun v _ =>
      mul_nonneg (Real.exp_pos _).le (S.P.eta_nonneg _ _ _)
  -- `w_k(t♯_k) ∈ X^{s_h}` (`lem:regions-basic`(4))
  have hpert : S.P.PertDefined k (S.P.tsh k) := hsupp.trans (HandoffAux.Nmk_subset_Nk S.P k)
  have hwX : Lin.MemXFn S.sh (S.P.w k (S.P.tsh k)) :=
    (Approx.regions_basic_four S.P hP hN hkmem htsh.le hpert).2.2.2.2.1 S.sh
  -- `cor:quiet-handoff` for ring `k`: `|ℓ_*(w_k(t♯_k)) - ℓ_*(wlin(τ♯))| ≤ ‖ℓ_*‖C_Q maj²`
  have hellle : ‖Eig.ell S.P.χ 0 (S.P.G k)‖ ≤ Eig.ellNorm S.P.χ :=
    ((Eig.uniform_constants S.P.χ hχ hN).2.2.2.2.2.2.2.2 (S.P.G k) hG).2.2.2.1
  have hEN : 0 ≤ Eig.ellNorm S.P.χ := (ContinuousLinearMap.opNorm_nonneg _).trans hellle
  have hEL : ‖Eig.ellFn S.P.χ (S.P.G k) (S.P.w k (S.P.tsh k)) -
      Eig.ellFn S.P.χ (S.P.G k) (S.wlinK k (S.P.tash k)).fn‖ ≤
        Eig.ellNorm S.P.χ * S.CQ * S.maj k (S.P.tash k) ^ 2 := by
    have hkey := HandoffAux.norm_ellFn_sub_le S.P.χ hχ hN hG hwX.1
      (HandoffAux.Y_memH_fn (S.wlinK k (S.P.tash k))).1 hwX.2.1
      (HandoffAux.Y_fn_zero_outside (S.wlinK k (S.P.tash k)))
    calc _ ≤ ‖Eig.ell S.P.χ 0 (S.P.G k)‖ *
          Sob.normH S.sh (S.P.w k (S.P.tsh k) - (S.wlinK k (S.P.tash k)).fn) := hkey
      _ ≤ Eig.ellNorm S.P.χ *
          Sob.normH S.sh (S.P.w k (S.P.tsh k) - (S.wlinK k (S.P.tash k)).fn) :=
        mul_le_mul_of_nonneg_right hellle (Sob.normH_nonneg _ _)
      _ ≤ Eig.ellNorm S.P.χ * (S.CQ * S.maj k (S.P.tash k) ^ 2) :=
        mul_le_mul_of_nonneg_left hlin hEN
      _ = Eig.ellNorm S.P.χ * S.CQ * S.maj k (S.P.tash k) ^ 2 := by ring
  -- Step 2: `ℓ_*(wlin(τ♯)) = c + ℓ_*(wlin_{out,k}(τ♯))` (`lem:coupling`(2),(3))
  have hin : ∀ t ∈ Icc (0 : ℝ) (S.P.tsh k), S.P.HInDefined k t := fun t ht => (hdef t ht).1
  have hc2 := Kick.coupling_two S.P hP hN hGs hk hkn hc hin
  have hc3 := Kick.coupling_three S.P hP hN hGs hk hkn hc hdef S.sh
  have hellw : ∀ w : Sect.Y S.sh annN, Eig.ell S.P.χ S.sh (S.P.G k) w =
      Eig.ellFn S.P.χ (S.P.G k) w.fn :=
    Eig.ell_spec_of_exists (Eig.exists_ell S.P.χ hχ hN hG S.sh)
  have hLsplit : Eig.ellFn S.P.χ (S.P.G k) (S.wlinK k (S.P.tash k)).fn =
      Eig.ellFn S.P.χ (S.P.G k) (S.P.wlinIn S.sh k (S.P.tash k)).fn +
        Eig.ellFn S.P.χ (S.P.G k) (S.P.wlinOut S.sh k (S.P.tash k)).fn := by
    have hsum := hc3.2 _ hτmem
    have hwK : S.wlinK k (S.P.tash k) =
        OneRing.wlin S.P.χ S.sh (S.P.G k) (S.P.hField k) (S.P.tash k) := rfl
    rw [← hellw, hwK, ← hsum, map_add, hellw, hellw]
  have hcin : Eig.ellFn S.P.χ (S.P.G k) (S.P.wlinIn S.sh k (S.P.tash k)).fn = S.P.cinK k :=
    HandoffAux.ellFn_wlin_level S.P.χ hχ hN hG (hc2.1 S.sh) (hc2.1 0) hτmem
  rw [hcin] at hLsplit
  -- Step 3: the outer term
  have hO := HandoffAux.ellFn_wlinOut_le S hS hk hkn hc h hτ0 hdef
  -- Step 4: the arithmetic
  have hE : ‖Eig.ellFn S.P.χ (S.P.G k) (S.P.w k (S.P.tsh k)) - S.P.cinK k‖ ≤
      3 / 8 * ‖S.P.cinK k‖ := by
    refine HandoffAux.norm_sub_le_aux (m := S.maj k (S.P.tash k)) (K₁ := K₁)
      (X := Eig.ellNorm S.P.χ * S.CQ) (Y := Eig.Cls S.P.χ * θ * S.P.tash k) hK₁ hmaj0
      hEL hLsplit ?_ h.maj_small h.theta_small h.maj_le_cin
    calc _ ≤ Eig.Cls S.P.χ * θ * S.maj k (S.P.tash k) * S.P.tash k := hO
      _ = Eig.Cls S.P.χ * θ * S.P.tash k * S.maj k (S.P.tash k) := by ring
  have hksh : S.P.ksh k = ‖Eig.ellFn S.P.χ (S.P.G k) (S.P.w k (S.P.tsh k))‖ := rfl
  have habs := abs_norm_sub_norm_le (Eig.ellFn S.P.χ (S.P.G k) (S.P.w k (S.P.tsh k)))
    (S.P.cinK k)
  rw [← hksh] at habs
  obtain ⟨hlo, hhi⟩ := abs_le.1 (habs.trans hE)
  have hc0 := norm_nonneg (S.P.cinK k)
  have h1 : 1 / 2 * ‖S.P.cinK k‖ ≤ S.P.ksh k := by linarith
  have h2 : S.P.ksh k ≤ 3 / 2 * ‖S.P.cinK k‖ := by linarith
  have h3 : S.maj k (S.P.tash k) ≤ K₁ * S.P.ksh k := by
    have hiii := h.maj_le_cin
    have : 1 / 2 * K₁ * ‖S.P.cinK k‖ ≤ K₁ * S.P.ksh k := by
      have := mul_le_mul_of_nonneg_left h1 hK₁.le
      linarith
    exact hiii.trans this
  refine ⟨h1, h2, h3, ?_, hsupp⟩
  calc Sob.normH S.sh (S.P.w k (S.P.tsh k)) ≤ S.CQ * S.maj k (S.P.tash k) := hbd
    _ ≤ S.CQ * (K₁ * S.P.ksh k) := mul_le_mul_of_nonneg_left h3 hCQ
    _ = K₁ * S.CQ * S.P.ksh k := by ring

end Relay

end NonUniqueEuler
