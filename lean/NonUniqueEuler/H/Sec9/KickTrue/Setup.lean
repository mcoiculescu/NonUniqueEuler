import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec9.Detuning
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.H.Sec9.KickTrue.Real

/-!
# Helpers for `P/Sec9/KickTrue`: the numerical setting of `lem:kicktrue`

Helper file of `P/Sec9/KickTrue.lean` (`lem:kicktrue`, `09_relay.tex:1239-1260`). For
`1 ≤ k < n` with `σ = σ(0)`, `σ₊ = σ_{k+1}`, `x = x_k`, `κ = κ♯_{k+1}`, `L = log(δ₀/κ)`, `T_g = T̂_{k+1}`:
* `C3_pos`, `CQ_nonneg`: signs of the chosen constants of `thm:active` / `thm:quiet`;
* `sigma_facts`: `0 < σ_b ≤ σ ≤ |z|`;
* `uniform_facts`: `c_out > 0`, `c_out ≤ 2π|pout_*(G)|`, `|pout_*(G)| ≤ max|pout_*|`, `C_ls ≥ 0`,
  `c_N > 0` on `[0,G₁]` (`lem:uniform`);
* `level_facts`: `G_k, G_{k+1} ∈ [0,G₁]`, both detuned (`lem:inner-circ`, (SA3), (Det));
* `rew_facts`: `eq:Rew` and its consequences (`lem:detuning`);
* `kappa_facts`: `0 < κ < δ₀`, `L ≥ (μ/(μ-1))log 4 ≥ 1`, `T_g = σ₊⁻¹L > 0` ((c));
* `kick2_of_ge`: `e^{-Re w T} ≤ 1/2` for `T ≥ (17/24)T_g` ((Kick2), `09_relay.tex:1281-1287`);
* `clock_facts`: `τ₀ = -t̄♯_{k+1} - T_g`, `T_{k+1} = t♯_{k+1} + T_g/A_{k+1}`, `t̄♯_{k+1} > 0` if
  `k+1 < n` and `= 0` if `k+1 = n` (`def:clock`, `lem:clock`(1)).
Everything here is proved.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Relay

namespace KickTrueAux

open RingData Datum

/-- The chosen `C₃` of `thm:active` is positive (`0 < C₃` is part of `IsActiveConst`; junk `1`). -/
theorem C3_pos (χ : ℝ → ℝ) (s : ℕ) (σ' : ℝ) : 0 < OneRing.C3 χ s σ' := by
  unfold OneRing.C3 OneRing.activeConsts
  split_ifs with h
  · exact h.choose_spec.2.2.1
  · norm_num

/-- The chosen `C_Q` of `thm:quiet` is nonnegative (`0 ≤ C_Q` is part of `IsQuietConst`; junk `0`). -/
theorem CQ_nonneg (χ : ℝ → ℝ) (sh NQ : ℕ) : 0 ≤ OneRing.CQ χ sh NQ := by
  unfold OneRing.CQ OneRing.quietConsts
  split_ifs with h
  · exact h.choose_spec.2.1
  · norm_num

variable (S : Standing)

/-- `0 < σ_b ≤ σ ≤ |z|`. -/
theorem sigma_facts (hS : S.Holds) :
    0 < S.sigb ∧ S.sigb ≤ S.sigma0 ∧ 0 < S.sigma0 ∧ S.sigma0 ≤ ‖S.z‖ ∧ 0 < ‖S.z‖ := by
  obtain ⟨hb, hbs, -⟩ := standing_levels S hS
  have hσ : 0 < S.sigma0 := lt_of_lt_of_le hb hbs
  have hz : S.sigma0 ≤ ‖S.z‖ := Complex.re_le_norm _
  exact ⟨hb, hbs, hσ, hz, lt_of_lt_of_le hσ hz⟩

/-- The constants of `lem:uniform` at `G ∈ [0,G₁]`. -/
theorem uniform_facts (hS : S.Holds) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) :
    0 < Eig.cout S.P.χ ∧ Eig.cout S.P.χ ≤ 2 * Real.pi * ‖Eig.pout S.P.χ G‖ ∧
      ‖Eig.pout S.P.χ G‖ ≤ S.poutMax ∧ 0 ≤ S.poutMax ∧ 0 ≤ Eig.Cls S.P.χ ∧
      0 < Eig.cN S.P.χ := by
  obtain ⟨-, -, -, hpmax, hell, -, hcN, hcout, hG'⟩ :=
    Eig.uniform_constants S.P.χ hS.admissible hS.hN
  have hle : ‖Eig.pout S.P.χ G‖ ≤ S.poutMax := hpmax.2 ⟨G, hG, rfl⟩
  refine ⟨hcout, (hG' G hG).2.2.1, hle, (norm_nonneg _).trans hle, ?_, hcN⟩
  have hell0 : 0 ≤ Eig.ellNorm S.P.χ := by
    obtain ⟨G₀, -, hG₀⟩ := hell.1
    rw [← hG₀]; exact norm_nonneg (Eig.ell S.P.χ 0 G₀)
  exact mul_nonneg hell0 (Sob.l2_nonneg _)

/-- `G_k, G_{k+1} ∈ [0,G₁]`, both detuned, and `G_i ≤ G₁` for all levels. -/
theorem level_facts (hS : S.Holds) (hDet : S.Det) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n) :
    S.P.G k ∈ Icc (0 : ℝ) Gbar ∧ S.P.G (k + 1) ∈ Icc (0 : ℝ) Gbar ∧
      Kick.Detuned S.P.χ S.P.μ (S.P.G k) ∧ Kick.Detuned S.P.χ S.P.μ (S.P.G (k + 1)) ∧
      S.P.GSmall := by
  obtain ⟨-, -, hGs, hlev⟩ := standing_levels S hS
  have h1 := hlev k (Finset.mem_Icc.2 ⟨hk, hkn.le⟩)
  have h2 := hlev (k + 1) (Finset.mem_Icc.2 ⟨by omega, hkn⟩)
  exact ⟨h1.2.1, h2.2.1, hDet _ h1.1, hDet _ h2.1, hGs⟩

/-- **`eq:Rew`** and its consequences (`09_relay.tex:1243-1255`): with `σ₊ = σ_{k+1}`, `x = x_k`,
`15σ/16 ≤ σ₊ ≤ 17σ/16`, `x ≥ σ/4`, `(3/4)σ(μ-1)/μ ≤ σ₊ - x ≤ σ/8`, `1 - x/σ₊ ≥ ϑ_μ`, and
`Re w = σ₊ - x`. -/
theorem rew_facts (hS : S.Holds) (hDet : S.Det) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n) :
    15 / 16 * S.sigma0 ≤ S.P.sigma (k + 1) ∧ S.P.sigma (k + 1) ≤ 17 / 16 * S.sigma0 ∧
      S.sigma0 / 4 ≤ S.P.xk k ∧
      3 / 4 * S.sigma0 * ((S.P.μ - 1) / S.P.μ) ≤ S.P.sigma (k + 1) - S.P.xk k ∧
      S.P.sigma (k + 1) - S.P.xk k ≤ S.sigma0 / 8 ∧
      S.varthetaMu ≤ 1 - S.P.xk k / S.P.sigma (k + 1) ∧
      0 < S.P.xk k ∧ S.P.xk k < S.P.sigma (k + 1) ∧
      (Eig.lam S.P.χ (S.P.G (k + 1)) - Eig.lam S.P.χ (S.P.G k) / S.P.μ).re =
        S.P.sigma (k + 1) - S.P.xk k := by
  obtain ⟨-, -, hσ, -⟩ := sigma_facts S hS
  obtain ⟨he1, he2, hlev⟩ := detuning S hS hDet
  have hkI : k ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hk, hkn.le⟩
  have hk1I : k + 1 ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨by omega, hkn⟩
  obtain ⟨hdk, -, -, hxk, -, -⟩ := hlev k hkI
  obtain ⟨hdk1, hσp, -, -, -, hmix⟩ := hlev (k + 1) hk1I
  obtain ⟨hm1, hm2, -, -⟩ := hmix k hkI
  have hμ1 := hS.one_lt_μ
  have hμle := hS.μ_le
  have hμ0 : 0 < S.P.μ := by linarith
  set σ := S.sigma0
  set σp := S.P.sigma (k + 1)
  set σk := S.P.sigma k
  set μ := S.P.μ
  set e := S.emu
  have hx : S.P.xk k = σk / μ := rfl
  have he0 : 0 ≤ e := by
    show 0 ≤ (S.P.μ - 1) / (8 * S.P.μ)
    exact div_nonneg (by linarith) (by positivity)
  -- `σ₊ ≤ 17σ/16`
  have hσp_le : σp ≤ 17 / 16 * σ := by
    have := (abs_le.1 hdk1).2
    have : e * σ ≤ 1 / 136 * σ := mul_le_mul_of_nonneg_right he1 hσ.le
    linarith
  -- `μσ₊ - σ_k ≤ (5/4)σ(μ-1)`
  have hup : μ * σp - σk ≤ 5 / 4 * σ * (μ - 1) := by
    have h1 := (abs_le.1 hdk1).2
    have h2 := (abs_le.1 hdk).1
    have h3 : μ * σp ≤ μ * (σ + e * σ) := mul_le_mul_of_nonneg_left (by linarith) hμ0.le
    have h4 : σ * (e * (μ + 1)) ≤ σ * ((μ - 1) / 4) := mul_le_mul_of_nonneg_left he2 hσ.le
    nlinarith
  have hRe : σp - S.P.xk k = (μ * σp - σk) / μ := by rw [hx]; field_simp
  have hlow : 3 / 4 * σ * ((μ - 1) / μ) ≤ σp - S.P.xk k := by
    rw [hRe]
    have : 3 / 4 * σ * (μ - 1) ≤ μ * σp - σk := hm2.trans hm1
    rw [show 3 / 4 * σ * ((μ - 1) / μ) = 3 / 4 * σ * (μ - 1) / μ by ring]
    exact div_le_div_of_nonneg_right this hμ0.le
  have hupp : σp - S.P.xk k ≤ σ / 8 := by
    rw [hRe]
    have h1 : (μ * σp - σk) / μ ≤ μ * σp - σk := by
      have hpos : 0 ≤ μ * σp - σk := le_trans (by
        have : 0 < μ - 1 := by linarith
        positivity) (hm2.trans hm1)
      exact div_le_self hpos (by linarith)
    have h2 : 5 / 4 * σ * (μ - 1) ≤ σ / 8 := by nlinarith
    linarith
  have hσp0 : 0 < σp := lt_of_lt_of_le (by positivity) hσp
  have hxpos : 0 < S.P.xk k := lt_of_lt_of_le (by positivity) hxk
  have hxlt : S.P.xk k < σp := by
    have : 0 < 3 / 4 * σ * ((μ - 1) / μ) := by
      have : 0 < μ - 1 := by linarith
      positivity
    linarith
  have hvt : S.varthetaMu ≤ 1 - S.P.xk k / σp := by
    show (μ - 1) / 3 ≤ 1 - S.P.xk k / σp
    have h1 : 1 - S.P.xk k / σp = (σp - S.P.xk k) / σp := by field_simp
    rw [h1, le_div_iff₀ hσp0]
    have h3 : (μ - 1) / 3 * σp ≤ (μ - 1) / 3 * (17 / 16 * σ) :=
      mul_le_mul_of_nonneg_left hσp_le (by linarith)
    have h4 : (μ - 1) / 3 * (17 / 16 * σ) ≤ 3 / 4 * σ * ((μ - 1) / μ) := by
      rw [show 3 / 4 * σ * ((μ - 1) / μ) = (μ - 1) * σ * (3 / 4 / μ) by ring]
      rw [show (μ - 1) / 3 * (17 / 16 * σ) = (μ - 1) * σ * (17 / 48) by ring]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) hσ.le)
      rw [le_div_iff₀ hμ0]; linarith
    linarith
  refine ⟨hσp, hσp_le, hxk, hlow, hupp, hvt, hxpos, hxlt, ?_⟩
  rw [Complex.sub_re, Complex.div_ofReal_re]
  rfl

/-- `0 < κ < δ₀`, `L = log(δ₀/κ) ≥ (μ/(μ-1)) log 4`, `L ≥ 1`, `T_g = σ₊⁻¹L > 0`, `κ = κ♯_{k+1}`,
`T_g = T̂_{k+1}` (`09_relay.tex:1255-1259`; (c)). -/
theorem kappa_facts (hS : S.Holds) (hDet : S.Det) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (hC : S.kickIneqC (S.P.ksh (k + 1))) :
    0 < S.P.ksh (k + 1) ∧ S.P.ksh (k + 1) < S.P.δ₀ ∧
      S.P.μ / (S.P.μ - 1) * Real.log 4 ≤ Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ∧
      1 ≤ Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ∧
      S.P.That (k + 1) = (S.P.sigma (k + 1))⁻¹ * Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ∧
      0 < S.P.That (k + 1) := by
  have hmem := (hc (k + 1) (Finset.mem_Icc.2 ⟨le_rfl, hkn⟩)).2
  obtain ⟨hσp, -⟩ := rew_facts S hS hDet hk hkn
  obtain ⟨-, -, hσ, -⟩ := sigma_facts S hS
  have hσp0 : 0 < S.P.sigma (k + 1) := lt_of_lt_of_le (by positivity) hσp
  have hlog := log_ge_of_le_rpow hmem.1 hC
  have hL1 := one_le_log_of_le_rpow hmem.1 hS.one_lt_μ hC
  refine ⟨hmem.1, hmem.2, hlog, hL1, rfl, ?_⟩
  show 0 < (S.P.sigma (k + 1))⁻¹ * Real.log (S.P.δ₀ / S.P.ksh (k + 1))
  exact mul_pos (inv_pos.2 hσp0) (by linarith)

/-- **(Kick2) for `T ≥ (17/24)T_g`** (`09_relay.tex:1281-1287`, `:1388-1390`):
`Re w T ≥ (17/24)(24/17) log 2 = log 2`, so `e^{-Re w T} ≤ 1/2`. -/
theorem kick2_of_ge (hS : S.Holds) (hDet : S.Det) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (hC : S.kickIneqC (S.P.ksh (k + 1))) {T : ℝ}
    (hT : 17 / 24 * S.P.That (k + 1) ≤ T) :
    Real.exp (-((Eig.lam S.P.χ (S.P.G (k + 1)) - Eig.lam S.P.χ (S.P.G k) / S.P.μ).re * T)) ≤
      1 / 2 := by
  obtain ⟨hσp, hσp_le, -, hlow, -, -, -, -, hRe⟩ := rew_facts S hS hDet hk hkn
  obtain ⟨-, -, hσ, -⟩ := sigma_facts S hS
  obtain ⟨-, -, hlog, hL1, hTg, -⟩ := kappa_facts S hS hDet hk hkn hc hC
  rw [hRe]
  have hμ1 : 1 < S.P.μ := hS.one_lt_μ
  set σ := S.sigma0
  set σp := S.P.sigma (k + 1)
  set μ := S.P.μ
  set L := Real.log (S.P.δ₀ / S.P.ksh (k + 1))
  set a := σp - S.P.xk k
  have hσp0 : 0 < σp := lt_of_lt_of_le (by positivity) hσp
  have hμ0 : 0 < μ := by linarith
  have hm1 : 0 < μ - 1 := by linarith
  have ha0 : 0 < 3 / 4 * σ * ((μ - 1) / μ) := by positivity
  have ha : 0 < a := lt_of_lt_of_le ha0 hlow
  -- `a T ≥ a (17/24) L/σ₊ ≥ (1/2)((μ-1)/μ) L ≥ (1/2) log 4 = log 2`
  have hTg' : S.P.That (k + 1) = L / σp := by rw [hTg]; ring
  have h1 : a * (17 / 24 * (L / σp)) ≤ a * T := by
    rw [← hTg']; exact mul_le_mul_of_nonneg_left hT ha.le
  have h2 : 3 / 4 * σ * ((μ - 1) / μ) / σp ≤ a / σp := div_le_div_of_nonneg_right hlow hσp0.le
  have h3 : 12 / 17 * ((μ - 1) / μ) ≤ 3 / 4 * σ * ((μ - 1) / μ) / σp := by
    rw [le_div_iff₀ hσp0]
    have : 0 ≤ (μ - 1) / μ := by positivity
    nlinarith
  have hL0 : 0 ≤ L := by linarith
  have h4 : 12 / 17 * ((μ - 1) / μ) * L ≤ a / σp * L := by
    exact mul_le_mul_of_nonneg_right (h3.trans h2) hL0
  have h5 : Real.log 4 ≤ (μ - 1) / μ * L := by
    have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ (μ - 1) / μ)
    calc Real.log 4 = (μ - 1) / μ * (μ / (μ - 1) * Real.log 4) := by
          field_simp
      _ ≤ (μ - 1) / μ * L := this
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hkey : Real.log 2 ≤ a * T := by
    have e1 : a * (17 / 24 * (L / σp)) = 17 / 24 * (a / σp * L) := by ring
    have e2 : 17 / 24 * (12 / 17 * ((μ - 1) / μ) * L) = 1 / 2 * ((μ - 1) / μ * L) := by ring
    nlinarith
  calc Real.exp (-(a * T)) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 (by linarith)
    _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

/-- **The clock at level `k+1`** (`def:clock`, `lem:clock`(1), `09_relay.tex:1374-1377`, `:1383-1384`):
`T_{k+1} = t♯_{k+1} + T_g/A_{k+1}`, `τ₀ = -t̄♯_{k+1} - T_g`, `t̄♯_{k+1} ≥ 0`, `t̄♯_{k+1} > 0` if `k+1 < n`,
and `t♯_{k+1} = 0` if `k+1 = n`. -/
theorem clock_facts (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) :
    S.P.T (k + 1) = S.P.tsh (k + 1) + S.P.That (k + 1) / S.P.A (k + 1) ∧
      S.P.tau0 k = -S.P.tash (k + 1) - S.P.That (k + 1) ∧
      0 ≤ S.P.tash (k + 1) ∧
      (k + 1 < S.P.n → 0 < S.P.tash (k + 1)) ∧
      (k + 1 = S.P.n → S.P.tsh (k + 1) = 0) := by
  have hA := hS.valid.A_pos (k + 1)
  have hG : S.P.GSmall := (standing_levels S hS).2.2.1
  obtain ⟨h1, -, h3, h4⟩ := Approx.clock_order S.P hS.valid hS.hN hG (by omega : 1 ≤ k + 1) hc
  have hT : S.P.T (k + 1) = S.P.tsh (k + 1) + S.P.That (k + 1) / S.P.A (k + 1) := by
    have hne : ¬(k + 1 = S.P.n + 1) := by omega
    simp only [Approx.T, hne, ↓reduceIte]
  have htsh0 : 0 ≤ S.P.tsh (k + 1) := h4 (k + 1) (Finset.mem_Icc.2 ⟨le_rfl, hkn⟩)
  refine ⟨hT, ?_, mul_nonneg hA.le htsh0, ?_, ?_⟩
  · simp only [Approx.tau0, Approx.tash]
    rw [hT]
    field_simp
    ring
  · intro hlt
    have hT2 : S.P.T (k + 2) < S.P.tsh (k + 1) := h3 (k + 1) (k + 2) le_rfl (by omega) (by omega)
    have hi : k + 2 ∈ Finset.Icc (k + 1) S.P.n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have h5 : S.P.tsh (k + 2) < S.P.T (k + 2) := h1 (k + 2) hi
    have h6 : 0 ≤ S.P.tsh (k + 2) := h4 (k + 2) hi
    exact mul_pos hA (by linarith)
  · intro heq
    simp only [Approx.tsh]
    rw [show S.P.n - (k + 1) = 0 by omega]
    rfl

end KickTrueAux

end Relay

end NonUniqueEuler
