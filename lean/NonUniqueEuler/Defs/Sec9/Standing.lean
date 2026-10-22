import NonUniqueEuler.Defs.Sec7.All
import NonUniqueEuler.Defs.Sec8.All

/-!
# Section 9.1: the standing assumptions (SA), the derived quantities, (Det) (definitions)

Manuscript `def:standing`
(`09_relay.tex:27-69`), the conventions after it (`:71-91`) and the number `e_μ` of
`lem:detuning` (`:104-113`).

* `Relay.Standing`: the data fixed by (SA): the approximation `P : Datum.Approx` ((SA3): `χ`, `A₁`,
  `μ`, `s̄`, `κ_seed`, `n`, `δ₀`, `T_pin` and `ω^{(n)}`), the integer `s` and the number `σ'` of
  (SA1). Every constant of (SA1)–(SA2) is a function of these data: `S.M`, `S.sh` (`s_h`), `S.NQ`
  (`N_Q`), `S.Mh` (`M_h`), `S.dH`, `S.C2`, `S.C3`, `S.kappa0` (`κ₀(·)`), `S.Cact` (`C(·)`),
  `S.majst`, `S.CQ`, `S.CDelta`, `S.CM`, `S.CO`, `S.Cin` (the chosen constants of Sections 5 and 7).
* `Standing.Holds`: (N1)–(N3) and the conditions (SA1)–(SA3) (a structure of Props).
* the derived quantities of `def:standing`: `cgamma` (`c_γ`), `varthetaMu` (`ϑ_μ`), `gammaMu`
  (`γ_μ`), `gammaMu'` (`γ'_μ`), `CDuh` (`C_Duh`), `rT` (`r_T`), `gammaJ` (`γ_j`), `ahatK` (`â_k`),
  `rhoHatK` (`ρ̂_k`), and the detuning hypothesis `Det`;
* `emu` (`e_μ` of `lem:detuning`), and the abbreviations `S.etaIn`, `S.etaOut`, `S.eta`, `S.maj`,
  `S.majIn` of the field norms and majorants of `def:regions` at the order `M_h` of (SA2).

Namespace `NonUniqueEuler.Relay`; the objects of `S : Standing` are in `Relay.Standing` (dot
notation `S.KO`, `S.maj j τ`, …). Here `m = p = 3` are written as the literal `3`, and
`(Q̄, p_K) = (C_mom, m)` is `(Rings.Cmom, 3)`. All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- **The data fixed by the standing assumptions (SA)** (`def:standing`, `09_relay.tex:27-48`):
the approximation `P` (the objects of `def:datum`–`def:clock` with the parameters
`χ, A₁, μ, s̄, κ_seed, n, δ₀, T_pin` of (SA3), and `ω^{(n)}`), the integer `s` and the number `σ'`
of (SA1). All constants of (SA1)–(SA2) are determined by `(P.χ, s, σ')`; the conditions are
`Standing.Holds`. -/
structure Standing where
  /-- the approximation of (SA3) (`def:approx`, `def:regions`, `def:clock`) -/
  P : Datum.Approx
  /-- the Sobolev index `s ≥ 3` of (SA1) (the `s` of `thm:active`) -/
  s : ℕ
  /-- the rate `σ' ∈ (9/200, min(σ_b, 3σ/4))` of (SA1) -/
  σ' : ℝ

namespace Standing

variable (S : Standing)

/-! ### Eigendata and the constants of (SA1)–(SA2) -/

/-- `σ = σ(0) = Re z` (`def:eigendata`, `04_ring.tex:1323`). -/
def sigma0 : ℝ := Eig.sigma S.P.χ 0

/-- `σ_b = min_{[0,G₁]} σ` (`04_ring.tex:1323`). -/
def sigb : ℝ := Eig.sigb S.P.χ

/-- `z = λ_*(0)` (`04_ring.tex:1323`). -/
def z : ℂ := Eig.z S.P.χ

/-- The integer `M` of `thm:active` for `s` ((SA1), `09_relay.tex:33-34`). -/
def M : ℕ := OneRing.Mact S.P.χ S.s

/-- `s_h = M - 1` ((SA2), `09_relay.tex:37`). -/
def sh : ℕ := S.M - 1

/-- `N_Q = max(2, ⌈Λ(s_h)/σ_b⌉)` ((SA2), `09_relay.tex:37`), with `Λ` of `lem:energy`. -/
def NQ : ℕ := max 2 ⌈OneRing.Lam S.P.χ S.sh / Eig.sigb S.P.χ⌉₊

/-- `M_h = s_h + N_Q + 1` ((SA2), `09_relay.tex:37`). -/
def Mh : ℕ := OneRing.Mh S.sh S.NQ

/-- `d_H` of `thm:active` for `(s, σ')` ((SA1)). -/
def dH : ℝ := OneRing.dH S.P.χ S.s S.σ'

/-- `C₂` of `thm:active` for `(s, σ')` ((SA1)). -/
def C2 : ℝ := OneRing.C2 S.P.χ S.s S.σ'

/-- `C₃` of `thm:active` / `cor:active-moment` for `(s, σ')` ((SA1)). -/
def C3 : ℝ := OneRing.C3 S.P.χ S.s S.σ'

/-- The function `κ₀(·)` of `thm:active` for `(s, σ')` ((SA1)). -/
def kappa0 : ℝ → ℝ := OneRing.kappa0 S.P.χ S.s S.σ'

/-- The function `C(·)` of `thm:active`: `C(C₀) = max(C₀, e^{σ_max t̄₁(C₀)})` ((SA1)). -/
def Cact (C₀ : ℝ) : ℝ := OneRing.Cact S.P.χ S.σ' C₀

/-- `maj_*` of `thm:quiet` for `(s_h, N_Q)` ((SA2)). -/
def majst : ℝ := OneRing.majst S.P.χ S.sh S.NQ

/-- `C_Q` of `thm:quiet` for `(s_h, N_Q)` ((SA2)). -/
def CQ : ℝ := OneRing.CQ S.P.χ S.sh S.NQ

/-- `C_Δ` of `thm:quiet` for `(s_h, N_Q)` ((SA2)). -/
def CDelta : ℝ := OneRing.CDelta S.P.χ S.sh S.NQ

/-- `C_M` of `lem:transfer` at order `M_h` ((SA2); `C_M = C^T_M max(1, C_{L1})`). -/
def CM : ℝ := Rings.CM S.P.χ S.Mh

/-- `C_O` of `lem:transfer` at order `M_h` ((SA2); `C_O = C^T_O max(1, C_{L1})`). -/
def CO : ℝ := Rings.CO S.P.χ S.Mh

/-- `C_in` of `lem:inner-field` at order `M_h` ((SA2)). -/
def Cin : ℝ := Rings.Cin S.P.χ S.Mh

/-! ### The standing assumptions -/

/-- **The standing assumptions (SA)** (`def:standing`, `09_relay.tex:27-48`), together with
(N1)–(N3):
* (SA1) `s ≥ 3` and `σ' ∈ (9/200, min(σ_b, 3σ/4))`;
* (SA2) holds by the definitions `S.sh`, `S.NQ`, `S.Mh` and the chosen constants;
* (SA3) `δ₀ ∈ (0, d_H]`, `μ ∈ (1, 17/16]`, `T_pin > 0`, `κ_seed ∈ (0, κ_L]`, `s̄ ∈ (0, a/16]` with
  `s̄^{m-2} ≤ 1/2`, `μ⁴s̄² ≤ 1/8` and `C_G μ s̄² ≤ G₁`, `n ≥ 2`, and `P` is the approximation with
  these parameters (`P.Valid`: the positivity conditions, `μ ≤ 2`, `s̄ ≤ a/16`, `n ≥ 2`,
  `κ_seed ≤ κ_L`, and `ω^{(n)} = Smooth.sol f^{(n)}`). -/
structure Holds : Prop where
  hN : NumericalHypothesis S.P.χ
  valid : S.P.Valid
  three_le_s : 3 ≤ S.s
  σ'_gt : 9 / 200 < S.σ'
  σ'_lt_sigb : S.σ' < Eig.sigb S.P.χ
  σ'_lt_sigma : S.σ' < 3 / 4 * Eig.sigma S.P.χ 0
  δ₀_le_dH : S.P.δ₀ ≤ S.dH
  μ_le : S.P.μ ≤ 17 / 16
  sbar_pow_le : S.P.sbar ^ (3 - 2) ≤ 1 / 2
  mu_sbar_le : S.P.μ ^ 4 * S.P.sbar ^ 2 ≤ 1 / 8
  CG_le : CG S.P.χ * S.P.μ * S.P.sbar ^ 2 ≤ Gbar

/-! ### Derived quantities of `def:standing` -/

/-- `c_γ = 1 - 16σ'/(15σ)` (`09_relay.tex:51`). -/
def cgamma : ℝ := 1 - 16 * S.σ' / (15 * S.sigma0)

/-- `ϑ_μ = (μ-1)/3` (`09_relay.tex:52`). -/
def varthetaMu : ℝ := (S.P.μ - 1) / 3

/-- `γ_μ = min(ϑ_μ, c_γ)` (`09_relay.tex:52`). -/
def gammaMu : ℝ := min S.varthetaMu S.cgamma

/-- `γ'_μ = min((13/20)(μ-1)/μ, c_γ)` (`09_relay.tex:53`). -/
def gammaMu' : ℝ := min (13 / 20 * ((S.P.μ - 1) / S.P.μ)) S.cgamma

/-- `C_Duh = 2μ/(σ_b(μ-1))` (`09_relay.tex:54`). -/
def CDuh : ℝ := 2 * S.P.μ / (S.sigb * (S.P.μ - 1))

/-- `r_T(T) = (1+T)^{p_K} e^{-σT/4}`, `p_K = m = 3` (`09_relay.tex:55-56`; meaningful for `T ≥ 0`). -/
def rT (T : ℝ) : ℝ := (1 + T) ^ 3 * Real.exp (-(S.sigma0 * T / 4))

/-- `γ_j = max(σ_j, μσ')/(μσ_{j+1})` for a level `j < n` (`09_relay.tex:58-61`). -/
def gammaJ (j : ℕ) : ℝ := max (S.P.sigma j) (S.P.μ * S.σ') / (S.P.μ * S.P.sigma (j + 1))

/-- The envelope `â_k(u) = κ♯_k e^{σ_k u}`, `u ≥ 0` (`09_relay.tex:63-64`; `OneRing.ahat`),
meaningful when `κ♯_k` is defined (`P.ClockUpTo k`). -/
def ahatK (k : ℕ) (u : ℝ) : ℝ := OneRing.ahat (S.P.ksh k) (S.P.sigma k) u

/-- The transient `ρ̂_k` of `thm:active` with `G = G_k` and the constant `C₀` named in each
statement (`09_relay.tex:64-66`; `OneRing.rhoHat`). -/
def rhoHatK (C₀ : ℝ) (k : ℕ) (u : ℝ) : ℝ := OneRing.rhoHat S.P.χ S.σ' C₀ (S.P.G k) u

/-- **The detuning hypothesis (Det)** (`09_relay.tex:67-68`):
`sup_{0 ≤ G ≤ C_G μ s̄²} |λ_*(G) - z| ≤ σ(μ-1)/(8μ)`, stated for every `G` in the interval
(equivalent to the bound on the supremum; `Kick.Detuned`). -/
def Det : Prop := ∀ G ∈ Icc (0 : ℝ) (CG S.P.χ * S.P.μ * S.P.sbar ^ 2), Kick.Detuned S.P.χ S.P.μ G

/-- `e_μ = (μ-1)/(8μ)` (`lem:detuning`, `09_relay.tex:106`). -/
def emu : ℝ := (S.P.μ - 1) / (8 * S.P.μ)

/-! ### Field norms and majorants at the order `M_h` (`def:regions`, ring-`k` time) -/

/-- `η^in_k(τ) = ‖h^in_k(τ)‖_{C^{M_h}(N')}` (`06_datum.tex:197-201`), `τ` ring-`k` time. -/
def etaIn (k : ℕ) (τ : ℝ) : ℝ := S.P.etaIn S.Mh k τ

/-- `η^out_k(τ) = ‖h^out_k(τ)‖_{C^{M_h}(N')}` (`06_datum.tex:197-201`). -/
def etaOut (k : ℕ) (τ : ℝ) : ℝ := S.P.etaOut S.Mh k τ

/-- `η_k = η^in_k + η^out_k` (`06_datum.tex:200`). -/
def eta (k : ℕ) (τ : ℝ) : ℝ := S.P.eta S.Mh k τ

/-- The Duhamel majorant `maj_k(τ) = ∫₀^τ e^{σ_k(τ-v)} η_k(v) dv` (`06_datum.tex:202-207`). -/
def maj (k : ℕ) (τ : ℝ) : ℝ := S.P.majK S.Mh k τ

/-- `maj^in_k`, the majorant of `η^in_k` (`06_datum.tex:209`). -/
def majIn (k : ℕ) (τ : ℝ) : ℝ := S.P.majIn S.Mh k τ

/-- The linear response of `thm:quiet`(b) for ring `k` in ring-`k` time:
`wlin_k(τ) = ∫₀^τ e^{(τ-v)L(G_k)}(-h_k(v)·∇Φ) dv ∈ Y^{s_h}(N)` (`05_single_ring.tex:424-426`,
`09_relay.tex:76-80`; `OneRing.wlin` with `G = G_k`, `h = h_k`). -/
def wlinK (k : ℕ) (τ : ℝ) : Sect.Y S.sh annN := OneRing.wlin S.P.χ S.sh (S.P.G k) (S.P.hField k) τ

/-! ### Basic lemmas (fully proved) -/

theorem sigma0_def : S.sigma0 = Eig.sigma S.P.χ 0 := rfl
theorem sigb_def : S.sigb = Eig.sigb S.P.χ := rfl
theorem z_def : S.z = Eig.z S.P.χ := rfl
theorem sh_def : S.sh = OneRing.Mact S.P.χ S.s - 1 := rfl
theorem Mh_def : S.Mh = S.sh + S.NQ + 1 := rfl
theorem etaIn_def (k : ℕ) (τ : ℝ) : S.etaIn k τ = S.P.etaIn S.Mh k τ := rfl
theorem etaOut_def (k : ℕ) (τ : ℝ) : S.etaOut k τ = S.P.etaOut S.Mh k τ := rfl
theorem eta_def (k : ℕ) (τ : ℝ) : S.eta k τ = S.P.eta S.Mh k τ := rfl
theorem maj_def (k : ℕ) (τ : ℝ) : S.maj k τ = S.P.majK S.Mh k τ := rfl
theorem majIn_def (k : ℕ) (τ : ℝ) : S.majIn k τ = S.P.majIn S.Mh k τ := rfl
theorem ahatK_def (k : ℕ) (u : ℝ) : S.ahatK k u = S.P.ksh k * Real.exp (S.P.sigma k * u) := rfl
theorem rT_def (T : ℝ) : S.rT T = (1 + T) ^ 3 * Real.exp (-(S.sigma0 * T / 4)) := rfl

theorem eta_eq_add (k : ℕ) (τ : ℝ) : S.eta k τ = S.etaIn k τ + S.etaOut k τ := rfl

theorem etaIn_nonneg (k : ℕ) (τ : ℝ) : 0 ≤ S.etaIn k τ := S.P.etaIn_nonneg _ _ _
theorem etaOut_nonneg (k : ℕ) (τ : ℝ) : 0 ≤ S.etaOut k τ := S.P.etaOut_nonneg _ _ _
theorem eta_nonneg (k : ℕ) (τ : ℝ) : 0 ≤ S.eta k τ := S.P.eta_nonneg _ _ _

theorem maj_zero (k : ℕ) : S.maj k 0 = 0 := S.P.majK_zero _ _
theorem majIn_zero (k : ℕ) : S.majIn k 0 = 0 := S.P.majIn_zero _ _

theorem two_le_NQ : 2 ≤ S.NQ := le_max_left _ _

/-- `Λ(s_h)/σ_b ≤ N_Q`. -/
theorem div_le_NQ : OneRing.Lam S.P.χ S.sh / Eig.sigb S.P.χ ≤ S.NQ :=
  (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)

/-- The hypothesis `N_Q σ_b ≥ Λ(s_h)` of `thm:quiet` (given `σ_b > 0`, `prop:SU`). -/
theorem Lam_le_NQ_mul (h : 0 < Eig.sigb S.P.χ) :
    OneRing.Lam S.P.χ S.sh ≤ S.NQ * Eig.sigb S.P.χ :=
  (div_le_iff₀ h).1 S.div_le_NQ

theorem ahatK_zero (k : ℕ) : S.ahatK k 0 = S.P.ksh k := OneRing.ahat_zero _ _

theorem gammaMu_le_varthetaMu : S.gammaMu ≤ S.varthetaMu := min_le_left _ _
theorem gammaMu_le_cgamma : S.gammaMu ≤ S.cgamma := min_le_right _ _
theorem gammaMu'_le_cgamma : S.gammaMu' ≤ S.cgamma := min_le_right _ _

variable {S}

theorem Holds.one_lt_μ (h : S.Holds) : 1 < S.P.μ := h.valid.datumParams.one_lt_μ
theorem Holds.δ₀_pos (h : S.Holds) : 0 < S.P.δ₀ := h.valid.δ₀_pos
theorem Holds.Tpin_pos (h : S.Holds) : 0 < S.P.Tpin := h.valid.Tpin_pos
theorem Holds.two_le_n (h : S.Holds) : 2 ≤ S.P.n := h.valid.two_le_n
theorem Holds.sbar_pos (h : S.Holds) : 0 < S.P.sbar := h.valid.datumParams.sbar_pos
theorem Holds.sbar_le (h : S.Holds) : S.P.sbar ≤ a / 16 := h.valid.datumParams.sbar_le
theorem Holds.kseed_pos (h : S.Holds) : 0 < S.P.κs := h.valid.kseed_pos
theorem Holds.kseed_le (h : S.Holds) : S.P.κs ≤ OneRing.kL S.P.χ := h.valid.kseed_le
theorem Holds.admissible (h : S.Holds) : IsAdmissibleCutoff S.P.χ := h.valid.admissible

theorem Holds.δ₀_mem (h : S.Holds) : S.P.δ₀ ∈ Ioc (0 : ℝ) S.dH := ⟨h.δ₀_pos, h.δ₀_le_dH⟩
theorem Holds.μ_mem (h : S.Holds) : S.P.μ ∈ Ioc (1 : ℝ) (17 / 16) := ⟨h.one_lt_μ, h.μ_le⟩

theorem Holds.σ'_mem (h : S.Holds) :
    S.σ' ∈ Ioo (9 / 200 : ℝ) (Eig.sigb S.P.χ) := ⟨h.σ'_gt, h.σ'_lt_sigb⟩

/-- `M ≥ s + 4` (`thm:active`), hence `s_h = M - 1 ≥ s + 3 ≥ 3`, as `thm:quiet` requires. -/
theorem Holds.three_le_sh (h : S.Holds) : 3 ≤ S.sh := by
  have h4 := OneRing.add_four_le_Mact S.P.χ S.s
  have h3 := h.three_le_s
  simp only [sh, M]
  omega

/-- `M ≤ M_h` (indeed `M_h = M + N_Q`): bounds in `C^{M_h}(N')` give the `C^M(N')` bounds of
(Field) of `thm:active`. -/
theorem M_le_Mh : S.M ≤ S.Mh := by
  simp only [Mh, OneRing.Mh_eq, sh]
  omega

end Standing

end Relay

end NonUniqueEuler
