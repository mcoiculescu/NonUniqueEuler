import NonUniqueEuler.Defs.Sec9.Standing

/-!
# Section 9: `thm:quiet` and `thm:active` applied to ring `k` (definitions)

Manuscript `09_relay.tex:71-84` (applying
Section 5 to ring `k` in ring-`k` units, with `G = G_k`, `h = h_k`, `η = η_k`, `maj = maj_k` and
perturbation `w_k`) and `:759-767` (the active phase: time origin `t♯_k`, active time
`u = A_k(t - t♯_k)`, `w(u) = w_k(t♯_k + u/A_k)`, `h(u) = h_k(t̄♯_k + u)`, `c = c_k`).

The hypotheses and conclusions of `thm:quiet` and `thm:active` (with `cor:active-moment`) for ring `k`
of an approximation, written with the objects of `def:regions`/`def:clock` (the translation the
manuscript makes "without further comment", `09_relay.tex:72-80`):
* `S.QuietHyp i T`, `S.QuietConcl i T` (ring-`i` time `T`): "the hypotheses / the conclusions
  (a)–(c) of `thm:quiet` hold for ring `i` on `[0,T]`";
* `S.ActiveInitK`, `S.ActiveFieldK`, `S.CoefK` ((Init), (Field), (Coef) of `thm:active` for ring `k`
  with time origin `t♯_k`, `G = G_k`, `κ = κ♯_k`), `S.ActiveConclAB`, `S.ActiveConclAt` (the
  conclusions (a)–(b), resp. (a)–(b) and `cor:active-moment`, at active time `u`), and
  `S.ActiveConcl C₀ η_b k` ("on `Ph_k`", i.e. for `u ∈ [0, T̂_k]`);
* `P.activeConfig k`: the configuration of `lem:reduction` of ring `k` with time origin `t♯_k` (the
  object to which `thm:active` is applied; `P.ringConfig k` is the one with time origin `0`).

That these P-level bundles are what `IsQuietConst`/`IsActiveConst` give for `P.ringConfig i`,
`P.activeConfig k` is an interface statement. All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Datum

namespace Approx

open RingData

variable (P : Approx)

/-- **The configuration of ring `k` with time origin `t♯_k`** (`09_relay.tex:759-767`): the
vorticity `ω^{(n)}(t♯_k)` in ring-`k` units, split into its parts on `S_k(t♯_k)` (ring), on
`D_{k+1}(t♯_k)` (inner) and on `S_1(t♯_k) ∪ … ∪ S_{k-1}(t♯_k)` (outer). `thm:active` is applied to
it with `G = G_k`, `κ = κ♯_k`; its solution is `ω^{(n)}(t♯_k + ·/A_k)` in ring-`k` units, its
`w(u)` is `w_k(t♯_k + u/A_k)`, its `h(u)` is `h_k(t̄♯_k + u)` on `N'`, and its running coefficient
is `c_k` (interface statements). -/
def activeConfig (k : ℕ) : OneRing.RingConfig where
  ring0 := P.unitsVort k (P.omegaRing k (P.tsh k))
  inner0 := P.unitsVort k (P.omegaGe (k + 1) (P.tsh k))
  outer0 := P.unitsVort k (P.omegaOut k (P.tsh k))

theorem activeConfig_ring0 (k : ℕ) :
    (P.activeConfig k).ring0 = P.unitsVort k (P.omegaRing k (P.tsh k)) := rfl

theorem activeConfig_inner0 (k : ℕ) :
    (P.activeConfig k).inner0 = P.unitsVort k (P.omegaGe (k + 1) (P.tsh k)) := rfl

theorem activeConfig_outer0 (k : ℕ) :
    (P.activeConfig k).outer0 = P.unitsVort k (P.omegaOut k (P.tsh k)) := rfl

/-- `h^out_1 = 0`: no ring lies outside ring `1` (`lem:transfer-step`(2), `09_relay.tex:182`). -/
theorem hOut_one (τ : ℝ) : P.hOut 1 τ = 0 := by
  funext y
  simp [hOut, nuOut, omegaOut, unitsVort, scaleVort, velocity]

/-- `η^out_1 = 0` (`lem:transfer-step`(2), `09_relay.tex:182`). -/
theorem etaOut_one (Mh : ℕ) (τ : ℝ) : P.etaOut Mh 1 τ = 0 := by
  have h0 : ∀ q : ℕ, supIterDerivE q annN' (0 : ℂ → ℂ) = 0 := by
    intro q
    simp only [supIterDerivE]
    refine le_antisymm (iSup₂_le fun x _ => ?_) bot_le
    rw [show (0 : ℂ → ℂ) = fun _ => (0 : ℂ) from rfl, iteratedFDeriv_fun_zero]
    rw [Pi.zero_apply, enorm_eq_nnnorm, nnnorm_zero]; rfl
  simp [etaOut, hOut_one, normCk, normCkE, h0]

end Approx

end Datum

namespace Relay

open RingData Datum

namespace Standing

variable (S : Standing)

/-! ### `thm:quiet` for ring `i` (`09_relay.tex:72-84`) -/

/-- **The hypotheses of `thm:quiet` hold for ring `i` on `[0,T]`** (`T` in ring-`i` time), with
`G = G_i`, `h = h_i`, `η = η_i`, `maj = maj_i` (`09_relay.tex:72-84`, `:315-319`):
* `1 ≤ i < n`, so ring `i` starts at `Φ` in ring-`i` units (`ω_r(0) = Φ`);
* the geometric hypotheses of `lem:reduction` in ring-`i` units on `[0,T]`: for `t ∈ [0, T/A_i]`,
  `D_{i+1}(t) ⊂ B_{a r_i/8}` and the rings `l < i` lie outside `B_{6 r_i}` (`HDefined`); the
  remaining hypotheses of `lem:reduction` (smooth compactly supported datum, disjoint 3-fold
  symmetric parts) hold for every valid approximation;
* `G_i ∈ [0, G₁]`;
* `η_i ≤ 1` and `maj_i ≤ maj_*` on `[0,T]`.
The bound `‖h_i(τ)‖_{C^{M_h}(N')} ≤ η^in_i(τ) + η^out_i(τ) = η_i(τ)` and the measurability of `η_i`
(continuity on `[0,T]`, paragraph after `lem:regions-basic`) follow from the geometric hypotheses
and are not repeated. -/
structure QuietHyp (i : ℕ) (T : ℝ) : Prop where
  one_le : 1 ≤ i
  lt_n : i < S.P.n
  hdef : ∀ t ∈ Icc (0 : ℝ) (T / S.P.A i), S.P.HDefined i t
  G_mem : S.P.G i ∈ Icc (0 : ℝ) Gbar
  eta_le : ∀ τ ∈ Icc (0 : ℝ) T, S.eta i τ ≤ 1
  maj_le : ∀ τ ∈ Icc (0 : ℝ) T, S.maj i τ ≤ S.majst

/-- **The conclusions (a)–(c) of `thm:quiet` hold for ring `i` on `[0,T]`** (`T` in ring-`i` time;
`05_single_ring.tex:415-427` read for ring `i`, `09_relay.tex:76-80`): for `τ ∈ [0,T]`, `t = τ/A_i`,
(a) every trajectory of ring `i` moves radially by at most `C_Δ maj_i(τ)` (in ring-`i` units) on
`[0,t]`: `||Φ_{t'}(x)| - |x|| ≤ r_i C_Δ maj_i(τ)` for `x ∈ S_i`, `t' ∈ [0,t]`; and
`S_i(t) ⊂ 𝒩₋_i = r_i 𝒩₋` (`supp ω_r(t) ⊂ 𝒩₋` in ring-`i` units);
(b) `‖w_i(t) - wlin_i(τ)‖_{H^{s_h}} ≤ C_Q maj_i(τ)²`, with the linear response `wlin_i` of `h_i`;
(c) `‖w_i(t)‖_{H^{s_h}} ≤ C_Q maj_i(τ)`.
The clause "`w` solves `eq:ring`" of (a) is not used in Sections 9–11 and is omitted (it is part of
`OneRing.IsQuietConst` for the configuration `P.ringConfig i`). -/
structure QuietConcl (i : ℕ) (T : ℝ) : Prop where
  radial : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x ∈ S.P.S i, ∀ t' ∈ Icc (0 : ℝ) (τ / S.P.A i),
    |‖S.P.flow t' x‖ - ‖x‖| ≤ S.P.r i * (S.CDelta * S.maj i τ)
  supp : ∀ τ ∈ Icc (0 : ℝ) T, S.P.St i (τ / S.P.A i) ⊆ S.P.Nmk i
  lin : ∀ τ ∈ Icc (0 : ℝ) T,
    Sob.normH S.sh (S.P.w i (τ / S.P.A i) - (S.wlinK i τ).fn) ≤ S.CQ * S.maj i τ ^ 2
  bound : ∀ τ ∈ Icc (0 : ℝ) T, Sob.normH S.sh (S.P.w i (τ / S.P.A i)) ≤ S.CQ * S.maj i τ

/-! ### `thm:active` for ring `k` (`09_relay.tex:759-767`) -/

/-- **(Init) of `thm:active` for ring `k`** (`05_single_ring.tex:886` at time origin `t♯_k`):
`‖w_k(t♯_k)‖_{H^{M-1}} ≤ C₀ κ♯_k` and `supp(Φ + w_k(t♯_k)) ⊂ 𝒩₋`, i.e. `S_k(t♯_k) ⊂ 𝒩₋_k`. -/
def ActiveInitK (C₀ : ℝ) (k : ℕ) : Prop :=
  Sob.normH (S.M - 1) (S.P.w k (S.P.tsh k)) ≤ C₀ * S.P.ksh k ∧ S.P.St k (S.P.tsh k) ⊆ S.P.Nmk k

/-- **(Field) of `thm:active` for ring `k`** on `[0,ū]` (`05_single_ring.tex:887-889` with
`h(u) = h_k(t̄♯_k + u)`, `κ = κ♯_k`, `σ = σ_k`, `M = S.M`, `p = 3`): `h_k(t̄♯_k + u) = h₁(u) + h₂(u)`
near `N'`, with `‖h₁(u)‖_{C^M(N')} ≤ C₀κ♯_k⟨u⟩^p` and `‖h₂(u)‖_{C^M(N')} ≤ η_b â_k(u)` (memberships
explicit, as in `OneRing.RingConfig.ActiveField`). -/
def ActiveFieldK (C₀ ηb : ℝ) (k : ℕ) (ubar : ℝ) : Prop :=
  ∃ h₁ h₂ : ℝ → ℂ → ℂ, ∀ u ∈ Icc (0 : ℝ) ubar,
    (∃ U : Set ℂ, IsOpen U ∧ annN' ⊆ U ∧
        ∀ x ∈ U, S.P.hField k (S.P.tash k + u) x = h₁ u x + h₂ u x) ∧
      MemCk S.M annN' (h₁ u) ∧
      normCk S.M annN' (h₁ u) ≤ C₀ * S.P.ksh k * Prelim.jap u ^ OneRing.pW ∧
      MemCk S.M annN' (h₂ u) ∧
      normCk S.M annN' (h₂ u) ≤ ηb * S.ahatK k u

/-- **(Coef) of `thm:active` for ring `k`** on `[0,ū]` (`05_single_ring.tex:890` with `c = c_k`,
`κ = κ♯_k`, `σ = σ_k`): `|c_k(u)| ≤ κ♯_k(2 + C₀⟨u⟩^p e^{-σ_k u})`. -/
def CoefK (C₀ : ℝ) (k : ℕ) (ubar : ℝ) : Prop :=
  ∀ u ∈ Icc (0 : ℝ) ubar,
    ‖S.P.runCoefK k u‖ ≤
      S.P.ksh k * (2 + C₀ * Prelim.jap u ^ OneRing.pW * Real.exp (-(S.P.sigma k * u)))

/-- **The conclusions (a)–(b) of `thm:active` for ring `k` at active time `u`**
(`05_single_ring.tex:893-899` read with `09_relay.tex:759-767`), `t = t♯_k + u/A_k`:
(a) every trajectory of ring `k` moves radially by at most `C₂δ₀ + κ♯_k^{1/2}` (ring-`k` units)
between `t♯_k` and `t`: `||Φ_{t',t♯_k}(x)| - |x|| ≤ r_k(C₂δ₀ + κ♯_k^{1/2})` for `x ∈ S_k(t♯_k)`,
`t' ∈ [t♯_k, t]` (`Φ_{t',t♯_k}` the flow of `v^{(n)}` from time `t♯_k`); and
`S_k(t) ⊂ 𝒩_k` (`supp(Φ + w(u)) ⊂ 𝒩` in ring-`k` units);
(b) `‖w_k(t) - 2Re(c_k(u)e^{λ_k u}φ_*(G_k))‖_{H^s} ≤ C₂ â_k(u)[ρ̂_k(u) + â_k(u) + κ♯_k^{1/2} + η_b]`
and `‖w_k(t)‖_{H^s} ≤ C₂ â_k(u)(1 + ρ̂_k(u))` (`ρ̂_k` with the constant `C₀`). -/
structure ActiveConclAB (C₀ ηb : ℝ) (k : ℕ) (u : ℝ) : Prop where
  radial : ∀ x ∈ S.P.St k (S.P.tsh k), ∀ t' ∈ Icc (S.P.tsh k) (S.P.tsh k + u / S.P.A k),
    |‖Smooth.flowOf (velocityField S.P.om) t' (S.P.tsh k) x‖ - ‖x‖| ≤
      S.P.r k * (S.C2 * S.P.δ₀ + Real.sqrt (S.P.ksh k))
  supp : S.P.St k (S.P.tsh k + u / S.P.A k) ⊆ S.P.Nnk k
  mode : Sob.normH S.s (S.P.w k (S.P.tsh k + u / S.P.A k) -
      OneRing.modeFn S.P.χ (S.P.G k) (S.P.runCoefK k u * Complex.exp (S.P.lam k * u))) ≤
    S.C2 * S.ahatK k u * (S.rhoHatK C₀ k u + S.ahatK k u + Real.sqrt (S.P.ksh k) + ηb)
  bound : Sob.normH S.s (S.P.w k (S.P.tsh k + u / S.P.A k)) ≤
    S.C2 * S.ahatK k u * (1 + S.rhoHatK C₀ k u)

/-- **The conclusions of `thm:active` and `cor:active-moment` for ring `k` at active time `u`**
(`05_single_ring.tex:893-899`, `:1104-1111`; `09_relay.tex:759-767`): (a)–(b) (`ActiveConclAB`) and,
with `q(u) = 2π pout_3[w_k(t)]`, `t = t♯_k + u/A_k`,
`|q(u) - 2π pout_*(G_k) c_k(u) e^{λ_k u}| ≤ 2π C₃ â_k(u)[ρ̂_k(u) + â_k(u) + κ♯_k^{1/2} + η_b]`. -/
structure ActiveConclAt (C₀ ηb : ℝ) (k : ℕ) (u : ℝ) : Prop extends
    ActiveConclAB S C₀ ηb k u where
  moment : ‖2 * Real.pi * BS.pout 3 (S.P.w k (S.P.tsh k + u / S.P.A k)) -
      2 * Real.pi * Eig.pout S.P.χ (S.P.G k) *
        (S.P.runCoefK k u * Complex.exp (S.P.lam k * u))‖ ≤
    2 * Real.pi * S.C3 * S.ahatK k u *
      (S.rhoHatK C₀ k u + S.ahatK k u + Real.sqrt (S.P.ksh k) + ηb)

/-- **The conclusions of `thm:active` and `cor:active-moment` hold for ring `k` on `Ph_k`**
(`09_relay.tex:759-767`), with `G = G_k`, `κ = κ♯_k`, the constant `C₀` and `η_b`: for every
active time `u ∈ [0, T̂_k]` (`t ∈ Ph_k = [t♯_k, T_k]`). -/
def ActiveConcl (C₀ ηb : ℝ) (k : ℕ) : Prop :=
  ∀ u ∈ Icc (0 : ℝ) (S.P.That k), S.ActiveConclAt C₀ ηb k u

/-- **The conclusions (a)–(b) of `thm:active` hold for ring `k` on `Ph_k`** (as used by
`lem:readout`, `09_relay.tex:1414-1416`). -/
def ActiveConclABOn (C₀ ηb : ℝ) (k : ℕ) : Prop :=
  ∀ u ∈ Icc (0 : ℝ) (S.P.That k), S.ActiveConclAB C₀ ηb k u

/-! ### Basic lemmas (fully proved) -/

variable {S}

theorem QuietConcl.mono {i : ℕ} {T T' : ℝ} (h : S.QuietConcl i T) (hT : T' ≤ T) :
    S.QuietConcl i T' where
  radial τ hτ := h.radial τ ⟨hτ.1, hτ.2.trans hT⟩
  supp τ hτ := h.supp τ ⟨hτ.1, hτ.2.trans hT⟩
  lin τ hτ := h.lin τ ⟨hτ.1, hτ.2.trans hT⟩
  bound τ hτ := h.bound τ ⟨hτ.1, hτ.2.trans hT⟩

theorem QuietHyp.mono {i : ℕ} {T T' : ℝ} (h : S.QuietHyp i T) (hT : T' ≤ T)
    (hA : 0 ≤ S.P.A i) : S.QuietHyp i T' where
  one_le := h.one_le
  lt_n := h.lt_n
  hdef t ht := h.hdef t ⟨ht.1, ht.2.trans (div_le_div_of_nonneg_right hT hA)⟩
  G_mem := h.G_mem
  eta_le τ hτ := h.eta_le τ ⟨hτ.1, hτ.2.trans hT⟩
  maj_le τ hτ := h.maj_le τ ⟨hτ.1, hτ.2.trans hT⟩

theorem ActiveConcl.ab {C₀ ηb : ℝ} {k : ℕ} (h : S.ActiveConcl C₀ ηb k) :
    S.ActiveConclABOn C₀ ηb k :=
  fun u hu => (h u hu).toActiveConclAB

theorem CoefK.mono {C₀ : ℝ} {k : ℕ} {ubar ubar' : ℝ} (h : S.CoefK C₀ k ubar) (hu : ubar' ≤ ubar) :
    S.CoefK C₀ k ubar' :=
  fun u hu' => h u ⟨hu'.1, hu'.2.trans hu⟩

end Standing

end Relay

end NonUniqueEuler
