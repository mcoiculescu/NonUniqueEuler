import NonUniqueEuler.Defs.Sec11.Extra2Boot
import NonUniqueEuler.I.Sec4.Annuli
import NonUniqueEuler.I.Sec5.Seed
import NonUniqueEuler.I.Sec5.ActiveT1
import NonUniqueEuler.I.Sec6.DefClock
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec7.SkSmall
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec10.ConstantsPos
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv

/-!
# Proof: Step 0 of the proof of `prop:bootstrap` (the initial time) and `eq:boot-start`

Proof of `I/Sec11/BootStart.lean` (`11_bootstrap.tex:230-250`): same declaration, same statement.

* Ring `n` (`:231-243`): `t♯_n = 0` (`tsh_n`), `G_n = 0` (`G_n`), `S_n(0) = S_n ⊂ 𝒩₋_n`,
  `S_n(0) ⊂ N_n`, `w_n(0) = Φ^{κ_seed} - Φ`, `c_n(0) = ℓ_*(0)(Φ^{κ_seed} - Φ)` (`clock_start`,
  `regions_basic_one`); `κ_seed ≤ κ_L` (`Valid.kseed_le`), so `lem:seed` (`seed`, `seed_const`)
  gives `κ♯_n ∈ [½κ_seed, 2κ_seed]` and `‖w_n(0)‖_{H^{M-1}} ≤ C_seedκ_seed ≤ 2C_seedκ♯_n ≤ C₀κ♯_n`
  (`two_Cseed_le_C0`); (κ1) at `2κ_seed` (`KappaList.two_lt_δ₀`) gives `κ♯_n < δ₀`, so the clock
  is defined up to level `n`. `t₁(C₀, 0) > 0` (`tOneOf_spec`, since `σ' < σ`) gives
  `ρ̂_n(0) = C₀`; `s ≤ M - 1` (`MemH.normH_mono`), `C₂ ≥ 1` (`constants_pos`) give
  `eq:boot-start`.
* Rings `j < n` (`:244-249`): `S_j(0) = S_j ⊂ {ar_j ≤ |x| ≤ r_j} ⊂ r_j𝒩₋`; `w_j(0) = 0`
  (`f_j = A_jΦ(·/r_j)` and `Φ_0⁻¹ = id`, `regions_basic_three`); `h_j` is defined at `0`:
  `D_{j+1}(0) ⊂ \bar B_{5r_{j+1}/4} ⊂ B_{ar_j/8}` and, for `i < j`,
  `S_i ⊂ {|x| ≥ ar_i} ⊂ ℝ² ∖ B_{6r_j}` (`r_{j+1} ≤ (a/32) r_j` by `eq:sk-small`, `sk_small`).
* (BA*)(0): (BA1) by the above and `𝒩₋ ⊂ 𝒩` (`annuli_chain`); (BA2) since `maj_j(0) = 0`
  (`majK_zero`) and `Ā > 0` (`constants_pos`); (BA3) for ring `n` at `u = 0` is `eq:boot-start`,
  and a ring `k < n` is not active at `0` (`t♯_k > T_n > t♯_n = 0`, `clock_order`, with
  `P.GSmall` from `standing_levels`).

The auxiliary lemmas are in the namespace `Relay.BootStartAux` to avoid clashes.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace BootStartAux

/-! ### Dilated annuli and the radii -/

/-- Membership in a dilated closed annulus `r{ρ₋ ≤ |y| ≤ ρ₊}`, `r > 0`. -/
theorem mem_scaleSet_closedAnnulus {r : ℝ} (hr : 0 < r) {ρm ρp : ℝ} {x : ℂ} :
    x ∈ scaleSet r (Sect.closedAnnulus ρm ρp) ↔ ρm * r ≤ ‖x‖ ∧ ‖x‖ ≤ ρp * r := by
  have hnorm : ‖(r : ℂ)⁻¹ * x‖ = ‖x‖ / r := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le, inv_mul_eq_div]
  show ρm ≤ ‖(r : ℂ)⁻¹ * x‖ ∧ ‖(r : ℂ)⁻¹ * x‖ ≤ ρp ↔ _
  rw [hnorm, le_div_iff₀ hr, div_le_iff₀ hr]

/-- The dilation `scaleSet r` is monotone. -/
theorem scaleSet_mono {r : ℝ} {U V : Set ℂ} (h : U ⊆ V) : scaleSet r U ⊆ scaleSet r V :=
  fun _ hx => h hx

/-- `𝒩₋_k ⊂ 𝒩_k` (`lem:annuli`, dilated by `r_k`). -/
theorem Nmk_subset_Nnk (P : Approx) (k : ℕ) : P.Nmk k ⊆ P.Nnk k :=
  scaleSet_mono annuli_chain.2.1

/-- `{a r_k ≤ |x| ≤ r_k} ⊂ 𝒩₋_k` (`lem:annuli`, dilated by `r_k`). -/
theorem ringAnn_subset_Nmk {P : Approx} (hP : P.Valid) (k : ℕ) :
    {x : ℂ | a * P.r k ≤ ‖x‖ ∧ ‖x‖ ≤ P.r k} ⊆ P.Nmk k := by
  intro x hx
  have hr := hP.r_pos k
  have ha := zero_lt_a
  show x ∈ scaleSet (P.r k) (Sect.closedAnnulus (7 / 8 * a) (5 / 4))
  rw [mem_scaleSet_closedAnnulus hr]
  obtain ⟨h1, h2⟩ := hx
  constructor
  · nlinarith
  · nlinarith

/-- `r_{i+1} ≤ (a/32) r_i` for `i ≥ 1` (`r_{i+1} = s_i r_i`, `s_i ≤ a/32` by `eq:sk-small`). -/
theorem r_succ_le {P : Approx} (hP : P.Valid) {i : ℕ} (hi : 1 ≤ i) :
    P.r (i + 1) ≤ a / 32 * P.r i := by
  have h : P.s i ≤ a / 32 := ((Rings.sk_small P hP).1 i hi).2.2
  show radius P.sbar P.μ (i + 1) ≤ a / 32 * radius P.sbar P.μ i
  rw [radius_succ _ _ hi]
  exact mul_le_mul_of_nonneg_right h (hP.r_pos i).le

/-- The radii decrease: `r_k ≤ r_i` for `1 ≤ i ≤ k`. -/
theorem r_le_of_le {P : Approx} (hP : P.Valid) {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    P.r k ≤ P.r i := by
  induction k, hik using Nat.le_induction with
  | base => exact le_rfl
  | succ m him ih =>
    have h1 := r_succ_le hP (le_trans hi him)
    have h2 : a / 32 * P.r m ≤ P.r m := by
      have hr := (hP.r_pos m).le
      have ha := a_lt_one
      nlinarith
    linarith

/-! ### Ring `n` at the initial time -/

/-- The data of `lem:seed` for the chosen seed flow. -/
theorem seedFlow_spec (S : Standing) (hS : S.Holds) :
    OneRing.IsSeedFlow S.P.χ (OneRing.seedFlow S.P.χ) (OneRing.kL S.P.χ)
      (OneRing.Cprime S.P.χ) :=
  OneRing.seedData_spec (OneRing.seed S.P.χ hS.admissible hS.hN)

/-- `κ_seed ∈ (0, κ_L]`. -/
theorem kseed_mem (S : Standing) (hS : S.Holds) : S.P.κs ∈ Ioc (0 : ℝ) (OneRing.kL S.P.χ) :=
  ⟨hS.kseed_pos, hS.kseed_le⟩

/-- `w_n(0) = Φ^{κ_seed} - Φ` (`def:clock`, `clock_start`). -/
theorem w_n_zero (S : Standing) (hS : S.Holds) :
    S.P.w S.P.n 0 = OneRing.seedDiffOf S.P.χ (OneRing.seedFlow S.P.χ) S.P.κs :=
  (Approx.clock_start S.P hS.valid hS.hN).2.2.1

/-- `κ♯_n = |ℓ_*(0)(Φ^{κ_seed} - Φ)| ∈ [½κ_seed, 2κ_seed]` (`lem:seed`). -/
theorem ksh_n_mem (S : Standing) (hS : S.Holds) :
    S.P.ksh S.P.n ∈ Icc (1 / 2 * S.P.κs) (2 * S.P.κs) := by
  have hc : S.P.c0 S.P.n =
      Eig.ellFn S.P.χ 0 (OneRing.seedDiffOf S.P.χ (OneRing.seedFlow S.P.χ) S.P.κs) :=
    (Approx.clock_start S.P hS.valid hS.hN).2.2.2
  have h := (seedFlow_spec S hS).ell_mem S.P.κs (kseed_mem S hS)
  have hk : S.P.ksh S.P.n = ‖S.P.c0 S.P.n‖ := rfl
  rw [hk, hc]
  obtain ⟨h1, h2⟩ := h
  exact ⟨by linarith, h2⟩

/-- `κ♯_n > 0`. -/
theorem ksh_n_pos (S : Standing) (hS : S.Holds) : 0 < S.P.ksh S.P.n := by
  have h := (ksh_n_mem S hS).1
  have := hS.kseed_pos
  linarith

/-- `w_n(0) ∈ H^{M-1}` and `‖w_n(0)‖_{H^{M-1}} ≤ C_seed κ_seed` (`lem:seed`). -/
theorem w_n_seed (S : Standing) (hS : S.Holds) :
    Sob.MemH (S.M - 1) (S.P.w S.P.n 0) ∧
      Sob.normH (S.M - 1) (S.P.w S.P.n 0) ≤ OneRing.Cseed S.P.χ S.s * S.P.κs := by
  have hC := (OneRing.Cseed_spec (OneRing.seed_const S.P.χ hS.admissible hS.hN
    hS.three_le_s)).2 S.P.κs (kseed_mem S hS)
  rw [w_n_zero S hS]
  exact hC

/-- `‖w_n(0)‖_{H^{M-1}} ≤ C₀κ♯_n` (`C_seedκ_seed ≤ 2C_seedκ♯_n ≤ C₀κ♯_n`, (P4)). -/
theorem w_n_le (S : Standing) (hS : S.Holds) :
    Sob.normH (S.M - 1) (S.P.w S.P.n 0) ≤ S.C0 * S.P.ksh S.P.n := by
  have h1 := (w_n_seed S hS).2
  have hk := (ksh_n_mem S hS).1
  have hCs := OneRing.Cseed_nonneg S.P.χ S.s
  have h2 := S.two_Cseed_le_C0
  have hkpos := (ksh_n_pos S hS).le
  calc Sob.normH (S.M - 1) (S.P.w S.P.n 0) ≤ OneRing.Cseed S.P.χ S.s * S.P.κs := h1
    _ ≤ OneRing.Cseed S.P.χ S.s * (2 * S.P.ksh S.P.n) :=
        mul_le_mul_of_nonneg_left (by linarith) hCs
    _ = 2 * OneRing.Cseed S.P.χ S.s * S.P.ksh S.P.n := by ring
    _ ≤ S.C0 * S.P.ksh S.P.n := mul_le_mul_of_nonneg_right h2 hkpos

/-- `S_n(0) = S_n ⊂ 𝒩₋_n` (`clock_start`, `lem:regions-basic`(1)). -/
theorem St_n_zero (S : Standing) (hS : S.Holds) : S.P.St S.P.n 0 ⊆ S.P.Nmk S.P.n := by
  rw [(Approx.clock_start S.P hS.valid hS.hN).1 S.P.n]
  exact (Approx.regions_basic_one S.P hS.valid hS.hN).2.2.2

/-- `σ' < σ = σ(0)` (from `σ' > 9/200 > 0` and `σ' < 3σ/4`). -/
theorem σ'_lt_sigma0 (S : Standing) (hS : S.Holds) : S.σ' < Eig.sigma S.P.χ 0 := by
  have h1 := hS.σ'_gt
  have h2 := hS.σ'_lt_sigma
  linarith

/-- `ρ̂_n(0) = C₀`: `G_n = 0` and `t₁(C₀, 0) > 0` (`2^{p/2}C₀ > 1`). -/
theorem rhoHat_n_zero (S : Standing) (hS : S.Holds) : S.rhoHatK S.C0 S.P.n 0 = S.C0 := by
  have ht := (OneRing.tOneOf_spec (σ'_lt_sigma0 S hS) S.one_le_C0).1
  show OneRing.rhoHatOf (Eig.sigma S.P.χ (S.P.G S.P.n)) S.σ' S.C0 0 = S.C0
  rw [S.P.G_n, OneRing.rhoHatOf_of_lt ht]
  simp

/-! ### The rings `j < n` at the initial time -/

/-- `S_j(0) = S_j` for every `j` (`clock_start`). -/
theorem St_zero (S : Standing) (hS : S.Holds) (j : ℕ) : S.P.St j 0 = S.P.S j :=
  (Approx.clock_start S.P hS.valid hS.hN).1 j

/-- The maximal flow at its initial time is the identity (also for the junk value). -/
theorem maxFlow_self (F : ℝ → ℂ → ℂ) (U : Set (ℝ × ℂ)) (s : ℝ) (y : ℂ) :
    Smooth.maxFlow F U s s y = y := by
  classical
  by_cases h : ∃ (J : Set ℝ) (γ : ℝ → ℂ), Smooth.IsMaxSol F U s y J γ
  · exact (Smooth.isMaxSol_maxFlow h).init
  · rw [Smooth.maxFlow, dite_eq_right h]

/-- `w_j(0) = 0` for `1 ≤ j < n`: ring `j` starts at `Φ` in ring-`j` units. -/
theorem w_zero (S : Standing) (hS : S.Holds) {j : ℕ} (hj : 1 ≤ j) (hjn : j < S.P.n) :
    S.P.w j 0 = 0 := by
  have hmem : j ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.mpr ⟨hj, hjn.le⟩
  have h3 := (Approx.regions_basic_three S.P hS.valid hS.hN hmem le_rfl).1
  have hfun : S.P.omegaRing j 0 = S.P.term j := by
    rw [h3]
    funext x
    exact congrArg (S.P.term j) (maxFlow_self _ _ _ _)
  have h0 : S.P.unitsVort j (S.P.term j) = ringPhi S.P.χ := hS.valid.ringConfig_ring0 hj hjn
  funext y
  rw [Approx.w_apply, hfun, h0]
  simp

/-- `S_j(0) ⊂ 𝒩₋_j` for `1 ≤ j < n` (`S_j ⊂ {ar_j ≤ |x| ≤ r_j}`, `lem:regions-basic`(1)). -/
theorem St_zero_sub (S : Standing) (hS : S.Holds) {j : ℕ} (hj : 1 ≤ j) (hjn : j < S.P.n) :
    S.P.St j 0 ⊆ S.P.Nmk j := by
  rw [St_zero S hS j]
  exact ((Approx.regions_basic_one S.P hS.valid hS.hN).2.2.1 j hj hjn).trans
    (ringAnn_subset_Nmk hS.valid j)

/-- Every point of `S_i(0)`, `1 ≤ i ≤ n`, has `|x| ≤ (5/4) r_i`. -/
theorem norm_le_of_mem_St_zero (S : Standing) (hS : S.Holds) {i : ℕ} (hi : 1 ≤ i)
    (hin : i ≤ S.P.n) {x : ℂ} (hx : x ∈ S.P.St i 0) : ‖x‖ ≤ 5 / 4 * S.P.r i := by
  have hr := hS.valid.r_pos i
  rcases lt_or_eq_of_le hin with hlt | heq
  · rw [St_zero S hS i] at hx
    have h := ((Approx.regions_basic_one S.P hS.valid hS.hN).2.2.1 i hi hlt hx).2
    linarith
  · subst heq
    have h := St_n_zero S hS hx
    have h' : x ∈ scaleSet (S.P.r S.P.n) (Sect.closedAnnulus (7 / 8 * a) (5 / 4)) := h
    exact ((mem_scaleSet_closedAnnulus hr).1 h').2

/-- `h^in_j` is defined at `0` for `1 ≤ j < n`: `D_{j+1}(0) ⊂ \bar B_{5r_{j+1}/4} ⊂ B_{ar_j/8}`. -/
theorem hInDefined_zero (S : Standing) (hS : S.Holds) {j : ℕ} (hj : 1 ≤ j) :
    S.P.HInDefined j 0 := by
  intro x hx
  simp only [Approx.D, mem_iUnion] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  have hi' := Finset.mem_Icc.mp hi
  have h1 := norm_le_of_mem_St_zero S hS (by omega) hi'.2 hxi
  have h2 := r_le_of_le hS.valid (by omega : 1 ≤ j + 1) hi'.1
  have h3 := r_succ_le hS.valid hj
  have hr := hS.valid.r_pos j
  have ha := zero_lt_a
  rw [mem_ball_zero_iff]
  nlinarith

/-- `h^out_j` is defined at `0` for `1 ≤ j < n`: the rings `i < j` lie in
`{|x| ≥ ar_i} ⊂ ℝ² ∖ B_{6r_j}`. -/
theorem hOutDefined_zero (S : Standing) (hS : S.Holds) {j : ℕ} (hjn : j < S.P.n) :
    S.P.HOutDefined j 0 := by
  intro i hi
  have hi' := Finset.mem_Ico.mp hi
  rw [eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hxb⟩
  rw [St_zero S hS i] at hx
  have h1 := ((Approx.regions_basic_one S.P hS.valid hS.hN).2.2.1 i hi'.1 (by omega) hx).1
  have h2 := r_le_of_le hS.valid (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ j)
  have h3 := r_succ_le hS.valid hi'.1
  have hr := hS.valid.r_pos i
  have ha := zero_lt_a
  rw [mem_ball_zero_iff] at hxb
  nlinarith

/-- `h_j` is defined at `0` for `1 ≤ j < n`. -/
theorem hDefined_zero (S : Standing) (hS : S.Holds) {j : ℕ} (hj : 1 ≤ j) (hjn : j < S.P.n) :
    S.P.HDefined j 0 :=
  ⟨hInDefined_zero S hS hj, hOutDefined_zero S hS hjn⟩

/-- A ring `k < n` is not active at `0`: `t♯_k > T_n > t♯_n = 0` (`lem:clock`(1)). -/
theorem not_activeAt_zero (S : Standing) (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < S.P.n) : ¬ S.P.ActiveAt k 0 := by
  rintro ⟨hc, htsh, -⟩
  obtain ⟨-, -, hG, -⟩ := standing_levels S hS
  obtain ⟨h1, -, h3, -⟩ := Approx.clock_order S.P hS.valid hS.hN hG hk hc
  have a1 := h1 S.P.n (Finset.mem_Icc.mpr ⟨hkn.le, le_rfl⟩)
  have a3 := h3 k S.P.n le_rfl hkn le_rfl
  rw [S.P.tsh_n] at a1
  linarith

end BootStartAux

open BootStartAux in
/-- **Step 0 of the proof of `prop:bootstrap`** (`11_bootstrap.tex:230-250`), with `eq:boot-start`:
under (N) and (P0)–(P6), the conclusions `S.BootStartConcl` hold. -/
theorem boot_start (S : Standing) (hS : S.Holds) (hL : S.ParamLists) : S.BootStartConcl := by
  have hpos := constants_pos S hS.admissible hS.hN hS.σ'_gt hS.σ'_lt_sigma hS.δ₀_pos
    hS.one_lt_μ hS.Tpin_pos
  have htsh : S.P.tsh S.P.n = 0 := S.P.tsh_n
  have hkpos := ksh_n_pos S hS
  have hkmem := ksh_n_mem S hS
  have h2k := hL.kappa.two_lt_δ₀ hS.δ₀_pos hS.one_lt_μ
  -- the clock is defined up to level `n`
  have hclock : S.P.ClockUpTo S.P.n := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hin : i = S.P.n := le_antisymm hi'.2 hi'.1
    subst hin
    rw [htsh]
    exact ⟨(Approx.clock_start S.P hS.valid hS.hN).2.1, hkpos, by linarith [hkmem.2]⟩
  -- (Init) for ring `n`
  have hinit : S.ActiveInitK S.C0 S.P.n := by
    show Sob.normH (S.M - 1) (S.P.w S.P.n (S.P.tsh S.P.n)) ≤ S.C0 * S.P.ksh S.P.n ∧
      S.P.St S.P.n (S.P.tsh S.P.n) ⊆ S.P.Nmk S.P.n
    rw [htsh]
    exact ⟨w_n_le S hS, St_n_zero S hS⟩
  have hrho := rhoHat_n_zero S hS
  -- `eq:boot-start`
  have hle : Sob.normH S.s (S.P.w S.P.n 0) ≤ S.C0 * S.P.ksh S.P.n := by
    have hsM : S.s ≤ S.M - 1 := by
      show S.s ≤ OneRing.Mact S.P.χ S.s - 1
      rw [OneRing.Mact_eq]
      omega
    exact ((w_n_seed S hS).1.normH_mono hsM).trans (w_n_le S hS)
  have hahat : S.ahatK S.P.n 0 = S.P.ksh S.P.n := OneRing.ahat_zero _ _
  have hlt : S.C0 * S.P.ksh S.P.n < S.C2 * S.ahatK S.P.n 0 * (1 + S.rhoHatK S.C0 S.P.n 0) := by
    rw [hahat, hrho]
    have hC2 := hpos.one_le_C2
    have hC0 := S.one_le_C0
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hC2) hkpos.le)
      (by linarith : (0 : ℝ) ≤ 1 + S.C0)]
  -- the rings `j < n`
  have hquiet : ∀ j ∈ Finset.Ico 1 S.P.n,
      S.P.St j 0 ⊆ S.P.Nmk j ∧ S.P.w j 0 = 0 ∧ S.P.HDefined j 0 := by
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    exact ⟨St_zero_sub S hS hj'.1 hj'.2, w_zero S hS hj'.1 hj'.2,
      hDefined_zero S hS hj'.1 hj'.2⟩
  -- (BA*)(0)
  have hba : S.BAstar 0 := by
    refine ⟨?_, ?_, ?_⟩
    · intro t' ht' j hj _
      have ht0 : t' = 0 := le_antisymm ht'.2 ht'.1
      subst ht0
      have hj' := Finset.mem_Icc.mp hj
      rcases lt_or_eq_of_le hj'.2 with hlt' | heq
      · exact ((hquiet j (Finset.mem_Ico.mpr ⟨hj'.1, hlt'⟩)).1).trans (Nmk_subset_Nnk S.P j)
      · subst heq
        exact (St_n_zero S hS).trans (Nmk_subset_Nnk S.P _)
    · intro t' ht' j hj _
      have ht0 : t' = 0 := le_antisymm ht'.2 ht'.1
      subst ht0
      refine ⟨fun t'' ht'' => ?_, ?_⟩
      · have ht0' : t'' = 0 := le_antisymm ht''.2 ht''.1
        subst ht0'
        exact (hquiet j hj).2.2
      · have hm : S.maj j (S.P.A j * 0) = 0 := by
          rw [mul_zero]
          exact S.P.majK_zero S.Mh j
        rw [hm]
        exact mul_nonneg hpos.Abar_pos.le (hS.valid.eps_pos j).le
    · intro t' ht' k hk hact
      have ht0 : t' = 0 := le_antisymm ht'.2 ht'.1
      subst ht0
      have hk' := Finset.mem_Icc.mp hk
      rcases lt_or_eq_of_le hk'.2 with hlt' | heq
      · exact absurd hact (not_activeAt_zero S hS hk'.1 hlt')
      · subst heq
        have hu : S.P.activeTime S.P.n 0 = 0 := by
          rw [Approx.activeTime, htsh]
          ring
        rw [hu]
        exact hle.trans hlt.le
  exact ⟨hclock, hkmem, hinit, hrho, hle, hlt, hquiet, hba⟩

end Relay

end NonUniqueEuler
