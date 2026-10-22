import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.Seed.Field
import NonUniqueEuler.I.Infra.Sobolev.TaylorFamily
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.SmoothB.Flow
import NonUniqueEuler.I.SmoothB.FlowFacts
import NonUniqueEuler.I.Infra.Equimeasurable.Lipschitz
import NonUniqueEuler.H.Sec5.Seed.Ell

/-!
# Proof of `lem:seed` (the seeded ring)

Proof of `I/Sec5/Seed.lean` (`seed`, `seed_const`; `05_single_ring.tex:1131-1219`).

Structure (`05_single_ring.tex:1148-1219`):
1. the seed field `V` and `eq:seed-first` (`V·∇Φ = 2Re φ_*(0)`): `seedField_exists`
   (`I/Sec5/Seed/Field.lean`);
2. the flow `Y_κ = Φ_V(κ, 0, ·)` and its properties: `lem:flow` (`I/SmoothB/Flow.lean`) and the
   flow facts (`I/SmoothB/FlowFacts.lean`); `Φ^κ = Φ ∘ Y_κ` is `C_c^∞`, `≥ 0`, symmetric,
   equimeasurable with `Φ` (`Equimeasurable.comp_measurePreserving`);
3. the expansion `‖Φ^κ - Φ - 2κRe φ_*(0)‖_{H^k} ≤ C'_k κ²`: the generic second-order Taylor
   estimate `Sob.normH_taylor_two_le` (`I/Infra/Sobolev/TaylorFamily.lean`) for
   `F(t, y) = Φ(Y_t y)`, with `∂_tF(0, ·) = V·∇Φ = 2Re φ_*(0)`;
4. `κ_L = min(1, a/(8(1+M)), 1/(2(1+‖ℓ_*(0)‖C'_0)))` with `M = sup|V|`: support in `𝒩₋` from the
   displacement bound `|Y_κ y - y| ≤ κM ≤ a/8` (`flowOf_disp_le`), and
   `|ℓ_*(0)(Φ^κ - Φ) - κ| ≤ ‖ℓ_*(0)‖C'_0κ² ≤ κ/2` (`H/Sec5/Seed/Ell.lean`).
`seed_const`: `‖Φ^κ - Φ‖_{H^{M-1}} ≤ ‖2κRe φ_*(0)‖_{H^{M-1}} + C'_{M-1}κ² ≤
(2‖Re φ_*(0)‖_{H^{M-1}} + C'_{M-1}κ_L)κ` for the chosen data.

Deviation: the support statement `supp Φ^κ ⊂ 𝒩₋` is obtained
directly from `|Y_κ y - y| ≤ a/8` (`{7a/8 ≤ |y| ≤ 1 + a/8} ⊆ 𝒩₋` because `a < 1`), without
`lem:annuli`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

namespace SeedP

/-! ### The flow of the seed field -/

section Flow

variable {V : ℂ → ℂ} {K : Set ℂ}

theorem hasCompactSupport_of_off (hK : IsCompact K) (hoff : ∀ y ∉ K, V y = 0) :
    HasCompactSupport V :=
  HasCompactSupport.intro hK hoff

theorem exists_bound (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hK : IsCompact K)
    (hoff : ∀ y ∉ K, V y = 0) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖V x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hV.continuous.bounded_above_of_compact_support
    (hasCompactSupport_of_off hK hoff)
  exact ⟨max M 0, le_max_right _ _, fun x => (hM x).trans (le_max_left _ _)⟩

theorem isSmoothBoundedField (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hK : IsCompact K)
    (hoff : ∀ y ∉ K, V y = 0) : Smooth.IsSmoothBoundedField fun _ : ℝ => V := by
  obtain ⟨M, -, hM⟩ := exists_bound hV hK hoff
  refine ⟨?_, fun T _ => ⟨M, fun _ _ x => hM x⟩⟩
  have : Function.uncurry (fun _ : ℝ => V) = fun p : ℝ × ℂ => V p.2 := rfl
  rw [this]
  exact hV.comp contDiff_snd

theorem flow_contDiff (hu : Smooth.IsSmoothBoundedField fun _ : ℝ => V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℂ => Smooth.flowOf (fun _ => V) p.1 0 p.2) := by
  have h := Smooth.flowOf_contDiff hu
  exact h.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))

theorem flow_zero (hu : Smooth.IsSmoothBoundedField fun _ : ℝ => V) (y : ℂ) :
    Smooth.flowOf (fun _ => V) 0 0 y = y :=
  (Smooth.flowOf_global hu 0 y).2.init

theorem flow_hasDerivAt (hu : Smooth.IsSmoothBoundedField fun _ : ℝ => V) (y : ℂ) (t : ℝ) :
    HasDerivAt (fun τ => Smooth.flowOf (fun _ => V) τ 0 y)
      (V (Smooth.flowOf (fun _ => V) t 0 y)) t :=
  (Smooth.flowOf_global hu 0 y).2.hasDerivAt t (mem_univ t)

theorem flow_off (hu : Smooth.IsSmoothBoundedField fun _ : ℝ => V) (hoff : ∀ y ∉ K, V y = 0)
    (κ : ℝ) {y : ℂ} (hy : y ∉ K) : Smooth.flowOf (fun _ => V) κ 0 y = y :=
  Smooth.flowOf_eq_self_of_zero hu (fun _ => hoff y hy) κ 0

theorem flow_disp (hu : Smooth.IsSmoothBoundedField fun _ : ℝ => V) {M : ℝ}
    (hM : ∀ x, ‖V x‖ ≤ M) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (y : ℂ) :
    ‖Smooth.flowOf (fun _ => V) κ 0 y - y‖ ≤ κ * M := by
  have h := Smooth.flowOf_disp_le hu (T := 1) (M := M) (fun _ _ x => hM x)
    (s := 0) (t := κ) ⟨by norm_num, by norm_num⟩ ⟨by linarith, hκ1⟩ y
  rwa [sub_zero, abs_of_nonneg hκ0] at h

end Flow

/-! ### Elementary facts -/

theorem isClosed_annNm : IsClosed annNm := by
  have h : annNm = {x : ℂ | 7 / 8 * a ≤ ‖x‖} ∩ {x : ℂ | ‖x‖ ≤ 5 / 4} := rfl
  rw [h]
  exact (isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)

theorem subset_annN {K : Set ℂ} (hK : K ⊆ {y : ℂ | a / 2 < ‖y‖ ∧ ‖y‖ < 2}) : K ⊆ annN :=
  fun _ hy => ⟨(hK hy).1.le, (hK hy).2.le⟩

end SeedP

open SeedP

/-- **`lem:seed`, the `Φ`-only data** (`05_single_ring.tex:1131-1147`). Assume (N1)–(N3). There
are a smooth area-preserving flow `(Y_κ)_{κ∈ℝ}` on `ℝ²` that is the identity outside a compact
subset of `{a/2 < |y| < 2}` and commutes with `O_{2π/3}`, a number `κ_L > 0` and numbers `C'_k`,
such that `Φ^κ = Φ∘Y_κ` satisfies, for every `κ ∈ (0,κ_L]`: `Φ^κ ∈ C_c^∞`, `Φ^κ ≥ 0`, `Φ^κ` is
`3`-fold symmetric and equimeasurable with `Φ`, `supp Φ^κ ⊂ 𝒩₋`, `|ℓ_*(0)(Φ^κ - Φ)| ∈ [κ/2,2κ]`,
and `‖Φ^κ - Φ - 2κRe φ_*(0)‖_{H^k} ≤ C'_kκ²` for every `k` (`IsSeedFlow`). -/
theorem seed (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ∃ (Y : ℝ → ℂ → ℂ) (κL : ℝ) (C' : ℕ → ℝ), IsSeedFlow χ Y κL C' := by
  obtain ⟨V, K, hV, hK, hKsub, hoff, hdiv, hrot, hfirst⟩ := seedField_exists χ hχ hN
  obtain ⟨hΦs, hΦc, hΦrad, hΦb, -, hΦsupp, ha0, ha1⟩ := ringFacts_of_admissible hχ
  have hu := isSmoothBoundedField hV hK hoff
  obtain ⟨M, hM0, hM⟩ := exists_bound hV hK hoff
  set Y : ℝ → ℂ → ℂ := fun κ y => Smooth.flowOf (fun _ => V) κ 0 y with hYdef
  have hYs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => Y p.1 p.2) :=
    flow_contDiff hu
  have hY0 : ∀ y, Y 0 y = y := flow_zero hu
  have hYoff : ∀ κ, ∀ y ∉ K, Y κ y = y := fun κ y hy => flow_off hu hoff κ hy
  have hYκ : ∀ κ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Y κ) := fun κ =>
    hYs.comp (contDiff_const.prodMk contDiff_id)
  have hΦd : Differentiable ℝ (ringPhi χ) := hΦs.differentiable (by simp)
  -- the Taylor expansion of `F(t, y) = Φ(Y_t y)`
  set F : ℝ → ℂ → ℝ := fun t y => ringPhi χ (Y t y) with hFdef
  have hFs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => F p.1 p.2) :=
    hΦs.comp hYs
  have hFoff : ∀ t : ℝ, ∀ y ∉ K, F t y = F 0 y := by
    intro t y hy
    simp only [hFdef, hYoff t y hy, hY0]
  choose C' hC'0 hC' using fun k => Sob.normH_taylor_two_le hFs hK hFoff k
  have hderiv : ∀ y, deriv (fun t => F t y) 0 = 2 * (Eig.phi χ 0 y).re := by
    intro y
    have h0 : HasDerivAt (fun t => Y t y) (V (Y 0 y)) 0 := flow_hasDerivAt hu y 0
    have h1 : HasDerivAt (ringPhi χ ∘ fun t => Y t y)
        (fderiv ℝ (ringPhi χ) (Y 0 y) (V (Y 0 y))) 0 :=
      HasFDerivAt.comp_hasDerivAt (l := ringPhi χ) (f := fun t => Y t y) 0
        (hΦd (Y 0 y)).hasFDerivAt h0
    have h2 : deriv (fun t => F t y) 0 = fderiv ℝ (ringPhi χ) (Y 0 y) (V (Y 0 y)) := h1.deriv
    rw [h2, hY0, hfirst]
  have hexp_eq : ∀ κ : ℝ, (fun y => seedDiffOf χ Y κ y - modeFn χ 0 κ y) =
      fun y => ((F κ y - F 0 y - κ * deriv (fun t => F t y) 0 : ℝ) : ℂ) := by
    intro κ
    funext y
    rw [hderiv y, SeedH.modeFn_eq]
    simp only [seedDiffOf, PhiOf, hFdef, hY0]
    push_cast
    ring
  -- the constants
  set L : ℝ := ‖Eig.ell χ 0 0‖ with hLdef
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    exact norm_nonneg (Eig.ell χ 0 0)
  have hLC : 0 ≤ L * C' 0 := mul_nonneg hL0 (hC'0 0)
  set κL : ℝ := min 1 (min (a / (8 * (1 + M))) (1 / (2 * (1 + L * C' 0)))) with hκLdef
  have hκL1 : κL ≤ 1 := min_le_left _ _
  have hκLa : κL ≤ a / (8 * (1 + M)) := (min_le_right _ _).trans (min_le_left _ _)
  have hκLe : κL ≤ 1 / (2 * (1 + L * C' 0)) := (min_le_right _ _).trans (min_le_right _ _)
  have hκLpos : 0 < κL := by
    refine lt_min one_pos (lt_min ?_ ?_)
    · exact div_pos ha0 (by positivity)
    · exact div_pos one_pos (by positivity)
  have hIcc : ∀ κ ∈ Ioc (0 : ℝ) κL, κ ∈ Icc (0 : ℝ) 1 := fun κ hκ =>
    ⟨hκ.1.le, hκ.2.trans hκL1⟩
  have hmp : ∀ κ, MeasurePreserving (Y κ) volume volume := fun κ =>
    Smooth.flowOf_measurePreserving hu (fun _ x => hdiv x) κ 0
  refine ⟨Y, κL, C', ?_⟩
  exact
    { contDiff := hYs
      zero := hY0
      add := fun κ κ' y => Smooth.flowOf_autonomous_add hu κ κ' y
      measurePreserving := hmp
      eq_self_off := ⟨K, hK, hKsub, hYoff⟩
      rot_comm := fun κ y => Smooth.flowOf_rot hu (fun _ x => hrot x) κ 0 y
      kL_pos := hκLpos
      phi_contDiff := fun κ _ => hΦs.comp (hYκ κ)
      phi_hasCompactSupport := by
        intro κ _
        refine HasCompactSupport.intro (hK.union hΦc) ?_
        intro y hy
        simp only [mem_union, not_or] at hy
        simp only [PhiOf, hYoff κ y hy.1]
        exact image_eq_zero_of_notMem_tsupport hy.2
      phi_nonneg := fun κ _ y => (hΦb _).1
      phi_sym := by
        intro κ _ y
        simp only [PhiOf]
        have h : Y κ (rot (2 * Real.pi / 3) y) = rot (2 * Real.pi / 3) (Y κ y) :=
          Smooth.flowOf_rot hu (fun _ x => hrot x) κ 0 y
        rw [h]
        exact hΦrad _ _
      phi_equimeasurable := by
        intro κ _
        have hL1 : MemLp (ringPhi χ) 1 volume := hΦs.continuous.memLp_of_hasCompactSupport hΦc
        exact Equimeasurable.comp_measurePreserving hL1 (hmp κ)
      phi_tsupport := by
        intro κ hκ
        refine closure_minimal ?_ isClosed_annNm
        intro y hy
        have hy' : Y κ y ∈ tsupport (ringPhi χ) := subset_tsupport _ hy
        obtain ⟨h1, h2⟩ := hΦsupp hy'
        have hd := flow_disp hu hM hκ.1.le (hκ.2.trans hκL1) y
        have hκM : κ * M ≤ a / 8 := by
          have h3 : κ * (8 * (1 + M)) ≤ a :=
            (le_div_iff₀ (by positivity)).1 (hκ.2.trans hκLa)
          nlinarith [hκ.1]
        have hn1 : ‖Y κ y‖ ≤ ‖y‖ + κ * M := by
          have := norm_sub_norm_le (Y κ y) y
          linarith
        have hn2 : ‖y‖ ≤ ‖Y κ y‖ + κ * M := by
          have := norm_sub_norm_le y (Y κ y)
          rw [norm_sub_rev] at this
          linarith
        exact ⟨by linarith, by linarith⟩
      ell_mem := by
        intro κ hκ
        set f : ℂ → ℂ := seedDiffOf χ Y κ with hfdef
        set m : ℂ → ℂ := modeFn χ 0 κ with hmdef
        have hr : Sob.MemH 0 (fun y => f y - m y) := by
          rw [hexp_eq κ]
          exact (hC' 0 κ (hIcc κ hκ)).1
        have hrn : Sob.normH 0 (fun y => f y - m y) ≤ C' 0 * κ ^ 2 := by
          rw [hexp_eq κ]
          exact (hC' 0 κ (hIcc κ hκ)).2
        have hm : Sob.MemH 0 m := SeedH.modeFn_memH hχ hN κ 0
        have hmK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → m x = 0 :=
          SeedH.modeFn_zero_outside hχ hN κ
        have hfK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → f x = 0 := by
          refine Eventually.of_forall fun x hx => ?_
          have hxK : x ∉ K := fun h => hx (subset_annN hKsub h)
          simp only [hfdef, seedDiffOf, PhiOf, hYoff κ x hxK, sub_self, Complex.ofReal_zero]
        have hf : Sob.MemH 0 f := by
          have h := (hr.add hm).1
          have he : ((fun y => f y - m y) + m) = f := by
            funext y
            simp
          rwa [he] at h
        have hrK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → f x - m x = 0 := by
          filter_upwards [hfK, hmK] with x h1 h2 hx
          rw [h1 hx, h2 hx, sub_zero]
        have hsub := SeedH.ellFn_sub hχ hN hf hfK hm hmK
        rw [SeedH.ellFn_modeFn hχ hN κ] at hsub
        have hb := SeedH.ellFn_bound hχ hN hr hrK
        have hsmall : ‖Eig.ellFn χ 0 (fun y => f y - m y)‖ ≤ κ / 2 := by
          refine hb.trans ?_
          have h1 : L * Sob.normH 0 (fun y => f y - m y) ≤ L * (C' 0 * κ ^ 2) :=
            mul_le_mul_of_nonneg_left hrn hL0
          have h2 : κ * (2 * (1 + L * C' 0)) ≤ 1 :=
            (le_div_iff₀ (by positivity)).1 (hκ.2.trans hκLe)
          have h3 : L * (C' 0 * κ ^ 2) ≤ κ / 2 := by
            have hκ0 := hκ.1
            nlinarith
          exact h1.trans h3
        have hfe : Eig.ellFn χ 0 f = (κ : ℂ) + Eig.ellFn χ 0 (fun y => f y - m y) := by
          rw [hsub]
          ring
        have hnκ : ‖(κ : ℂ)‖ = κ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hκ.1.le]
        constructor
        · have h1 := norm_sub_le (Eig.ellFn χ 0 f) (Eig.ellFn χ 0 (fun y => f y - m y))
          rw [hfe, add_sub_cancel_right, hnκ] at h1
          rw [hfe]
          linarith
        · have h1 := norm_add_le (κ : ℂ) (Eig.ellFn χ 0 (fun y => f y - m y))
          rw [hnκ] at h1
          rw [hfe]
          linarith [hκ.1]
      expansion_memH := by
        intro κ hκ k
        rw [hexp_eq κ]
        exact (hC' k κ (hIcc κ hκ)).1
      expansion := by
        intro κ hκ k
        rw [hexp_eq κ]
        exact (hC' k κ (hIcc κ hκ)).2 }

/-- **`lem:seed`, the constant `C_seed`** (`05_single_ring.tex:1137-1143`). Assume (N1)–(N3) and
let `s ≥ 3`, `M = s + N_G + 2`. For the chosen seed data (`seedFlow χ`, `kL χ`) there is
`C_seed ≥ 0` with `Φ^κ - Φ ∈ H^{M-1}` and `‖Φ^κ - Φ‖_{H^{M-1}} ≤ C_seed κ` for every
`κ ∈ (0,κ_L]` (`IsSeedConst`). -/
theorem seed_const (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 3 ≤ s) : ∃ C : ℝ, 0 ≤ C ∧ IsSeedConst χ s C := by
  have _ : 3 ≤ s := hs
  have hS := seedData_spec (seed χ hχ hN)
  set k : ℕ := Mact χ s - 1 with hkdef
  set B : ℝ := Sob.normH k fun x => (((Eig.phi χ 0 x).re : ℝ) : ℂ) with hBdef
  have hB0 : 0 ≤ B := Sob.normH_nonneg _ _
  have hkL := hS.kL_pos
  have hC'0 : 0 ≤ Cprime χ k := by
    have h1 := hS.expansion (kL χ) ⟨hkL, le_rfl⟩ k
    have h2 := Sob.normH_nonneg k
      (fun y => seedDiffOf χ (seedFlow χ) (kL χ) y - modeFn χ 0 (kL χ) y)
    have h3 : 0 ≤ Cprime χ k * kL χ ^ 2 := h2.trans h1
    have h4 : 0 < kL χ ^ 2 := by positivity
    exact nonneg_of_mul_nonneg_left h3 h4
  refine ⟨2 * B + Cprime χ k * kL χ, by positivity, ?_⟩
  intro κ hκ
  have hr := hS.expansion_memH κ hκ k
  have hrn := hS.expansion κ hκ k
  have hm := SeedH.modeFn_memH hχ hN κ k
  have hmn := SeedH.normH_modeFn hχ hN hκ.1.le k
  have hsum := hr.add hm
  have he : ((fun y => seedDiffOf χ (seedFlow χ) κ y - modeFn χ 0 κ y) + modeFn χ 0 κ) =
      seedDiffOf χ (seedFlow χ) κ := by
    funext y
    simp
  rw [he] at hsum
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  rw [hmn]
  have h1 : Cprime χ k * κ ^ 2 ≤ Cprime χ k * kL χ * κ := by
    have : Cprime χ k * κ ^ 2 = Cprime χ k * κ * κ := by ring
    rw [this]
    have h2 : Cprime χ k * κ ≤ Cprime χ k * kL χ := mul_le_mul_of_nonneg_left hκ.2 hC'0
    exact mul_le_mul_of_nonneg_right h2 hκ.1.le
  nlinarith

end OneRing

end NonUniqueEuler
