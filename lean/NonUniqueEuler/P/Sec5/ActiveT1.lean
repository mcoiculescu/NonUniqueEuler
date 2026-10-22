import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec4.PropU

/-!
# Proof: the `t₁` facts of `thm:active` (`tOneOf_spec`, `active_tOne`)

Proof of `I/Sec5/ActiveT1.lean`. The two declarations, with their statements copied verbatim,
are those of `I/Sec5/Active.lean` that concern `t₁`:

* `tOneOf_spec` — `t₁(C₀,G)` (`05_single_ring.tex:874-875`) and `t̄₁(C₀)` (`:901-905`) are well
  defined: the infimum `tOneOf σ σ' C₀` is positive, has the defining property, and is minimal.
* `active_tOne` — the "Moreover" part of `thm:active` (`:901-911`, proof `:960-971`):
  `t₁(C₀,G) ≤ t̄₁(C₀)` and `â(u)ρ̂(u) ≤ C(C₀)κ⟨u⟩^pe^{σ'u}` for `u ≥ 0`.

**Proof** (`05_single_ring.tex:960-971`, plus the existence of `t₁`, which the manuscript takes
for granted). Write `f(t) = 2^{p/2}C₀⟨t⟩^pe^{-(σ-σ')t}`.
1. `f(t) → 0` as `t → ∞` (`⟨t⟩ ≤ 1 + t` and `x^pe^{-x} → 0`), so the set
   `S = {t ≥ 0 | f ≤ 1 on [t,∞)}` is nonempty; it is bounded below by `0`. Its infimum `t₁` lies in
   `S`: `f ≤ 1` on `(t₁,∞)` by the infimum property, hence on the closure `[t₁,∞)` since `f` is
   continuous. `f(0) = 2^{p/2}C₀ > 1`, so `t₁ ≠ 0`, i.e. `t₁ > 0`.
2. `σ_b ≤ σ(G) ≤ σ_max` (`prop:U`(a), `I/Sec4/PropU.lean`), so `f_{σ(G)} ≤ f_{σ_b}` on `[0,∞)`
   and minimality gives `t₁ ≤ t̄₁`.
3. For `u < t₁`, `âρ̂ = C₀κ⟨u⟩^pe^{σ'u}`; for `u ≥ t₁`,
   `âρ̂ = κe^{σt₁}⟨u-t₁⟩^pe^{σ'(u-t₁)} ≤ e^{σ_max t̄₁}κ⟨u⟩^pe^{σ'u}` (`σ' > 0`, `σ_max ≥ σ_b > 0`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-! ### Elementary facts about `⟨t⟩` -/

theorem ActiveT1.jap_nonneg (t : ℝ) : 0 ≤ Prelim.jap t := Real.sqrt_nonneg _

theorem ActiveT1.jap_zero : Prelim.jap 0 = 1 := by
  simp [Prelim.jap]

theorem ActiveT1.jap_le_one_add {t : ℝ} (ht : 0 ≤ t) : Prelim.jap t ≤ 1 + t := by
  rw [Prelim.jap, Real.sqrt_le_left (by linarith)]
  nlinarith

theorem ActiveT1.jap_le_jap {t u : ℝ} (h : t ^ 2 ≤ u ^ 2) : Prelim.jap t ≤ Prelim.jap u :=
  Real.sqrt_le_sqrt (by linarith)

theorem ActiveT1.continuous_jap : Continuous Prelim.jap := by
  unfold Prelim.jap
  fun_prop

/-! ### The function `f(t) = 2^{p/2}C₀⟨t⟩^pe^{-(σ-σ')t}` -/

theorem ActiveT1.continuous_f (σ σ' C₀ : ℝ) :
    Continuous fun t : ℝ =>
      (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t ^ pW * Real.exp (-((σ - σ') * t)) := by
  have := ActiveT1.continuous_jap
  fun_prop

/-- Upper bound for `f` on `[0,∞)` by a multiple of `x^pe^{-x}` at `x = ε(1+t)`, `ε = σ - σ'`. -/
theorem ActiveT1.f_le {σ σ' C₀ t : ℝ} (hσ : σ' < σ) (hC₀ : 0 ≤ C₀) (ht : 0 ≤ t) :
    (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t ^ pW * Real.exp (-((σ - σ') * t)) ≤
      (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Real.exp (σ - σ') / (σ - σ') ^ pW *
        (((σ - σ') * (1 + t)) ^ pW * Real.exp (-((σ - σ') * (1 + t)))) := by
  set ε := σ - σ' with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hA : 0 ≤ (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ := by positivity
  have h1 : Prelim.jap t ^ pW ≤ (1 + t) ^ pW :=
    pow_le_pow_left₀ (ActiveT1.jap_nonneg t) (ActiveT1.jap_le_one_add ht) _
  have h2 : Real.exp (-(ε * t)) = Real.exp ε * Real.exp (-(ε * (1 + t))) := by
    rw [← Real.exp_add]
    ring_nf
  have h3 : (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Real.exp ε / ε ^ pW *
        ((ε * (1 + t)) ^ pW * Real.exp (-(ε * (1 + t)))) =
      (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * (1 + t) ^ pW * Real.exp (-(ε * t)) := by
    rw [h2, mul_pow]
    field_simp
  rw [h3]
  gcongr

/-- `f(t) → 0` as `t → ∞`, in the form: `f ≤ 1` on some half-line `[T,∞)`. -/
theorem ActiveT1.exists_f_le_one {σ σ' C₀ : ℝ} (hσ : σ' < σ) (hC₀ : 0 ≤ C₀) :
    ∃ T : ℝ, ∀ t' : ℝ, T ≤ t' →
      (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t' ^ pW * Real.exp (-((σ - σ') * t')) ≤ 1 := by
  set ε := σ - σ' with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set K := (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Real.exp ε / ε ^ pW with hK
  -- the upper bound tends to `0`
  have hx : Tendsto (fun t : ℝ => ε * (1 + t)) atTop atTop :=
    Tendsto.const_mul_atTop hεpos (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  have hg : Tendsto (fun t : ℝ => K * ((ε * (1 + t)) ^ pW * Real.exp (-(ε * (1 + t)))))
      atTop (𝓝 0) := by
    have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero pW).comp hx
    simpa using this.const_mul K
  have hev : ∀ᶠ t in atTop, K * ((ε * (1 + t)) ^ pW * Real.exp (-(ε * (1 + t)))) < 1 :=
    (tendsto_order.1 hg).2 1 one_pos
  obtain ⟨T, hT⟩ := eventually_atTop.1 hev
  refine ⟨max T 0, fun t' ht' => ?_⟩
  have ht'0 : 0 ≤ t' := le_trans (le_max_right _ _) ht'
  have ht'T : T ≤ t' := le_trans (le_max_left _ _) ht'
  exact (ActiveT1.f_le hσ hC₀ ht'0).trans (hT t' ht'T).le

/-- **`t₁` is well defined** (`thm:active`, `05_single_ring.tex:874-875` with `σ = σ(G)`, and
`:901-905` with `σ = σ_b`). For `σ' < σ` and `C₀ ≥ 1`, `tOneOf σ σ' C₀` is the least `t ≥ 0`
such that `2^{p/2}C₀⟨t'⟩^pe^{-(σ-σ')t'} ≤ 1` for all `t' ≥ t`: it is positive (at `t' = 0` the
left side is `2^{p/2}C₀ > 1`), it has the property, and it is below every `t ≥ 0` that has it. -/
theorem tOneOf_spec {σ σ' C₀ : ℝ} (hσ : σ' < σ) (hC₀ : 1 ≤ C₀) :
    0 < tOneOf σ σ' C₀ ∧
      (∀ t' : ℝ, tOneOf σ σ' C₀ ≤ t' →
        (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t' ^ pW * Real.exp (-((σ - σ') * t')) ≤ 1) ∧
      ∀ t : ℝ, 0 ≤ t →
        (∀ t' : ℝ, t ≤ t' →
          (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t' ^ pW * Real.exp (-((σ - σ') * t')) ≤ 1) →
        tOneOf σ σ' C₀ ≤ t := by
  set S : Set ℝ := {t : ℝ | 0 ≤ t ∧ ∀ t' : ℝ, t ≤ t' →
    (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t' ^ pW * Real.exp (-((σ - σ') * t')) ≤ 1}
    with hS
  have hdef : tOneOf σ σ' C₀ = sInf S := rfl
  have hne : S.Nonempty := by
    obtain ⟨T, hT⟩ := ActiveT1.exists_f_le_one (C₀ := C₀) hσ (by linarith)
    exact ⟨max T 0, le_max_right _ _, fun t' ht' => hT t' (le_trans (le_max_left _ _) ht')⟩
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  have hinf0 : 0 ≤ sInf S := le_csInf hne fun t ht => ht.1
  -- `f ≤ 1` on `[sInf S, ∞)`
  have hprop : ∀ t' : ℝ, sInf S ≤ t' →
      (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t' ^ pW * Real.exp (-((σ - σ') * t')) ≤ 1 := by
    have hcl : IsClosed {t' : ℝ |
        (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t' ^ pW * Real.exp (-((σ - σ') * t')) ≤ 1} :=
      isClosed_le (ActiveT1.continuous_f σ σ' C₀) continuous_const
    have hsub : Ioi (sInf S) ⊆ {t' : ℝ |
        (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t' ^ pW * Real.exp (-((σ - σ') * t')) ≤ 1} := by
      intro t' ht'
      obtain ⟨t, htS, htt'⟩ := exists_lt_of_csInf_lt hne ht'
      exact htS.2 t' htt'.le
    have hsub' := hcl.closure_subset_iff.2 hsub
    rw [closure_Ioi] at hsub'
    exact fun t' ht' => hsub' ht'
  -- `f(0) > 1`
  have hf0 : 1 < (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap 0 ^ pW *
      Real.exp (-((σ - σ') * 0)) := by
    rw [ActiveT1.jap_zero]
    have h2 : 1 < (2 : ℝ) ^ ((pW : ℝ) / 2) := Real.one_lt_rpow (by norm_num) (by norm_num)
    simp only [one_pow, mul_one, mul_zero, neg_zero, Real.exp_zero]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hdef]
    refine lt_of_le_of_ne hinf0 fun h => ?_
    have := hprop 0 h.symm.le
    linarith
  · rw [hdef]
    exact hprop
  · intro t ht0 ht
    rw [hdef]
    exact csInf_le hbdd ⟨ht0, ht⟩

/-- `σ_b ≤ σ(G) ≤ σ_max` and `σ_b > 0` for `G ∈ [0,G₁]` (`prop:U`(a)). -/
theorem ActiveT1.sigma_bounds (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) :
    Eig.sigb χ ≤ Eig.sigma χ G ∧ Eig.sigma χ G ≤ sigmaMax χ ∧ 0 < Eig.sigb χ := by
  obtain ⟨-, -, ⟨G₀, -, hG₀, hmin⟩, hpos, G₁, -, hmax⟩ := Eig.propU_a χ hχ hN
  refine ⟨hG₀ ▸ hmin G hG, ?_, by linarith⟩
  refine le_csSup ⟨Eig.sigma χ G₁, ?_⟩ (mem_image_of_mem _ hG)
  rintro _ ⟨G', hG', rfl⟩
  exact hmax G' hG'

/-- **`thm:active`, "Moreover"** (`05_single_ring.tex:901-911`). Assume (N1)–(N3), let
`σ' ∈ (9/200, σ_b)`, `C₀ ≥ 1`, `G ∈ [0,G₁]`, `σ = σ(G)`, `κ > 0`, `â(u) = κe^{σu}`, and let
`ρ̂` be the transient. Then `t₁(C₀,G) ≤ t̄₁(C₀)`, and for all `u ≥ 0`,
`â(u)ρ̂(u) ≤ C(C₀)κ⟨u⟩^pe^{σ'u}` with `C(C₀) = max(C₀, e^{σ_max t̄₁(C₀)})`. -/
theorem active_tOne (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {σ' : ℝ} (hσ' : σ' ∈ Ioo (9 / 200 : ℝ) (Eig.sigb χ)) {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {κ : ℝ} (hκ : 0 < κ) :
    tOne χ σ' C₀ G ≤ tOneBar χ σ' C₀ ∧
      ∀ u : ℝ, 0 ≤ u →
        ahat κ (Eig.sigma χ G) u * rhoHat χ σ' C₀ G u ≤
          Cact χ σ' C₀ * κ * Prelim.jap u ^ pW * Real.exp (σ' * u) := by
  obtain ⟨hbG, hGM, hb0⟩ := ActiveT1.sigma_bounds χ hχ hN hG
  set σ := Eig.sigma χ G with hσdef
  set σb := Eig.sigb χ with hσbdef
  set σM := sigmaMax χ with hσMdef
  have hσ'0 : 0 < σ' := by linarith [hσ'.1]
  have hσ'b : σ' < σb := hσ'.2
  have hσ'σ : σ' < σ := lt_of_lt_of_le hσ'b hbG
  obtain ⟨hb1, hb2, -⟩ := tOneOf_spec hσ'b hC₀
  obtain ⟨hs1, -, hs3⟩ := tOneOf_spec hσ'σ hC₀
  -- `t₁ ≤ t̄₁`
  have hle : tOneOf σ σ' C₀ ≤ tOneOf σb σ' C₀ := by
    refine hs3 _ hb1.le fun t' ht' => le_trans ?_ (hb2 t' ht')
    have ht'0 : 0 ≤ t' := hb1.le.trans ht'
    have hexp : Real.exp (-((σ - σ') * t')) ≤ Real.exp (-((σb - σ') * t')) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_right (by linarith) ht'0
    have hA : 0 ≤ (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t' ^ pW := by
      have := ActiveT1.jap_nonneg t'
      positivity
    exact mul_le_mul_of_nonneg_left hexp hA
  refine ⟨hle, fun u hu => ?_⟩
  have hCact : C₀ ≤ Cact χ σ' C₀ := le_Cact χ σ' C₀
  have hCact' : Real.exp (σM * tOneOf σb σ' C₀) ≤ Cact χ σ' C₀ := le_max_right _ _
  have hJ := ActiveT1.jap_nonneg u
  simp only [ahat, rhoHat]
  rw [← hσdef]
  by_cases hut : u < tOneOf σ σ' C₀
  · rw [rhoHatOf_of_lt hut]
    have he : Real.exp (σ * u) * Real.exp (-((σ - σ') * u)) = Real.exp (σ' * u) := by
      rw [← Real.exp_add]
      ring_nf
    calc κ * Real.exp (σ * u) * (C₀ * Prelim.jap u ^ pW * Real.exp (-((σ - σ') * u)))
        = C₀ * (κ * Prelim.jap u ^ pW * (Real.exp (σ * u) * Real.exp (-((σ - σ') * u)))) := by
          ring
      _ = C₀ * (κ * Prelim.jap u ^ pW * Real.exp (σ' * u)) := by rw [he]
      _ ≤ Cact χ σ' C₀ * (κ * Prelim.jap u ^ pW * Real.exp (σ' * u)) :=
          mul_le_mul_of_nonneg_right hCact (by positivity)
      _ = Cact χ σ' C₀ * κ * Prelim.jap u ^ pW * Real.exp (σ' * u) := by ring
  · rw [not_lt] at hut
    rw [rhoHatOf_of_le hut]
    set t₁ := tOneOf σ σ' C₀ with ht₁
    have he : Real.exp (σ * u) * Real.exp (-((σ - σ') * (u - t₁))) =
        Real.exp (σ * t₁) * Real.exp (σ' * (u - t₁)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
    have hJ' : Prelim.jap (u - t₁) ^ pW ≤ Prelim.jap u ^ pW := by
      refine pow_le_pow_left₀ (ActiveT1.jap_nonneg _) (ActiveT1.jap_le_jap ?_) _
      nlinarith
    have hE1 : Real.exp (σ * t₁) ≤ Cact χ σ' C₀ := by
      refine le_trans (Real.exp_le_exp.2 ?_) hCact'
      calc σ * t₁ ≤ σM * t₁ := mul_le_mul_of_nonneg_right hGM hs1.le
        _ ≤ σM * tOneOf σb σ' C₀ := mul_le_mul_of_nonneg_left hle (by linarith)
    have hE2 : Real.exp (σ' * (u - t₁)) ≤ Real.exp (σ' * u) := by
      rw [Real.exp_le_exp]
      nlinarith
    calc κ * Real.exp (σ * u) *
          (Prelim.jap (u - t₁) ^ pW * Real.exp (-((σ - σ') * (u - t₁))))
        = κ * Prelim.jap (u - t₁) ^ pW *
            (Real.exp (σ * u) * Real.exp (-((σ - σ') * (u - t₁)))) := by ring
      _ = κ * Prelim.jap (u - t₁) ^ pW * (Real.exp (σ * t₁) * Real.exp (σ' * (u - t₁))) := by
          rw [he]
      _ ≤ κ * Prelim.jap u ^ pW * (Cact χ σ' C₀ * Real.exp (σ' * u)) := by
          have := ActiveT1.jap_nonneg (u - t₁)
          have : 0 ≤ Cact χ σ' C₀ := le_trans (by linarith) hCact
          gcongr
      _ = Cact χ σ' C₀ * κ * Prelim.jap u ^ pW * Real.exp (σ' * u) := by ring

end OneRing

end NonUniqueEuler
