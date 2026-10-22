import NonUniqueEuler.Defs.Sec11.All
import NonUniqueEuler.I.SmoothB.SmoothFlow
import NonUniqueEuler.I.Sec6.Adm
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Paths

/-!
# Proof: the continuity properties used in Step 7 of the proof of `prop:bootstrap`

Proof of `I/Sec11/ContinuityProps.lean` (`11_bootstrap.tex:543-552`, `:563-569`).

* `flow_image_eventually`: `(t, y) ↦ Φ_t(y)` is continuous (`thm:smooth`(4), `flow_contDiff`), so
  the tube lemma (`IsCompact.eventually_forall_of_forall_eventually`) applies to the open set
  `{(t, y) | Φ_t(y) ∈ U}`.
* `w_continuous`: for `t ≥ 0`, `w_k(t, y) = A_k⁻¹ f^{(n)}_k(Φ_t⁻¹(r_k y)) - Φ(y)`
  (`eq:omega-ge`, `regions_basic_three`). The right side `W(t, y)` (`ContinuityPropsP.wExt`) is
  jointly smooth on `ℝ × ℝ²` (`flow_contDiff`, `f^{(n)}_k ∈ C_c^∞`, `Φ ∈ C_c^∞`) and, for `t` in a
  bounded interval `J`, supported in the fixed compact set `r_k⁻¹ Φ(J × S_k) ∪ supp Φ`. The `H^k`
  path lemma `Sob.continuousOn_toHk_of_contDiff` gives the continuity of `t ↦ W(t)` into the
  Hilbert space `Hk s'`, and `Sob.norm_toHk`, `Sob.toHk_add`, `Sob.toHk_smul` translate it into
  the statement about `Sob.normH`. **Remark:** the hypothesis `S_k(t) ⊂ N_k` is not needed for
  these properties (it is the condition under which `w_k(t)` is the manuscript's object).
* `rhoHat_semicontinuous`: both branches of `ρ̂` are continuous; at `t₁ > 0` the set defining `t₁`
  is nonempty, and `2^{p/2}C₀⟨t₁⟩^pe^{-(σ-σ')t₁} ≤ 1` by continuity from the right, so the left
  limit `C₀⟨t₁⟩^pe^{-(σ-σ')t₁}` is at most `1 = ρ̂(t₁)`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff

namespace NonUniqueEuler

namespace Datum

namespace Approx

open RingData

namespace ContinuityPropsP

/-- `f^{(n)}` is a datum of `thm:smooth` (`lem:adm`: `f^{(n)} ∈ C_c^∞`). -/
theorem exists_isSmoothDatum (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) :
    ∃ R : ℝ, Smooth.IsSmoothDatum P.f R := by
  obtain ⟨hcd, hcs, -⟩ := (Datum.adm P.χ hP.admissible hN hP.datumParams
    ⟨hP.kseed_pos, hP.kseed_le⟩).1 P.n hP.two_le_n
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).mp hcs.isCompact.isBounded
  exact ⟨R, hcd, hR⟩

/-- The flow of a valid approximation is jointly continuous (`thm:smooth`(4)). -/
theorem continuous_flow (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) :
    Continuous (fun p : ℝ × ℂ => P.flow p.1 p.2) := by
  obtain ⟨R, hR⟩ := exists_isSmoothDatum P hP hN
  have h := (Smooth.flow_contDiff hR).1.continuous
  have he : (fun p : ℝ × ℂ => P.flow p.1 p.2) = fun p : ℝ × ℂ => Smooth.flow P.f p.1 p.2 := by
    funext p
    rw [hP.flow_eq]
  rw [he]
  exact h

/-- `Φ_0⁻¹ = id`. -/
theorem flowInv_zero (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) (x : ℂ) :
    P.flowInv 0 x = x := by
  obtain ⟨R, hR⟩ := exists_isSmoothDatum P hP hN
  have h := (Smooth.flow_global hR x).2.init
  have h' : P.flowInv 0 x = Smooth.flow P.f 0 x := by
    rw [← hP.flow_eq]
    rfl
  rw [h']
  exact h

/-- The terms `f^{(n)}_k`, `1 ≤ k ≤ n`, are `C_c^∞` (`f^{(n)}_k = ω(0)1_{S_k(0)}`,
`lem:regions-basic`(3) at `t = 0`). -/
theorem term_smooth (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) :
    ContDiff ℝ ∞ (P.term k) ∧ HasCompactSupport (P.term k) := by
  have h3 := regions_basic_three P hP hN hk le_rfl
  have he : P.term k = P.omegaRing k 0 := by
    rw [h3.1]
    funext x
    rw [flowInv_zero P hP hN x]
  rw [he]
  exact ⟨h3.2.2.2.2.2.2.1.1, h3.2.2.2.2.2.2.1.2.1⟩

/-- The smooth extension `W(t, y) = A_k⁻¹ f^{(n)}_k(Φ_t⁻¹(r_k y)) - Φ(y)` of the perturbation
`w_k(t, y)` (they agree for `t ≥ 0`, `wExt_eq`). -/
def wExt (P : Approx) (k : ℕ) (t : ℝ) (y : ℂ) : ℂ :=
  (((P.A k)⁻¹ * P.term k (Smooth.flowInv P.f t ((P.r k : ℂ) * y)) - ringPhi P.χ y : ℝ) : ℂ)

/-- `w_k(t) = W(t)` for `t ≥ 0` (`eq:omega-ge`). -/
theorem wExt_eq (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) {t : ℝ} (ht : 0 ≤ t) : P.w k t = wExt P k t := by
  have h3 := (regions_basic_three P hP hN hk ht).1
  funext y
  rw [w_apply, wExt, h3, unitsVort, scaleVort_apply, hP.flowInv_eq]

/-- `W` is jointly smooth on `ℝ × ℝ²`. -/
theorem wExt_contDiff (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => wExt P k p.1 p.2) := by
  obtain ⟨R, hR⟩ := exists_isSmoothDatum P hP hN
  have hinv := (Smooth.flow_contDiff hR).2
  have hterm := (term_smooth P hP hN hk).1
  have hphi := (ringFacts_of_admissible hP.admissible).1
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × ℂ => (p.1, (P.r k : ℂ) * p.2)) :=
    contDiff_fst.prodMk (contDiff_const.mul contDiff_snd)
  have h1 : ContDiff ℝ ∞
      (fun p : ℝ × ℂ => Smooth.flowInv P.f p.1 ((P.r k : ℂ) * p.2)) :=
    hinv.comp hmap
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℂ =>
      (P.A k)⁻¹ * P.term k (Smooth.flowInv P.f p.1 ((P.r k : ℂ) * p.2)) - ringPhi P.χ p.2) :=
    (contDiff_const.mul (hterm.comp h1)).sub (hphi.comp contDiff_snd)
  exact Complex.ofRealCLM.contDiff.comp h2

/-- For `t` in `[a, b]`, `W(t)` vanishes off the compact set `r_k⁻¹ Φ([a, b] × S_k) ∪ supp Φ`. -/
theorem wExt_support (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) (k : ℕ)
    (a b : ℝ) {t : ℝ} (ht : t ∈ Icc a b) {y : ℂ}
    (hy : y ∉ (fun p : ℝ × ℂ => (P.r k : ℂ)⁻¹ * Smooth.flow P.f p.1 p.2) '' (Icc a b ×ˢ P.S k) ∪
      tsupport (ringPhi P.χ)) :
    wExt P k t y = 0 := by
  obtain ⟨R, hR⟩ := exists_isSmoothDatum P hP hN
  have hr : (P.r k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hP.r_pos k).ne'
  rw [mem_union, not_or] at hy
  have hphi : ringPhi P.χ y = 0 := image_eq_zero_of_notMem_tsupport hy.2
  have hterm : P.term k (Smooth.flowInv P.f t ((P.r k : ℂ) * y)) = 0 := by
    by_contra hne
    apply hy.1
    refine ⟨(t, Smooth.flowInv P.f t ((P.r k : ℂ) * y)), ⟨ht, subset_tsupport _ hne⟩, ?_⟩
    have hri := (Smooth.flow_diffeo hR t).2.1 ((P.r k : ℂ) * y)
    simp only
    rw [hri, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]
  simp [wExt, hphi, hterm]

/-- The compact set of `wExt_support` is compact. -/
theorem isCompact_wExt_set (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) (a b : ℝ) :
    IsCompact ((fun p : ℝ × ℂ => (P.r k : ℂ)⁻¹ * Smooth.flow P.f p.1 p.2) '' (Icc a b ×ˢ P.S k) ∪
      tsupport (ringPhi P.χ)) := by
  obtain ⟨R, hR⟩ := exists_isSmoothDatum P hP hN
  have hS : IsCompact (P.S k) := (term_smooth P hP hN hk).2
  have hc : Continuous (fun p : ℝ × ℂ => (P.r k : ℂ)⁻¹ * Smooth.flow P.f p.1 p.2) :=
    continuous_const.mul (Smooth.flow_contDiff hR).1.continuous
  exact ((isCompact_Icc.prod hS).image hc).union
    (ringFacts_of_admissible hP.admissible).2.1

/-- For `t` in a bounded interval `[a, b]`, the functions `W(t)` vanish off one compact set. -/
theorem exists_compact_wExt (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) (a b : ℝ) :
    ∃ K : Set ℂ, IsCompact K ∧ ∀ t ∈ Icc a b, ∀ x ∉ K, wExt P k t x = 0 :=
  ⟨_, isCompact_wExt_set P hP hN hk a b, fun _ ht _ hx => wExt_support P hP hN k a b ht hx⟩

/-- Each slice `W(t)` is smooth. -/
theorem wExt_slice_contDiff (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) (t : ℝ) : ContDiff ℝ ∞ (wExt P k t) := by
  have hW := wExt_contDiff P hP hN hk
  have hsl : ContDiff ℝ ∞ (fun y : ℂ => ((t, y) : ℝ × ℂ)) := contDiff_const.prodMk contDiff_id
  have hsm : ContDiff ℝ ∞ (fun y : ℂ => wExt P k (t, y).1 (t, y).2) := hW.comp hsl
  exact hsm

/-- `‖f - g‖_{H^k} = ‖toHk f - toHk g‖` for `f, g ∈ H^k`. -/
theorem normH_sub_eq {s : ℕ} {f g : ℂ → ℂ} (hf : Sob.MemH s f) (hg : Sob.MemH s g) :
    Sob.normH s (f - g) = ‖Sob.toHk s f - Sob.toHk s g‖ := by
  have hg' := (hg.const_smul (-1 : ℂ)).1
  have hfg : f - g = f + (-1 : ℂ) • g := by
    funext x
    simp [sub_eq_add_neg]
  rw [← Sob.norm_toHk (hf.sub hg).1, hfg, Sob.toHk_add hf hg', Sob.toHk_smul hg, neg_one_smul,
    ← sub_eq_add_neg]

end ContinuityPropsP

open ContinuityPropsP

/-- **Stability of inclusions under the flow** (`11_bootstrap.tex:545-547`, from `thm:smooth`(2),(4)):
for a compact set `K`, an open set `U` and `t₀ ≥ 0` with `Φ_{t₀}(K) ⊂ U`, `Φ_t(K) ⊂ U` for every
`t ≥ 0` close enough to `t₀`. -/
theorem flow_image_eventually (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (h : P.flow t₀ '' K ⊆ U) : ∀ᶠ t in 𝓝[Ici 0] t₀, P.flow t '' K ⊆ U := by
  have hc := continuous_flow P hP hN
  have hev : ∀ᶠ t in 𝓝 t₀, ∀ y ∈ K, P.flow t y ∈ U := by
    refine hK.eventually_forall_of_forall_eventually fun y hy => ?_
    exact (hU.preimage hc).mem_nhds (h ⟨y, hy, rfl⟩)
  exact nhdsWithin_le_nhds (hev.mono fun t ht => image_subset_iff.mpr ht)

/-- **Continuity of the perturbation in `H^{s'}`** (`11_bootstrap.tex:547-550`): if `S_k(t) ⊂ N_k`
for every `t ∈ [t₁, t₂] ⊂ [0, ∞)`, then for every `s'`, `w_k(t) ∈ H^{s'}` for `t ∈ [t₁, t₂]`,
`t ↦ w_k(t)` is continuous from `[t₁, t₂]` into `H^{s'}`, and `t ↦ ‖w_k(t)‖_{H^{s'}}` is continuous on
`[t₁, t₂]`. -/
theorem w_continuous (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 P.n) {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁)
    (hdef : ∀ t ∈ Icc t₁ t₂, P.PertDefined k t) (s' : ℕ) :
    (∀ t ∈ Icc t₁ t₂, Sob.MemH s' (P.w k t)) ∧
    (∀ t ∈ Icc t₁ t₂,
      Tendsto (fun t' => Sob.normH s' (P.w k t' - P.w k t)) (𝓝[Icc t₁ t₂] t) (𝓝 0)) ∧
    ContinuousOn (fun t => Sob.normH s' (P.w k t)) (Icc t₁ t₂) := by
  obtain ⟨Kset, hKc, hsuppK⟩ := exists_compact_wExt P hP hN hk (t₁ - 1) (t₂ + 1)
  have hW := wExt_contDiff P hP hN hk
  have hsuppI : ∀ t ∈ Ioo (t₁ - 1) (t₂ + 1), ∀ x ∉ Kset, wExt P k t x = 0 :=
    fun t ht x hx => hsuppK t (Ioo_subset_Icc_self ht) x hx
  have hIcc : Icc t₁ t₂ ⊆ Ioo (t₁ - 1) (t₂ + 1) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcont : ContinuousOn (fun s => Sob.toHk s' (wExt P k s)) (Icc t₁ t₂) :=
    (Sob.continuousOn_toHk_of_contDiff hW hKc isOpen_Ioo hsuppI).mono hIcc
  -- `W(t) ∈ H^{s'}` for `t ∈ [t₁, t₂]`
  have hmem : ∀ t ∈ Icc t₁ t₂, Sob.MemH s' (wExt P k t) := by
    intro t ht
    have hsm : ContDiff ℝ ∞ (wExt P k t) := wExt_slice_contDiff P hP hN hk t
    have hcs : HasCompactSupport (wExt P k t) :=
      HasCompactSupport.intro hKc (fun x hx => hsuppI t (hIcc ht) x hx)
    exact (Sob.memH_of_contDiff_hasCompactSupport hsm hcs s').1
  have heq : ∀ t ∈ Icc t₁ t₂, P.w k t = wExt P k t := fun t ht =>
    wExt_eq P hP hN hk (h0.trans ht.1)
  refine ⟨fun t ht => by rw [heq t ht]; exact hmem t ht, ?_, ?_⟩
  · intro t ht
    have htend : Tendsto (fun t' => ‖Sob.toHk s' (wExt P k t') - Sob.toHk s' (wExt P k t)‖)
        (𝓝[Icc t₁ t₂] t) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (hcont t ht)
    refine htend.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t' ht'
    rw [heq t' ht', heq t ht, normH_sub_eq (hmem t' ht') (hmem t ht)]
  · refine (hcont.norm).congr fun t ht => ?_
    simp only
    rw [heq t ht, Sob.norm_toHk (hmem t ht)]

end Approx

end Datum

namespace Relay

namespace ContinuityPropsP

/-- The left branch `C₀⟨u⟩^pe^{-(σ-σ')u}` of `ρ̂` is continuous. -/
theorem continuous_left (σ σ' C₀ : ℝ) :
    Continuous fun u : ℝ => C₀ * Prelim.jap u ^ OneRing.pW * Real.exp (-((σ - σ') * u)) := by
  unfold Prelim.jap
  fun_prop

/-- The right branch `⟨u-t₁⟩^pe^{-(σ-σ')(u-t₁)}` of `ρ̂` is continuous. -/
theorem continuous_right (σ σ' t₁ : ℝ) :
    Continuous fun u : ℝ =>
      Prelim.jap (u - t₁) ^ OneRing.pW * Real.exp (-((σ - σ') * (u - t₁))) := by
  unfold Prelim.jap
  fun_prop

/-- `ρ̂(t₁) = 1`. -/
theorem rhoHatOf_tOne (σ σ' C₀ : ℝ) :
    OneRing.rhoHatOf σ σ' C₀ (OneRing.tOneOf σ σ' C₀) = 1 := by
  rw [OneRing.rhoHatOf_of_le le_rfl]
  simp [Prelim.jap]

/-- If `t₁ > 0`, then `C₀⟨t₁⟩^pe^{-(σ-σ')t₁} ≤ 1` (in fact `≤ 2^{-p/2}`): the set defining `t₁` is
nonempty, its defining inequality holds for every `t' > t₁`, hence at `t₁` by continuity. -/
theorem left_tOne_le {σ σ' C₀ : ℝ} (hC₀ : 1 ≤ C₀) (h : 0 < OneRing.tOneOf σ σ' C₀) :
    C₀ * Prelim.jap (OneRing.tOneOf σ σ' C₀) ^ OneRing.pW *
      Real.exp (-((σ - σ') * OneRing.tOneOf σ σ' C₀)) ≤ 1 := by
  set t₁ := OneRing.tOneOf σ σ' C₀ with ht₁
  set S : Set ℝ := {t : ℝ | 0 ≤ t ∧ ∀ t' : ℝ, t ≤ t' →
    (2 : ℝ) ^ ((OneRing.pW : ℝ) / 2) * C₀ * Prelim.jap t' ^ OneRing.pW *
      Real.exp (-((σ - σ') * t')) ≤ 1} with hS
  have ht₁S : t₁ = sInf S := rfl
  have hne : S.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [ht₁S, hne, Real.sInf_empty] at h
    exact lt_irrefl _ h
  set g : ℝ → ℝ := fun t' => (2 : ℝ) ^ ((OneRing.pW : ℝ) / 2) * C₀ *
    Prelim.jap t' ^ OneRing.pW * Real.exp (-((σ - σ') * t')) with hg
  have hgc : Continuous g := by
    rw [hg]
    unfold Prelim.jap
    fun_prop
  have hright : ∀ t' : ℝ, t₁ < t' → g t' ≤ 1 := by
    intro t' ht'
    obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hne (ht₁S ▸ ht')
    exact hs.2 t' hst.le
  have hg1 : g t₁ ≤ 1 := by
    have hev : ∀ᶠ t' in 𝓝[>] t₁, g t' ≤ 1 :=
      Filter.eventually_of_mem self_mem_nhdsWithin fun t' ht' => hright t' ht'
    have hlim : Tendsto g (𝓝[>] t₁) (𝓝 (g t₁)) :=
      hgc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto hlim hev
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ ((OneRing.pW : ℝ) / 2) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hnn : 0 ≤ C₀ * Prelim.jap t₁ ^ OneRing.pW * Real.exp (-((σ - σ') * t₁)) := by
    have : 0 ≤ Prelim.jap t₁ := Real.sqrt_nonneg _
    have : (0 : ℝ) ≤ C₀ := by linarith
    positivity
  have hgt : g t₁ = (2 : ℝ) ^ ((OneRing.pW : ℝ) / 2) *
      (C₀ * Prelim.jap t₁ ^ OneRing.pW * Real.exp (-((σ - σ') * t₁))) := by
    rw [hg]
    ring
  calc C₀ * Prelim.jap t₁ ^ OneRing.pW * Real.exp (-((σ - σ') * t₁))
      ≤ (2 : ℝ) ^ ((OneRing.pW : ℝ) / 2) *
        (C₀ * Prelim.jap t₁ ^ OneRing.pW * Real.exp (-((σ - σ') * t₁))) :=
        le_mul_of_one_le_left hnn h2
    _ = g t₁ := hgt.symm
    _ ≤ 1 := hg1

end ContinuityPropsP

open ContinuityPropsP

/-- **Semicontinuity of the transient `ρ̂`** (`11_bootstrap.tex:563-569`): for `σ > σ'` and
`C₀ ≥ 1`, `ρ̂ = OneRing.rhoHatOf σ σ' C₀` is right-continuous at every `u ≥ 0`, and at every `u > 0`
its values just to the left of `u` are at most `ρ̂(u) + ε` for every `ε > 0` (`ρ̂(u) ≥ limsup_{v↑u} ρ̂(v)`;
the only discontinuity is the upward jump at `t₁`). -/
theorem rhoHat_semicontinuous {σ σ' C₀ : ℝ} (hσ : σ' < σ) (hC₀ : 1 ≤ C₀) :
    (∀ u : ℝ, 0 ≤ u → ContinuousWithinAt (OneRing.rhoHatOf σ σ' C₀) (Ici u) u) ∧
    ∀ u : ℝ, 0 < u → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ v in 𝓝[<] u, OneRing.rhoHatOf σ σ' C₀ v ≤ OneRing.rhoHatOf σ σ' C₀ u + ε := by
  set t₁ := OneRing.tOneOf σ σ' C₀ with ht₁
  set L : ℝ → ℝ := fun u => C₀ * Prelim.jap u ^ OneRing.pW * Real.exp (-((σ - σ') * u))
    with hL
  set R : ℝ → ℝ := fun u =>
    Prelim.jap (u - t₁) ^ OneRing.pW * Real.exp (-((σ - σ') * (u - t₁))) with hR
  have hLc : Continuous L := continuous_left σ σ' C₀
  have hRc : Continuous R := continuous_right σ σ' t₁
  have hρL : ∀ u, u < t₁ → OneRing.rhoHatOf σ σ' C₀ u = L u := fun u hu =>
    OneRing.rhoHatOf_of_lt hu
  have hρR : ∀ u, t₁ ≤ u → OneRing.rhoHatOf σ σ' C₀ u = R u := fun u hu =>
    OneRing.rhoHatOf_of_le hu
  -- continuity of `ρ̂` at points `u ≠ t₁`
  have hcontL : ∀ u, u < t₁ → ContinuousAt (OneRing.rhoHatOf σ σ' C₀) u := by
    intro u hu
    have hev : L =ᶠ[𝓝 u] OneRing.rhoHatOf σ σ' C₀ := by
      filter_upwards [Iio_mem_nhds hu] with v hv
      exact (hρL v hv).symm
    exact hLc.continuousAt.congr hev
  have hcontR : ∀ u, t₁ < u → ContinuousAt (OneRing.rhoHatOf σ σ' C₀) u := by
    intro u hu
    have hev : R =ᶠ[𝓝 u] OneRing.rhoHatOf σ σ' C₀ := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact (hρR v (le_of_lt hv)).symm
    exact hRc.continuousAt.congr hev
  have hlt : ∀ u, ContinuousAt (OneRing.rhoHatOf σ σ' C₀) u → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ v in 𝓝[<] u, OneRing.rhoHatOf σ σ' C₀ v ≤ OneRing.rhoHatOf σ σ' C₀ u + ε := by
    intro u hu ε hε
    have h := hu.tendsto.eventually (Iio_mem_nhds (lt_add_of_pos_right
      (OneRing.rhoHatOf σ σ' C₀ u) hε))
    exact nhdsWithin_le_nhds (h.mono fun v hv => le_of_lt hv)
  refine ⟨fun u _ => ?_, fun u hu ε hε => ?_⟩
  · rcases lt_or_ge u t₁ with hu | hu
    · exact (hcontL u hu).continuousWithinAt
    · refine hRc.continuousAt.continuousWithinAt.congr (fun v hv => hρR v (hu.trans hv))
        (hρR u hu)
  · rcases lt_trichotomy u t₁ with hut | hut | hut
    · exact hlt u (hcontL u hut) ε hε
    · -- the jump point `u = t₁ > 0`
      subst hut
      have hle : L t₁ ≤ 1 := left_tOne_le hC₀ hu
      have h1 : OneRing.rhoHatOf σ σ' C₀ t₁ = 1 := rhoHatOf_tOne σ σ' C₀
      have h := hLc.continuousAt.tendsto.eventually (Iio_mem_nhds (lt_add_of_pos_right
        (L t₁) hε))
      filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with v hv hv'
      rw [hρL v hv', h1]
      have : L v < L t₁ + ε := hv
      linarith
    · exact hlt u (hcontR u hut) ε hε

end Relay

end NonUniqueEuler
