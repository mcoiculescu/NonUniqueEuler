import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Helpers for `P/Sec3/EquivRemaining.lean` (`prop:equiv`, the remaining implications)

Generic lemmas used in the proof of `prop:equiv` (`03_compactness.tex:1099-1128`):

* `lintegral_enorm_mul_le`, `enorm_integral_mul_le`: Hölder's inequality for the pairing
  `|∫ g ψ| ≤ ‖g‖_{L^p} ‖ψ‖_{L^{p'}}` (`03_compactness.tex:1111-1112`);
* `tendsto_of_enorm_sub_le`: real convergence from an `ℝ≥0∞` bound tending to `0`;
* `tendsto_zero_of_limsup_eq_zero`: in `ℝ≥0∞`, `limsup uₙ = 0` gives `uₙ → 0`;
* `tendsto_integral_mul_of_eLpNorm_one`: `L¹` convergence plus a uniform `L²` bound gives
  weak `L²` convergence (`03_compactness.tex:1119-1121`), along any filter;
* `tendsto_eLpNorm_of_tendsto_eLpNorm_sub`: `‖gᵢ - g‖_{L^p} → 0` gives `‖gᵢ‖_{L^p} → ‖g‖_{L^p}`;
* `tendsto_iSup_of_tendsto_comap_fst`: convergence along `comap Prod.fst atTop` on `ℕ × s` is
  uniform convergence on `s`.

All lemmas are fully proved.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.EquivRemaining

/-- Hölder's inequality: `∫⁻ |f g| ≤ ‖f‖_{L^p} ‖g‖_{L^{p'}}` for Hölder conjugate `p`, `p'`. -/
theorem lintegral_enorm_mul_le {f g : ℂ → ℝ} {p p' : ℝ≥0∞} [ENNReal.HolderTriple p p' 1]
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    ∫⁻ x, ‖f x * g x‖ₑ ≤ eLpNorm f p volume * eLpNorm g p' volume := by
  rw [← eLpNorm_one_eq_lintegral_enorm]
  have := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := p) (q := p') (r := 1) hf hg
    (fun a b : ℝ => a * b) 1 (Eventually.of_forall fun x => by simp [norm_mul])
  simpa using this

/-- Hölder's inequality for the pairing: `|∫ f g| ≤ ‖f‖_{L^p} ‖g‖_{L^{p'}}` (also when `f g` is
not integrable, the integral being `0` then). -/
theorem enorm_integral_mul_le {f g : ℂ → ℝ} {p p' : ℝ≥0∞} [ENNReal.HolderTriple p p' 1]
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    ‖∫ x, f x * g x‖ₑ ≤ eLpNorm f p volume * eLpNorm g p' volume :=
  (enorm_integral_le_lintegral_enorm _).trans (lintegral_enorm_mul_le hf hg)

/-- Real convergence `uᵢ → a` from a bound `‖uᵢ - a‖ₑ ≤ vᵢ` with `vᵢ → 0` in `ℝ≥0∞`. -/
theorem tendsto_of_enorm_sub_le {ι : Type*} {l : Filter ι} {u : ι → ℝ} {a : ℝ}
    {v : ι → ℝ≥0∞} (hv : Tendsto v l (𝓝 0)) (h : ∀ᶠ i in l, ‖u i - a‖ₑ ≤ v i) :
    Tendsto u l (𝓝 a) := by
  rw [tendsto_iff_edist_tendsto_0]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hv
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [h] with i hi
  rwa [edist_eq_enorm_sub]

/-- In `ℝ≥0∞`, `limsup uₙ = 0` gives `uₙ → 0`. -/
theorem tendsto_zero_of_limsup_eq_zero {ι : Type*} {l : Filter ι} {u : ι → ℝ≥0∞}
    (h : limsup u l = 0) : Tendsto u l (𝓝 0) :=
  tendsto_of_le_liminf_of_limsup_le (zero_le) h.le

/-- **`L¹` convergence plus a uniform `L²` bound gives weak `L²` convergence**
(`03_compactness.tex:1119-1121`): if `gᵢ, g ∈ L²`, `‖gᵢ - g‖_{L¹} → 0` and eventually
`‖gᵢ - g‖_{L²} ≤ M < ∞`, then `∫ gᵢ ψ → ∫ g ψ` for every `ψ ∈ L²`. Proof: approximate `ψ` in `L²`
by a continuous compactly supported `φ` (`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`); then
`|∫ (gᵢ - g) ψ| ≤ ‖gᵢ - g‖_{L¹} ‖φ‖_{L^∞} + ‖gᵢ - g‖_{L²} ‖ψ - φ‖_{L²}`. -/
theorem tendsto_integral_mul_of_eLpNorm_one {ι : Type*} {l : Filter ι} {gs : ι → ℂ → ℝ}
    {g : ℂ → ℝ} (hgs : ∀ i, MemLp (gs i) 2 volume) (hg : MemLp g 2 volume)
    (h1 : Tendsto (fun i => eLpNorm (gs i - g) 1 volume) l (𝓝 0))
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hbd : ∀ᶠ i in l, eLpNorm (gs i - g) 2 volume ≤ M)
    {ψ : ℂ → ℝ} (hψ : MemLp ψ 2 volume) :
    Tendsto (fun i => ∫ x, gs i x * ψ x) l (𝓝 (∫ x, g x * ψ x)) := by
  rw [tendsto_iff_edist_tendsto_0, ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ≥0∞, δ ≠ 0 ∧ M * δ ≤ ε / 2 := by
    by_cases hM0 : M = 0
    · exact ⟨1, one_ne_zero, by simp [hM0]⟩
    · refine ⟨ε / 2 / M, ENNReal.div_ne_zero.2 ⟨hε2.ne', hM⟩, ?_⟩
      rw [ENNReal.mul_div_cancel hM0 hM]
  obtain ⟨φ, hφc, hφd, hφcont, hφm⟩ :=
    hψ.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofNat_ne_top hδ0
  have hφtop : MemLp φ ⊤ volume := hφcont.memLp_of_hasCompactSupport hφc
  have hC : eLpNorm φ ⊤ volume ≠ ∞ := hφtop.eLpNorm_ne_top
  have h1C : Tendsto (fun i => eLpNorm (gs i - g) 1 volume * eLpNorm φ ⊤ volume) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hC)
  have hev := (ENNReal.tendsto_nhds_zero.1 h1C) (ε / 2) hε2
  filter_upwards [hev, hbd] with i hi hbi
  rw [edist_eq_enorm_sub]
  have hint1 : Integrable (fun x => gs i x * ψ x) volume := (hgs i).integrable_mul hψ
  have hint2 : Integrable (fun x => g x * ψ x) volume := hg.integrable_mul hψ
  rw [← integral_sub hint1 hint2]
  have heq : (fun x => gs i x * ψ x - g x * ψ x) = fun x => (gs i - g) x * ψ x := by
    funext x; simp [sub_mul]
  rw [heq]
  have hd : AEStronglyMeasurable (gs i - g) volume := (hgs i).1.sub hg.1
  calc ‖∫ x, (gs i - g) x * ψ x‖ₑ ≤ ∫⁻ x, ‖(gs i - g) x * ψ x‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, (‖(gs i - g) x * φ x‖ₑ + ‖(gs i - g) x * (ψ - φ) x‖ₑ) := by
        refine lintegral_mono fun x => ?_
        calc ‖(gs i - g) x * ψ x‖ₑ = ‖(gs i - g) x * φ x + (gs i - g) x * (ψ - φ) x‖ₑ := by
              congr 1; simp only [Pi.sub_apply]; ring
          _ ≤ _ := enorm_add_le _ _
    _ = (∫⁻ x, ‖(gs i - g) x * φ x‖ₑ) + ∫⁻ x, ‖(gs i - g) x * (ψ - φ) x‖ₑ :=
        lintegral_add_left' (f := fun x => ‖(gs i - g) x * φ x‖ₑ) (hd.mul hφm.1).enorm _
    _ ≤ eLpNorm (gs i - g) 1 volume * eLpNorm φ ⊤ volume +
          eLpNorm (gs i - g) 2 volume * eLpNorm (ψ - φ) 2 volume :=
        add_le_add (lintegral_enorm_mul_le (p := 1) (p' := ⊤) hd hφm.1)
          (lintegral_enorm_mul_le (p := 2) (p' := 2) hd (hψ.1.sub hφm.1))
    _ ≤ ε / 2 + M * δ := add_le_add hi (mul_le_mul' hbi hφd)
    _ ≤ ε / 2 + ε / 2 := add_le_add le_rfl hδ
    _ = ε := ENNReal.add_halves ε

/-- `‖gᵢ - g‖_{L^p} → 0` gives `‖gᵢ‖_{L^p} → ‖g‖_{L^p}` (`1 ≤ p`, `g ∈ L^p`). -/
theorem tendsto_eLpNorm_of_tendsto_eLpNorm_sub {ι : Type*} {l : Filter ι} {gs : ι → ℂ → ℝ}
    {g : ℂ → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hgs : ∀ i, AEStronglyMeasurable (gs i) volume)
    (hg : MemLp g p volume) (h : Tendsto (fun i => eLpNorm (gs i - g) p volume) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (gs i) p volume) l (𝓝 (eLpNorm g p volume)) := by
  have hup : Tendsto (fun i => eLpNorm (gs i - g) p volume + eLpNorm g p volume) l
      (𝓝 (eLpNorm g p volume)) := by
    simpa using h.add_const (eLpNorm g p volume)
  have hlo : Tendsto (fun i => eLpNorm g p volume - eLpNorm (gs i - g) p volume) l
      (𝓝 (eLpNorm g p volume)) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl hg.eLpNorm_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup (fun i => ?_) (fun i => ?_)
  · rw [tsub_le_iff_right]
    calc eLpNorm g p volume = eLpNorm (gs i - (gs i - g)) p volume := by
          congr 1; abel
      _ ≤ eLpNorm (gs i) p volume + eLpNorm (gs i - g) p volume :=
          eLpNorm_sub_le (hgs i) ((hgs i).sub hg.1) hp
  · calc eLpNorm (gs i) p volume = eLpNorm ((gs i - g) + g) p volume := by
          congr 1; abel
      _ ≤ eLpNorm (gs i - g) p volume + eLpNorm g p volume :=
          eLpNorm_add_le ((hgs i).sub hg.1) hg.1 hp

/-- Convergence to `0` along `comap Prod.fst atTop` on `ℕ × s` is uniform convergence on `s`:
`sup_{t ∈ s} F n t → 0`. -/
theorem tendsto_iSup_of_tendsto_comap_fst {s : Set ℝ} {F : ℕ → ℝ → ℝ≥0∞}
    (h : Tendsto (fun i : ℕ × s => F i.1 i.2) (comap Prod.fst atTop) (𝓝 0)) :
    Tendsto (fun n => ⨆ t ∈ s, F n t) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at h ⊢
  intro ε hε
  have h' := h ε hε
  rw [eventually_comap] at h'
  filter_upwards [h'] with n hn
  exact iSup₂_le fun t ht => hn ⟨n, ⟨t, ht⟩⟩ rfl

end NonUniqueEuler.Compact.EquivRemaining
