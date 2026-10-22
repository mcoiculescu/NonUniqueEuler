import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.Quiet
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.H.Sec5.QuietHandoff.Basic

/-!
# Proof: `cor:quiet-handoff` (the quiet ring at the hand-off)

Proof of `I/Sec5/QuietHandoff.lean` (`05_single_ring.tex:565-577`).

The first two assertions are `thm:quiet`(a) and (c) (`quiet`, through `quietConsts_spec`). For
the third: `w(t)` lies in `X^{s_h}` (`thm:quiet`(a): `w` solves `eq:ring`, `RingConfig.PertEq`)
and `wlin(t) ∈ Y^{s_h}(N)`; both are represented in `Y^0(N) = L²(N)`, where `ℓ_*(G)` is the
bounded functional `Eig.ell χ 0 G` (`exists_ell`) of norm `≤ ‖ℓ_*‖` (`uniform_constants`), and
`Eig.ellFn` only sees the a.e. class (`QuietHandoffH.ellFn_congr_ae`). So
`|ℓ_*(w) - ℓ_*(wlin)| ≤ ‖ℓ_*‖ ‖w - wlin‖_{L²} ≤ ‖ℓ_*‖ ‖w - wlin‖_{H^{s_h}} ≤ ‖ℓ_*‖ C_Q maj²`
(`thm:quiet`(b)).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- `|ℓ_*(G)(f) - ℓ_*(G)(g)| ≤ ‖ℓ_*(G)‖_{(Y^0)^*} ‖f - g‖_{H^s}` for `f, g ∈ H^s` vanishing a.e.
outside `N`. -/
theorem QuietHandoffH.norm_ellFn_sub_le (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {s : ℕ} {f g : ℂ → ℂ}
    (hf : Sob.MemH s f) (hg : Sob.MemH s g)
    (hfs : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → f x = 0)
    (hgs : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → g x = 0) :
    ‖Eig.ellFn χ G f - Eig.ellFn χ G g‖ ≤ ‖Eig.ell χ 0 G‖ * Sob.normH s (f - g) := by
  have hspec := Eig.ell_spec_of_exists (Eig.exists_ell χ hχ hN hG 0)
  have hf0 : Sob.MemH 0 f := hf.mono_order (Nat.zero_le s)
  have hg0 : Sob.MemH 0 g := hg.mono_order (Nat.zero_le s)
  obtain ⟨f', hf'⟩ := QuietHandoffH.exists_Y_of_memH (K := annN) hf0 hfs
  obtain ⟨g', hg'⟩ := QuietHandoffH.exists_Y_of_memH (K := annN) hg0 hgs
  have e1 : Eig.ellFn χ G f = Eig.ell χ 0 G f' := by
    rw [hspec, QuietHandoffH.ellFn_congr_ae χ G hf']
  have e2 : Eig.ellFn χ G g = Eig.ell χ 0 G g' := by
    rw [hspec, QuietHandoffH.ellFn_congr_ae χ G hg']
  rw [e1, e2, ← map_sub]
  refine ((Eig.ell χ 0 G).le_opNorm _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (ContinuousLinearMap.opNorm_nonneg _)
  obtain ⟨hm, hn⟩ := QuietHandoffH.Y_memH_fn (f' - g')
  have hae : (f' - g').fn =ᵐ[volume] f - g := by
    filter_upwards [QuietHandoffH.Y_fn_sub f' g', hf', hg'] with x hx h1 h2
    rw [hx, h1, h2]
    rfl
  rw [← hn, ← (hm.congr_ae hae).2]
  exact (hf.sub hg).1.normH_mono (Nat.zero_le s)

/-- **`cor:quiet-handoff`** (`05_single_ring.tex:565-570`). Under the assumptions of
`thm:quiet` (with its constants `maj_* = majst χ sh NQ`, `C_Q = CQ χ sh NQ`), for every
`t ∈ [0,T]`: `supp(Φ + w(t)) ⊂ 𝒩₋`, `‖w(t)‖_{H^{s_h}} ≤ C_Q maj(t)`, and
`|ℓ_*(w(t)) - ℓ_*(wlin(t))| ≤ ‖ℓ_*‖ C_Q maj(t)²`. -/
theorem quiet_handoff (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {sh NQ : ℕ} (hs : 3 ≤ sh) (hQ : 2 ≤ NQ) (hΛ : Lam χ sh ≤ NQ * Eig.sigb χ)
    {c : RingConfig} {T : ℝ} (hc : c.Hyp T) (hr : c.ring0 = ringPhi χ)
    (hG : c.G ∈ Icc (0 : ℝ) Gbar) {η : ℝ → ℝ} (hη : Measurable η)
    (hh : ∀ t ∈ Icc (0 : ℝ) T, normCk (Mh sh NQ) annN' (c.h t) ≤ η t ∧ η t ≤ 1)
    (hmaj : ∀ t ∈ Icc (0 : ℝ) T, maj (Eig.sigma χ c.G) η t ≤ majst χ sh NQ) :
    ∀ t ∈ Icc (0 : ℝ) T, tsupport (c.ringPart t) ⊆ annNm ∧
      Sob.normH sh (c.w χ t) ≤ CQ χ sh NQ * maj (Eig.sigma χ c.G) η t ∧
      ‖Eig.ellFn χ c.G (c.w χ t) - Eig.ellFn χ c.G (wlin χ sh c.G c.h t).fn‖ ≤
        Eig.ellNorm χ * CQ χ sh NQ * maj (Eig.sigma χ c.G) η t ^ 2 := by
  obtain ⟨-, -, -, -, hall⟩ := quietConsts_spec (quiet χ hχ hN hs hQ hΛ)
  obtain ⟨hpert, hbd⟩ := hall c T hc hr hG η hη hh hmaj
  intro t ht
  obtain ⟨-, hsupp, hdiff, hw⟩ := hbd t ht
  refine ⟨hsupp, hw, ?_⟩
  have hwX : Lin.MemXFn sh (c.w χ t) := (hpert sh).1.1 t ht
  have hellle : ‖Eig.ell χ 0 c.G‖ ≤ Eig.ellNorm χ :=
    ((Eig.uniform_constants χ hχ hN).2.2.2.2.2.2.2.2 c.G hG).2.2.2.1
  have hEN : 0 ≤ Eig.ellNorm χ := (ContinuousLinearMap.opNorm_nonneg _).trans hellle
  have hkey := QuietHandoffH.norm_ellFn_sub_le χ hχ hN hG hwX.1
    (QuietHandoffH.Y_memH_fn (wlin χ sh c.G c.h t)).1 hwX.2.1
    (QuietHandoffH.Y_fn_zero_outside (wlin χ sh c.G c.h t))
  calc ‖Eig.ellFn χ c.G (c.w χ t) - Eig.ellFn χ c.G (wlin χ sh c.G c.h t).fn‖
      ≤ ‖Eig.ell χ 0 c.G‖ * Sob.normH sh (c.w χ t - (wlin χ sh c.G c.h t).fn) := hkey
    _ ≤ Eig.ellNorm χ * Sob.normH sh (c.w χ t - (wlin χ sh c.G c.h t).fn) :=
        mul_le_mul_of_nonneg_right hellle (Sob.normH_nonneg _ _)
    _ ≤ Eig.ellNorm χ * (CQ χ sh NQ * maj (Eig.sigma χ c.G) η t ^ 2) :=
        mul_le_mul_of_nonneg_left hdiff hEN
    _ = Eig.ellNorm χ * CQ χ sh NQ * maj (Eig.sigma χ c.G) η t ^ 2 := by ring

end OneRing

end NonUniqueEuler
