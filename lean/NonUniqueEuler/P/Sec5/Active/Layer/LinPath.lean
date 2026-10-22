import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec4.Duhamel
import NonUniqueEuler.I.Sec4.SemigroupLaw
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.H.Sec5.Active.Layer.LinPath.Bridge
import NonUniqueEuler.H.Sec5.Active.Layer.LinPath.Forcing

/-!
# Proof: the linear response `wlin₀` as an approximate solution for `lem:energy`

Proof of `I/Sec5/Active/Layer/LinPath.lean` (`05_single_ring.tex:976-981`: "Lemma
`lem:duhamel` with `k = M-1` shows that `wlin ∈ C([0,ū];X^{M-1}) ∩ C¹([0,ū];X^{M-2})` is real
with `∂_u wlin = L wlin + F`", here at a general level `k + 1`).

Proof. The forcing `v ↦ toY (k+1) N (F v)` is a real path in `C([0,T];X^{k+1})`
(`LinPathH.forcing_path`), and `toY (k+1) N w₀ ∈ X^{k+1}` is real with function `w₀`. Then
`lem:duhamel` (`Lin.duhamel_spec`) gives continuity in `Y^{k+1}(N)`, membership in `X^{k+1}`,
realness, and the derivative `L(G)wlin₀ + lowerY (toY (F u))` of `lowerY ∘ wlin₀` in `Y^k(N)`.
The bridges `toY (k+1) N (y.fn) = y`, `lowerY k (k+1) N y = toY k N (y.fn)` (`lowerY_toY`) and
`(L(G)y).fn = Lfn χ G (y.fn)` (`L_fn_ae`) turn these into `PathC` / `PathC1` on functions; the
derivative lies in `X^k` because it is the derivative of a path in the closed subspace `X^k`
(`memX_of_hasDerivWithinAt`). Finally `wlin₀(0) = e^{0L}toY w₀ = toY w₀` (`semigroup_zero`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- **The linear response as a `C¹` path** (`05_single_ring.tex:976-981`, `lem:duhamel` at level
`k + 1`): `wapp(u) = (wlin0 χ (k+1) G w₀ h u).fn` lies in `C([0,T];X^{k+1}) ∩ C¹([0,T];X^k)`
with derivative `L(G)wapp + F`, is real, and starts at `w₀`. -/
theorem wlin0_path (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {k : ℕ} {G T : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) (hT : 0 < T)
    {w₀ : ℂ → ℂ} (hw₀ : Lin.MemXFn (k + 1) w₀)
    (hw₀r : ∀ᵐ x ∂(volume : Measure ℂ), (w₀ x).im = 0)
    {h : ℝ → ℂ → ℂ} (hh : CkPathOn (k + 1) annN' (Icc 0 T) h)
    (hsym : ∀ u ∈ Icc (0 : ℝ) T, IsSymFieldOn annN' (h u)) :
    PathC (k + 1) T (fun u => (wlin0 χ (k + 1) G w₀ h u).fn) ∧
      PathC1 k T (fun u => (wlin0 χ (k + 1) G w₀ h u).fn)
        (fun u x => Lin.Lfn χ G (wlin0 χ (k + 1) G w₀ h u).fn x + forcing χ h u x) ∧
      (∀ u ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure ℂ),
        ((wlin0 χ (k + 1) G w₀ h u).fn x).im = 0) ∧
      (wlin0 χ (k + 1) G w₀ h 0).fn =ᵐ[volume] w₀ := by
  -- the datum `toY w₀ ∈ X^{k+1}`, real, with function `w₀`
  have hw₀fn : (Sect.toY (k + 1) annN w₀).fn =ᵐ[volume] w₀ := LinPathH.MemXFn.toY_fn hw₀
  have hw₀X : Lin.MemX (Sect.toY (k + 1) annN w₀) := LinPathH.MemXFn.memX_toY hw₀
  have hw₀R : (Sect.toY (k + 1) annN w₀).IsReal := by
    show ∀ᵐ x ∂(volume : Measure ℂ), ((Sect.toY (k + 1) annN w₀).fn x).im = 0
    filter_upwards [hw₀fn, hw₀r] with x h1 h2
    rw [h1]
    exact h2
  -- the forcing path
  obtain ⟨hFc, hF⟩ := LinPathH.forcing_path χ hχ hN hh hsym
  -- `lem:duhamel`
  obtain ⟨hc, hX, hd, hc', hR⟩ :=
    Lin.duhamel_spec χ hχ hG hT k hw₀X hFc fun t ht => (hF t ht).2.1
  set W : ℝ → Sect.Y (k + 1) annN := wlin0 χ (k + 1) G w₀ h with hWdef
  have hc : ContinuousOn W (Icc 0 T) := hc
  have hX : ∀ t ∈ Icc (0 : ℝ) T, Lin.MemX (W t) := hX
  have hd : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun τ => Sect.lowerY k (k + 1) annN (W τ))
        (Lin.L χ k G (W t) + Sect.lowerY k (k + 1) annN
          (Sect.toY (k + 1) annN (forcing χ h t))) (Icc 0 T) t := hd
  have hc' : ContinuousOn (fun t => Lin.L χ k G (W t) + Sect.lowerY k (k + 1) annN
      (Sect.toY (k + 1) annN (forcing χ h t))) (Icc 0 T) := hc'
  have hR : ∀ t ∈ Icc (0 : ℝ) T, (W t).IsReal := hR hw₀R fun t ht => (hF t ht).2.2
  -- `PathC (k+1)`
  have hDX : ∀ t ∈ Icc (0 : ℝ) T, Lin.MemXFn (k + 1) (W t).fn := fun t ht =>
    LinPathH.memXFn_of_memX (hX t ht)
  have hPC : PathC (k + 1) T (fun u => (W u).fn) :=
    ⟨hDX, hc.congr fun t _ => LinPathH.toY_fn_self _⟩
  -- lowering the level
  have hlow : ∀ t ∈ Icc (0 : ℝ) T,
      Sect.lowerY k (k + 1) annN (W t) = Sect.toY k annN (W t).fn := fun t ht => by
    rw [← LinPathH.lowerY_toY (Nat.le_succ k) (hDX t ht), LinPathH.toY_fn_self]
  have hPCk : PathC k T (fun u => (W u).fn) := by
    refine ⟨fun t ht => LinPathH.MemXFn.mono (hDX t ht) (Nat.le_succ k), ?_⟩
    exact ((Sect.lowerY k (k + 1) annN).continuous.comp_continuousOn hc).congr fun t ht =>
      (hlow t ht).symm
  -- the derivative `V t = L(G)W t + F t` in `Y^k(N)`
  have hVX : ∀ t ∈ Icc (0 : ℝ) T,
      Lin.MemX (Lin.L χ k G (W t) + Sect.lowerY k (k + 1) annN
        (Sect.toY (k + 1) annN (forcing χ h t))) := fun t ht =>
    LinPathH.memX_of_hasDerivWithinAt hT ht (fun τ hτ => by
      show Lin.MemX (Sect.lowerY k (k + 1) annN (W τ))
      rw [hlow τ hτ]
      exact LinPathH.MemXFn.memX_toY (LinPathH.MemXFn.mono (hDX τ hτ) (Nat.le_succ k)))
      (hd t ht)
  have hVfn : ∀ t ∈ Icc (0 : ℝ) T,
      (Lin.L χ k G (W t) + Sect.lowerY k (k + 1) annN
        (Sect.toY (k + 1) annN (forcing χ h t))).fn =ᵐ[volume]
        fun x => Lin.Lfn χ G (W t).fn x + forcing χ h t x := by
    intro t ht
    have h1 := LinPathH.Y_fn_add (Lin.L χ k G (W t))
      (Sect.lowerY k (k + 1) annN (Sect.toY (k + 1) annN (forcing χ h t)))
    have h2 := LinPathH.L_fn_ae χ hχ k G (W t)
    have h3 : (Sect.lowerY k (k + 1) annN (Sect.toY (k + 1) annN (forcing χ h t))).fn
        =ᵐ[volume] forcing χ h t :=
      ((Sect.lowerY_spec (Nat.le_succ k) annN).1 _).trans (hF t ht).1
    filter_upwards [h1, h2, h3] with y e1 e2 e3
    rw [e1, e2, e3]
  have hu'X : ∀ t ∈ Icc (0 : ℝ) T,
      Lin.MemXFn k (fun x => Lin.Lfn χ G (W t).fn x + forcing χ h t x) := fun t ht =>
    LinPathH.MemXFn.congr_ae (LinPathH.memXFn_of_memX (hVX t ht)) (hVfn t ht)
  have hu'Y : ∀ t ∈ Icc (0 : ℝ) T,
      Sect.toY k annN (fun x => Lin.Lfn χ G (W t).fn x + forcing χ h t x) =
        Lin.L χ k G (W t) + Sect.lowerY k (k + 1) annN
          (Sect.toY (k + 1) annN (forcing χ h t)) := fun t ht => by
    rw [← LinPathH.toY_congr_ae (hVfn t ht), LinPathH.toY_fn_self]
  have hPC1 : PathC1 k T (fun u => (W u).fn)
      (fun u x => Lin.Lfn χ G (W u).fn x + forcing χ h u x) := by
    refine ⟨hPCk, ⟨hu'X, hc'.congr fun t ht => hu'Y t ht⟩, fun t ht => ?_⟩
    exact ((hd t ht).congr_of_mem (fun τ hτ => (hlow τ hτ).symm) ht).congr_deriv
      (hu'Y t ht).symm
  -- the initial value
  have h0 : W 0 = Sect.toY (k + 1) annN w₀ := by
    rw [hWdef, wlin0_def, intervalIntegral.integral_same, add_zero]
    show (ringPhiSetting χ).semigroup (k + 1) G 0 (Sect.toY (k + 1) annN w₀) = _
    rw [(ringPhiSetting χ).semigroup_zero (ringPhiSetting_valid hχ)]
    rfl
  refine ⟨hPC, hPC1, hR, ?_⟩
  rw [h0]
  exact hw₀fn

end OneRing

end NonUniqueEuler
