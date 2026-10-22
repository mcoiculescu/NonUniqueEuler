import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.ReductionField
import NonUniqueEuler.H.Sec5.Energy.RappPath.Linear
import NonUniqueEuler.H.Sec5.Energy.RappPath.Terms

/-!
# Proof (step of `P/Sec5/Energy`): `R_app ∈ C([0,t]; X^s)`

Proof of `I/Sec5/Energy/RappPath.lean`: the sentence "Every term lies in `C([0,t];H^s)`" of the
proof of `lem:energy` (`05_single_ring.tex:331`).

`R_app = w_app' - (L(G)w_app + B(w_app,w_app) - h·∇w_app - h·∇Φ)`, and each term is a path in
`C([0,t];X^s)`:
* `w_app'`: `PathC1 s t w_app w_app'` contains `PathC s t w_app'`;
* `L(G)w_app`: `RappPathH.pathC_Lfn` (`Lin.L χ s G : Y^{s+1} → Y^s` is bounded and acts on
  functions by `L(G)`, `lem:semigroup-construct`(2); `L(G)` commutes with rotations,
  `lem:sector`(2));
* `B(w_app,w_app)`: `RappPathH.pathC_Bfn` (`lem:bilinear`(1) and the a.e. bilinearity of `B`);
* `h·∇w_app`, `h·∇Φ`: `RappPathH.pathC_hGrad`, `RappPathH.pathC_hGradPhi` (`lem:bilinear`(2),(3);
  `t ↦ h(t) ∈ C^s(N')` is continuous and `h(t)` is `3`-fold symmetric near `N'` by
  `lem:reduction`(1), `reduction_field`).
`X^s` is a linear space and `Sect.toY` is additive on it (`RappPathH.PathC.add`, `.sub`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- **`R_app ∈ C([0,t];X^s)`** (proof of `lem:energy`, `05_single_ring.tex:331`). -/
theorem rapp_pathC (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 3 ≤ s) {c : RingConfig} {t : ℝ} (hc : c.Hyp t) {wapp wapp' : ℝ → ℂ → ℂ}
    (happ : PathC (s + 1) t wapp) (happ' : PathC1 s t wapp wapp') :
    PathC s t (Rapp χ c.G c.h wapp wapp') := by
  obtain ⟨hfield, hpath⟩ := reduction_field hc
  have hs2 : 2 ≤ s := by omega
  -- `h(τ)` is `3`-fold symmetric on `N'` (`lem:reduction`(1))
  have hsym : ∀ τ ∈ Icc (0 : ℝ) t, IsSymFieldOn annN' (c.h τ) := by
    intro τ hτ
    obtain ⟨U, -, hNU, -, -, -, hsymU, -⟩ := hfield τ hτ
    exact fun x hx => hsymU x (hNU hx)
  -- the four terms of `eq:ring` at `w_app`
  have hL := RappPathH.pathC_Lfn χ hχ c.G happ
  have hB := RappPathH.pathC_Bfn hs2 happ
  have hH := RappPathH.pathC_hGrad hs2 happ (hpath s) hsym
  have hP := RappPathH.pathC_hGradPhi χ hχ hN hs2 (hpath s) hsym
  have hR := RappPathH.PathC.sub happ'.2.1
    (RappPathH.PathC.sub (RappPathH.PathC.sub (RappPathH.PathC.add hL hB) hH) hP)
  exact hR

end OneRing

end NonUniqueEuler
