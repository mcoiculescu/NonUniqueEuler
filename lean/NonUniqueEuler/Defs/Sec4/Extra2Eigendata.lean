import NonUniqueEuler.Defs.Sec4.Eigendata

/-!
# Section 4.5: two auxiliary objects of the eigendata (definitions)

Manuscript `04_ring.tex:1333-1338` (the representer of
`ℓ_*(G)` on `L²(N)`, the remark after `def:eigendata`) and `04_ring.tex:1522-1530`
(`lem:uniform`: the field term `h·∇Φ`).

* `Eig.ellRep χ G`: the function
  `x ↦ (n_*/(2π conj J)) conj(ψ_*(log|x|) M_*(|x|)) e^{3iθ}` restricted to `N`, which represents
  `ℓ_*(G)` on `L²(N)`: `ℓ_*(G)(w) = ∫ w conj(ellRep)` (`04_ring.tex:1333-1338`). With
  `S.adjEig ℓ z G r = conj(ψ_*(log r) M_*(r))` this is `n_*/(2π conj J) · ofProfile 3 adjEig` on
  `N`. Check: `∫_N w · conj(ellRep) = (n_*/(2πJ)) ∫ (∫_0^{2π} w e^{-3iθ} dθ) ψ_* M_* r dr
  = n_* J⁻¹ ∫ w_3 ψ_* M_* r dr = n_* ℓ_*(w_3)`.
* `Eig.hGradPhi χ h = h·∇Φ` for a vector field `h : ℂ → ℂ` (`Sob.dotGrad`, weak derivatives of
  the complexified ring `Φ`; it equals `DΦ(x)(h(x))` a.e. since `Φ` is smooth). This is the
  convention of `I/Infra/Sobolev/Leibniz.lean` (`MemH.dotGrad_of_memCk`).

No lemmas; nothing here is a manuscript statement.
-/

noncomputable section

open MeasureTheory Set Real ComplexConjugate

namespace NonUniqueEuler

namespace Eig

open RingData

/-- The representer of `ℓ_*(G)` on `L²(N)` (`04_ring.tex:1333-1338`):
`x ↦ (n_*/(2π conj J)) conj(ψ_*(log|x|) M_*(|x|)) e^{3iθ}` on `N`, and `0` outside `N`. -/
def ellRep (χ : ℝ → ℝ) (G : ℝ) : ℂ → ℂ :=
  annN.indicator fun x =>
    ((nstar χ G : ℝ) : ℂ) / (2 * π * conj (J χ G)) *
      Ang.ofProfile 3 ((ringPhiSetting χ).adjEig 3 (lam χ G) G) x

/-- The field term `h·∇Φ = h₁ ∂₁Φ + h₂ ∂₂Φ` for a vector field `h = h₁ + i h₂ : ℂ → ℂ`
(`04_ring.tex:1522-1530`), with the complexified ring `Φ`. -/
def hGradPhi (χ : ℝ → ℝ) (h : ℂ → ℂ) : ℂ → ℂ :=
  Sob.dotGrad h fun y => ((ringPhi χ y : ℝ) : ℂ)

end Eig

end NonUniqueEuler
