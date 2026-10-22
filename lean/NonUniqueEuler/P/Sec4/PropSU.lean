import NonUniqueEuler.Defs.Sec4.Eigendata
import NonUniqueEuler.H.Sec4.PropSU.Spectrum
import NonUniqueEuler.H.Sec4.PropSU.Riesz

/-!
# Proof of `prop:SU` (the spectral hypothesis `(S_U)` holds with gap `9/200`)

Proof of the interface `I/Sec4/PropSU.lean` (`04_ring.tex:1253-1267`, proof `:1268-1295`).

* `lam_SU`: the sector-by-sector argument of the manuscript
  (`H/Sec4/PropSU/Spectrum.lean`, `PropSUH.lam_SU_core`): `eq:evans-units`, (N1), (N2) via
  `hypN_lamC`, `lem:resolvent`, `thm:evans-simple` (also in the conjugate sector `-3`),
  `cor:sector-6`, `cor:sectors-9`, and `L_0 = 0`.
* `SU_holds`: `lam_SU` with the rank-one projection `rieszSec = rankOneProj ℓ_* g_*`
  (`Dunford.IsAlgSimpleEig`).
* `R_sector` (R2 replacement of the second paragraph): `H/Sec4/PropSU/Riesz.lean`,
  `PropSUH.R_sector_core`: `R(G)w = ℓ_*(G)(w)φ_* + conj(ℓ_*(G)(conj w)) conj φ_*` is identified
  sector by sector (`P_3 φ_* = φ_*`, `conj φ_*` in the sector `-3`, `ℓ_*(G)` only sees `P_3 w`);
  idempotence and commutation with `e^{tL(G)}` are checked on each sector
  (`semigroup_sector`, `P² = P` and `L P = P L` of the simple spectral projections).
-/

noncomputable section

open Set ComplexConjugate

namespace NonUniqueEuler

namespace Eig

open RingData Sect

/-- **`prop:SU`** (`04_ring.tex:1253-1259`): under (N1)–(N3), `(S_U)` holds with gap `9/200`. -/
theorem SU_holds (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    SU χ (9 / 200) := by
  intro G hG
  refine ⟨lam χ G, ?_, fun s => ?_⟩
  · have h := (PropSUH.lam_SU_core χ hχ hN hG 0).1
    linarith
  · obtain ⟨-, h3, hg, hP, hm3, -, -, hrest⟩ := PropSUH.lam_SU_core χ hχ hN hG s
    exact ⟨h3, ⟨(ringPhiSetting χ).ellStarY s 3 (lam χ G) G,
      (ringPhiSetting χ).gStarY s 3 (lam χ G) G, hg, hP⟩, hm3, hrest⟩

/-- **`prop:SU` with the named eigenvalue** (`04_ring.tex:1255-1259`; R2 form of algebraic
simplicity): for `G ∈ [0,Ḡ]` and every `s`, with `λ_*(G) = Eig.lam χ G = λ_*^c(R_c²G)`:
`Re λ_*(G) > 211/2500`; the spectrum of `L_3(G)` on `X^s_3` in `{Re > 9/200}` is `{λ_*(G)}`, with
simple spectral projection `g ↦ ℓ_*(g) g_*` (`ℓ_*(g_*) = 1`); the spectrum of `L_{-3}(G)` on
`X^s_{-3}` in `{Re > 9/200}` is `{conj λ_*(G)}`, with simple spectral projection
`h ↦ conj(ℓ_*(conj h)) conj g_*`; and it is empty for `ℓ ∈ 3ℤ \ {3, -3}`. -/
theorem lam_SU (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) :
    211 / 2500 < (lam χ G).re ∧
      spectrum ℂ (Lin.Lsec χ s 3 G) ∩ {w : ℂ | 9 / 200 < w.re} = {lam χ G} ∧
      (ringPhiSetting χ).ellStarY s 3 (lam χ G) G ((ringPhiSetting χ).gStarY s 3 (lam χ G) G) = 1 ∧
      Dunford.IsSimpleSpectralProj (Lin.Lsec χ s 3 G)
        ((ringPhiSetting χ).rieszSec s 3 (lam χ G) G) (lam χ G) ∧
      spectrum ℂ (Lin.Lsec χ s (-3) G) ∩ {w : ℂ | 9 / 200 < w.re} = {conj (lam χ G)} ∧
      (ringPhiSetting χ).ellStarBarY s 3 (lam χ G) G
          ((ringPhiSetting χ).gStarBarY s 3 (lam χ G) G) = 1 ∧
      Dunford.IsSimpleSpectralProj (Lin.Lsec χ s (-3) G)
        ((ringPhiSetting χ).rieszSecBar s 3 (lam χ G) G) (conj (lam χ G)) ∧
      ∀ ℓ : ℤ, (3 : ℤ) ∣ ℓ → ℓ ≠ 3 → ℓ ≠ -3 →
        spectrum ℂ (Lin.Lsec χ s ℓ G) ∩ {w : ℂ | 9 / 200 < w.re} = ∅ :=
  PropSUH.lam_SU_core χ hχ hN hG s

/-- **R2 replacement of the second paragraph of `prop:SU`** (`04_ring.tex:1259-1267`): the Riesz
projection `R(G)` (`Eig.R`, the explicit rank-two operator) acts as the Riesz projection of `L_3(G)`
at `λ_*(G)` on the sector `3`, as that of `L_{-3}(G)` at `conj λ_*(G)` on the sector `-3`, and as
`0` on the other sectors; it is a projection and commutes with `e^{tL(G)}` (`t ≥ 0`). -/
theorem R_sector (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) :
    (∀ w : Y s annN, secProj s annN 3 (R χ s G w) =
        (ringPhiSetting χ).rieszSec s 3 (lam χ G) G (secProj s annN 3 w)) ∧
      (∀ w : Y s annN, secProj s annN (-3) (R χ s G w) =
        (ringPhiSetting χ).rieszSecBar s 3 (lam χ G) G (secProj s annN (-3) w)) ∧
      (∀ ℓ : ℤ, ℓ ≠ 3 → ℓ ≠ -3 → ∀ w : Y s annN, secProj s annN ℓ (R χ s G w) = 0) ∧
      R χ s G * R χ s G = R χ s G ∧
      ∀ t : ℝ, 0 ≤ t → Lin.S χ s G t * R χ s G = R χ s G * Lin.S χ s G t :=
  PropSUH.R_sector_core χ hχ hN hG s

end Eig

end NonUniqueEuler
