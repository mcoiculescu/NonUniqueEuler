import NonUniqueEuler.Statement.Evans
import NonUniqueEuler.Statement.Certificate
import NonUniqueEuler.Defs.Verify.Winding
import NonUniqueEuler.Defs.Verify.Contour

/-!
# The statements (N1′) and (N2′) (Definition A.5)

Manuscript: Definition A.5 (`def:Nprime`, `A_verification.tex:518-534`), the rectangle
`R_A = [9/200, 3] × [-5, 3]` and `G'_max = d` (`A_verification.tex:30-33`), and the remark on
halved intervals (`A_verification.tex:744-751`: "the proof of Lemma A.6 does not use their
number").

* `RA`: the rectangle `R_A`.
* `WindsOnce χ R G`: `E_3(·; G) ≠ 0` on `∂R` and `wind(E_3(∂R; G), 0) = 1`, along the
  counterclockwise boundary curve `R.bdryPath` on `[0, 4]` (`HasWinding` contains the
  nonvanishing; the image of `[0, 4]` is `∂R` for a nondegenerate `R`).
* `CellCertified χ c w`: the output contract of one successful certification of a cell
  `c = (𝒢, ℛ')` with result `w`: for every `G ∈ 𝒢` with `G ≥ 0`, `E_3(·; G)` winds `w` times
  along `∂ℛ'` (Proposition A.7's argument for one cell). The code side proves
  `CellCertified χ c w` from a successful run; `N1'_of_cells` and `N2'_of_cells` assemble (N1′)
  and (N2′) from the cells of the two runs.
* `N1' χ`: for every `G ∈ [0, d]`, `WindsOnce χ RA G`.
* `N2' χ`: finitely many cells (a list of statement-layer `CertCell`s: an interval of `G` with
  rational endpoints and a rectangle with rational vertices) whose intervals cover `[0, d]`,
  whose rectangles have left edge on `Re λ = 211/2500`, are nondegenerate and lie in `R_A`,
  and such that `WindsOnce χ c.rect G` for every `G ∈ c.G ∩ [0, d]`. (The manuscript's "236
  intervals with union `[0, G'_max]`" is the instance of the run; Lemma A.6 does not use the
  number of cells, and only `G ∈ [0, d]` matter since the union is `[0, d]`.)
-/

noncomputable section

open Set

namespace NonUniqueEuler

open RingData

/-- The rectangle `R_A = [9/200, 3] × [-5, 3]` (`A_verification.tex:32`). -/
def RA : QRect := ⟨9 / 200, 3, -5, 3⟩

/-- `E_3(·; G) ≠ 0` on `∂R` and `wind(E_3(∂R; G), 0) = 1`. -/
def WindsOnce (χ : ℝ → ℝ) (R : QRect) (G : ℝ) : Prop :=
  HasWinding (fun t => evans χ 3 (R.bdryPath t) G) 0 4 1

/-- The certified property of one cell `c = (𝒢, ℛ')` with result `w`: for every `G ∈ 𝒢`,
`G ≥ 0`, `E_3(·; G)` is nonvanishing on `∂ℛ'` and winds `w` times around `0` along it. -/
def CellCertified (χ : ℝ → ℝ) (c : CertCell) (w : ℤ) : Prop :=
  ∀ G ∈ c.G.toSet, 0 ≤ G → HasWinding (fun t => evans χ 3 (c.rect.bdryPath t) G) 0 4 w

/-- **(N1′)** (`A_verification.tex:522-523`): for every `G ∈ [0, G'_max] = [0, d]`,
`E_3(·; G) ≠ 0` on `∂R_A` and `wind(E_3(∂R_A; G), 0) = 1`. -/
def N1' (χ : ℝ → ℝ) : Prop :=
  ∀ G ∈ Icc (0 : ℝ) d, WindsOnce χ RA G

/-- The shape conditions on a rectangle of the (N2′) run (`A_verification.tex:526-528`, and
the re-check of `A_verification.tex:619-626`): left edge on `Re λ = 211/2500`, nondegenerate,
contained in `R_A`. -/
structure GapRectOK (R : QRect) : Prop where
  left : R.x₀ = 211 / 2500
  nondeg : R.Nondeg
  subset : R.closedSet ⊆ RA.closedSet

/-- **(N2′)** (`A_verification.tex:524-529`): finitely many cells whose intervals cover
`[0, d]`, with rectangles as in `GapRectOK`, such that for every cell and every `G` of its
interval (in `[0, d]`), `E_3(·; G) ≠ 0` on the boundary of its rectangle and winds once
around `0` along it. -/
def N2' (χ : ℝ → ℝ) : Prop :=
  ∃ cells : List CertCell,
    (∀ G ∈ Icc (0 : ℝ) d, ∃ c ∈ cells, G ∈ c.G.toSet) ∧
    (∀ c ∈ cells, GapRectOK c.rect) ∧
    (∀ c ∈ cells, ∀ G ∈ c.G.toSet, G ∈ Icc (0 : ℝ) d → WindsOnce χ c.rect G)

/-! ### Assembling (N1′) and (N2′) from certified cells (proved) -/

/-- (N1′) from a list of certified cells with rectangle `R_A` whose intervals cover `[0, d]`
(the first run, `A_verification.tex:653-657`). -/
theorem N1'_of_cells {χ : ℝ → ℝ} (cells : List CertCell)
    (hcov : ∀ G ∈ Icc (0 : ℝ) d, ∃ c ∈ cells, G ∈ c.G.toSet)
    (hrect : ∀ c ∈ cells, c.rect = RA) (hcert : ∀ c ∈ cells, CellCertified χ c 1) :
    N1' χ := by
  intro G hG
  obtain ⟨c, hc, hGc⟩ := hcov G hG
  have h := hcert c hc G hGc hG.1
  rw [hrect c hc] at h
  exact h

/-- (N2′) from a list of certified cells with admissible rectangles whose intervals cover
`[0, d]` (the second run, `A_verification.tex:657-659`). -/
theorem N2'_of_cells {χ : ℝ → ℝ} (cells : List CertCell)
    (hcov : ∀ G ∈ Icc (0 : ℝ) d, ∃ c ∈ cells, G ∈ c.G.toSet)
    (hrect : ∀ c ∈ cells, GapRectOK c.rect) (hcert : ∀ c ∈ cells, CellCertified χ c 1) :
    N2' χ :=
  ⟨cells, hcov, hrect, fun c hc G hGc hG => hcert c hc G hGc hG.1⟩

end NonUniqueEuler
