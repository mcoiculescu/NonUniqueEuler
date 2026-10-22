import NonUniqueEuler.Statement.Certificate
import NonUniqueEuler.Verify.Comp.RunCore

/-!
# Part 2 algorithms: the top-level checker `Verify.check`

`Verify.check : CertificateData → Bool` (types of `Statement/Certificate.lean`) converts the
statement-layer data to the core mirror `CertSpec` (field by field; the rationals are the same
type, core `Rat` = Mathlib `ℚ`) and runs `checkCore defaultPrec` (`Comp/RunCore.lean`),
the port of `sector3.run` for the two items followed by the exact re-check of
`ringcert check`.

The conversion exists so that the executable (`Verify/Main.lean`, built by `tools/ncert_build.sh`) needs only
core Lean: it evaluates `checkCore defaultPrec certLits`, and
`Verify.check_cert : check cert = checkCore defaultPrec certLits` (`Data/Cells.lean`, proved
without evaluating anything, from `CertSpec.ofCertificateData_toCertificateData`) says that this
is the value of `check cert`.

The final theorem's hypothesis is `check cert = true`; it is never evaluated in the kernel or
by `decide` (checker design decisions D1, D14).
-/

namespace NonUniqueEuler.Verify

/-- Core mirror of a statement-layer rectangle. -/
def Rect.ofQRect (R : QRect) : Rect := ⟨R.x₀, R.x₁, R.y₀, R.y₁⟩

/-- The statement-layer rectangle of a core rectangle. -/
def Rect.toQRect (R : Rect) : QRect := ⟨R.x0, R.x1, R.y0, R.y1⟩

/-- Core mirror of a statement-layer cell. -/
def CellSpec.ofCertCell (c : CertCell) : CellSpec := ⟨c.G.lo, c.G.hi, Rect.ofQRect c.rect⟩

/-- The statement-layer cell of a core cell. -/
def CellSpec.toCertCell (c : CellSpec) : CertCell := ⟨⟨c.lo, c.hi⟩, c.rect.toQRect⟩

/-- Core mirror of statement-layer run parameters. -/
def RunSpec.ofRunParams (r : RunParams) : RunSpec :=
  ⟨r.density, r.maxRounds, r.maxSegments, r.maxHalvings⟩

/-- The statement-layer run parameters of core run parameters. -/
def RunSpec.toRunParams (r : RunSpec) : RunParams :=
  ⟨r.density, r.maxRounds, r.maxSegments, r.maxHalvings⟩

/-- Core mirror of the statement-layer certificate data. -/
def CertSpec.ofCertificateData (c : CertificateData) : CertSpec :=
  ⟨c.countCells.map CellSpec.ofCertCell, RunSpec.ofRunParams c.countParams,
    c.gapCells.map CellSpec.ofCertCell, RunSpec.ofRunParams c.gapParams⟩

/-- The statement-layer certificate data of core data. -/
def CertSpec.toCertificateData (c : CertSpec) : CertificateData :=
  ⟨c.countCells.map CellSpec.toCertCell, c.countParams.toRunParams,
    c.gapCells.map CellSpec.toCertCell, c.gapParams.toRunParams⟩

theorem CellSpec.ofCertCell_toCertCell (c : CellSpec) : CellSpec.ofCertCell c.toCertCell = c :=
  rfl

theorem CertSpec.ofCertificateData_toCertificateData (c : CertSpec) :
    CertSpec.ofCertificateData c.toCertificateData = c := by
  obtain ⟨cc, cp, gc, gp⟩ := c
  have h : ∀ l : List CellSpec, (l.map CellSpec.toCertCell).map CellSpec.ofCertCell = l := by
    intro l
    rw [List.map_map]
    exact List.map_id'' (fun x => rfl) l
  simp only [CertSpec.ofCertificateData, CertSpec.toCertificateData, h]
  rfl

/-- **The certificate checker** (Part (2)): the two runs of §A.6 and the exact re-check of
§A.7 on the given data, at the package's precision of 128 bits. -/
def check (c : CertificateData) : Bool :=
  checkCore defaultPrec (CertSpec.ofCertificateData c)

end NonUniqueEuler.Verify
