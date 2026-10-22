# Part I: A Compactness Criterion and the Linear Analysis

LaTeX source of

> M. P. Coiculescu, *Non-Uniqueness of Weak Solutions to the Unforced Two-Dimensional Euler
> Equations with Vorticity in L¹ ∩ Lᵖ, I: A Compactness Criterion and the Linear Analysis.*

These are the files submitted to arXiv (comments stripped). The paper proves a compactness
criterion that turns approximate solutions with a non-radial moment bounded below into a second
renormalized weak solution (Theorem 1.2), and the linear instability of the ring, the building
block of the multiscale datum (Theorem 1.3). The instability uses the numerical Hypothesis 4.17,
which Part II verifies with rigorous interval arithmetic.

## Status

Part I is complete and ready for public sharing, on arXiv and with the mathematical community;
comments are welcome. Part II, which contains the nonlinear construction, the verification of
Hypothesis 4.17 and the proof of the main theorem, is still in preparation and will be added to
this repository when it is ready.

## Building

From this directory, with a standard TeX Live installation:

```
pdflatex main.tex
pdflatex main.tex
```

(or `latexmk -pdf main.tex`). The bibliography is written into `refs.tex`, so no BibTeX run is
needed. The output is a 42-page PDF.

## Layout

```
main.tex          preamble, title, abstract
macros.tex        notation macros
refs.tex          bibliography
sections/         01_intro, 02_prelim, 03_compactness, 04_ring
figures/          ring.pdf (Figure 2), datum.pdf (Figure 1)
figures/*.wls     Mathematica scripts that draw the figures and print the decimal values of the
                  ring constants in Definition 4.1
```

The figures are illustrations and are not used in any proof. To redraw them:

```
wolframscript -file figures/ring.wls
wolframscript -file figures/datum.wls
wolframscript -file figures/ring_constants.wls
```

## License

Apache License 2.0; see `LICENSE` at the top of the repository.
