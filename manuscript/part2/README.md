# Part II: The Nonlinear Construction

LaTeX source of

> M. P. Coiculescu, *Non-Uniqueness of Weak Solutions to the Unforced Two-Dimensional Euler
> Equations with Vorticity in L¹ ∩ Lᵖ, II: The Nonlinear Construction.*

Part II proves the main theorem. It reduces it to three explicit statements about the ring of
Part I (Hypothesis 4.17 of Part I), constructs the approximate solutions by relaying an
instability outward through a multiscale datum, and verifies the three statements: two with
rigorous interval arithmetic (Appendix A, using the package `euler-ring-certificate`) and one by
hand. Appendix B gives the existence theory for the smooth solutions used in the construction.

## Building

Part II refers to statements of Part I by their numbers (printed as "Lemma I.x.y"), which it reads
from Part I's `main.aux` with the `xr-hyper` package. Build Part I first:

```
cd ../part1 && pdflatex main.tex && pdflatex main.tex
cd ../part2 && pdflatex main.tex && pdflatex main.tex
```

(or `latexmk -pdf main.tex` in each directory, Part I first).

## License

Apache License 2.0; see `LICENSE` at the top of the repository.
