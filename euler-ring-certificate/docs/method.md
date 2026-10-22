# Method

This file states what each computation proves and why it is rigorous. The proofs of the analytic
statements (Lemma A.1 on the end regions, Lemma A.2 on the location of the zeros, Proposition A.3 on
the enclosure, Proposition A.4 on the winding count, and Lemma A.6, which deduces (N1) and (N2) from
(N1′) and (N2′)) are in Appendix A of the paper, and the correspondence between zeros of the Evans
function and eigenvalues is in its main text; they are summarized here only as far as needed to read
the code.

## 1. Objects

Data (exact dyadic rationals; `src/ringcert/data.py`):

| symbol | code | value |
|---|---|---|
| $a_0$ | `A0_Q` | $-7304210039150669\cdot2^{-54}$ |
| $d$ | `DD_Q` | $5764607523034235\cdot2^{-58}$ |
| $\xi_L$ | `SL_Q` | $-4528212286209965\cdot2^{-52}$ |
| $\xi_a$ | `SA_Q` | $-4077852323472915\cdot2^{-52}$ |
| $\xi_b$ | `SB_Q` | $1/2$ |
| $\xi_R$ | `SR_Q` | $5404319552844595\cdot2^{-53}$ |
| $G_{\max}$ | `G_MAX_Q` | $d$ |

The code writes $s$ for the variable $\xi=\log r$ of the paper. $H(x)=(1+e^{-2x})^{-1}$. A cutoff
$\chi\in C_c^\infty(\mathbb R)$ is *admissible* if $0\le\chi\le1$, $\chi$ is nondecreasing on
$(-\infty,\xi_a]$, equal to $1$ on $[\xi_a,\xi_b]$, nonincreasing on $[\xi_b,\infty)$, and supported in
$[\xi_L,\xi_R]$. The profile is $\bar\omega=\chi\,H((\xi-a_0)/d)\,H(-\xi/d)$, with
$f_s=\bar\omega'$, $g(\xi)=\int_{-\infty}^\xi\bar\omega e^{2\xi'}d\xi'$ and $\Omega_G=(g+G)e^{-2\xi}$.

For $m\ge1$, real $G$ and $\Re\lambda>0$: $\psi''=Q\psi$ on $[\xi_L,\xi_R]$ with
$Q=m^2+imf_s/(\lambda+im\Omega_G)$, $\psi(\xi_L)=1$, $\psi'(\xi_L)=m$, and
$\mathcal E_m(\lambda;G)=e^{-m(\xi_R-\xi_L)}(\psi'+m\psi)(\xi_R)$. Since $\Omega_G$ is real,
$\lvert\lambda+im\Omega_G\rvert\ge\Re\lambda$.

Derived constants: $x_a=(\xi_a-a_0)/d$, $y_b=-\xi_b/d$, $TV_{\rm end}=\frac94e^{2\max(x_a,y_b)}$,
$\Omega_{\max}=\frac12+G_{\max}e^{-2\xi_L}$, $X_m=\pi md/\sin(\pi md)$,
$\epsilon_*=\max(H(x_a),H(y_b))$.

## 2. Ball arithmetic

Every real quantity is an Arb ball (`arb`, an interval $[c-r,c+r]$ with exact dyadic $c,r$) and
every complex quantity an Arb box (`acb`, a product of two real balls), at 128 bits. The property
used is Arb's containment contract: each operation returns a ball (box) containing the exact result
for every choice of the inputs in the input balls. Comparisons such as `x > 0` are *certain*: they
return true only if every point of the ball satisfies the relation. Rational inputs enter only through
`balls.dy` (exact dyadics, asserted exact) and `balls.qball` (exact or `arb(p)/arb(q)`); no Python
float enters a certified quantity (`tests/test_float_free.py` checks this statically and dynamically).

## 3. The enclosure of $\mathcal E_m$ (`evans.evans`)

**Statement (box form).** For every acb box $\Lambda$ with $\Re\Lambda>0$ certainly and every arb ball
$\mathcal G$, `evans(Λ, 𝒢, m, grid)` returns an acb box containing $\mathcal E_m(\lambda;G)$ for all
$\lambda\in\Lambda$, $G\in\mathcal G$ and every admissible $\chi$, or a NaN box.

**End regions** $[\xi_L,\xi_a]$, $[\xi_b,\xi_R]$ (Lemma A.1). There $\int\lvert f_s\rvert\le TV_{\rm end}$, and
the exact check `LA` gives $TV_{\rm end}\le3e^{-50}$; the code uses `TVEND`, an exact upper bound of
$3e^{-50}$. With $Y=(m\psi,\psi')$ and $\lvert Y\rvert_w=\max(m\lvert\psi\rvert,\lvert\psi'\rvert)$, the
propagator of $\psi''=m^2\psi$ has norm $e^{mt}$ in $\lvert\cdot\rvert_w$ and the perturbation has
norm $\le\lvert f_s\rvert/\Re\lambda$, so by Gronwall the solution after a region of length $L$ differs
from the unperturbed one by at most $e^{mL}\lvert Y\rvert_w(e^\varepsilon-1)$,
$\varepsilon=TV_{\rm end}/\Re\lambda$. The code requires $\varepsilon\le1$ and uses
$e^\varepsilon-1\le2\varepsilon$. On the left end $\lvert Y(\xi_L)\rvert_w=m$, which gives
$\psi(\xi_a)\in e^{mL_1}+\bar D(0,e^{mL_1}(e^\varepsilon-1))$ and $\psi'(\xi_a)\in m\cdot(\text{same set})$;
the disks are replaced by the boxes $[-\rho,\rho]^2\supset\bar D(0,\rho)$. On the right end
$\lvert(\psi'+m\psi)\text{ error}\rvert\le2e^{mL_2}\lvert Y(\xi_b)\rvert_w(e^\varepsilon-1)$.

**Middle region** $[\xi_a,\xi_b]$, where $\chi=1$. Grid: exact dyadic points
$s_i={\rm RN}(\xi_a+(\xi_b-\xi_a)i/360)$, $s_0=\xi_a$, $s_{360}=\xi_b$, strictly increasing (asserted);
order $N=16$. Taylor coefficients come from the exact ODEs $A'=\frac2dA\bar A$, $\bar A'=-A'$ for
$A=H((s-a_0)/d)$, $\bar A=1-A$, and likewise for $B=H(-s/d)$ (with $B'=-\frac2dB\bar B$);
$w=AB$, $f_s=w'$, $(e^{\pm2s})_k=e^{\pm2s_0}(\pm2)^k/k!$, $q=we^{2s}=g'$, $g_k=q_{k-1}/k$,
$\Omega_k=(ge^{-2s})_k+G(e^{-2s})_k$, $R=1/(\lambda+im\Omega)$ by $R_0=1/D_0$,
$R_k=-R_0\sum_{j=1}^kD_jR_{k-j}$, $Q=m^2+imf_sR$, and $(k+1)(k+2)\psi_{k+2}=\sum_{j\le k}Q_j\psi_{k-j}$.
These are evaluated at each step point and, separately, on the ball hull of the whole step, so that the
second set contains the Taylor coefficients at every point of the step.

The values $g(s_i)$: $g(\xi_a)\in[0,e^{2x_a+2\xi_a}/(2/d+2)]$ because
$0\le\bar\omega\le H((s-a_0)/d)\le e^{2(s-a_0)/d}$ on $(-\infty,\xi_a]$; each increment is the Taylor
sum of $q$ plus the Lagrange remainder $q_N(\text{step})h^{N+1}/(N+1)$ (valid since $q$ is real),
intersected with $[0,\infty)$ (since $q\ge0$); on a step, $g\in{\rm hull}(g(s_i),g(s_{i+1}))$ since $g$ is
nondecreasing.

*A priori enclosure over a step.* With $q_{\sup}\ge\sup\lvert Q\rvert$ (over $\Lambda$, $\mathcal G$ and
the step) and $\kappa=\sqrt{\max(q_{\sup},m^2)}$, the system for $(\kappa\psi,\psi')$ has matrix
$\begin{pmatrix}0&\kappa\\Q/\kappa&0\end{pmatrix}$ of $\infty$-norm $\le\kappa$, so
$\max(\kappa\lvert\psi\rvert,\lvert\psi'\rvert)$ grows at most by the factor $e^{\kappa t}$ after a length $t$; with
$M=\max(\kappa\lvert\psi(s_0)\rvert,\lvert\psi'(s_0)\rvert)e^{\kappa h}$,
$\psi(\text{step})\subset\psi(s_0)+\bar D(0,hM)$ and $\psi'(\text{step})\subset\psi'(s_0)+\bar D(0,hq_{\sup}M/\kappa)$.
This step is verified by reading the code (`evans.evans`, the lines computing `qsup`, `kap`, `M`,
`psiI`, `dpsiI`); a black-box test cannot detect its omission, because its effect on the radius is
numerically small.

*Step.* By the integral form of the Taylor remainder (an average of $\psi^{(N)}/N!$ against a
probability density on the step),
$\psi(s_1)\in\sum_{k<N}\psi_k(s_0)h^k+h^N\psi_N(\text{step})$ and
$\psi'(s_1)\in\sum_{1\le k\le N}k\psi_k(s_0)h^{k-1}+(N+1)h^N\psi_{N+1}(\text{step})$; the coefficient boxes over
the step are closed and convex and contain $\psi^{(N)}(\xi)/N!$ for every $\xi$ in the step, so they
contain these averages. The code fails closed (NaN) if $\Re\Lambda>0$, $\varepsilon\le1$ or
$\kappa h\le700$ is not certain, or if anything becomes non-finite.

## 4. The winding count (`winding.certify_cell`)

**Statement (box form).** Let $\Gamma$ be the boundary of a rectangle in $\{\Re\lambda>0\}$ cut into
segments with exact rational endpoints, and $\mathcal C$ a $G$-cell. If each segment's enclosure
$B_i$ (computed on segment box $\times$ cell ball) certainly avoids $(-\infty,0]$ (type P) or
$[0,\infty)$ (type N), then $\mathcal E(\cdot;G)\ne0$ on $\Gamma$ for all $G\in\mathcal C$ and
$${\rm wind}(\mathcal E(\cdot;G)\circ\Gamma,0)=\sum_{\text{type N}}\big(\mathbf 1[\Im\mathcal E(q;G)<0]-\mathbf 1[\Im\mathcal E(p;G)<0]\big).$$
On a type-P segment the principal argument is continuous; on a type-N segment
${\rm Arg}+2\pi\mathbf 1[\Im<0]$ is. The principal parts telescope. Indicators are needed only at
junctions of a type-N and a type-P segment, where the value lies in $B_N\cap B_P$, which avoids
$\mathbb R$; the sign is read from a point enclosure whose imaginary part certainly excludes 0, else
the cell is *ambiguous* (not certified). Segments that cannot be classified are bisected; a cell that
does not converge is *dead* (not certified) and, in the adaptive driver, is halved.

## 5. The two runs and the deductions

- **(N1′)**, `sector3-count`: 25 $G$-cells partitioning $[0,G_{\max}]$, each certified on
  $\partial R_A$, $R_A=[\frac9{200},3]\times[-5,3]$; contour density 20 points per unit length,
  at most 16 bisection rounds and 6000 segments per cell.
- **(N2′)**, `sector3-gap`: 236 $G$-cells partitioning $[0,G_{\max}]$, each with its own rectangle
  $[\frac{211}{2500},x_1]\times[y_0,y_1]$ (exact rationals, in `certificates/sector3_gap_cells.json`);
  density $3/(x_1-\frac{211}{2500})$, at most 10 rounds and 800 segments.

**(N1′) + Lemma A.2 ⇒ (N1)** (Lemma A.6). Lemma A.2: every zero of $\mathcal E_3(\cdot;G)$ with $\Re\lambda>0$ satisfies
$\lvert\lambda+3i\Omega_G(\xi)\rvert\le TV/\ln2$ for some $\xi$, hence $\Re\lambda<TV/\ln2$ and
$-3\Omega_{\max}-TV/\ln2<\Im\lambda<TV/\ln2$; the exact checks `LB1`–`LB5` give
$TV/\ln2<2.886<3$ and $-3\Omega_{\max}-TV/\ln2>-5$ (for $TV=2+2TV_{\rm end}$ and for
$TV=2+6e^{-50}$). So every zero with $\Re\lambda\ge\frac9{200}$ lies in $R_A$, and not on
$\partial R_A$; by the argument principle there is exactly one, counted with multiplicity. Since
$[0,\frac1{50}]\subset[0,G_{\max}]$ (check `D2`), (N1) follows.

**(N1) + (N2′) ⇒ (N2)** (Lemma A.6). For $G$ in a cell of (N2′), the rectangle has winding 1 and no zero on its
boundary, so it contains a zero in its interior, which has $\Re\lambda>\frac{211}{2500}>\frac9{200}$;
by (N1) it is the zero of (N1).

## 6. The exact checks (`constants`)

Each check is done in CPython `Fraction` arithmetic ([exact], the verification) and in Arb ([arb], a
cross-check). The [exact] bounds use only:

1. $e^x\le S_n(x)+\lvert x\rvert^{n+1}/(n+1)!$ for $x<0$ (Lagrange remainder), $S_n(x)=\sum_{k\le n}x^k/k!$;
2. $S_n(x)\le e^x\le S_n(x)+3^{\lceil x\rceil}x^{n+1}/(n+1)!$ for $x\ge0$; reciprocals for $x<0$;
3. $\pi=16\arctan\frac15-4\arctan\frac1{239}$ with alternating partial sums, giving $\pi<\frac{355}{113}$;
4. $\sin u\ge u-\frac{u^3}{6}+\frac{u^5}{120}-\frac{u^7}{5040}$ for $0\le u\le1$, and $u/\sin u$
   increasing on $(0,\pi)$, so $X_m\le u/\sin u$ evaluated at $u=\frac{355}{113}md\le1$;
5. $\ln2\ge\sum_{k\le80}1/(k2^k)$;
6. $H(x)\le e^{2x}$, so $\epsilon_*<e^{-48}<(1000/2718)^{48}$ when $x_a,y_b<-24$ and $e>2.718$.

| id | statement | value (outward-rounded decimal) |
|---|---|---|
| D1 | $\xi_L<\xi_a\le a_0/2\le\xi_b<\xi_R$ | |
| D2 | $d>\frac1{50}$ | $d-\frac1{50}\approx4.16\cdot10^{-19}$ |
| D3 | $x_a<-24$, $y_b<-24$ | $x_a+25\approx3.3\cdot10^{-15}$, $y_b+25\approx5.2\cdot10^{-16}$ |
| D4, D5 | $\pi<\frac{355}{113}$, $e>\frac{2718}{1000}$ | |
| D6 | $0<\frac{355}{113}md\le1$, $m=6,9$ | |
| LA | $TV_{\rm end}\le3e^{-50}$ | ratio $\le0.750000000000005$ |
| LB1–LB5 | $TV/\ln2<2.886$; $-3\Omega_{\max}-TV/\ln2>-5$ | $TV/\ln2\le2.8853900818$; $\Omega_{\max}\le0.6494052616$; $\ge-4.833606$ |
| N3.6 | $\frac12(e^{6a_0}X_6+\epsilon_*)<\frac9{200}$ | $\le0.0449530111$ (margin $\ge4.69\cdot10^{-5}$) |
| N3.9 | $\frac12(e^{9a_0}X_9+\epsilon_*)<\frac9{200}$ | $\le0.0137260837$ |

Informational (not used by any proof): D7 (each datum is the binary64 number nearest to its decimal
expression) and D8 ($\lvert a_0-\log\frac23\rvert<6\cdot10^{-17}$).
