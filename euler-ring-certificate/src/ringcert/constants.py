"""Exact rational checks: (N3), the constants of Lemmas A.1 and A.2 of the paper, and the hypotheses
on the data.

Every check is done twice.
  [exact]  CPython int / fractions.Fraction only.  Transcendental numbers are bounded by explicit
       rational bounds whose validity is elementary (listed below).  This is the verification.
  [arb]  FLINT/Arb balls (exp, sin, pi, log 2 from Arb), as an independent cross-check.
No Python float enters any bound.

Notation: x_a = (s_a - a_0)/d, y_b = -s_b/d, beta_r = e^{a_0}, X_m = pi m d / sin(pi m d),
eps_* = max(H(x_a), H(y_b)) with H(x) = 1/(1 + e^{-2x}), TV_end = (9/4) e^{2 max(x_a, y_b)},
Omega_max = 1/2 + G_MAX e^{-2 s_L}.

Elementary bounds used by [exact] (each is a lemma with a one-line proof):
  (b1) for x < 0 and n >= 0:  e^x <= S_n(x) + |x|^{n+1}/(n+1)!,  S_n(x) = sum_{k<=n} x^k/k!
       (Taylor with Lagrange remainder e^xi x^{n+1}/(n+1)!, 0 < e^xi < 1);
  (b2) for x >= 0:  S_n(x) <= e^x <= S_n(x) + 3^{ceil(x)} x^{n+1}/(n+1)!   (e^xi <= e^x < 3^{ceil x});
       for x < 0 the bounds of e^{-x} are inverted;
  (b3) Machin: pi = 16 arctan(1/5) - 4 arctan(1/239); the arctan series alternates with decreasing
       terms, so partial sums bracket it;
  (b4) for 0 <= u <= 1:  sin u >= u - u^3/6 + u^5/120 - u^7/5040 (alternating, decreasing terms), and
       u / sin u is increasing on (0, pi), so X_m = f(pi m d) <= f(u) <= u / (lower bound of sin u) with
       u = (355/113) m d, provided pi < 355/113 and u <= 1;
  (b5) ln 2 = sum_{k>=1} 1/(k 2^k) >= sum_{k<=80} 1/(k 2^k);
  (b6) H(x) <= e^{2x}, hence eps_* <= e^{2 max(x_a, y_b)} < e^{-48} < (1000/2718)^48 when
       x_a, y_b < -24 and e > 2718/1000.
"""
import math
from fractions import Fraction as F
from flint import arb

from .data import (A0_Q as A0, DD_Q as Dd, SL_Q as SL, SA_Q as SA, SB_Q as SB, SR_Q as SR, G_MAX_Q as G_MAX,
                   dec_up, dec_down, sci, rounding_provenance)
from . import balls


# ------------------------------------------------------------------ [exact] rational bounds
def exp_upper_neg(x, n=60):
    """(b1): an upper bound of e^x for x < 0."""
    assert x < 0
    return sum(x ** k / math.factorial(k) for k in range(n + 1)) + abs(x) ** (n + 1) / math.factorial(n + 1)


def exp_lower_pos(x, n=30):
    """(b2): a lower bound of e^x for x > 0."""
    assert x > 0
    return sum(x ** k / math.factorial(k) for k in range(n + 1))


def exp_lo(x, n=250):
    """(b2): a lower bound of e^x for every rational x."""
    if x >= 0:
        return sum(x ** k / math.factorial(k) for k in range(n + 1))
    return 1 / exp_up(-x, n)


def exp_up(x, n=250):
    """(b2): an upper bound of e^x for every rational x."""
    if x >= 0:
        c = math.ceil(x)
        return sum(x ** k / math.factorial(k) for k in range(n + 1)) + 3 ** c * x ** (n + 1) / math.factorial(n + 1)
    return 1 / exp_lo(-x, n)


def atan_inv(q, n):
    """(b3): a pair (lo, hi) with lo <= arctan(1/q) <= hi, from n terms of the alternating series."""
    s = F(0)
    for k in range(n):
        s += F((-1) ** k, (2 * k + 1) * q ** (2 * k + 1))
    nxt = F(1, (2 * n + 1) * q ** (2 * n + 1))
    return (s, s + nxt) if n % 2 == 0 else (s - nxt, s)


def sector_bound(m, beta_up, eps_chi_up):
    """(b4): an upper bound of (1/2)(beta_r^m X_m + eps_*), given upper bounds of beta_r and eps_*.
    Requires 0 < u = (355/113) m d <= 1 (asserted) and pi < 355/113 (checked separately)."""
    u = F(355, 113) * m * Dd
    assert 0 < u <= 1
    sin_lo = u - u ** 3 / 6 + u ** 5 / 120 - u ** 7 / 5040
    return (beta_up ** m * (u / sin_lo) + eps_chi_up) / 2


def run_checks():
    """Run all checks.  Returns a list of dicts (id, group, method ("exact" or "arb"), statement, passed, value)."""
    out = []

    def rep(cid, group, method, statement, cond, value=""):
        out.append(dict(id=cid, group=group, method=method, statement=statement, passed=bool(cond), value=value))

    # ---- [exact] data hypotheses
    a, b = atan_inv(5, 30), atan_inv(239, 30)
    PI_HI = 16 * a[1] - 4 * b[0]
    rep("D1", "data", "exact", "s_L < s_a <= a_0/2 <= s_b < s_R", SL < SA <= A0 / 2 <= SB < SR)
    rep("D2", "data", "exact", "d > 1/50 (so [0, 1/50] is inside the certified range [0, G_MAX], G_MAX = d)",
        Dd > F(1, 50), f"d - 1/50 = {sci(Dd - F(1, 50))}")
    xa = (SA - A0) / Dd
    yb = -SB / Dd
    rep("D3", "data", "exact", "x_a < -24 and y_b < -24", xa < -24 and yb < -24,
        f"x_a + 25 = {sci(xa + 25)}, y_b + 25 = {sci(yb + 25)}")
    rep("D4", "data", "exact", "pi < 355/113 (Machin bracket)", PI_HI < F(355, 113))
    rep("D5", "data", "exact", "e > 2718/1000", exp_lower_pos(F(1)) > F(2718, 1000))
    for m in (6, 9):
        u = F(355, 113) * m * Dd
        rep(f"D6.{m}", "data", "exact", f"0 < (355/113)*{m}*d <= 1", 0 < u <= 1, f"u = {dec_up(u, 6)}")
    for name, expr, holds in rounding_provenance():
        rep(f"D7.{name}", "data (informational)", "exact", f"{name} = {expr} (nearest binary64)", holds)

    # ---- [exact] Lemma A.1 (the end regions)
    xm = max(xa, yb)
    tv_end = F(9, 4) * exp_up(2 * xm)
    e50_lo = exp_lo(F(-50))
    rep("LA", "Lemma A.1", "exact", "TV_end = (9/4) e^{2 max(x_a, y_b)} <= 3 e^{-50}", tv_end <= 3 * e50_lo,
        f"TV_end / (3 e^-50) <= {dec_up(tv_end / (3 * e50_lo), 15)}")

    # ---- [exact] Lemma A.2 (a priori location of the zeros; two forms of TV, the second dominates the
    #      first when LA holds)
    ln2_lo = sum(F(1, k * 2 ** k) for k in range(1, 81))
    Om = F(1, 2) + G_MAX * exp_up(-2 * SL)
    R1 = (2 + 2 * tv_end) / ln2_lo
    R2 = (2 + 6 * exp_up(F(-50))) / ln2_lo
    rep("LB1", "Lemma A.2", "exact", "TV/ln2 < 2.886 with TV = 2 + 2 TV_end", R1 < F(2886, 1000), f"TV/ln2 <= {dec_up(R1, 10)}")
    rep("LB2", "Lemma A.2", "exact", "-3 Omega_max - TV/ln2 > -5 with TV = 2 + 2 TV_end", -3 * Om - R1 > -5,
        f"Omega_max <= {dec_up(Om, 10)}; -3 Omega_max - TV/ln2 >= {dec_down(-3 * Om - R1, 6)}")
    rep("LB3", "Lemma A.2", "exact", "TV/ln2 < 2.886 with TV = 2 + 6 e^{-50}", R2 < F(2886, 1000), f"TV/ln2 <= {dec_up(R2, 10)}")
    rep("LB4", "Lemma A.2", "exact", "-3 Omega_max - TV/ln2 > -5 with TV = 2 + 6 e^{-50}", -3 * Om - R2 > -5,
        f"-3 Omega_max - TV/ln2 >= {dec_down(-3 * Om - R2, 6)}")
    rep("LB5", "Lemma A.2", "exact", "TV/ln2 < 3 (so every zero with Re lambda > 0 has Re lambda < 3 and Im lambda < 3)",
        R2 < 3)

    # ---- [exact] (N3)
    beta_up = exp_upper_neg(A0)
    eps_chi_up = F(1000, 2718) ** 48
    bounds = {}
    for m in (6, 9):
        bm = sector_bound(m, beta_up, eps_chi_up)
        bounds[m] = bm
        rep(f"N3.{m}", "(N3)", "exact", f"(1/2)(e^{{{m} a_0}} X_{m} + eps_*) < 9/200, i.e. e^{{{m} a_0}} X_{m} + eps_* < 9/100",
            bm < F(9, 200), f"(1/2)(...) <= {dec_up(bm, 10)}; margin >= {dec_down(F(9, 200) - bm, 10)}")

    # ---- [arb] Arb cross-checks
    A0b, Ddb, SLb, SAb, SBb = (balls.dy(v) for v in (A0, Dd, SL, SA, SB))
    Gm = balls.qball(G_MAX)
    pi = arb.pi()

    def Hb(x):
        return 1 / (1 + (-2 * x).exp())

    def bound_arb(m):
        u = pi * m * Ddb
        X = u / u.sin()
        eps = Hb((SAb - A0b) / Ddb).max(Hb(-SBb / Ddb))
        return (A0b.exp() ** m * X + eps) / 2

    for m in (6, 9):
        Bm = bound_arb(m)
        rep(f"N3.{m}.A", "(N3)", "arb", f"(1/2)(e^{{{m} a_0}} X_{m} + eps_*) < 9/200", Bm < balls.qball(F(9, 200)),
            f"enclosure {Bm.str(12, radius=True)}")
        rep(f"N3.{m}.AQ", "(N3)", "arb", f"[arb] enclosure <= [exact] bound (m = {m})", Bm <= balls.qball(bounds[m]))
    xmb = ((SAb - A0b) / Ddb).max(-SBb / Ddb)
    tvb = arb(9) / 4 * (2 * xmb).exp()
    rep("LA.A", "Lemma A.1", "arb", "(9/4) e^{2 max(x_a, y_b)} <= 3 e^{-50}", tvb < 3 * arb(-50).exp(),
        f"ratio {(tvb / (3 * arb(-50).exp())).str(16)}")
    Rb = (2 + 2 * tvb) / arb(2).log()
    Omb = arb(1) / 2 + Gm * (-2 * SLb).exp()
    rep("LB1.A", "Lemma A.2", "arb", "TV/ln2 < 2.886", Rb < balls.qball(F(2886, 1000)), f"TV/ln2 in {Rb.str(12, radius=True)}")
    rep("LB2.A", "Lemma A.2", "arb", "-3 Omega_max - TV/ln2 > -5", -3 * Omb - Rb > -5, f"Omega_max in {Omb.str(12, radius=True)}")
    dist = (A0b - (arb(2) / 3).log()).abs_upper()
    rep("D8.A", "data (informational)", "arb", "|a_0 - log(2/3)| < 6e-17", dist < balls.qball(F(6, 10 ** 17)),
        f"|a_0 - log(2/3)| <= {dist.str(3)}")
    return out


def summary(checks):
    """Exact-rational summary of the load-bearing [exact] bounds (recomputed; strings only)."""
    xa = (SA - A0) / Dd
    yb = -SB / Dd
    beta_up = exp_upper_neg(A0)
    eps_chi_up = F(1000, 2718) ** 48
    b6 = sector_bound(6, beta_up, eps_chi_up)
    b9 = sector_bound(9, beta_up, eps_chi_up)
    return {
        "x_a": str(xa), "y_b": str(yb),
        "N3.6_upper_bound_decimal": dec_up(b6, 10), "N3.6_threshold": "9/200",
        "N3.9_upper_bound_decimal": dec_up(b9, 10), "N3.9_threshold": "9/200",
        "all_pass": all(c["passed"] for c in checks),
    }
