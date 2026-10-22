"""Failure paths: the enclosure routine and the classifier must refuse, never answer wrongly.

- Re lambda <= 0, a box straddling Re lambda = 0, and Re lambda = 10^-30 (so eps > 1) are refused (NaN).
- An oversized step (h = 1/4, N = 6) is refused or gives a useless (wide) box.
- A deliberately broken enclosure routine (Taylor remainder multiplied by 0, h = 2^-8, N = 4) gives a narrow
  box that misses an independent reference value, while the honest code with the same h, N contains it.
- Perturbing a_0 by 10^-3 gives an enclosure disjoint from the true one (the data pin is not vacuous).
"""
from fractions import Fraction as F

from flint import arb, acb

from testlib import Checks
from ringcert import balls, evans as ev, winding as wd
from ringcert.balls import frac_of_exact as frac

REF_AT_1 = 5.337493855096643 + 0.5515669112905699j     # E_3(1; 0), independent double-precision solver


def box_contains_c(B, z, tol=0.0):
    return (float(frac(B.real.lower())) - tol <= z.real <= float(frac(B.real.upper())) + tol and
            float(frac(B.imag.lower())) - tol <= z.imag <= float(frac(B.imag.upper())) + tol)


def cq(a, b):
    return acb(balls.qball(a), balls.qball(b))


def test_refusals():
    c = Checks("failure paths: refusals")
    g = ev.Grid(8, 16)
    NANs = [ev.evans(acb(-0.01, -0.5), arb(0), 3, g), ev.evans(acb(arb(0, 0.01), -0.5), arb(0), 3, g),
            ev.evans(acb(0, -0.5), arb(0), 3, g)]
    for E in NANs:
        c(not E.is_finite() and wd.classify(E) == 0, "Re lam <= 0 (or straddling 0) refused")
    c(not ev.evans(acb(balls.qball(F(1, 10 ** 30)), -0.5), arb(0), 3, g).is_finite(), "eps > 1 refused")
    gbig = ev.Grid(2, 6)
    Eb = ev.evans(cq(F(45, 1000), F(-1, 2)), arb(0), 3, gbig)
    c(wd.classify(Eb) == 0 or not (Eb.real.rad() < 1 and Eb.imag.rad() < 1), "large step refused or wide")
    c.finish()


def test_broken_enclosure_is_caught():
    c = Checks("failure paths: broken enclosure routine caught")
    g = ev.Grid(8, 16)
    gb = ev.Grid(8, 4)
    for i in range(gb.n):
        gb.Omg[i] = g.Omg[i][:4]; gb.OmgI[i] = g.OmgI[i][:4]
    Eh = ev.evans(acb(1, 0), arb(0), 3, gb)                     # honest code, same step and order
    c(box_contains_c(Eh, REF_AT_1, 1e-10), "honest coarse grid still encloses the reference")
    for i in range(gb.n):
        gb.hp[i][gb.N] = arb(0)                                 # remainder terms multiplied by 0
    Ebk = ev.evans(acb(1, 0), arb(0), 3, gb)
    c(not box_contains_c(Ebk, REF_AT_1, 1e-10), f"broken enclosure routine (no remainder) must miss the reference: {Ebk}")
    c.finish()


def test_perturbed_data_rejected():
    c = Checks("failure paths: perturbed a_0")
    g = ev.Grid(8, 16)
    E0 = ev.evans(cq(F(45, 1000), F(-1, 2)), arb(0), 3, g)
    save = ev.A0
    try:
        ev.A0 = ev.A0 + balls.qball(F(1, 1000))
        gp = ev.Grid(8, 16)
        Ep = ev.evans(cq(F(45, 1000), F(-1, 2)), arb(0), 3, gp)
    finally:
        ev.A0 = save
    c(not E0.overlaps(Ep), "a0 + 1e-3 gives a disjoint enclosure")
    c.finish()
