"""Known answers for the enclosure of the Evans function.

(a) No ring (f_s = 0): psi = e^{m(s - s_L)}, so E_m = 2m exactly; the enclosure must contain 6 (m = 3).
(b) Constant coefficient on the middle region (f_s = 7 there, Omega = 0, so Q = m^2 + 7im/lambda):
    the closed-form cosh/sinh propagator, evaluated in Arb, must lie in the enclosure, and a wrong
    constant (7.001) must give a value disjoint from it (non-vacuity).
(c) Agreement (not containment) with an independent double-precision solver (scipy DOP853, rtol
    1e-12; fixture ``dop853_reference.json``; chi = 1 there, which changes E by O(e^-50)): every
    reference value lies within the enclosure enlarged by 1e-10.  The enclosure radius is about
    4.5e-11, so this is an agreement test; containment is tested in ``test_reference_rk4.py``.
"""
import cmath
import json
import math
from fractions import Fraction as F

from flint import arb, acb

from testlib import Checks, fixture
from ringcert import balls, evans as ev
from ringcert.balls import frac_of_exact as frac

M = 3


def cq(a, b):
    return acb(balls.qball(a), balls.qball(b))


def box_contains_c(B, z, tol=0.0):
    """float check: complex z within the box B, with slack tol (test only)."""
    return (float(frac(B.real.lower())) - tol <= z.real <= float(frac(B.real.upper())) + tol and
            float(frac(B.imag.lower())) - tol <= z.imag <= float(frac(B.imag.upper())) + tol)


def test_no_ring():
    c = Checks("known answer: no ring, E = 2m")
    Z = arb(0)
    gz = ev.Grid(8, 16)
    for i in range(gz.n):
        gz.pt[i]["fs"] = [Z] * len(gz.pt[i]["fs"])
        gz.iv[i]["fs"] = [Z] * len(gz.iv[i]["fs"])
    for lam in (cq(F(1, 20), F(-3, 10)), acb(1, 1), acb(arb(0.5, 0.01), arb(0, 0.01))):
        Ez = ev.evans(lam, arb(0).union(balls.qball(F(1, 50))), M, gz)
        c(Ez.contains(acb(6)), f"no ring: E = 2m contained ({Ez})")
        c(Ez.real.rad() < 1e-9 and Ez.imag.rad() < 1e-9, f"no ring: radius small ({Ez})")
    c.finish()


def test_constant_coefficient():
    c = Checks("known answer: constant coefficient closed form")
    Z = arb(0)
    c0 = arb(7)
    gc = ev.Grid(8, 16)
    for i in range(gc.n):
        for dat in (gc.pt[i], gc.iv[i]):
            dat["fs"] = [c0] + [Z] * (len(dat["fs"]) - 1)
            dat["em2"] = [Z] * len(dat["em2"])
        gc.Omg[i] = [Z] * len(gc.Omg[i]); gc.OmgI[i] = [Z] * len(gc.OmgI[i])
    m = M
    L1 = ev.SA - ev.SL; L2 = ev.SR - ev.SB; Lm = ev.SB - ev.SA; Lt = ev.SR - ev.SL
    for lamq in ((F(1, 20), F(-3, 10)), (F(1, 5), F(1, 10)), (F(3, 2), F(-2))):
        lam = acb(balls.qball(lamq[0]), balls.qball(lamq[1]))
        Ec = ev.evans(lam, arb(0), m, gc)
        q = m * m + acb(0, m) * c0 / lam
        k = q.sqrt()
        p0 = (m * L1).exp(); dp0 = m * p0
        p1 = (k * Lm).cosh() * p0 + (k * Lm).sinh() / k * dp0
        dp1 = k * (k * Lm).sinh() * p0 + (k * Lm).cosh() * dp0
        Eref = (dp1 + m * p1) * (m * L2).exp() * (-m * Lt).exp()
        c(Ec.contains(Eref), f"const-coef lam={lamq}: closed form (Arb) inside enclosure")
        lf = complex(float(lamq[0]), float(lamq[1]))
        kf = cmath.sqrt(m * m + 1j * m * 7.0 / lf)
        L1f, L2f, Lmf, Ltf = (float(frac(x)) for x in (L1, L2, Lm, Lt))
        p0f = math.exp(m * L1f); dp0f = m * p0f
        p1f = cmath.cosh(kf * Lmf) * p0f + cmath.sinh(kf * Lmf) / kf * dp0f
        dp1f = kf * cmath.sinh(kf * Lmf) * p0f + cmath.cosh(kf * Lmf) * dp0f
        Ereff = (dp1f + m * p1f) * math.exp(m * L2f) * math.exp(-m * Ltf)
        c(box_contains_c(Ec, Ereff, 1e-12 * abs(Ereff)), f"const-coef lam={lamq}: float closed form (agreement)")
        qw = m * m + acb(0, m) * balls.qball(F(7001, 1000)) / lam
        kw = qw.sqrt()
        p1w = (kw * Lm).cosh() * p0 + (kw * Lm).sinh() / kw * dp0
        dp1w = kw * (kw * Lm).sinh() * p0 + (kw * Lm).cosh() * dp0
        Ew = (dp1w + m * p1w) * (m * L2).exp() * (-m * Lt).exp()
        c(not Ec.overlaps(Ew), f"const-coef lam={lamq}: wrong closed form (c0=7.001) excluded")
    c.finish()


def test_float_reference_agreement():
    c = Checks("agreement with an independent double-precision solver")
    g = ev.Grid(8, 16)
    with open(fixture("dop853_reference.json")) as f:
        refs = json.load(f)
    for r in refs:
        lam = acb(balls.qball(F(r["lam"][0])), balls.qball(F(r["lam"][1])))
        E = ev.evans(lam, balls.qball(F(r["G"])), 3, g)
        z = complex(*r["E"])
        c(box_contains_c(E, z, 1e-10), f"DOP853 lam={r['lam']} G={r['G']}: {E} vs {z}")
    # two further reference values from an independent double-precision ODE solver
    for (lr, li), val in (((F(45, 1000), F(-1, 2)), -0.690275888915 - 0.294713146953j),
                          ((F(1), F(0)), 5.337493855096 + 0.551566911289j)):
        E = ev.evans(acb(balls.qball(lr), balls.qball(li)), arb(0), 3, g)
        c(box_contains_c(E, val, 2e-12), f"reference value at lam=({lr},{li})")
    c.finish()
