"""Exact data: the pinned dyadics, binary64 rounding, exactness in Arb, the integration grid.

Floats appear here only as independent test references (CPython's own binary64 rounding)."""
import random
from fractions import Fraction as F

from testlib import Checks
from ringcert import data, evans as ev
from ringcert.balls import frac_of_exact as frac


def test_pinned_data():
    c = Checks("data: pinned values")
    A0f = float.fromhex("-0x1.9f323ecbf984dp-2")
    c(data.A0_Q == F(A0f), "a0 equals the hex literal -0x1.9f323ecbf984dp-2")
    c(data.A0_Q == F(-7304210039150669, 2 ** 54), "a0 rational")
    c(data.SL_Q == F(A0f - 0.6), "sL = RN(a0 - 0.6) (binary64 subtraction)")
    c(data.SA_Q == F(A0f - 0.5), "sa = RN(a0 - 0.5)")
    c(data.SB_Q == F(0.5) and data.SR_Q == F(0.6), "sb, sR")
    c(data.DD_Q == F(0.02) and data.DD_Q > F(1, 50), "d = RN(0.02) > 1/50")
    c(data.SL_Q == F(float.fromhex("-0x1.0166294c97fadp+0")), "sL hex literal")
    c(data.SA_Q == F(float.fromhex("-0x1.cf991f65fcc26p-1")), "sa hex literal")
    for q in (data.A0_Q, data.DD_Q, data.SL_Q, data.SA_Q, data.SB_Q, data.SR_Q):
        c(q.denominator & (q.denominator - 1) == 0, f"{q} is dyadic")
    c(data.G_MAX_Q == data.DD_Q, "G_MAX = d")
    c(all(h for _, _, h in data.rounding_provenance()), "each datum is RN of its decimal expression")
    c.finish()


def test_rn_binary64():
    c = Checks("data: rn_binary64 against CPython float rounding")
    rng = random.Random(20261014)
    for _ in range(20000):
        num = rng.randrange(-10 ** rng.randrange(1, 40), 10 ** rng.randrange(1, 40))
        den = rng.randrange(1, 10 ** rng.randrange(1, 40))
        q = F(num, den)
        if q == 0 or not (2.0 ** -1021 < abs(q) < 2.0 ** 1020):
            continue
        c(data.rn_binary64(q) == F(float(q)), f"rn_binary64 {q}")
    # ties to even: 1 + 2^-53 -> 1, 1 + 3*2^-53 -> 1 + 2^-51
    c(data.rn_binary64(1 + F(1, 2 ** 53)) == 1, "tie to even down")
    c(data.rn_binary64(1 + F(3, 2 ** 53)) == 1 + F(1, 2 ** 51), "tie to even up")
    c.finish()


def test_arb_data_and_grid():
    c = Checks("data: exact in Arb; grid")
    for X in (ev.A0, ev.DD, ev.SL, ev.SA, ev.SB, ev.SR):
        c(X.is_exact(), "pinned data exact in Arb")
    c(frac(ev.A0) == data.A0_Q and frac(ev.SL) == data.SL_Q and frac(ev.DD) == data.DD_Q, "Arb data = rationals")
    g = ev.Grid(8, 16)
    c(g.n == 360 and g.ptsQ[0] == data.SA_Q and g.ptsQ[-1] == data.SB_Q, "grid ends, n = 360")
    c(all(g.ptsQ[i] < g.ptsQ[i + 1] for i in range(g.n)), "grid increasing")
    c(all(frac(g.s[i]) == g.ptsQ[i] for i in range(g.n + 1)), "grid points exact")
    c(all(h.is_exact() and frac(h) == g.ptsQ[i + 1] - g.ptsQ[i] for i, h in enumerate(g.h)), "steps exact")
    c.finish()
