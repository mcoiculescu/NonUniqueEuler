"""Exact conversions (dy, qball), Arb exp against 60-digit Decimal, the constant of Lemma A.1, H and 1 - H."""
import random
from decimal import Decimal, getcontext
from fractions import Fraction as F

from flint import arb, fmpq

from testlib import Checks
from ringcert import balls, evans as ev
from ringcert.balls import frac_of_exact as frac


def lo(x):
    return frac(x.lower())


def hi(x):
    return frac(x.upper())


def contains_q(x, q):
    return lo(x) <= q <= hi(x)


def dec(q):
    return Decimal(q.numerator) / Decimal(q.denominator)


def test_qball_dyadic():
    c = Checks("conversions: qball contains its rational; dyadics exact")
    rng = random.Random(20261014)
    for _ in range(5000):
        q = F(rng.randrange(-10 ** 30, 10 ** 30), rng.randrange(1, 10 ** 30))
        c(contains_q(balls.qball(q), q), f"qball contains {q}")
        d = F(rng.randrange(-2 ** 60, 2 ** 60), 2 ** rng.randrange(0, 70))
        x = balls.qball(d)
        c(x.is_exact() and frac(x) == d, f"dyadic exact {d}")
    c.finish()


def test_exp_and_H():
    c = Checks("conversions: exp, TVEND, H, 1 - H against 60-digit Decimal")
    getcontext().prec = 60
    for xs in ("-50", "-25.5", "-1", "0.36", "2", "50", "-700", "699"):
        e = Decimal(xs).exp()
        X = arb(fmpq(*F(xs).as_integer_ratio())).exp()
        c(dec(lo(X)) <= e <= dec(hi(X)), f"exp({xs})")
    c(dec(hi(ev.TVEND)) >= 3 * Decimal(-50).exp(), "TVEND >= 3 e^-50")
    c(ev.TVEND.is_exact(), "TVEND exact upper endpoint")
    for xs in ("-25", "-24.9999999999999967", "0", "3.7", "25", "-0.5"):
        xd = Decimal(xs)
        Hd = 1 / (1 + (-2 * xd).exp())
        Hbd = 1 / (1 + (2 * xd).exp())
        X = balls.qball(F(xs))
        Hv, Hb = ev._H_pair_iv(X, X)
        c(dec(lo(Hv)) <= Hd <= dec(hi(Hv)), f"H({xs})")
        c(dec(lo(Hb)) <= Hbd <= dec(hi(Hb)), f"1-H({xs})")
        c(Hb.rel_accuracy_bits() > 100, f"1-H relative accuracy at {xs}")
    c.finish()
