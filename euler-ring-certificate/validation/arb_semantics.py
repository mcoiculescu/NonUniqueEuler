"""Probes of the python-flint 0.9.0 semantics that the certified code relies on.

Each probe states the expected behaviour of a predicate, constructor or ball operation used in
``ringcert.evans`` / ``ringcert.winding`` (certain comparisons, radius rounding, union, hull,
nonnegative_part, abs_upper, non-finite boxes, exact dyadics).  Exit status 0 iff all probes behave
as expected."""
import sys
from fractions import Fraction as F

import _common  # noqa: F401
from flint import arb, acb, ctx, fmpz

ctx.prec = 128


def fr(x):
    m, e = x.man_exp()
    return F(int(m)) * F(2) ** int(e)


def lo(x):
    return fr(x.lower())


def hi(x):
    return fr(x.upper())


out = []


def chk(name, cond):
    out.append((name, bool(cond)))
    print(("OK  " if cond else "BAD ") + name)


b = arb(0, 1)
chk("arb(0,1) > 0 is False", (b > 0) is False)
chk("arb(0,1) < 0 is False", (b < 0) is False)
chk("arb(1,1) > 0 is False (touches 0)", (arb(1, 1) > 0) is False)
chk("arb(2,1) > 0 is True", (arb(2, 1) > 0) is True)
chk("arb(-2,1) < 0 is True", (arb(-2, 1) < 0) is True)
chk("arb(1,1) >= 0 is False (the radius is rounded up, so the ball reaches below 0)", (arb(1, 1) >= 0) is False)
chk("1/2 + arb(0,1) <= 1 is False (the ball contains numbers > 1)", (arb(1) / 2 + arb(0, 1) <= 1) is False)
n = arb('nan')
chk("nan > 0 False", (n > 0) is False)
chk("nan < 0 False", (n < 0) is False)
chk("nan <= 1 False", (n <= 1) is False)
chk("not (arb(inf) <= 700)", not (arb('inf') <= 700))
x = arb(0, arb(1, arb(1) / 2))
chk("arb(0, [0.5, 1.5]) has radius >= 1.5 (an upper bound of the radius ball is used)",
    hi(x) >= F(3, 2) and lo(x) <= -F(3, 2))
x = arb(0, arb(3) / 7)
chk("arb(0, 3/7 ball) hi >= 3/7", hi(x) >= F(3, 7))
x = arb(5, arb(3) / 7)
chk("arb(5, 3/7 ball) contains [5-3/7, 5+3/7]", lo(x) <= 5 - F(3, 7) and hi(x) >= 5 + F(3, 7))
y = arb(1) / 3
chk("upper exact and >= 1/3", y.upper().is_exact() and fr(y.upper()) >= F(1, 3))
chk("lower exact and <= 1/3", y.lower().is_exact() and fr(y.lower()) <= F(1, 3))
u = (arb(1) / 3).union(arb(2) / 3)
chk("union contains [1/3, 2/3]", lo(u) <= F(1, 3) and hi(u) >= F(2, 3))
h = (arb(1) / 3).lower().union((arb(2) / 3).upper())
chk("hull contains [1/3, 2/3]", lo(h) <= F(1, 3) and hi(h) >= F(2, 3))
z = arb(0, 1).nonnegative_part()
chk("nonnegative_part(arb(0,1)) contains [0,1], no negatives", lo(z) >= 0 and hi(z) >= 1)
z = arb(-3, 1).nonnegative_part()
chk("nonnegative_part(strictly negative) is 0 (documented)", lo(z) == 0 and hi(z) == 0)
z = arb(2, 1).nonnegative_part()
chk("nonnegative_part(positive ball) unchanged", lo(z) <= 1 and hi(z) >= 3)
mx = arb(1, 1).max(arb(3, 1))
chk("max(arb(1,1), arb(3,1)) contains the max", hi(mx) >= 4 and lo(mx) <= 2)
cbox = acb(arb(3, 1), arb(4, 1))
au = cbox.abs_upper()
chk("acb abs_upper >= sqrt(4^2+5^2)", fr(au) ** 2 >= 41)
chk("abs_upper exact", au.is_exact())
chk("acb nan not finite", not acb(arb('nan'), arb('nan')).is_finite())
chk("acb(inf) not finite", not acb(arb('inf'), 0).is_finite())
chk("acb(1, arb(0,inf)) not finite", not acb(1, arb(0, arb('inf'))).is_finite())
q = 1 / acb(arb(0, 1), arb(0, 1))
chk("1/(box containing 0) not finite", not q.is_finite())
for e in (1, 50, 54, 58, 60):
    t = arb(2) ** (-e)
    chk(f"2^-{e} exact", t.is_exact() and fr(t) == F(1, 2 ** e))
chk("arb(fmpz(7304210039150669)) exact", arb(fmpz(7304210039150669)).is_exact())
chk("arb(2**16) exact", arb(2 ** 16).is_exact())
t = arb(1) / 3
chk("arb/int encloses 1/3", lo(t) <= F(1, 3) <= hi(t))
t = (arb(1) / 7) * 3
chk("arb*int encloses 3/7", lo(t) <= F(3, 7) <= hi(t))
cbox = acb(0, arb(2))
chk("acb(0, x) has imaginary part x", cbox.real == 0 and cbox.imag == 2)
chk("arb(0.1) equals binary64 0.1 (floats are accepted silently, so the code must avoid them)",
    fr(arb(0.1)) == F(0.1))
chk("dyadic 5764607523034235*2^-58 exact", (arb(fmpz(5764607523034235)) * arb(2) ** (-58)).is_exact())
bad = sum(not v for _, v in out)
print(f"arb_semantics: {len(out)} probes, {bad} unexpected")
sys.exit(1 if bad else 0)
