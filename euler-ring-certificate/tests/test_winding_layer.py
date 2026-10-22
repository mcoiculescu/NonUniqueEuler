"""The winding layer: segment boxes, the classifier on hand-made boxes (including NaN and inf),
the contour points, and the precision independence of a point enclosure."""
import random
from fractions import Fraction as F

from flint import arb, acb

from testlib import Checks
from ringcert import balls, evans as ev, winding as wd
from ringcert.balls import frac_of_exact as frac


def contains_q(x, q):
    return frac(x.lower()) <= q <= frac(x.upper())


def test_segment_boxes():
    c = Checks("winding layer: segment boxes contain their segments")
    rng = random.Random(20261014)
    for _ in range(2000):
        p = (F(rng.randrange(-10 ** 6, 10 ** 6), rng.randrange(1, 10 ** 6)), F(rng.randrange(-10 ** 6, 10 ** 6), 10 ** 6))
        q = (p[0] + F(rng.randrange(-10 ** 3, 10 ** 3), 10 ** 6), p[1])
        B = wd.seg_box(p, q)
        mid = ((p[0] + q[0]) / 2, (p[1] + q[1]) / 2)
        for z in (p, q, mid):
            c(contains_q(B.real, z[0]) and contains_q(B.imag, z[1]), "segment box contains segment points")
    c.finish()


def test_classify():
    c = Checks("winding layer: classify")
    cases = [(acb(arb(-1, 0.5), arb(0, 0.1)), 2), (acb(arb(1, 0.5), arb(0, 0.1)), 1), (acb(arb(0, 0.1), arb(0, 0.1)), 0),
             (acb(arb(-0.05, 0.1), arb(0, 0.01)), 0), (acb(arb(-1, 0.5), arb(0.2, 0.1)), 1), (acb(arb(-1, 0.5), arb(-0.2, 0.1)), 1),
             (acb(arb(-1, 0.5), arb(0.05, 0.1)), 2), (acb(arb(1e-30, 1e-31), arb(0, 1)), 1), (acb(arb(-1e-30, 1e-31), arb(0, 1)), 2),
             (acb(arb(0, 1e-31), arb(1e-30, 1e-31)), 1), (acb(arb("nan"), arb(0)), 0), (acb(arb(1), arb("nan")), 0),
             (acb(arb("inf"), arb(1)), 0)]
    for B, t in cases:
        c(wd.classify(B) == t, f"classify {B} expected {t} got {wd.classify(B)}")
    c.finish()


def test_rect_points():
    c = Checks("winding layer: rect_points")
    pts = wd.rect_points(F(9, 200), F(3), F(-5), F(3), F(20))
    c(pts[0] == pts[-1] == (F(9, 200), F(-5)), "rect closed")
    c(all(p[0] in (F(9, 200), F(3)) or p[1] in (F(-5), F(3)) for p in pts), "rect points on boundary")
    c(len(pts) - 1 == 60 + 160 + 60 + 160, f"rect point count {len(pts)-1}")  # ceil(2.955*20) = 60
    c.finish()


def test_precision():
    c = Checks("precision: 64-bit and 128-bit point enclosures")
    rads = {}
    try:
        for p in (64, 128):
            balls.set_prec(p)
            gg = ev.Grid(8, 16)
            E = ev.evans(acb(balls.qball(F(12, 100)), balls.qball(F(-417, 1000))), arb(0), 3, gg)
            rads[p] = (float(E.real.rad()), float(E.imag.rad()), E)
    finally:
        balls.set_prec()
    c(rads[64][2].overlaps(rads[128][2]), "64/128-bit enclosures overlap")
    c(abs(rads[64][0] / rads[128][0] - 1) < 1e-3, "point radius is method-dominated, not rounding-dominated")
    c.finish()
