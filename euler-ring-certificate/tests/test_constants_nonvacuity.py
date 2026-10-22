"""The exact checks are not vacuous: moving a threshold across the computed bound flips the result,
and the rational bounds bracket the Arb enclosures of the same quantities."""
from fractions import Fraction as F

from flint import arb

from testlib import Checks
from ringcert import balls, constants as K
from ringcert.data import A0_Q, DD_Q, SA_Q, SB_Q


def test_thresholds_are_tight():
    c = Checks("constants: non-vacuity")
    checks = K.run_checks()
    c(all(x["passed"] for x in checks), "all constants checks pass")
    beta_up = K.exp_upper_neg(A0_Q)
    eps_up = F(1000, 2718) ** 48
    b6 = K.sector_bound(6, beta_up, eps_up)
    b9 = K.sector_bound(9, beta_up, eps_up)
    c(b6 < F(9, 200) and not (b6 < F(4495, 100000)), "sector 6: passes 9/200, fails 0.04495")
    c(b9 < F(9, 200) and not (b9 < F(137, 10000)), "sector 9: passes 9/200, fails 0.0137")
    xm = max((SA_Q - A0_Q) / DD_Q, -SB_Q / DD_Q)
    ratio = F(9, 4) * K.exp_up(2 * xm) / (3 * K.exp_lo(F(-50)))
    c(ratio <= 1 and not (ratio <= F(7499, 10000)), "Lemma A.1: ratio <= 1, but not <= 0.7499")
    # the [exact] bounds are upper bounds of the true values (bracket the Arb enclosures)
    pi = arb.pi()
    for m, b in ((6, b6), (9, b9)):
        u = pi * m * balls.dy(DD_Q)
        X = u / u.sin()
        H = lambda x: 1 / (1 + (-2 * x).exp())      # noqa: E731
        A0, D, SA, SB = (balls.dy(v) for v in (A0_Q, DD_Q, SA_Q, SB_Q))
        true = (A0.exp() ** m * X + H((SA - A0) / D).max(H(-SB / D))) / 2
        c(true < balls.qball(b), f"sector {m}: Arb enclosure of the true value lies below the [exact] bound")
        c(true > balls.qball(b - F(1, 10 ** 8)), f"sector {m}: [exact] bound is within 1e-8 of the true value")
    # the exp bounds bracket e^x
    try:
        balls.set_prec(400)      # Arb ball of e^x of radius ~1e-120: must meet the rational bracket [lo, hi]
        for x in (F(-50), F(-1, 3), F(1, 7), F(5, 2)):
            lo, hi = K.exp_lo(x), K.exp_up(x)
            e = balls.qball(x).exp()
            c(lo <= hi and balls.lower_q(e) <= hi and lo <= balls.upper_q(e), f"exp bounds bracket e^{x}")
            c(balls.upper_q(e) - balls.lower_q(e) < F(1, 10 ** 100), f"Arb ball of e^{x} narrow at 400 bits")
    finally:
        balls.set_prec()
    a, b = K.atan_inv(5, 30), K.atan_inv(239, 30)
    try:
        balls.set_prec(400)      # the bracket (width ~1e-43) is narrower than pi's ball at 128 bits
        c(balls.qball(16 * a[0] - 4 * b[1]) < arb.pi() < balls.qball(16 * a[1] - 4 * b[0]), "Machin bracket contains pi")
    finally:
        balls.set_prec()
    c.finish()
