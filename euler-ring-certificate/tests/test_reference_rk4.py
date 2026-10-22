"""Containment against an independent high-accuracy reference, and a mutation control.

Reference (not rigorous; written independently of ``ringcert.evans``): classical RK4 for
    psi' = dpsi,  dpsi' = Q psi,  g' = wbar e^{2s}  on [s_L, s_R],
    Q = m^2 + i m f_s / (lambda + i m (g + G) e^{-2s}),  wbar = H((s - a_0)/d) H(-s/d),
    f_s = (2/d) H_A H_B (H_B - H_A),  psi(s_L) = 1, psi'(s_L) = m, g(s_L) = 0,
with chi = 1 on [s_L, s_R] (this changes E by O(e^-50), far below every radius here).  Uniform steps
n = 2^11 .. 2^15 at 192 bits, then Richardson extrapolation in h^4, h^5, h^6; the reference error is
estimated from the last extrapolants.

Test: the reference lies inside the enclosure, with margin larger than its estimated error, on the
production grid (h = 2^-8, N = 16) and on coarse grids where the Taylor remainder and the a priori
enclosure dominate the radius.  Control: a copy of ``evans`` with the Taylor remainder dropped (M1)
must miss the reference on some coarse grid.  (A copy with the a priori enclosure not inflated is
not detectable by such a black-box test; that step is verified by reading ``evans``.)
"""
from fractions import Fraction as F

from flint import arb, acb, ctx

from testlib import Checks
from ringcert import balls, data, evans as ev
from ringcert.balls import frac_of_exact as fr


def qb(q):
    q = F(q)
    return arb(q.numerator) / arb(q.denominator)


def coeff_tables(n):
    ctx.prec = 192
    a0, d = qb(data.A0_Q), qb(data.DD_Q)
    sL, sR = qb(data.SL_Q), qb(data.SR_Q)
    h = (sR - sL) / n
    tab = []
    for j in range(2 * n + 1):
        s = sL + h * j / 2
        HA = 1 / (1 + (-2 * (s - a0) / d).exp())
        HB = 1 / (1 + (2 * s / d).exp())
        fs = 2 / d * HA * HB * (HB - HA)
        tab.append((fs, HA * HB * (2 * s).exp(), (-2 * s).exp()))
    return h, tab


def ref_E(lam, G, m, h, tab):
    ctx.prec = 192
    n = (len(tab) - 1) // 2
    im = acb(0, m)

    def f(k, psi, dpsi, g):
        fs, q, em2 = tab[k]
        Q = m * m + im * fs / (lam + im * ((g + G) * em2))
        return dpsi, Q * psi, q
    psi, dpsi, g = acb(1), acb(m), arb(0)
    for i in range(n):
        k0, k1, k2 = 2 * i, 2 * i + 1, 2 * i + 2
        a1 = f(k0, psi, dpsi, g)
        a2 = f(k1, psi + h / 2 * a1[0], dpsi + h / 2 * a1[1], g + h / 2 * a1[2])
        a3 = f(k1, psi + h / 2 * a2[0], dpsi + h / 2 * a2[1], g + h / 2 * a2[2])
        a4 = f(k2, psi + h * a3[0], dpsi + h * a3[1], g + h * a3[2])
        psi = psi + h / 6 * (a1[0] + 2 * a2[0] + 2 * a3[0] + a4[0])
        dpsi = dpsi + h / 6 * (a1[1] + 2 * a2[1] + 2 * a3[1] + a4[1])
        g = g + h / 6 * (a1[2] + 2 * a2[2] + 2 * a3[2] + a4[2])
    sL, sR = qb(data.SL_Q), qb(data.SR_Q)
    return ((dpsi + m * psi) * (-m * (sR - sL)).exp()).mid()


def richardson(vals):
    T = [vals]
    for p in (4, 5, 6):
        prev = T[-1]
        f = 2 ** p
        T.append([(f * prev[i + 1] - prev[i]) / (f - 1) for i in range(len(prev) - 1)])
    return T


def evans_without_remainder(lam, G, m, grid):
    """Mutation M1: ``evans`` with the integral-form Taylor remainder dropped (unsound on purpose)."""
    N = grid.N
    relo = lam.real.lower()
    L1 = ev.SA - ev.SL
    eps = (ev.TVEND / relo).upper()
    eg = (2 * eps).upper()
    emL1 = (m * L1).exp()
    psi = acb(emL1) + balls.box(emL1.upper() * eg)
    dpsi = psi * m
    for i in range(grid.n):
        Q = ev._step_coeffs(lam, G, m, grid.Omg[i], grid.pt[i]["em2"], grid.pt[i]["fs"], N)
        hp, khp = grid.hp[i], grid.khp[i]
        pc = ev._psi_coeffs(Q, psi, dpsi, N)
        new_psi = pc[0]
        for k in range(1, N):
            new_psi = new_psi + pc[k] * hp[k]
        new_dpsi = pc[1]
        for k in range(2, N + 1):
            new_dpsi = new_dpsi + pc[k] * khp[k]
        psi, dpsi = new_psi, new_dpsi
    L2 = ev.SR - ev.SB
    emL2 = (m * L2).exp()
    Wv = dpsi + psi * m
    Wn = (m * psi.abs_upper()).upper().max(dpsi.abs_upper())
    Eend = Wv * emL2 + balls.box(2 * emL2.upper() * Wn * eg)
    return Eend * (-m * (ev.SR - ev.SL)).exp()


def margin(B, z):
    """min over components of the distance from z to the nearer box edge; negative if outside."""
    zr, zi = fr(z.real), fr(z.imag)
    mr = min(zr - fr(B.real.lower()), fr(B.real.upper()) - zr)
    mi = min(zi - fr(B.imag.lower()), fr(B.imag.upper()) - zi)
    return min(mr, mi)


def test_reference_containment():
    c = Checks("independent RK4 reference inside the enclosure; mutation M1 caught")
    m = 3
    pts = [((F("0.1220448"), F("-0.4171233")), F(0)), ((F("0.0844781"), F("-0.5144718")), F(1, 50)),
           ((F(9, 200), F(-1, 2)), F(0)), ((F(9, 200), F(-1, 2)), F(1, 50)), ((F(9, 200), F(0)), F(1, 100)),
           ((F(9, 200), F(-9, 10)), F(1, 50)), ((F(1), F(0)), F(0)), ((F("2.9"), F("-4.9")), F(1, 50)),
           ((F("0.3"), F("0.7")), F(1, 200))]
    levels = [2 ** 11, 2 ** 12, 2 ** 13, 2 ** 14, 2 ** 15]
    tabs = {n: coeff_tables(n) for n in levels}
    balls.set_prec()
    grids = {k: ev.Grid(*k) for k in ((8, 16), (8, 8), (8, 6), (9, 5), (7, 10), (10, 4))}
    caught = False
    try:
        for (lr, li), G in pts:
            lamr = acb(qb(lr), qb(li))
            vals = [ref_E(lamr, qb(G), m, *tabs[n]) for n in levels]
            T = richardson(vals)
            d1, d2 = (T[-1][-1] - T[-2][-1]).mid(), (T[-2][-1] - T[-3][-1]).mid()
            err = max(abs(fr(d1.real)), abs(fr(d1.imag)), abs(fr(d2.real)), abs(fr(d2.imag)))
            ref = T[-1][-1].mid()
            balls.set_prec()
            lam = acb(balls.qball(lr), balls.qball(li))
            Gb = balls.qball(G)
            for key, gr in grids.items():
                B = ev.evans(lam, Gb, m, gr)
                c(B.is_finite(), f"enclosure finite at lam=({lr},{li}) G={G} grid {key}")
                if not B.is_finite():
                    continue
                c(margin(B, ref) > err, f"reference inside enclosure at lam=({lr},{li}) G={G} grid {key}")
                if key != (8, 16):
                    Bm = evans_without_remainder(lam, Gb, m, gr)
                    if Bm.is_finite() and margin(Bm, ref) < -err:
                        caught = True
    finally:
        balls.set_prec()
    c(caught, "mutation M1 (remainder dropped) is caught on some coarse grid")
    c.finish()
