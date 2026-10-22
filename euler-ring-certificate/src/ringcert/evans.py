"""Validated enclosure of the Evans function E_m(lambda; G) in Arb ball arithmetic.

The object.  For an integer m >= 1, a real G and Re lambda > 0, let psi solve

    psi'' = Q psi on [s_L, s_R],   Q = m^2 + i m f_s / (lambda + i m Omega),   psi(s_L) = 1,  psi'(s_L) = m,

where f_s = d wbar / ds, g(s) = int_{-inf}^s wbar(s') e^{2 s'} ds', Omega = (g + G) e^{-2s}, and wbar is
the ring profile of ``ringcert.data`` (with any admissible cutoff chi).  The Evans function is

    E_m(lambda; G) = (psi' + m psi)(s_R) e^{-m (s_R - s_L)}.

Since Omega is real, |lambda + i m Omega| >= Re lambda > 0, so Q is bounded and E_m is well defined and
holomorphic in lambda on {Re lambda > 0}.

The method (Appendix A of the paper: Lemma A.1 and Proposition A.3, box form).
  * End regions [s_L, s_a] and [s_b, s_R].  There chi may vary and wbar <= e^{-50}.  By Lemma A.1,
    int |f_s| <= TVEND on each end region, with TVEND = 3 e^{-50} (the exact check ``constants``
    verifies (9/4) e^{2 max(x_a, y_b)} <= 3 e^{-50}).  The solution is compared with that of
    psi'' = m^2 psi: in the norm |Y|_w = max(m|psi|, |psi'|) the difference after a region of length L
    is at most e^{mL} |Y|_w (e^eps - 1), eps = TVEND / Re lambda (Gronwall), and e^eps - 1 <= 2 eps for
    0 <= eps <= 1.
  * Middle region [s_a, s_b], where chi = 1.  Fixed steps of length about h = 2^-8 (exact dyadic grid
    points), Taylor method of order N = 16.  Taylor coefficients of every coefficient function are
    computed by recurrences (below), once at the step point and once over the whole step (the same
    recurrences evaluated on the ball hull of the step).  Over each step an a priori enclosure of
    (psi, psi') is obtained from a Gronwall bound in the norm max(kappa|psi|, |psi'|), and the
    integral form of the Taylor remainder is added as a convex box.

What is enclosed.  ``evans(lam, G, m, grid)`` returns an acb box containing E_m(lambda'; G') for every
lambda' in the acb box ``lam`` and every real G' in the arb ball ``G``, simultaneously for every
admissible cutoff chi.  It returns a NaN box (and so fails closed) if Re lam > 0 is not certain, if
eps <= 1 is not certain, if a step bound is not finite, or if any intermediate quantity is not finite.
"""
import math
from fractions import Fraction
from flint import arb, acb, fmpz

from .data import A0_Q, DD_Q, SL_Q, SA_Q, SB_Q, SR_Q, rn_binary64
from .balls import PREC, set_prec, dy, qball, box, hull   # noqa: F401  (re-exported)

# ------------------------------------------------------------------ the data as exact Arb balls
A0, DD, SL, SA, SB, SR = [dy(v) for v in (A0_Q, DD_Q, SL_Q, SA_Q, SB_Q, SR_Q)]
# TVEND >= 3 e^{-50} >= int |f_s| on each end region (Lemma A.1); an exact dyadic upper endpoint.
TVEND = (arb(3) * arb(-50).exp()).upper()


def _cauchy(a, b, k):
    """The k-th coefficient of the product of two Taylor series: sum_{j<=k} a_j b_{k-j}."""
    s = a[0] * b[k]
    for j in range(1, k + 1):
        s = s + a[j] * b[k - j]
    return s


# ------------------------------------------------------------------ Taylor data (lambda independent)
def _H(x):
    """H(x) = 1/(1 + e^{-2x}), evaluated in ball arithmetic (encloses H on the ball x)."""
    return 1 / (1 + (-2 * x).exp())


def _H_pair_iv(xlo, xhi):
    """Enclosures of H and of 1 - H = H(-x) over the interval [xlo, xhi].

    H is increasing, so H([xlo, xhi]) is contained in the hull of H(xlo) and H(xhi), and
    H(-[xlo, xhi]) in the hull of H(-xhi) and H(-xlo).  Computing 1 - H as H(-x) keeps relative
    accuracy where H is close to 1.
    """
    Hv = hull(_H(xlo), _H(xhi))
    Hb = hull(_H(-xhi), _H(-xlo))
    return Hv, Hb


def _coeffs(Slo, Shi, N):
    """Taylor coefficients in s of the coefficient functions, valid at every point of [Slo, Shi].

    With A = H((s - a_0)/d), Abar = 1 - A, B = H(-s/d), Bbar = 1 - B (on [s_a, s_b], where chi = 1):
        A' = (2/d) A Abar,  Abar' = -A',  B' = -(2/d) B Bbar,  Bbar' = -B'   (exact ODEs of H),
        w = A B = wbar,  f_s = w',  e^{+-2s} (coefficients e^{+-2 s0} (+-2)^k / k!),  q = w e^{2s} = g'.
    The k-th coefficient of a product is a Cauchy sum.  Every coefficient is a ball computed from
    the enclosures of A, Abar, B, Bbar, e^{+-2s} on the ball S = hull(Slo, Shi) by inclusion-monotone
    operations, so it contains the k-th Taylor coefficient at every point of [Slo, Shi].
    (If Slo == Shi this is the Taylor expansion at one point.)
    Returns dict(fs=[f_s,k]_{k<=N}, e2, em2, q=[q_k]_{k<=N}, w=[w_k]_{k<=N+1}).
    """
    S = hull(Slo, Shi)
    x1 = 1 / DD
    A, Ab = _H_pair_iv((Slo - A0) / DD, (Shi - A0) / DD)
    B, Bb = _H_pair_iv(-(Shi / DD), -(Slo / DD))
    A, Ab, B, Bb = [A], [Ab], [B], [Bb]
    for k in range(N + 1):
        PA = _cauchy(A, Ab, k)
        PB = _cauchy(B, Bb, k)
        ak = (2 * x1) * PA / (k + 1)
        bk = -((2 * x1) * PB) / (k + 1)
        A.append(ak); Ab.append(-ak)
        B.append(bk); Bb.append(-bk)
    w = [_cauchy(A, B, k) for k in range(N + 2)]
    fs = [w[k + 1] * (k + 1) for k in range(N + 1)]
    e2_0 = (2 * S).exp()
    em2_0 = (-2 * S).exp()
    e2, em2 = [], []
    for k in range(N + 1):
        c = arb(2 ** k) / arb(fmpz(math.factorial(k)))
        e2.append(e2_0 * c)
        em2.append(em2_0 * (c if k % 2 == 0 else -c))
    q = [_cauchy(w, e2, k) for k in range(N + 1)]
    return dict(fs=fs, e2=e2, em2=em2, q=q, w=w)


def _omega(dat, g0, N):
    """Taylor coefficients (k < N) of g e^{-2s}, from g_0 = g0 (a ball containing g at the point or
    over the step) and g_k = q_{k-1}/k (since g' = q)."""
    q, em2 = dat["q"], dat["em2"]
    g = [g0] + [q[k - 1] / k for k in range(1, N + 1)]
    return [_cauchy(g, em2, k) for k in range(N)]       # (g e^{-2s})_k, k < N


class Grid:
    """lambda-independent Taylor data on the steps of the middle region [s_a, s_b].

    Grid points: s_0 = s_a, s_n = s_b and s_i = RN(s_a + (s_b - s_a) i / n) for 0 < i < n, where
    n = ceil((s_b - s_a) / h), h = 2^-hpow.  These are exact dyadics; the partition is asserted to be
    strictly increasing and the step lengths h_i = s_{i+1} - s_i are asserted to be exact.  (Any
    strictly increasing partition is admissible for the method; this one has n = 360 for hpow = 8.)

    Stored per step i: the coefficient data at the point s_i (``pt``) and over [s_i, s_{i+1}] (``iv``);
    balls ``g[i]`` containing g(s_i); the coefficients of Omega - G e^{-2s} = g e^{-2s} at the point
    (``Omg``) and over the step (``OmgI``); and the powers h_i^k (``hp``) and k h_i^{k-1} (``khp``).

    The values g(s_i) are enclosed as follows.  g(s_a) lies in [0, e^{2 x_a + 2 s_a} / (2/d + 2)],
    x_a = (s_a - a_0)/d, because 0 <= wbar <= H((s - a_0)/d) <= e^{2(s - a_0)/d} on (-inf, s_a].  The
    increment over a step is int_{s_i}^{s_{i+1}} q = sum_{k<N} q_k(s_i) h^{k+1}/(k+1) + R with
    R in q_N([s_i, s_{i+1}]) h^{N+1}/(N+1) (Lagrange form, valid since q is real), and it is >= 0
    because q = wbar e^{2s} >= 0; the ball is intersected with [0, inf).  g is nondecreasing, so g on
    the step lies in hull(g(s_i), g(s_{i+1})).
    """

    def __init__(self, hpow=8, N=16):
        h = Fraction(1, 2 ** hpow)
        n = math.ceil((SB_Q - SA_Q) / h)
        ptsQ = [SA_Q] + [rn_binary64(SA_Q + (SB_Q - SA_Q) * Fraction(i, n)) for i in range(1, n)] + [SB_Q]
        assert all(ptsQ[i] < ptsQ[i + 1] for i in range(n)), "grid not increasing"
        self.ptsQ = ptsQ
        self.s = [dy(p) for p in ptsQ]
        self.n, self.N, self.hpow = n, N, hpow
        self.h = [self.s[i + 1] - self.s[i] for i in range(n)]
        assert all(x.is_exact() for x in self.h)
        self.pt = [_coeffs(self.s[i], self.s[i], N) for i in range(n)]
        self.iv = [_coeffs(self.s[i], self.s[i + 1], N) for i in range(n)]
        # g increments over each step: sum_{k<N} q_k(s_i) h^{k+1}/(k+1) + q_N(step) h^{N+1}/(N+1)
        dg = []
        for i in range(n):
            q, qI, hh = self.pt[i]["q"], self.iv[i]["q"], self.h[i]
            acc = arb(0)
            hp = hh
            for k in range(N):
                acc = acc + q[k] * hp / (k + 1)
                hp = hp * hh
            acc = acc + qI[N] * hp / (N + 1)
            dg.append(acc.nonnegative_part())                  # g is nondecreasing (wbar >= 0)
        xa = (SA - A0) / DD
        gmax = (2 * xa + 2 * SA).exp() / (2 / DD + 2)
        g = [hull(arb(0), gmax)]                                # g(sa) in [0, gmax]
        for i in range(n):
            g.append(g[i] + dg[i])
        self.g = g
        self.Omg = [_omega(self.pt[i], g[i], N) for i in range(n)]
        self.OmgI = [_omega(self.iv[i], hull(g[i], g[i + 1]), N) for i in range(n)]
        # powers of h for the Taylor sums
        self.hp = []
        self.khp = []
        for i in range(n):
            hp = [arb(1)]
            for k in range(N + 1):
                hp.append(hp[-1] * self.h[i])
            self.hp.append(hp)
            self.khp.append([None, None] + [hp[k - 1] * k for k in range(2, N + 1)])


def _step_coeffs(lam, G, m, Omg, em2, fs, N):
    """Taylor coefficients Q_k (k < N) of Q = m^2 + i m f_s R, R = 1/(lambda + i m Omega).

    D = lambda + i m (g e^{-2s} + G e^{-2s}) has coefficients D_k; R is obtained by the reciprocal
    recurrence R_0 = 1/D_0, R_k = -R_0 sum_{j=1}^{k} D_j R_{k-j}.  All operations are acb/arb ball
    operations, so each Q_k contains the true coefficient for every lambda in ``lam``, G in ``G`` and
    every point covered by the coefficient data (a point or a whole step).
    """
    Dk = [acb(0, m * (Omg[k] + G * em2[k])) for k in range(N)]
    Dk[0] = Dk[0] + lam
    R = [1 / Dk[0]]
    for k in range(1, N):
        s = Dk[1] * R[k - 1]
        for j in range(2, k + 1):
            s = s + Dk[j] * R[k - j]
        R.append(-(R[0] * s))
    Q = []
    for k in range(N):
        s = fs[0] * R[k]
        for j in range(1, k + 1):
            s = s + fs[j] * R[k - j]
        Q.append(acb(0, m) * s)
    Q[0] = Q[0] + m * m
    return Q


def _psi_coeffs(Q, p0, p1, N):
    """Taylor coefficients psi_0..psi_{N+1} of psi from psi_0 = p0, psi_1 = p1 and the ODE:
    (k+1)(k+2) psi_{k+2} = sum_{j<=k} Q_j psi_{k-j}."""
    psi = [p0, p1]
    for k in range(N):              # psi_{k+2} for k = 0, ..., N - 1, i.e. psi up to index N + 1
        s = Q[0] * psi[k]
        for j in range(1, k + 1):
            s = s + Q[j] * psi[k - j]
        psi.append(s / ((k + 1) * (k + 2)))
    return psi


def evans(lam, G, m, grid):
    """An acb box containing E_m(lambda'; G') for all lambda' in the acb box ``lam`` and all real G' in
    the arb ball ``G``, for every admissible cutoff chi; or a NaN box (fail closed).

    Steps (each line is an enclosure, by the containment contract of Arb):
    1. Left end [s_L, s_a] (Lemma A.1).  eps = TVEND / lower(Re lam) must be certainly <= 1.  Then
       |psi(s_a) - e^{m L1}| <= e^{m L1}(e^eps - 1) and |psi'(s_a) - m e^{m L1}| <= m e^{m L1}(e^eps - 1),
       L1 = s_a - s_L; both disks are contained in psi = e^{m L1} + box(e^{m L1} 2 eps), dpsi = m psi.
    2. Each middle step [s0, s1], length h.  With qsup >= sup|Q| over (lam, G, step) and
       kappa = sqrt(max(qsup, m^2)), the vector (kappa psi, psi') grows at most like e^{kappa t}, so with
       M = max(kappa|psi(s0)|, |psi'(s0)|) e^{kappa h}:  psi(step) in psi(s0) + box(h M) and
       psi'(step) in psi'(s0) + box(h qsup M / kappa).  The Taylor coefficients over the step built
       from these enclosures contain psi^{(k)}(xi)/k! for every xi in the step.  Then
           psi(s1)  in sum_{k<N} psi_k(s0) h^k + h^N psi_N(step),
           psi'(s1) in sum_{1<=k<=N} k psi_k(s0) h^{k-1} + (N+1) h^N psi_{N+1}(step),
       by the integral form of the Taylor remainder (an average of psi^{(N)}/N! against a probability
       density, hence in the closed convex box psi_N(step)).  kappa h must be certainly <= 700.
    3. Right end [s_b, s_R] (Lemma A.1 again).  (psi' + m psi)(s_R) lies within
       2 e^{m L2} max(m|psi|, |psi'|)(s_b) (e^eps - 1) of e^{m L2} (psi' + m psi)(s_b), L2 = s_R - s_b.
    4. Multiply by e^{-m (s_R - s_L)}.
    The only property of lam used is Re lambda >= lower(Re lam) > 0 (it bounds |lambda + i m Omega|
    from below and gives eps); the sign of G is not used (Omega is real for every real G).
    """
    N = grid.N
    NAN = acb(arb('nan'), arb('nan'))
    relo = lam.real.lower()
    if not (relo > 0):
        return NAN
    # ---- left end [sL, sa]: psi'' = (m^2 + delta) psi, int |delta|/m <= TVEND / Re lam = eps
    L1 = SA - SL
    eps = (TVEND / relo).upper()
    if not (eps <= 1):
        return NAN
    eg = (2 * eps).upper()                                # e^eps - 1 <= 2 eps   (0 <= eps <= 1)
    emL1 = (m * L1).exp()
    rad = emL1.upper() * eg
    psi = acb(emL1) + box(rad)
    dpsi = psi * m
    msq = arb(m * m)
    # ---- middle [sa, sb]
    for i in range(grid.n):
        Q = _step_coeffs(lam, G, m, grid.Omg[i], grid.pt[i]["em2"], grid.pt[i]["fs"], N)
        QI = _step_coeffs(lam, G, m, grid.OmgI[i], grid.iv[i]["em2"], grid.iv[i]["fs"], N)
        h = grid.h[i]
        # a priori enclosure over the step (Gronwall in the norm max(kappa|psi|, |psi'|))
        qsup = QI[0].abs_upper()
        if not qsup.is_finite():
            return NAN
        kap = qsup.max(msq).sqrt().upper()                 # kap^2 >= sup |Q| on the step, kap >= m > 0
        Mw = (kap * psi.abs_upper()).upper().max(dpsi.abs_upper())
        arg = (kap * h).upper()
        if not (arg <= 700):
            return NAN
        M = (Mw * arg.exp()).upper()
        psiI = psi + box(h * M)
        dpsiI = dpsi + box(h * qsup * M / kap)
        pc = _psi_coeffs(Q, psi, dpsi, N)
        pI = _psi_coeffs(QI, psiI, dpsiI, N)
        hp, khp = grid.hp[i], grid.khp[i]
        new_psi = pc[0]
        for k in range(1, N):
            new_psi = new_psi + pc[k] * hp[k]
        new_dpsi = pc[1]
        for k in range(2, N + 1):
            new_dpsi = new_dpsi + pc[k] * khp[k]
        psi = new_psi + pI[N] * hp[N]                       # integral-form remainder (convex box)
        dpsi = new_dpsi + pI[N + 1] * (hp[N] * (N + 1))
        if not (psi.is_finite() and dpsi.is_finite()):
            return NAN
    # ---- right end [sb, sR]
    L2 = SR - SB
    emL2 = (m * L2).exp()
    Wv = dpsi + psi * m                                   # (psi' + m psi)(sb)
    Wn = (m * psi.abs_upper()).upper().max(dpsi.abs_upper())
    Eend = Wv * emL2 + box(2 * emL2.upper() * Wn * eg)
    norm = (-m * (SR - SL)).exp()
    out = Eend * norm
    if not out.is_finite():
        return NAN
    return out
