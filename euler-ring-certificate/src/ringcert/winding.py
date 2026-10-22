"""Certified winding numbers of E_m along rectangle boundaries, uniformly over a G-cell.

The statement (Appendix A of the paper: Proposition A.4, box form).  Let Gamma be the
counter-clockwise boundary of a rectangle in {Re lambda > 0}, cut into segments [p_i, p_{i+1}] with
exact rational endpoints, and let C be a G-cell (an interval of G).  Suppose that for each i a box B_i
contains E(lambda; G) for all lambda in [p_i, p_{i+1}] and all G in C, and that each B_i is

    type P:  B_i avoids (-inf, 0]   (Im B_i > 0, or Im B_i < 0, or Re B_i > 0, certainly), or
    type N:  B_i avoids [0, +inf)   (Im B_i > 0, or Im B_i < 0, or Re B_i < 0, certainly).

Then E(.; G) has no zero on Gamma for every G in C, and

    wind(E(.; G) o Gamma, 0) = sum over type-N segments [p, q] of (1[Im E(q; G) < 0] - 1[Im E(p; G) < 0]).

Proof.  On a type-P segment the principal Arg is a continuous argument of the image; on a type-N
segment Arg + 2 pi 1[Im < 0] is one (a continuous branch of arg on C minus [0, inf)).  Summing the
increments around the closed curve, the principal parts telescope to 0, and what remains is the
indicator sum.  At a point shared by two type-N segments the indicators cancel; at a point shared by
a type-N and a type-P segment the value lies in B_N cap B_P, which avoids the real axis, so the sign
of Im E there is constant over the cell and is read from a point enclosure whose imaginary part
certainly excludes 0 (otherwise the cell is reported ambiguous, i.e. not certified).

By the argument principle the winding number is the number of zeros of E(.; G) inside the rectangle,
counted with multiplicity.  All decisions are Arb certain-comparisons on boxes; every reported
winding is therefore a proof (relative to the containment contract), and every failure to decide
results in refusal (a dead or ambiguous cell), never in a wrong number.
"""
import math
from fractions import Fraction as F
from flint import acb

from . import evans as ev
from .balls import qball


def qb(x):
    """Arb ball containing the rational x."""
    return qball(x)


def seg_box(p, q):
    """Arb box containing the axis-parallel segment [p, q] (p, q = (re, im) pairs of Fractions):
    the product of the hulls of the real parts and of the imaginary parts (a convex set containing
    both endpoints, hence the segment)."""
    re = qb(p[0]).union(qb(q[0]))
    im = qb(p[1]).union(qb(q[1]))
    return acb(re, im)


def pt_box(p):
    """Arb box containing the point p = (re, im)."""
    return acb(qb(p[0]), qb(p[1]))


def G_ball(cell):
    """Arb ball containing the G-cell [cell[0], cell[1]] (exact rational endpoints)."""
    return qb(cell[0]).union(qb(cell[1]))


def classify(B):
    """0 = rejected, 1 = type P (B certainly avoids (-inf, 0]), 2 = type N (B certainly avoids
    [0, inf)).  Non-finite boxes are rejected.  A box off the real axis is called type P (it would
    also qualify as type N; the formula holds for either choice)."""
    if not B.is_finite():
        return 0
    x, y = B.real, B.imag
    off = (y > 0) or (y < 0)
    if off or (x > 0):
        return 1
    if x < 0:
        return 2
    return 0


def rect_points(x0, x1, y0, y1, npu):
    """Exact rational points along the boundary of [x0, x1] x [y0, y1], counter-clockwise from
    (x0, y0), closed (the last point equals the first).  Each edge of length L gets
    max(2, ceil(L * npu)) equal sub-segments; the corners are among the points."""
    corners = [(x0, y0), (x1, y0), (x1, y1), (x0, y1), (x0, y0)]
    pts = []
    for a, b in zip(corners[:-1], corners[1:]):
        L = abs(b[0] - a[0]) + abs(b[1] - a[1])          # axis-parallel edge length (exact)
        k = max(2, math.ceil(F(L) * F(npu)))
        for j in range(k):
            t = F(j, k)
            pts.append((a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t))
    pts.append(corners[0])
    return pts


def certify_cell(m, rect, cell, grid, npu, max_iter, max_seg):
    """Certify the winding number of E_m(.; G) around the boundary of ``rect`` for all G in ``cell``.

    The boundary is cut by ``rect_points``; every segment is enclosed by ``evans`` on
    (segment box) x (G-cell ball) and classified; rejected segments are bisected at their exact
    midpoint (at most ``max_iter`` rounds, at most ``max_seg`` segments).  Then the indicator sum of the
    module docstring is evaluated.

    Returns (record, nevals).  record is None if the subdivision did not converge (a dead cell: not
    certified).  Otherwise record["winding"] is the certified winding number, or None if some
    indicator could not be decided (ambiguous: not certified).  The record also gives the number of
    segments, of type-N segments, of indicator points and of Evans evaluations.
    """
    x0, x1, y0, y1 = [F(v) for v in rect]
    base = rect_points(x0, x1, y0, y1, npu)
    segs = list(zip(base[:-1], base[1:]))
    Gb = G_ball(cell)
    accepted = {}
    pending = list(segs)
    nevals = 0
    it = 0
    while pending and it < max_iter:
        it += 1
        new_pending = []
        for (p, q) in pending:
            B = ev.evans(seg_box(p, q), Gb, m, grid)
            nevals += 1
            t = classify(B)
            if t > 0:
                accepted[(p, q)] = t
            else:
                if len(segs) > max_seg:
                    return None, nevals
                mid = ((p[0] + q[0]) / 2, (p[1] + q[1]) / 2)
                i = segs.index((p, q))
                segs[i:i + 1] = [(p, mid), (mid, q)]
                new_pending += [(p, mid), (mid, q)]
        pending = new_pending
    if pending:
        return None, nevals
    # contour check: consecutive, closed
    n = len(segs)
    assert all(segs[i][1] == segs[(i + 1) % n][0] for i in range(n))
    # indicators at junctions between a type-N and a non-type-N segment
    ind = {}
    for i in range(n):
        tp_prev = accepted[segs[i - 1]]
        tp = accepted[segs[i]]
        if (tp_prev == 2) != (tp == 2):
            p = segs[i][0]
            B = ev.evans(pt_box(p), Gb, m, grid)
            nevals += 1
            y = B.imag
            if B.is_finite() and (y < 0):
                ind[p] = 1
            elif B.is_finite() and (y > 0):
                ind[p] = 0
            else:
                ind[p] = None
    w, amb = 0, 0
    for (p, q) in segs:
        if accepted[(p, q)] == 2:
            for pt, sgn in ((q, 1), (p, -1)):
                if pt in ind:
                    if ind[pt] is None:
                        amb += 1
                    else:
                        w += sgn * ind[pt]
    return dict(G=[str(cell[0]), str(cell[1])], rect=[str(v) for v in (x0, x1, y0, y1)],
                winding=(w if amb == 0 else None), nseg=n, ambiguous=amb,
                nN=sum(1 for s in segs if accepted[s] == 2), nind=len(ind), nevals=nevals), nevals


def certify_cell_adaptive(m, rect, cell, grid, npu, max_iter, max_seg, depth):
    """Certify ``cell``; every sub-cell that is dead or ambiguous is halved at its exact rational
    midpoint, up to ``depth`` times.  Returns (records, failed, nevals): the records of the certified
    sub-cells (each with its halving ``level``), the sub-cells still not certified after ``depth``
    halvings, and the total number of Evans evaluations.  The certified sub-cells and the failed ones
    together partition ``cell``."""
    res, failed, ev_count = [], [], 0
    todo = [cell]
    for lev in range(depth + 1):
        nxt = []
        for c in todo:
            r, ne = certify_cell(m, rect, c, grid, npu, max_iter, max_seg)
            ev_count += ne
            if r is None or r["winding"] is None:
                mid = (c[0] + c[1]) / 2
                nxt += [(c[0], mid), (mid, c[1])]
            else:
                r["level"] = lev
                res.append(r)
        todo = nxt
        if not todo:
            break
    failed = [[str(a), str(b)] for (a, b) in todo]
    return res, failed, ev_count
