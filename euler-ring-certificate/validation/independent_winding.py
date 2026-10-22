"""An independently written winding counter, run on a seeded random sample of certificate cells.

It uses ``ringcert.evans.evans`` only as the enclosure oracle.  Everything else differs from
``ringcert.winding``:
  * its own contour (initial density 16 per unit for (N1'), 4/width for (N2'), at least 4 pieces per
    edge), with depth-first bisection;
  * its own rational-to-ball conversion, every lambda box and G ball checked by exact Fraction
    comparison to contain the segment and the G-cell;
  * its own acceptance: the image box must lie in one OPEN half-plane Re > 0, Im > 0, Re < 0 or Im < 0,
    decided by exact Fraction comparison of the box endpoints (not by Arb predicates);
  * its own winding formula, without point indicators: if segment j has half-plane index k_j (centre
    angle k_j pi/2), consecutive indices differ by 0 or +-1 mod 4 (opposite half-planes at a junction
    are impossible and abort), and the sum of the differences is 4 times the winding number.
Expected: winding 1 in every sampled cell.
Usage: python validation/independent_winding.py [--jobs N] [--seed S] [--count K] [--gap K] [--all]"""
import argparse
import json
import math
import os
import random
import sys
import time
import multiprocessing as mp
from fractions import Fraction as F

import _common


def fr(x):
    m, e = x.man_exp()
    return F(int(m)) * F(2) ** int(e)


def ball_q(q):
    from flint import arb, fmpz
    q = F(q)
    b = arb(fmpz(q.numerator)) / arb(fmpz(q.denominator))
    assert fr(b.lower()) <= q <= fr(b.upper())
    return b


def ball_iv(a, b):
    lo, hi = ball_q(a), ball_q(b)
    u = lo.union(hi)
    assert fr(u.lower()) <= min(a, b) and fr(u.upper()) >= max(a, b)
    return u


def halfplane(B):
    """Index of an open half-plane containing the box B (0: Re>0, 1: Im>0, 2: Re<0, 3: Im<0), or None."""
    if not B.is_finite():
        return None
    rl, rh = fr(B.real.lower()), fr(B.real.upper())
    il, ih = fr(B.imag.lower()), fr(B.imag.upper())
    for k, c in ((0, rl > 0), (1, il > 0), (2, rh < 0), (3, ih < 0)):
        if c:
            return k
    return None


def my_wind(m, rect, cell, npu, max_seg, max_depth=24):
    from ringcert import evans as ev
    from flint import acb
    x0, x1, y0, y1 = rect
    corners = [(x0, y0), (x1, y0), (x1, y1), (x0, y1)]
    segs = []
    for c in range(4):
        a, b = corners[c], corners[(c + 1) % 4]
        L = abs(b[0] - a[0]) + abs(b[1] - a[1])
        k = max(4, math.ceil(L * npu))
        for j in range(k):
            p = (a[0] + (b[0] - a[0]) * F(j, k), a[1] + (b[1] - a[1]) * F(j, k))
            q = (a[0] + (b[0] - a[0]) * F(j + 1, k), a[1] + (b[1] - a[1]) * F(j + 1, k))
            segs.append((p, q, 0))
    Gb = ball_iv(cell[0], cell[1])
    out, nev = [], 0
    stack = list(reversed(segs))
    while stack:
        p, q, dep = stack.pop()
        lam = acb(ball_iv(p[0], q[0]), ball_iv(p[1], q[1]))
        B = ev.evans(lam, Gb, m, _common.grid())
        nev += 1
        k = halfplane(B)
        if k is not None:
            out.append((p, q, k))
        else:
            if dep >= max_depth or len(out) + len(stack) > max_seg:
                return None, nev, len(out)
            mid = ((p[0] + q[0]) / 2, (p[1] + q[1]) / 2)
            stack.append((mid, q, dep + 1))
            stack.append((p, mid, dep + 1))
    n = len(out)
    assert all(out[i][1] == out[(i + 1) % n][0] for i in range(n))
    tot = 0
    for i in range(n):
        d = (out[i][2] - out[i - 1][2]) % 4
        if d == 2:
            raise RuntimeError("opposite half-planes at a junction: enclosure inconsistent")
        tot += {0: 0, 1: 1, 3: -1}[d]
    assert tot % 4 == 0
    return tot // 4, nev, n


def job(a):
    run, idx, rect, cell, npu, max_seg = a
    t = time.time()
    w, nev, n = my_wind(3, rect, cell, npu, max_seg)
    return run, idx, [str(cell[0]), str(cell[1])], w, nev, n, time.time() - t


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--seed", type=int, default=20261014)
    ap.add_argument("--count", type=int, default=3, help="number of (N1') cells to sample")
    ap.add_argument("--gap", type=int, default=8, help="number of (N2') cells to sample")
    ap.add_argument("--all", action="store_true", help="every cell of both certificates (hours)")
    a = ap.parse_args()
    rng = random.Random(a.seed)
    certs = {}
    for run, fn in (("N1'", "sector3_count_cells.json"), ("N2'", "sector3_gap_cells.json")):
        with open(os.path.join(_common.ROOT, "certificates", fn)) as f:
            certs[run] = json.load(f)["cells"]
    jobs = []
    for run, k in (("N1'", a.count), ("N2'", a.gap)):
        cells = certs[run]
        sel = range(len(cells)) if a.all else sorted(rng.sample(range(len(cells)), k))
        for i in sel:
            c = cells[i]
            rect = tuple(F(v) for v in c["rect"])
            cell = (F(c["G"][0]), F(c["G"][1]))
            npu, ms = (F(16), 8000) if run == "N1'" else (F(4) / (rect[1] - rect[0]), 1500)
            jobs.append((run, i, rect, cell, npu, ms))
    print(f"seed {a.seed}; {len(jobs)} cells on {a.jobs} processes", flush=True)
    t0 = time.time()
    bad = 0
    with mp.get_context("spawn").Pool(a.jobs, initializer=_common.init_worker) as pool:
        for run, idx, G, w, nev, n, dt in pool.imap_unordered(job, jobs):
            ok = w == 1
            bad += not ok
            print(f"{run} cell {idx} G={G}: independent winding {w} ({n} segments, {nev} evaluations, {dt:.0f}s) "
                  f"{'OK' if ok else 'MISMATCH'}", flush=True)
    print(f"independent_winding: {len(jobs)} cells, {bad} mismatches, {time.time()-t0:.0f}s", flush=True)
    sys.exit(1 if bad else 0)
