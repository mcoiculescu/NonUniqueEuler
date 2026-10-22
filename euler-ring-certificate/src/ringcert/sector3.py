"""The two sector-3 computations: (N1') the zero count and (N2') the spectral gap.

(N1')  For every G in [0, G_MAX]: E_3(.; G) has no zero on the boundary of R_A = [9/200, 3] x [-5, 3],
       and wind(E_3(.; G) o boundary(R_A), 0) = 1.
       Certificate: a list of G-cells with exact rational endpoints that partitions [0, G_MAX]; each
       cell is certified with ``winding.certify_cell`` on R_A.
(N2')  For every G in [0, G_MAX] there is a rectangle R = [211/2500, x1] x [y0, y1] (x1 > 211/2500,
       y0 < y1) such that E_3(.; G) has no zero on boundary(R) and wind(E_3(.; G) o boundary(R), 0) = 1.
       Certificate: a list of G-cells partitioning [0, G_MAX], each with its own rectangle of left
       edge exactly 211/2500 (exact rationals); each pair is certified with ``certify_cell``.

How the certificate lists were found (``--search``; not part of the proof).  For (N1'), 20 equal cells
of [0, G_MAX], each halved (at exact midpoints) when it fails, up to 4 times.  For (N2'), cells are
graded by the distance of an approximate eigenvalue path to the line Re lambda = 211/2500, and
rectangles are placed around Newton approximations of the eigenvalue computed on Arb midpoints.  The
placement is a heuristic; only the subsequent certification is part of the proof.  By default the
shipped certificate files (``certificates/``) are certified directly, so no heuristic runs.

All contour points, rectangle edges and cell endpoints are exact rationals (``fractions.Fraction``);
all enclosures are Arb balls.  Cells are independent, so the number of processes cannot change any
result.
"""
import json
import math
import os
import time
from fractions import Fraction as F
import multiprocessing as mp

from .data import G_MAX_Q, RECT_A, SIGMA_GAP, data_strings, dec_near
from . import balls

M_SECTOR = 3
HPOW, ORDER = 8, 16
EXPECTED_WINDING = 1

COUNT_PARAMS = dict(npu=F(20), max_iter=16, max_seg=6000, depth=4)
GAP_PARAMS = dict(npu_numerator=F(3), max_iter=10, max_seg=800, depth=5)   # npu = 3 / (x1 - x0)


# ---------------------------------------------------------------- worker side
_grid = None


def _init(hpow, N, prec):
    global _grid
    from . import evans as ev
    balls.set_prec(prec)
    _grid = ev.Grid(hpow, N)


def _work_cell(args):
    from . import winding as wd
    idx, m, rect, cell, npu, max_iter, max_seg, depth = args
    t = time.time()
    res, failed, nev = wd.certify_cell_adaptive(m, rect, cell, _grid, npu, max_iter, max_seg, depth)
    return idx, res, failed, nev, time.time() - t


def _to_frac(x):
    """Exact Fraction of the midpoint of an arb ball (placement only)."""
    man, ex = x.mid().man_exp()
    man, ex = int(man), int(ex)
    return F(man) * (F(2) ** ex)


def _dyadic_round(q, bits=50):
    return F(math.floor(q * 2 ** bits), 2 ** bits)


def _work_newton(args):
    """Newton iteration on Arb midpoints for the zero of E_3(.; G); only PLACES the rectangles of
    the search mode (not part of the proof)."""
    from . import evans as ev
    from flint import acb
    idx, G, lr, li = args
    Gb = balls.qball(G)
    delta = F(1, 10 ** 7)
    for it in range(8):
        lam = acb(balls.qball(lr), balls.qball(li))
        lam2 = acb(balls.qball(lr + delta), balls.qball(li))
        E0 = ev.evans(lam, Gb, 3, _grid)
        E1 = ev.evans(lam2, Gb, 3, _grid)
        der = (E1 - E0) / balls.qball(delta)
        step = E0 / der
        sr, si = _to_frac(step.real), _to_frac(step.imag)
        lr, li = _dyadic_round(lr - sr), _dyadic_round(li - si)
        if abs(sr) + abs(si) < F(1, 10 ** 12):
            break
    return idx, lr, li, it


# ---------------------------------------------------------------- cell lists
def count_cells_search():
    """The 20 equal G-cells of [0, G_MAX] (exact rationals) used by the search mode of (N1')."""
    ncell = 20
    return [(G_MAX_Q * i / ncell, G_MAX_Q * (i + 1) / ncell) for i in range(ncell)]


# An approximate eigenvalue path (floating-point orientation values, uncertified), used only to
# grade the cells and to seed the Newton placement of the search mode of (N2').
_TAB_G = [F(0), F(4, 1000), F(8, 1000), F(12, 1000), F(16, 1000), F(20, 1000)]
_TAB_R = [F(s) for s in ("0.1220448", "0.1164824", "0.1101324", "0.1028480", "0.0944118", "0.0844781")]
_TAB_I = [F(s) for s in ("-0.4171233", "-0.4365874", "-0.4560541", "-0.4755236", "-0.4949961", "-0.5144718")]


def _interp(x, tab):
    x = min(max(x, _TAB_G[0]), _TAB_G[-1])
    for j in range(len(_TAB_G) - 1):
        if _TAB_G[j] <= x <= _TAB_G[j + 1]:
            return tab[j] + (tab[j + 1] - tab[j]) * (x - _TAB_G[j]) / (_TAB_G[j + 1] - _TAB_G[j])


def gap_cells_search():
    """Graded G-cells of [0, G_MAX] for the search mode of (N2') (exact rationals).

    Width max(min(5e-4, dist/60), 1e-6), dist = (approximate Re lambda_* at the cell start) - 211/2500;
    endpoints floored to multiples of 2^-40; the last endpoint is G_MAX.
    """
    sig, fac = SIGMA_GAP, F(60)
    Gmax = G_MAX_Q
    cells, a = [], F(0)
    while a < Gmax:
        dist = _interp(min(a + F(1, 10 ** 4), F(1, 50)), _TAB_R) - sig
        w = max(min(F(5, 10 ** 4), dist / fac), F(1, 10 ** 6))
        b = min(Gmax, a + w)
        if b < Gmax:
            b = F(math.floor(b * 2 ** 40), 2 ** 40)
        if Gmax - b < F(1, 10 ** 12):
            b = Gmax
        assert b > a
        cells.append((a, b)); a = b
    return cells


def gap_rects_search(cells, pool, log, t0):
    """Rectangles of the search mode of (N2'): Newton approximations l(G) of the eigenvalue at all
    cell endpoints, then R = [s, max Re l + eta] x [min Im l - eta, max Im l + eta] with s = 211/2500
    and eta = min Re l - s > 0 (asserted).  Placement only."""
    sig = SIGMA_GAP
    ends = sorted(set([c[0] for c in cells] + [c[1] for c in cells]))
    log(f"{len(cells)} graded G-cells; Newton placement on {len(ends)} endpoints")
    nj = [(j, G, _dyadic_round(_interp(G, _TAB_R)), _dyadic_round(_interp(G, _TAB_I))) for j, G in enumerate(ends)]
    path = {}
    for j, lr, li, it in pool.imap_unordered(_work_newton, nj, chunksize=4):
        path[ends[j]] = (lr, li)
    log(f"Newton done ({time.time()-t0:.0f}s); path Re range [{dec_near(min(v[0] for v in path.values()), 8)}, "
        f"{dec_near(max(v[0] for v in path.values()), 8)}]")
    rects = []
    for i, (g1, g2) in enumerate(cells):
        l1, l2 = path[g1], path[g2]
        eta = min(l1[0], l2[0]) - sig
        assert eta > 0
        r = (sig, max(l1[0], l2[0]) + eta, min(l1[1], l2[1]) - eta, max(l1[1], l2[1]) + eta)
        rects.append(r)
    return rects


# ---------------------------------------------------------------- certificate files
def load_certificate(path):
    """Read a certificate file: a JSON object with "item", "data", "parameters" and "cells"
    (each cell has "G": [a, b] and "rect": [x0, x1, y0, y1] as exact "p/q" strings)."""
    with open(path) as f:
        C = json.load(f)
    cells = [(F(c["G"][0]), F(c["G"][1])) for c in C["cells"]]
    rects = [tuple(F(v) for v in c["rect"]) for c in C["cells"]]
    return C, cells, rects


def certificate_object(item, cells, rects, params):
    """The certificate file content for a list of cells and rectangles (exact strings)."""
    order = sorted(range(len(cells)), key=lambda i: cells[i][0])
    return {
        "format": "ringcert-certificate-1",
        "item": item,
        "sector": M_SECTOR,
        "data": data_strings(),
        "parameters": {k: (str(v) if isinstance(v, F) else v) for k, v in params.items()},
        "cells": [{"G": [str(cells[i][0]), str(cells[i][1])], "rect": [str(v) for v in rects[i]]} for i in order],
    }


# ---------------------------------------------------------------- driver
def rectangle_ok(item, rect):
    """The shape that the statement requires of a rectangle (x0, x1, y0, y1), in exact rationals.

    (N1'): rect = R_A.  (N2'): x0 = 211/2500 < x1 and y0 < y1 (so x0 is the left edge, and the
    boundary, traversed from (x0, y0) through (x1, y0), (x1, y1), (x0, y1), is traversed
    counterclockwise), and rect is inside R_A."""
    x0, x1, y0, y1 = rect
    if item == "N1'":
        return tuple(rect) == RECT_A
    return (x0 == SIGMA_GAP and x0 < x1 and y0 < y1
            and RECT_A[0] <= x0 and x1 <= RECT_A[1] and RECT_A[2] <= y0 and y1 <= RECT_A[3])


def _jobs(item, cells, rects):
    jobs = []
    for i, (cell, r) in enumerate(zip(cells, rects)):
        if item == "N1'":
            p = COUNT_PARAMS
            jobs.append((i, M_SECTOR, r, cell, p["npu"], p["max_iter"], p["max_seg"], p["depth"]))
        else:
            p = GAP_PARAMS
            npu = p["npu_numerator"] / (r[1] - r[0])
            jobs.append((i, M_SECTOR, r, cell, npu, p["max_iter"], p["max_seg"], p["depth"]))
    return jobs


STATEMENTS = {
    "N1'": "for every G in [0, G_MAX]: E_3(.;G) != 0 on the boundary of R_A = [9/200,3]x[-5,3] "
           "and wind(E_3(.;G) o boundary(R_A), 0) = 1",
    "N2'": "for every G in [0, G_MAX] there is a rectangle R = [211/2500, x1]x[y0, y1] with "
           "E_3(.;G) != 0 on boundary(R) and wind(E_3(.;G) o boundary(R), 0) = 1",
}


def run(item, nproc, cells_file=None, search=False, log=print, only=None):
    """Certify item "N1'" (count) or "N2'" (gap).

    Returns (result, meta): ``result`` is the deterministic record (no timings, no environment) that
    is written to the output JSON; ``meta`` has timings and run information.  ``only`` restricts the
    run to a list of cell indices (spot checks; the result is then marked partial).  ``result["ok"]``
    is true only if there is at least one certified cell, every certified cell has winding 1, no
    sub-cell failed, and every rectangle used has the shape required by ``rectangle_ok``.
    """
    t0 = time.time()
    Gmax = G_MAX_Q
    pool = mp.get_context("spawn").Pool(nproc, initializer=_init, initargs=(HPOW, ORDER, balls.PREC))
    try:
        if search:
            mode = "search"
            if item == "N1'":
                cells = count_cells_search()
                rects = [RECT_A] * len(cells)
            else:
                cells = gap_cells_search()
                rects = gap_rects_search(cells, pool, log, t0)
        else:
            mode = "certificate"
            C, cells, rects = load_certificate(cells_file)
            if C["item"] != item:
                raise ValueError(f"certificate file is for item {C['item']}, not {item}")
            if C["data"] != data_strings():
                raise ValueError("certificate file data differ from the pinned data")
            params = COUNT_PARAMS if item == "N1'" else GAP_PARAMS
            if C["parameters"] != {k: (str(v) if isinstance(v, F) else v) for k, v in params.items()}:
                raise ValueError("certificate file parameters differ from this version's parameters")
        jobs = _jobs(item, cells, rects)
        if only is not None:
            jobs = [jobs[i] for i in only]
        log(f"{item}: {len(jobs)} G-cells, mode {mode}, {nproc} processes")
        results, failed_all, nev_all = {}, [], 0
        for idx, res, failed, nev, dt in pool.imap_unordered(_work_cell, jobs):
            results[idx] = res
            failed_all += failed
            nev_all += nev
            j = [jb for jb in jobs if jb[0] == idx][0]
            ws = [r["winding"] for r in res]
            log(f"cell {idx} G=[{dec_near(j[3][0], 9)},{dec_near(j[3][1], 9)}] subcells={len(res)} "
                f"windings={ws} nseg={[r['nseg'] for r in res]} failed={len(failed)} evals={nev} {dt:.1f}s "
                f"(elapsed {time.time()-t0:.0f}s)")
    except BaseException:
        pool.terminate()          # do not wait for the queued cells after an error or Ctrl-C
        pool.join()
        raise
    pool.close()
    pool.join()
    allres = sorted((r for i in results for r in results[i]), key=lambda r: F(r["G"][0]))
    failed_all = sorted(failed_all, key=lambda c: F(c[0]))           # deterministic order
    rects_ok = all(rectangle_ok(item, tuple(F(v) for v in r["rect"])) for r in allres)
    ok = (bool(allres) and all(type(r["winding"]) is int and r["winding"] == EXPECTED_WINDING for r in allres)
          and not failed_all and rects_ok)
    cov = [(F(r["G"][0]), F(r["G"][1])) for r in allres]
    gapfree = bool(cov) and (not failed_all) and cov[0][0] == 0 and cov[-1][1] == Gmax and all(
        cov[i][1] == cov[i + 1][0] for i in range(len(cov) - 1))
    nseg = sum(r["nseg"] for r in allres)
    amb = sum(r["ambiguous"] for r in allres)
    params = COUNT_PARAMS if item == "N1'" else GAP_PARAMS
    result = {
        "format": "ringcert-result-1",
        "item": item,
        "statement": STATEMENTS[item],
        "mode": mode,
        "partial": only is not None,
        "sector": M_SECTOR,
        "prec": balls.PREC,
        "grid": {"h": f"2^-{HPOW}", "N": ORDER},
        "data": data_strings(),
        "parameters": {k: (str(v) if isinstance(v, F) else v) for k, v in params.items()},
        "expected_winding": EXPECTED_WINDING,
        "ok": ok,
        "gapfree": gapfree,
        "failed": failed_all,
        "ncells": len(allres),
        "nseg": nseg,
        "nevals": nev_all,
        "ambiguous": amb,
        "cells": allres,
    }
    meta = {"seconds": round(time.time() - t0, 1), "nproc": nproc, "mode": mode,
            "cells_file": None if cells_file is None else str(cells_file)}
    log(f"RESULT {item} m={M_SECTOR} expected winding {EXPECTED_WINDING}: all certified cells agree={ok}; "
        f"cells={len(allres)} failed={len(failed_all)}; rectangles as required={rects_ok}; "
        f"cover [0,G_MAX] without gaps={gapfree}; "
        f"windings={sorted(set(str(r['winding']) for r in allres))}; total segments={nseg}; "
        f"evaluations={nev_all}; ambiguous={amb}; time={time.time()-t0:.0f}s")
    return result, meta


def dump_json(obj, path):
    """Write JSON deterministically (fixed key order as constructed, indent 1, trailing newline).

    The file is written under a temporary name and then renamed, so an interrupted write never
    leaves a truncated file under the final name."""
    tmp = path + ".tmp"
    with open(tmp, "w", newline="\n") as f:
        json.dump(obj, f, indent=1)
        f.write("\n")
    os.replace(tmp, path)
