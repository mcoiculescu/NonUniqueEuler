"""Known windings on the G-cell [0, 10^-4], where lambda_*(G) ~ 0.1220 - 0.4171 i.

Expected: [0.125,3]x[-5,3] -> 0; [0.115,3]x[-5,3] -> 1; [0.115,0.13]x[-0.45,-0.40] -> 1;
[0.115,0.13]x[-0.40,-0.35] -> 0.  With --full also: a rectangle whose left edge passes through
lambda_*(0) (Re lambda_*(0) ~ 0.12204476) must NOT be certified for the whole cell (about 8 minutes).
Usage: python validation/known_windings.py [--jobs N] [--full]"""
import argparse
import sys
import time
import multiprocessing as mp
from fractions import Fraction as F

import _common


def job(a):
    from ringcert import winding as wd
    rect, exp, depth = a
    t = time.time()
    res, failed, nev = wd.certify_cell_adaptive(3, rect, (F(0), F(1, 10000)), _common.grid(), F(20), 16, 6000, depth)
    return rect, exp, [r["winding"] for r in res], failed, nev, time.time() - t


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--full", action="store_true")
    a = ap.parse_args()
    cases = [((F("0.125"), F(3), F(-5), F(3)), 0, 2), ((F("0.115"), F(3), F(-5), F(3)), 1, 2),
             ((F("0.115"), F("0.13"), F("-0.45"), F("-0.40")), 1, 2), ((F("0.115"), F("0.13"), F("-0.40"), F("-0.35")), 0, 2)]
    if a.full:
        cases.append(((F("0.12204476"), F("0.13"), F("-0.45"), F("-0.40")), None, 0))
    nfail = 0
    with mp.get_context("spawn").Pool(min(a.jobs, len(cases)), initializer=_common.init_worker) as pool:
        for rect, exp, w, failed, nev, dt in pool.imap(job, cases):
            if exp is None:
                good = not (len(w) == 1 and not failed)       # never a certified winding for the whole cell
            else:
                good = (w == [exp] and not failed)
            nfail += not good
            print([str(v) for v in rect], "expected", exp, "obtained", w, "failed", failed, "evals", nev,
                  f"{dt:.0f}s", "PASS" if good else "FAIL", flush=True)
    print("known_windings:", "0 failures" if nfail == 0 else f"{nfail} FAILURES")
    sys.exit(1 if nfail else 0)
