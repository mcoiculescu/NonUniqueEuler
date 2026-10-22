"""Sharpness of the gap statement near the end of the G-range.

Re lambda_*(1/50) ~ 0.0844781 and d Re lambda_*/dG ~ -2.5, so Re lambda_* = 0.0844 only near
G ~ 0.02003 > G_MAX.  With the rectangle [s, 0.086] x [-0.517, -0.512]:
  S1  s = 0.08455, G in [0.019999, G_MAX]: lambda_* left of the rectangle  -> winding 0
  S2  s = 211/2500, G in [0.019999, G_MAX]: lambda_* inside                 -> winding 1
  S3  s = 211/2500, G in [0.02019, 0.0202] (beyond G_MAX): lambda_* left    -> winding 0
  S4  s = 211/2500, G in [G_MAX, 0.0202]: lambda_* crosses the left edge    -> NOT certified
A certified 1 where 0 or refusal is expected would be a soundness failure.
Usage: python validation/sharpness.py [--jobs N]"""
import argparse
import sys
import time
import multiprocessing as mp
from fractions import Fraction as F

import _common


def job(a):
    from ringcert import winding as wd
    name, rect, cell, npu, max_iter, max_seg, expect = a
    t = time.time()
    r, nev = wd.certify_cell(3, rect, cell, _common.grid(), npu, max_iter, max_seg)
    w = "dead" if r is None else r["winding"]
    good = ((r is None) or (r["winding"] is None)) if expect == "fail" else (r is not None and r["winding"] == expect)
    return name, [str(v) for v in rect], [str(c) for c in cell], expect, w, nev, time.time() - t, good


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=4)
    a = ap.parse_args()
    from ringcert.data import G_MAX_Q as Gmax
    yb = (F("-0.5170"), F("-0.5120"))
    cases = [
        ("S1", (F("0.08455"), F("0.0860")) + yb, (F("0.019999"), Gmax), 10, 800, 0),
        ("S2", (F(211, 2500), F("0.0860")) + yb, (F("0.019999"), Gmax), 10, 800, 1),
        ("S3", (F(211, 2500), F("0.0860")) + yb, (F("0.020190"), F("0.020200")), 10, 800, 0),
        ("S4", (F(211, 2500), F("0.0860")) + yb, (Gmax, F("0.020200")), 10, 800, "fail"),
    ]
    cases = [(n, r, c, F(3) / (r[1] - r[0]), mi, ms, e) for n, r, c, mi, ms, e in cases]
    nbad = 0
    with mp.get_context("spawn").Pool(min(a.jobs, len(cases)), initializer=_common.init_worker) as pool:
        for name, rect, cell, expect, w, nev, dt, good in pool.imap(job, cases):
            nbad += not good
            print(f"{name} rect {rect} G {cell}: expected {expect}, obtained {w}, evals {nev}, {dt:.0f}s "
                  f"{'PASS' if good else 'FAIL'}", flush=True)
    print(f"sharpness: {nbad} failures", flush=True)
    sys.exit(1 if nbad else 0)
