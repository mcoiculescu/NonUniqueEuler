"""Command-line interface: ``python -m ringcert <command>`` (or the ``ringcert`` console script).

Exit codes: 0 every requested item passed; 1 some item failed or was not certified;
2 refused: environment (python -O, missing or non-reference python-flint), a command-line usage
error, or ``all --quick`` into a directory that holds the outputs of a full run; 3 internal error.
Every command refuses to run under ``python -O``.
"""
import argparse
import json
import os
import subprocess
import sys
import time
import traceback

from . import __version__
from . import environment as envmod

ROOT = envmod.repo_root()
DEFAULT_CELLS = {
    "N1'": os.path.join(ROOT, "certificates", "sector3_count_cells.json"),
    "N2'": os.path.join(ROOT, "certificates", "sector3_gap_cells.json"),
}
OUTNAME = {"N1'": "sector3_count", "N2'": "sector3_gap"}
# Files that ``all`` writes into its output directory; it removes them first, so that an interrupted
# run cannot leave the outputs or the PASS summary of an earlier run in place.
ALL_OUTPUTS = ("summary.json", "check.log", "constants.json", "constants.log", "selftest.log",
               "sector3_count.json", "sector3_count.log", "sector3_gap.json", "sector3_gap.log",
               "sector3_count_quick.json", "sector3_gap_quick.json")
# Default output directories of ``all``: a quick run never clears the directory of a full run.
DEFAULT_OUT, DEFAULT_OUT_QUICK = "out", "out_quick"
# Files that only a full run of ``all`` writes; ``all --quick`` refuses a directory that holds one.
FULL_ONLY_OUTPUTS = ("sector3_count.json", "sector3_gap.json", "selftest.log", "check.log")

ITEM_TEXT = {
    "N1": "(N1) for every G in [0, 1/50], E_3(.;G) has exactly one zero, counted with multiplicity, "
          "in {Re lambda >= 9/200}",
    "N2": "(N2) for every G in [0, 1/50], E_3(.;G) has no zero in the closed strip "
          "{9/200 <= Re lambda <= 211/2500}",
    "N3": "(N3) for m in {6, 9}: e^{m a_0} X_m + eps_* < 9/100",
}


class Logger:
    def __init__(self, path=None, quiet=False):
        self.f = open(path, "w", newline="\n") if path else None
        self.quiet = quiet

    def __call__(self, s):
        if not self.quiet:
            print(s, flush=True)
        if self.f:
            self.f.write(s + "\n")
            self.f.flush()

    def close(self):
        if self.f:
            self.f.close()


def _ensure(out):
    os.makedirs(out, exist_ok=True)
    return out


# ---------------------------------------------------------------- commands
def cmd_env(a):
    ref, msgs = envmod.verify(a.allow_other_flint)
    d = envmod.describe()
    for m in msgs:
        print(m)
    print(json.dumps(d, indent=1))
    print("reference environment" if ref else "NON-REFERENCE environment")
    return 0


def run_constants(out, log=print):
    from . import constants
    from .sector3 import dump_json
    from .data import data_strings
    t = time.time()
    checks = constants.run_checks()
    for c in checks:
        log(f"[{c['method']}] {c['id']:8s} {'TRUE ' if c['passed'] else 'FALSE'} {c['statement']}"
            + (f"  ({c['value']})" if c["value"] else ""))
    ok = all(c["passed"] for c in checks)
    log("ALL TRUE" if ok else "SOME CHECK FAILED")
    obj = {"format": "ringcert-constants-1", "data": data_strings(), "checks": checks,
           "summary": constants.summary(checks)}
    dump_json(obj, os.path.join(out, "constants.json"))
    return ok, checks, time.time() - t


def cmd_constants(a):
    envmod.verify(a.allow_other_flint)
    out = _ensure(a.out)
    log = Logger(os.path.join(out, "constants.log"))
    ok, _, _ = run_constants(out, log)
    log.close()
    return 0 if ok else 1


def run_sector3(item, a, log, only=None):
    from . import sector3
    cells = a.cells if getattr(a, "cells", None) else DEFAULT_CELLS[item]
    search = getattr(a, "search", False)
    result, meta = sector3.run(item, a.jobs, cells_file=None if search else cells, search=search, log=log, only=only)
    if not search:
        meta["cells_file"] = os.path.basename(cells)
    name = OUTNAME[item] + ("_quick" if only is not None else "")
    sector3.dump_json(result, os.path.join(a.out, name + ".json"))
    return result, meta


def cmd_sector3(item):
    def f(a):
        from . import results
        envmod.verify(a.allow_other_flint)
        out = _ensure(a.out)
        log = Logger(os.path.join(out, OUTNAME[item] + ".log"))
        result, meta = run_sector3(item, a, log)
        # the exact checks of the result object (coverage, windings, rectangle shapes, data), as in 'check'
        chk = results.check_sector3(result, item)
        for name, passed, detail in chk:
            if not passed:
                log(results.line(name, passed, detail))
        passed = bool(result["ok"] and result["gapfree"]) and results.verdict(chk)
        log(f"{item}: {'CERTIFIED' if passed else 'NOT CERTIFIED'} (run flags and exact checks of the result)")
        log.close()
        return 0 if passed else 1
    return f


def cmd_cell(a):
    """Re-certify one cell of a certificate file (spot check)."""
    envmod.verify(a.allow_other_flint)
    from . import sector3
    item = "N1'" if a.which == "count" else "N2'"
    cells = a.cells if a.cells else DEFAULT_CELLS[item]
    result, meta = sector3.run(item, 1, cells_file=cells, search=False, only=[a.index])
    for c in result["cells"]:
        print(json.dumps(c))
    ok = result["ok"]          # includes winding 1, no failed sub-cell, and the rectangle shape (sector3.rectangle_ok)
    print(f"cell {a.index} of {os.path.basename(cells)}: {'CERTIFIED, winding 1' if ok else 'NOT CERTIFIED'} "
          f"({meta['seconds']} s)")
    return 0 if ok else 1


def cmd_check(a):
    from . import results
    ok, res = results.check(a.dir, envmod.module_hashes())
    for name, passed, detail in res:
        print(results.line(name, passed, detail))
    print("CHECK: ALL TRUE" if ok else "CHECK: SOME FALSE")
    return 0 if ok else 1


def cmd_compare(a):
    from . import results
    same, lines = results.compare(a.dir, a.ref)
    for s in lines:
        print(s)
    print("identical to the reference outputs" if same else
          "NOT identical to the reference outputs (diagnostic only; see README, 'Interpreting the outputs')")
    return 0 if same else 1


def _run_script(path, args, log):
    env = dict(os.environ)
    env["PYTHONPATH"] = os.path.join(ROOT, "src") + (os.pathsep + env["PYTHONPATH"] if env.get("PYTHONPATH") else "")
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    p = subprocess.run([sys.executable, path] + list(args), env=env, capture_output=True, text=True, cwd=ROOT)
    for line in (p.stdout + p.stderr).splitlines():
        log(line)
    return p.returncode


def run_selftest(log):
    path = os.path.join(ROOT, "tests", "run_tests.py")
    if not os.path.exists(path):
        log("selftest: tests/ not found (run from a source checkout)")
        return 2
    return _run_script(path, [], log)


def cmd_selftest(a):
    out = _ensure(a.out)
    log = Logger(os.path.join(out, "selftest.log"))
    rc = run_selftest(log)
    log.close()
    return 0 if rc == 0 else 1


def cmd_validate(a):
    out = _ensure(a.out)
    log = Logger(os.path.join(out, "validate.log"))
    vdir = os.path.join(ROOT, "validation")
    scripts = [("arb_semantics.py", []), ("independent_winding.py", ["--jobs", str(a.jobs)]),
               ("sharpness.py", ["--jobs", str(a.jobs)]),
               ("known_windings.py", ["--jobs", str(a.jobs)] + (["--full"] if a.full else []))]
    bad = 0
    for s, args in scripts:
        log(f"==== validation/{s} {' '.join(args)}")
        rc = _run_script(os.path.join(vdir, s), args, log)
        log(f"==== {s}: {'PASS' if rc == 0 else 'FAIL'}")
        bad += rc != 0
    log("VALIDATION: all scripts passed" if bad == 0 else f"VALIDATION: {bad} script(s) failed")
    log.close()
    return 0 if bad == 0 else 1


def holds_full_run(out):
    """True if the directory ``out`` holds an output of a full (not quick) run of ``all``."""
    if any(os.path.exists(os.path.join(out, fn)) for fn in FULL_ONLY_OUTPUTS):
        return True
    p = os.path.join(out, "summary.json")
    if not os.path.exists(p):
        return False
    try:
        with open(p) as f:
            return json.load(f).get("quick") is not True
    except (OSError, ValueError, AttributeError):
        return True                              # unreadable summary: do not clear it


def cmd_all(a):
    from . import results
    from .sector3 import dump_json
    from .data import data_strings
    t0 = time.time()
    if a.out is None:
        a.out = DEFAULT_OUT_QUICK if a.quick else DEFAULT_OUT
    ref, msgs = envmod.verify(a.allow_other_flint)
    if a.quick and holds_full_run(a.out):
        print(f"ringcert: error: {a.out} holds the outputs of a full run, which --quick would delete; "
              f"use another directory (default {DEFAULT_OUT_QUICK}) or remove them first", file=sys.stderr)
        return 2
    out = _ensure(a.out)
    for fn in ALL_OUTPUTS:                       # invalidate the outputs of any earlier run
        p = os.path.join(out, fn)
        if os.path.exists(p):
            os.remove(p)
    log = Logger(os.path.join(out, "all.log"))
    for m in msgs:
        log(m)
    env = envmod.describe()
    log(f"ringcert {__version__}; python {env['python']}; python-flint {env['python_flint']}; "
        f"FLINT {env['flint']}; {env['platform']}; {a.jobs} processes"
        + ("" if ref else "; NON-REFERENCE ENVIRONMENT"))
    if a.quick:
        log("QUICK MODE: smoke test only. THIS IS NOT A VERIFICATION.")
    summary = {"format": "ringcert-summary-1", "package_version": __version__, "quick": bool(a.quick),
               "reference_environment": ref, "environment": env, "data": data_strings(),
               "complete": False, "all_pass": False, "steps": [], "items": []}
    dump_json(summary, os.path.join(out, "summary.json"))   # provisional: records a run that has not passed

    # 1. exact checks
    log("== constants (exact rational checks: (N3), Lemmas A.1 and A.2, data)")
    lc = Logger(os.path.join(out, "constants.log"), quiet=True)
    cok, checks, ct = run_constants(out, lambda s: (lc(s), log("   " + s)))
    lc.close()
    summary["steps"].append({"step": "constants", "passed": cok, "seconds": round(ct, 1), "output": "constants.json"})
    byid = {c["id"]: c for c in checks}

    # 2. unit tests
    st_ok = True
    if not a.no_selftest and not a.quick:
        log("== selftest (unit, known-answer and failure-path tests)")
        t = time.time()
        ls = Logger(os.path.join(out, "selftest.log"), quiet=True)
        rc = run_selftest(lambda s: (ls(s), log("   " + s) if (s.startswith("tests:") or "FAIL" in s) else None))
        ls.close()
        st_ok = rc == 0
        summary["steps"].append({"step": "selftest", "passed": st_ok, "seconds": round(time.time() - t, 1),
                                 "output": "selftest.log"})
    else:
        log("== selftest SKIPPED (" + ("--quick" if a.quick else "--no-selftest") + ")")
        summary["steps"].append({"step": "selftest", "passed": None, "skipped": True})

    # 3-4. sector 3
    sec = {}
    for item in ("N1'", "N2'"):
        log(f"== {OUTNAME[item]} ({item})")
        ls = Logger(os.path.join(out, OUTNAME[item] + ".log"), quiet=True)
        only = None
        if a.quick:
            only = [0, 1] if item == "N1'" else list(range(10))
        result, meta = run_sector3(item, a, lambda s: (ls(s), log("   " + s)), only=only)
        ls.close()
        sec[item] = result
        summary["steps"].append({"step": OUTNAME[item], "passed": bool(result["ok"] and result["gapfree"]),
                                 "seconds": meta["seconds"], "output": OUTNAME[item] + ".json", "mode": meta["mode"],
                                 "cells_file": meta["cells_file"]})

    # 5. exact check of the outputs
    if a.quick:
        chk_ok, chk = False, []
    else:
        log("== check (exact re-check of the outputs, Fraction arithmetic only)")
        summary["outputs_sha256"] = {fn: results.sha256_file(os.path.join(out, fn)) for fn in results.OUTPUTS}
        dump_json(summary, os.path.join(out, "summary.json"))   # still provisional; check reads the hashes
        chk_ok, chk = results.check(out, envmod.module_hashes(), in_progress=True)
        lk = Logger(os.path.join(out, "check.log"), quiet=True)
        for name, passed, detail in chk:
            s = results.line(name, passed, detail)
            lk(s)
            log("   " + s)
        lk.close()
        summary["steps"].append({"step": "check", "passed": chk_ok, "output": "check.log"})

    # items
    def allp(ids):
        return all(byid[i]["passed"] for i in ids)

    n3_ok = allp(["D3", "D4", "D5", "D6.6", "D6.9", "N3.6", "N3.9"])
    lemmaA2_ok = allp(["LB1", "LB2", "LB3", "LB4", "LB5"])      # constants of Lemma A.2 of the paper
    lemmaA1_ok = allp(["LA", "D1", "D3"])                      # constants of Lemma A.1 of the paper
    r1, r2 = sec["N1'"], sec["N2'"]

    def coverage(r):
        return [r["cells"][0]["G"][0], r["cells"][-1]["G"][1]] if r["cells"] else None
    n1p = bool(r1["ok"] and r1["gapfree"]) and not a.quick
    n2p = bool(r2["ok"] and r2["gapfree"]) and not a.quick
    n1_ok = n1p and lemmaA1_ok and lemmaA2_ok and byid["D2"]["passed"] and chk_ok
    n2_ok = n1_ok and n2p
    summary["items"] = [
        {"id": "N1", "statement": ITEM_TEXT["N1"], "status": "PASS" if n1_ok else ("NOT_CERTIFIED" if a.quick else "FAIL"),
         "evidence": {"N1'": {"cells": r1["ncells"], "coverage": coverage(r1),
                              "rectangle": ["9/200", "3", "-5", "3"], "windings": sorted(set(str(c["winding"]) for c in r1["cells"])),
                              "ambiguous": r1["ambiguous"], "failed": len(r1["failed"]), "segments": r1["nseg"],
                              "evaluations": r1["nevals"], "output": "sector3_count.json"},
                      "lemma_A1": "LA: TV_end/(3e^-50) <= " + byid["LA"]["value"].split("<= ")[-1],
                      "lemma_A2": byid["LB2"]["value"], "G_range": "d > 1/50: " + byid["D2"]["value"]}},
        {"id": "N2", "statement": ITEM_TEXT["N2"], "status": "PASS" if n2_ok else ("NOT_CERTIFIED" if a.quick else "FAIL"),
         "evidence": {"N2'": {"cells": r2["ncells"], "coverage": coverage(r2), "left_edge": "211/2500",
                              "windings": sorted(set(str(c["winding"]) for c in r2["cells"])),
                              "ambiguous": r2["ambiguous"], "failed": len(r2["failed"]), "segments": r2["nseg"],
                              "evaluations": r2["nevals"], "output": "sector3_gap.json"}, "uses": "N1"}},
        {"id": "N3", "statement": ITEM_TEXT["N3"], "status": "PASS" if n3_ok else "FAIL",
         "evidence": {"m=6": byid["N3.6"]["value"], "m=9": byid["N3.9"]["value"], "threshold": "9/200 (half of 9/100)",
                      "arb_cross_check": [byid["N3.6.A"]["value"], byid["N3.9.A"]["value"]], "output": "constants.json"}},
    ]
    all_pass = (not a.quick) and n1_ok and n2_ok and n3_ok and st_ok and cok and chk_ok
    summary["complete"] = True
    summary["all_pass"] = all_pass
    summary["reference_verification"] = bool(all_pass and ref)
    summary["seconds"] = round(time.time() - t0, 1)
    dump_json(summary, os.path.join(out, "summary.json"))   # final (written atomically)
    log("== summary")
    for it in summary["items"]:
        log(f"   {it['id']}: {it['status']}  {it['statement']}")
    if a.quick:
        log("QUICK MODE FINISHED: NOT A VERIFICATION (partial cell lists; outputs *_quick.json)")
        rc = 1
    else:
        log(f"ALL PASS: {all_pass}" + ("" if ref else " [NON-REFERENCE ENVIRONMENT]")
            + f"   (total {time.time()-t0:.0f} s; outputs in {os.path.basename(os.path.abspath(out))}/)")
        if all_pass and not ref:
            log(f"NON-REFERENCE ENVIRONMENT (python-flint {env['python_flint']} / FLINT {env['flint']}): this is not "
                f"the reference verification; the results hold relative to that FLINT version")
        rc = 0 if all_pass else 1
    log.close()
    return rc


def cmd_export(a):
    """Write a certificate file from a result file (used to regenerate certificates/ after --search)."""
    from fractions import Fraction as F
    from . import sector3
    with open(a.result) as f:
        J = json.load(f)
    item = J["item"]
    cells = [(F(c["G"][0]), F(c["G"][1])) for c in J["cells"]]
    rects = [tuple(F(v) for v in c["rect"]) for c in J["cells"]]
    params = sector3.COUNT_PARAMS if item == "N1'" else sector3.GAP_PARAMS
    sector3.dump_json(sector3.certificate_object(item, cells, rects, params), a.output)
    print(f"wrote {len(cells)} cells for {item}")
    return 0


# ---------------------------------------------------------------- parser
def build_parser():
    p = argparse.ArgumentParser(prog="ringcert", description="Verification of (N1) and (N2), and exact check of (N3), "
                                "of the numerical hypothesis (N).")
    p.add_argument("--version", action="version", version=f"ringcert {__version__}")
    sub = p.add_subparsers(dest="cmd", required=True)

    def common(sp, jobs=False, out=True):
        sp.add_argument("--allow-other-flint", action="store_true",
                        help="run with a python-flint/FLINT other than 0.9.0/3.6.0 (results marked non-reference)")
        if out:
            sp.add_argument("--out", default=DEFAULT_OUT, help="output directory (default ./out)")
        if jobs:
            sp.add_argument("--jobs", type=int, default=max(1, min(8, os.cpu_count() or 1)),
                            help="number of worker processes (default min(8, cores))")

    s = sub.add_parser("all", help="everything: constants, selftest, sector3-count, sector3-gap, check")
    common(s, jobs=True, out=False)
    s.add_argument("--out", default=None,
                   help="output directory, cleared first (default ./out, or ./out_quick with --quick)")
    s.add_argument("--quick", action="store_true",
                   help="smoke test on a few cells (NOT a verification); refuses a directory holding a full run")
    s.add_argument("--no-selftest", action="store_true", help="skip the unit tests")
    s.set_defaults(func=cmd_all)
    s = sub.add_parser("env", help="print and check the environment")
    common(s, out=False)
    s.set_defaults(func=cmd_env)
    s = sub.add_parser("constants", help="(N3), constants of Lemmas A.1 and A.2, data hypotheses (exact rationals)")
    common(s)
    s.set_defaults(func=cmd_constants)
    for name, item, h in (("sector3-count", "N1'", "(N1'): winding 1 on R_A for every G (zero count)"),
                          ("sector3-gap", "N2'", "(N2'): winding 1 on rectangles with left edge 211/2500 (gap)")):
        s = sub.add_parser(name, help=h)
        common(s, jobs=True)
        s.add_argument("--cells", help="certificate file (default: the shipped one in certificates/)")
        s.add_argument("--search", action="store_true", help="regenerate the cell list (and placement) instead")
        s.set_defaults(func=cmd_sector3(item))
    s = sub.add_parser("cell", help="re-certify one cell of a certificate file")
    common(s, out=False)
    s.add_argument("which", choices=["count", "gap"])
    s.add_argument("index", type=int)
    s.add_argument("--cells", help="certificate file (default: the shipped one)")
    s.set_defaults(func=cmd_cell)
    s = sub.add_parser("check", help="exact re-check of an output directory (Fraction arithmetic)")
    s.add_argument("dir", nargs="?", default="out")
    s.set_defaults(func=cmd_check)
    s = sub.add_parser("compare", help="compare an output directory with the reference outputs")
    s.add_argument("dir", nargs="?", default="out")
    s.add_argument("ref", nargs="?", default=os.path.join(ROOT, "expected"))
    s.set_defaults(func=cmd_compare)
    s = sub.add_parser("selftest", help="run the unit tests")
    common(s)
    s.set_defaults(func=cmd_selftest)
    s = sub.add_parser("validate", help="run the slower independent validation scripts")
    common(s, jobs=True)
    s.add_argument("--full", action="store_true", help="include the slow known-winding failure case (about 8 min)")
    s.set_defaults(func=cmd_validate)
    s = sub.add_parser("export-certificate", help="write a certificate file from a result file")
    s.add_argument("result")
    s.add_argument("output")
    s.set_defaults(func=cmd_export)
    return p


def main(argv=None):
    a = build_parser().parse_args(argv)
    try:
        envmod.refuse_optimized()
        return a.func(a)
    except envmod.EnvironmentRefused as exc:
        print(f"ENVIRONMENT REFUSED: {exc}", file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        return 3
    except Exception:
        traceback.print_exc()
        return 3
