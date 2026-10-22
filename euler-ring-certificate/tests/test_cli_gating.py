"""How ``ringcert all``, ``ringcert check`` and the per-item commands turn runs into PASS.

The two sector-3 computations are replaced by canned results built from the reference outputs in
``expected/`` (the real computations take minutes; their soundness is tested elsewhere).  Then:
  * the unmodified reference results give exit status 0, ``all_pass`` true, items PASS, and a
    passing ``check``;
  * each of the following makes ``all`` exit 1 with ``all_pass`` false and makes ``check`` fail: a cell
    with winding 2 whose run flags were left true, a run with ``ok`` false, an (N2') rectangle with
    reversed orientation, an (N1') rectangle different from R_A, a reversed G-cell [b, a], and a winding
    given as ``true`` or ``1.0``;
  * a passing run followed by a run into the same directory that crashes during (N2') exits 3 and
    leaves neither a PASS summary nor outputs of the earlier run, and ``check`` then fails;
  * a changed output file after a passing run makes ``check`` fail (recorded output hashes);
  * ``all --quick`` writes to ``out_quick`` by default, refuses a directory that holds a full run, and
    leaves that run unchanged;
  * ``--no-selftest`` is recorded in the summary, and a run in a non-reference environment is marked
    as such in the summary and in the log;
  * ``sector3-count`` and ``sector3-gap`` exit 1 on a result whose rectangles do not have the required
    shape, even if the run flags say otherwise;
  * every command refuses to run under ``python -O`` (``check`` included).
"""
import contextlib
import copy
import io
import json
import os
import subprocess
import sys
import tempfile
from fractions import Fraction as F

from testlib import Checks, ROOT, SRC
from ringcert import cli, results, sector3
from ringcert import environment as envmod

EXPECTED = os.path.join(ROOT, "expected")


def _load_expected():
    out = {}
    for item, fn in results.FILES.items():
        with open(os.path.join(EXPECTED, fn)) as f:
            out[item] = json.load(f)
    return out


def canned(mutate):
    """A replacement for sector3.run that returns the reference result of the item, after ``mutate``."""
    ref = _load_expected()

    def run(item, nproc, cells_file=None, search=False, log=print, only=None):
        J = copy.deepcopy(ref[item])
        mutate(item, J)
        return J, {"seconds": 0, "nproc": nproc, "mode": "certificate", "cells_file": cells_file}
    return run


def quiet_main(args):
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        rc = cli.main(args)
    return rc, buf.getvalue()


def run_all(out, mutate, extra=()):
    saved = sector3.run
    sector3.run = canned(mutate)
    try:
        rc, text = quiet_main(["all", "--no-selftest", "--jobs", "1", "--out", out] + list(extra))
    finally:
        sector3.run = saved
    p = os.path.join(out, "summary.json")
    S = None
    if os.path.exists(p):
        with open(p) as f:
            S = json.load(f)
    crc, ctext = quiet_main(["check", out])
    return rc, S, crc, text + ctext


def nothing(item, J):
    pass


def winding2(item, J):
    if item == "N2'":
        J["cells"][5]["winding"] = 2


def ok_false(item, J):
    if item == "N1'":
        J["ok"] = False


def reversed_rect(item, J):
    if item == "N2'":
        x0, x1, y0, y1 = (F(v) for v in J["cells"][7]["rect"])
        J["cells"][7]["rect"] = [str(x0), str(2 * x0 - x1), str(y1), str(y0)]


def not_RA(item, J):
    if item == "N1'":
        J["cells"][3]["rect"][2] = "-4"


def reversed_cell(item, J):
    if item == "N1'":
        a, b = J["cells"][3]["G"]
        J["cells"][3]["G"] = [b, a]


def winding_true(item, J):
    if item == "N1'":
        J["cells"][3]["winding"] = True


def winding_float(item, J):
    if item == "N1'":
        J["cells"][3]["winding"] = 1.0


def crash_in_gap(item, J):
    if item == "N2'":
        raise RuntimeError("simulated crash during (N2')")


def test_all_gating():
    c = Checks("ringcert all / check: gating of PASS")
    with tempfile.TemporaryDirectory() as d:
        out = os.path.join(d, "base")
        rc, S, crc, text = run_all(out, nothing)
        c(rc == 0 and S["all_pass"] is True and S["complete"] is True, f"reference results: all exits 0 ({rc})")
        c([i["status"] for i in S["items"]] == ["PASS"] * 3, "reference results: items PASS")
        c(crc == 0, f"reference results: check exits 0 ({crc})")
        c(S["reference_environment"] is True and S["reference_verification"] is True, "reference environment recorded")
        c({"step": "selftest", "passed": None, "skipped": True} in S["steps"] and "selftest SKIPPED" in text,
          "--no-selftest recorded in the summary and the log")
        c(sorted(S["outputs_sha256"]) == sorted(results.OUTPUTS), "output hashes recorded")

        # a changed output file after a passing run
        p = os.path.join(out, "sector3_gap.json")
        with open(p) as f:
            J = json.load(f)
        J["cells"][0]["nevals"] += 1
        sector3.dump_json(J, p)
        crc2, _ = quiet_main(["check", out])
        c(crc2 == 1, f"check fails when an output differs from the one recorded in summary.json ({crc2})")

        for name, mut in (("winding 2, flags left true", winding2), ("N1' ok false", ok_false),
                          ("N2' rectangle reversed", reversed_rect), ("N1' rectangle not R_A", not_RA),
                          ("N1' G-cell reversed", reversed_cell), ("winding true", winding_true),
                          ("winding 1.0", winding_float)):
            rc, S, crc, _ = run_all(os.path.join(d, "case"), mut)
            c(rc == 1 and S["all_pass"] is False, f"{name}: all exits 1 and all_pass false ({rc})")
            c(crc == 1, f"{name}: check exits 1 ({crc})")

        # a passing run, then a crashing run into the same directory
        out = os.path.join(d, "stale")
        rc, S, crc, _ = run_all(out, nothing)
        c(rc == 0 and crc == 0, "stale: first run passes")
        rc, S, crc, text = run_all(out, crash_in_gap)
        c(rc == 3, f"stale: the crashing run exits 3 ({rc})")
        c(S is not None and S["all_pass"] is False and S["complete"] is False,
          "stale: the summary left behind records an incomplete run that did not pass")
        c(not os.path.exists(os.path.join(out, "sector3_gap.json")), "stale: no (N2') output of the earlier run left")
        c(crc == 1, f"stale: check exits 1 after the crash ({crc})")

        # --quick never clears the outputs of a full run: its default directory is out_quick, and it
        # refuses a directory that holds a full run
        full = os.path.join(d, "out")
        rc, S, crc, _ = run_all(full, nothing)
        c(rc == 0 and crc == 0, "quick: the full run passes")
        before = snapshot(full)
        cwd, saved = os.getcwd(), sector3.run
        sector3.run = canned(nothing)
        try:
            os.chdir(d)
            q = ["all", "--quick", "--no-selftest", "--jobs", "1"]
            rc1, _ = quiet_main(q)
            rc2, _ = quiet_main(q)
            rc3, text3 = quiet_main(q + ["--out", "out"])
        finally:
            os.chdir(cwd)
            sector3.run = saved
        with open(os.path.join(d, "out_quick", "summary.json")) as f:
            SQ = json.load(f)
        c(rc1 == 1 and rc2 == 1 and SQ["quick"] is True and SQ["all_pass"] is False,
          f"quick: default directory out_quick, exit 1, repeatable ({rc1}, {rc2})")
        c(rc3 == 2 and "holds the outputs of a full run" in text3, f"quick: refuses --out out ({rc3})")
        c(snapshot(full) == before, "quick: the full run in out is unchanged")
        crc, _ = quiet_main(["check", full])
        c(crc == 0, f"quick: check of the full run still exits 0 ({crc})")
    c.finish()


def snapshot(directory):
    out = {}
    for fn in sorted(os.listdir(directory)):
        with open(os.path.join(directory, fn), "rb") as f:
            out[fn] = f.read()
    return out


def test_non_reference_marked():
    c = Checks("ringcert all: a non-reference environment is marked")
    saved, saved_describe = envmod.verify, envmod.describe

    def describe():
        d = saved_describe()
        d["flint"] = "0.0.0"
        return d
    envmod.verify = lambda allow=False: (False, ["WARNING: simulated non-reference environment"])
    envmod.describe = describe
    try:
        with tempfile.TemporaryDirectory() as d:
            out = os.path.join(d, "nonref")
            rc, S, crc, text = run_all(out, nothing, ["--allow-other-flint"])
            with open(os.path.join(out, "all.log")) as f:
                log = f.read()
    finally:
        envmod.verify, envmod.describe = saved, saved_describe
    c(rc == 0 and S["all_pass"] is True, f"all passes ({rc})")
    c(S["reference_environment"] is False and S["reference_verification"] is False,
      "summary: reference_environment and reference_verification false")
    c("ALL PASS: True [NON-REFERENCE ENVIRONMENT]" in log and "not the reference verification" in log,
      "the log marks the PASS as non-reference")
    c.finish()


def test_per_item_commands_check_rectangles():
    c = Checks("sector3-count / sector3-gap: exit status requires the exact checks of the result")
    saved = sector3.run
    try:
        with tempfile.TemporaryDirectory() as d:
            for cmd, mut, expect in (("sector3-count", nothing, 0), ("sector3-gap", nothing, 0),
                                     ("sector3-count", not_RA, 1), ("sector3-gap", reversed_rect, 1),
                                     ("sector3-gap", winding2, 1)):
                sector3.run = canned(mut)
                rc, _ = quiet_main([cmd, "--jobs", "1", "--out", os.path.join(d, "o")])
                c(rc == expect, f"{cmd} with {mut.__name__}: exit {rc}, expected {expect}")
    finally:
        sector3.run = saved
    c.finish()


def test_optimize_refused_everywhere():
    c = Checks("every command refuses python -O")
    env = dict(os.environ)
    env["PYTHONPATH"] = SRC
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    code = "import sys\nfrom ringcert.cli import main\nsys.exit(main(sys.argv[1:]))\n"
    for args in (["check", EXPECTED], ["compare", EXPECTED, EXPECTED]):
        p = subprocess.run([sys.executable, "-O", "-c", code] + args, env=env, capture_output=True, text=True)
        c(p.returncode == 2 and "python -O" in p.stderr, f"{args[0]} under -O: exit {p.returncode}")
    c.finish()

