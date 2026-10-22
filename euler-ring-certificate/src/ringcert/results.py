"""Exact re-check of the output files, and comparison with the reference outputs.

``check(out_dir)`` re-derives, with ``fractions.Fraction`` arithmetic on the JSON literals only (no
Arb, no floats), everything that the deductions (N1') => (N1) and (N1) + (N2') => (N2) need from the
sector-3 outputs, and re-runs the exact-rational checks of ``constants``.  It is independent of the
bookkeeping done during the runs (flags such as "ok" and "gapfree" are recomputed, not trusted).

Each line of the check is (name, passed, detail) with ``passed`` True or False, or None for a line that
records something that was not checked (printed as NOTE); the verdict is true only if no line is
False.  Integer fields (windings, counts) must be JSON integers: ``true`` or ``1.0`` is not 1.

``compare(out_dir, ref_dir)`` compares the certified cell lists with the shipped reference outputs
cell by cell.  It is diagnostic only: Arb is deterministic for a fixed FLINT version, so identical
results are expected with python-flint 0.9.0; a difference in counts with all windings equal to 1
and gap-free coverage is not a failure of the verification.
"""
import hashlib
import json
import os
from fractions import Fraction as F

from .data import DATA, G_MAX_Q, RECT_A, SIGMA_COUNT, SIGMA_GAP, G_TARGET

FILES = {"N1'": "sector3_count.json", "N2'": "sector3_gap.json"}
OUTPUTS = ("constants.json", "sector3_count.json", "sector3_gap.json")   # hashed in summary.json
CELL_FIELDS = ("G", "rect", "winding", "nseg", "ambiguous", "nN", "nind", "nevals", "level")


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        h.update(f.read())
    return h.hexdigest()


def is_int(x, value=None):
    """True if x is a JSON integer (not a boolean, not a float), equal to ``value`` if given."""
    return type(x) is int and (value is None or x == value)


def line(name, passed, detail=""):
    """The printed form of one line of the check."""
    tag = "NOTE " if passed is None else ("TRUE " if passed else "FALSE")
    return f"{tag} {name}" + (f"  ({detail})" if detail else "")


def verdict(res):
    """True if and only if no line of the check is False."""
    return all(passed is not False for _, passed, _ in res)


def check_sector3(J, item):
    """Exact checks of one sector-3 result object.  Returns a list of (name, passed, detail)."""
    res = []

    def rep(name, cond, detail=""):
        res.append((name, bool(cond), detail))

    rep(f"{item}: item and format", J.get("item") == item and J.get("format") == "ringcert-result-1")
    rep(f"{item}: not a partial run", J.get("partial") is False)
    rep(f"{item}: data equal the pinned data", all(F(J["data"][k]) == v for k, v in DATA.items()))
    rep(f"{item}: G_MAX = d > 1/50", F(J["data"]["Gmax"]) == F(J["data"]["d"]) == G_MAX_Q and G_MAX_Q > G_TARGET)
    rep(f"{item}: sector 3, expected winding 1", is_int(J["sector"], 3) and is_int(J["expected_winding"], 1))
    rep(f"{item}: no failed sub-cells", J["failed"] == [])
    cells = J["cells"]
    rep(f"{item}: every winding is 1 and no indicator is ambiguous",
        len(cells) > 0 and all(is_int(c["winding"], 1) and is_int(c["ambiguous"], 0) for c in cells),
        f"{len(cells)} cells")
    cov = sorted((F(c["G"][0]), F(c["G"][1])) for c in cells)
    gap = (len(cov) > 0 and cov[0][0] == 0 and cov[-1][1] == G_MAX_Q
           and all(cov[i][1] == cov[i + 1][0] for i in range(len(cov) - 1)) and all(a < b for a, b in cov))
    rep(f"{item}: the G-cells partition [0, G_MAX] (start 0, end G_MAX, consecutive, positive widths)", gap,
        f"coverage [{cov[0][0]}, {cov[-1][1]}]" if cov else "")
    rects = [tuple(F(v) for v in c["rect"]) for c in cells]
    if item == "N1'":
        rep("N1': every rectangle equals R_A = [9/200,3]x[-5,3]", all(r == RECT_A for r in rects))
    else:
        rep("N2': every left edge equals 211/2500", all(r[0] == SIGMA_GAP for r in rects))
        rep("N2': every rectangle has x0 < x1 and y0 < y1 (so x0 is its left edge and its boundary is traversed "
            "counterclockwise)", all(r[0] < r[1] and r[2] < r[3] for r in rects))
        rep("N2': 211/2500 > 9/200 (each rectangle lies in {Re lambda > 9/200})", SIGMA_GAP > SIGMA_COUNT)
        rep("N2': every rectangle lies inside R_A",
            all(r[0] >= RECT_A[0] and r[1] <= RECT_A[1] and r[2] >= RECT_A[2] and r[3] <= RECT_A[3] for r in rects))
    rep(f"{item}: totals consistent", all(is_int(c["nseg"]) for c in cells) and is_int(J["nseg"])
        and is_int(J["ncells"]) and is_int(J["ambiguous"])
        and sum(c["nseg"] for c in cells) == J["nseg"] and len(cells) == J["ncells"]
        and sum(c["ambiguous"] for c in cells) == J["ambiguous"], f"nseg {J['nseg']}, ncells {J['ncells']}")
    rep(f"{item}: recorded flags agree with the recomputation", J["ok"] is True and J["gapfree"] is True)
    return res


def check(out_dir, module_hashes=None, in_progress=False):
    """Exact check of an output directory.  Returns (all_passed, list of (name, passed, detail)).

    If ``module_hashes`` is given and the directory has a ``summary.json`` (written by ``ringcert
    all``), the check also requires that the SHA-256 recorded there for the modules and for the three
    output files equal those of the modules running now and of the files checked, and that the
    recorded reference-environment flag agrees with the recorded versions, and (unless ``in_progress``,
    which ``ringcert all`` passes for its own provisional summary) that the summary records a completed
    run that passed.  Without ``summary.json`` this is reported as NOTE (not checked)."""
    from . import constants
    res = []
    for item, fn in FILES.items():
        p = os.path.join(out_dir, fn)
        if not os.path.exists(p):
            res.append((f"{item}: output file {fn} present", False, ""))
            continue
        with open(p) as f:
            J = json.load(f)
        res += check_sector3(J, item)
    p = os.path.join(out_dir, "constants.json")
    if os.path.exists(p):
        with open(p) as f:
            C = json.load(f)
        rep_ok = all(c["passed"] for c in C["checks"])
        res.append(("constants: recorded checks all pass", rep_ok, f"{len(C['checks'])} checks"))
    else:
        res.append(("constants: output file constants.json present", False, ""))
    # re-run the exact-rational checks (Fraction only)
    fresh = [c for c in constants.run_checks() if c["method"] == "exact"]
    res.append(("constants: exact-rational checks re-run now, all pass", all(c["passed"] for c in fresh), f"{len(fresh)} checks"))
    if module_hashes is not None:
        res += check_summary(out_dir, module_hashes, in_progress)
    return verdict(res), res


def check_summary(out_dir, module_hashes, in_progress=False):
    """Provenance lines: summary.json against the modules running now and the output files."""
    from .environment import is_reference
    res = []
    p = os.path.join(out_dir, "summary.json")
    if not os.path.exists(p):
        res.append(("summary: provenance not checked (no summary.json; it is written only by 'ringcert all')",
                    None, ""))
        return res
    with open(p) as f:
        S = json.load(f)
    env = S.get("environment", {})
    res.append(("summary: recorded module sha256 equal the modules checking now",
                env.get("modules") == module_hashes, ""))
    rec = S.get("outputs_sha256")
    actual = {fn: sha256_file(os.path.join(out_dir, fn)) for fn in OUTPUTS if os.path.exists(os.path.join(out_dir, fn))}
    res.append(("summary: recorded sha256 of constants.json, sector3_count.json, sector3_gap.json equal the files "
                "checked", isinstance(rec, dict) and len(actual) == len(OUTPUTS) and rec == actual,
                "" if isinstance(rec, dict) else "no output hashes recorded: the run did not reach its check step"))
    ref = is_reference(env.get("python_flint"), env.get("flint"))
    res.append(("summary: recorded reference-environment flag agrees with the recorded versions",
                S.get("reference_environment") is ref, f"python-flint {env.get('python_flint')}, FLINT {env.get('flint')}"))
    if not ref:
        res.append(("summary: NON-REFERENCE environment; the results hold relative to the recorded FLINT version, "
                    "not the reference FLINT 3.6.0", None, ""))
    if not in_progress:
        res.append(("summary: the recorded run completed and passed (complete and all_pass are true)",
                    S.get("complete") is True and S.get("all_pass") is True, ""))
    return res


def compare(out_dir, ref_dir):
    """Cell-by-cell comparison with reference outputs.  Returns (identical, lines)."""
    lines, same = [], True
    for item, fn in list(FILES.items()) + [("constants", "constants.json")]:
        a, b = os.path.join(out_dir, fn), os.path.join(ref_dir, fn)
        if not (os.path.exists(a) and os.path.exists(b)):
            lines.append(f"{fn}: missing in one of the directories")
            same = False
            continue
        ha, hb = sha256_file(a), sha256_file(b)
        if ha == hb:
            lines.append(f"{fn}: byte-identical (sha256 {ha})")
            continue
        same = False
        with open(a) as f:
            A = json.load(f)
        with open(b) as f:
            B = json.load(f)
        if item == "constants":
            diff = [x["id"] for x, y in zip(A["checks"], B["checks"]) if x != y]
            lines.append(f"{fn}: differs; checks differing: {diff}")
            continue
        ka = {tuple(c["G"]): c for c in A["cells"]}
        kb = {tuple(c["G"]): c for c in B["cells"]}
        only_a, only_b = sorted(set(ka) - set(kb)), sorted(set(kb) - set(ka))
        nd = [g for g in ka if g in kb and any(ka[g].get(k) != kb[g].get(k) for k in CELL_FIELDS)]
        lines.append(f"{fn}: differs; cells only here {len(only_a)}, only in reference {len(only_b)}, "
                     f"common cells with different records {len(nd)}; totals here nseg={A['nseg']} nevals={A['nevals']}, "
                     f"reference nseg={B['nseg']} nevals={B['nevals']}")
    return same, lines
