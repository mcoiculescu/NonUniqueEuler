"""The exact output checker must reject tampered outputs.

A well-formed result object is synthesized from each shipped certificate file (every cell with
winding 1); the checker must accept it, and must reject each of the following tamperings: a gap
between cells, an overlap, a reversed G-cell [b, a], a winding 0 or 2, a winding given as the JSON
values true, 1.0 or "1" instead of the integer 1, an ambiguous indicator, a perturbed a_0, a left edge
0.0845 instead of 211/2500, a degenerate or reversed (negatively oriented) rectangle, a rectangle
leaving R_A, a last endpoint 1/50 instead of G_MAX, a rectangle different from R_A, a partial run, a
failed sub-cell, and a dropped cell.  The rectangle rule of the certification driver
(``sector3.rectangle_ok``) must accept the shipped rectangles and reject the same rectangle tamperings."""
import copy
import json
import os
from fractions import Fraction as F

from testlib import Checks, ROOT
from ringcert import results, sector3
from ringcert.data import data_strings


def synth(item):
    fn = "sector3_count_cells.json" if item == "N1'" else "sector3_gap_cells.json"
    with open(os.path.join(ROOT, "certificates", fn)) as f:
        C = json.load(f)
    cells = [dict(G=c["G"], rect=c["rect"], winding=1, nseg=10, ambiguous=0, nN=2, nind=2, nevals=12, level=0)
             for c in C["cells"]]
    return {"format": "ringcert-result-1", "item": item, "statement": "", "mode": "certificate", "partial": False,
            "sector": 3, "prec": 128, "grid": {"h": "2^-8", "N": 16}, "data": data_strings(), "parameters": {},
            "expected_winding": 1, "ok": True, "gapfree": True, "failed": [], "ncells": len(cells),
            "nseg": 10 * len(cells), "nevals": 12 * len(cells), "ambiguous": 0, "cells": cells}


def passes(J, item):
    return all(ok for _, ok, _ in results.check_sector3(J, item))


def test_checker_accepts_and_rejects():
    c = Checks("checker: accepts well-formed outputs, rejects tampered ones")
    for item in ("N1'", "N2'"):
        J = synth(item)
        c(passes(J, item), f"{item}: well-formed synthetic output accepted")

        def tampered(f):
            K = copy.deepcopy(J)
            f(K)
            return K
        cases = {
            "gap between cells": lambda K: K["cells"][3]["G"].__setitem__(0, str(F(K["cells"][3]["G"][0]) + F(1, 10 ** 30))),
            "overlap": lambda K: K["cells"][3]["G"].__setitem__(0, str(F(K["cells"][3]["G"][0]) - F(1, 10 ** 30))),
            "winding 0": lambda K: K["cells"][5].__setitem__("winding", 0),
            "winding 2": lambda K: K["cells"][5].__setitem__("winding", 2),
            "winding true": lambda K: K["cells"][5].__setitem__("winding", True),
            "winding 1.0": lambda K: K["cells"][5].__setitem__("winding", 1.0),
            "winding '1'": lambda K: K["cells"][5].__setitem__("winding", "1"),
            "reversed G-cell [b, a]": lambda K: K["cells"][4].__setitem__("G", [K["cells"][4]["G"][1], K["cells"][4]["G"][0]]),
            "ambiguous indicator": lambda K: (K["cells"][5].__setitem__("ambiguous", 1), K.__setitem__("ambiguous", 1)),
            "perturbed a0": lambda K: K["data"].__setitem__("a0", str(F(K["data"]["a0"]) + F(1, 2 ** 60))),
            "last endpoint 1/50": lambda K: K["cells"][-1]["G"].__setitem__(1, "1/50"),
            "partial run": lambda K: K.__setitem__("partial", True),
            "failed sub-cell": lambda K: K.__setitem__("failed", [["0", "1/1000"]]),
            "dropped cell": lambda K: (K["cells"].pop(7), K.__setitem__("ncells", K["ncells"] - 1),
                                       K.__setitem__("nseg", K["nseg"] - 10)),
        }
        if item == "N2'":
            cases["left edge 0.0845"] = lambda K: K["cells"][9]["rect"].__setitem__(0, "169/2000")
            cases["degenerate rectangle"] = lambda K: K["cells"][9]["rect"].__setitem__(1, K["cells"][9]["rect"][0])
            cases["reversed rectangle"] = lambda K: K["cells"][9].__setitem__("rect", reversed_rect(K["cells"][9]["rect"]))
            cases["rectangle leaving R_A"] = lambda K: K["cells"][9]["rect"].__setitem__(1, "4")
        else:
            cases["rectangle not R_A"] = lambda K: K["cells"][2]["rect"].__setitem__(0, "1/20")
            cases["rectangle [1/10,3]x[-5,3]"] = lambda K: K["cells"][2].__setitem__("rect", ["1/10", "3", "-5", "3"])
        for name, f in cases.items():
            c(not passes(tampered(f), item), f"{item}: tampering '{name}' rejected")
    c.finish()


def reversed_rect(r):
    """[x0, 2 x0 - x1] x [y1, y0]: left edge x0 kept, but x1 < x0 and y1 < y0."""
    x0, x1, y0, y1 = (F(v) for v in r)
    return [str(x0), str(2 * x0 - x1), str(y1), str(y0)]


def test_driver_rectangle_rule():
    c = Checks("certification driver: rectangle rule")
    for item, fn in (("N1'", "sector3_count_cells.json"), ("N2'", "sector3_gap_cells.json")):
        with open(os.path.join(ROOT, "certificates", fn)) as f:
            C = json.load(f)
        rects = [tuple(F(v) for v in x["rect"]) for x in C["cells"]]
        c(all(sector3.rectangle_ok(item, r) for r in rects), f"{item}: shipped rectangles accepted")
    r = tuple(F(v) for v in C["cells"][9]["rect"])
    bad = {"left edge 169/2000": (F(169, 2000),) + r[1:], "degenerate": (r[0], r[0], r[2], r[3]),
           "reversed": tuple(F(v) for v in reversed_rect([str(v) for v in r])), "leaving R_A": (r[0], F(4), r[2], r[3])}
    for name, rb in bad.items():
        c(not sector3.rectangle_ok("N2'", rb), f"N2': rectangle '{name}' rejected by the driver")
    for name, rb in {"[1/20,3]x[-5,3]": (F(1, 20), F(3), F(-5), F(3)), "[1/10,3]x[-5,3]": (F(1, 10), F(3), F(-5), F(3)),
                     "R_A reversed": (F(3), F(9, 200), F(3), F(-5))}.items():
        c(not sector3.rectangle_ok("N1'", rb), f"N1': rectangle '{name}' rejected by the driver")
    c.finish()
