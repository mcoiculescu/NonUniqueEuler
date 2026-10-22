"""The shipped certificate files: structure, exact coverage, rectangles, and agreement of the cell
lists with the rules of the search mode (so the files contain nothing but what the rules produce,
except the rectangle placement of the gap certificate, which is a heuristic and needs no
justification)."""
import json
import os
from fractions import Fraction as F

from testlib import Checks, ROOT
from ringcert import sector3
from ringcert.data import G_MAX_Q, RECT_A, SIGMA_GAP, data_strings


def load(fn):
    with open(os.path.join(ROOT, "certificates", fn)) as f:
        return json.load(f)


def partition(cells):
    cov = sorted(cells)
    return cov[0][0] == 0 and cov[-1][1] == G_MAX_Q and all(cov[i][1] == cov[i + 1][0] for i in range(len(cov) - 1)) \
        and all(a < b for a, b in cov)


def test_count_certificate():
    c = Checks("certificate files: sector3_count_cells.json")
    C = load("sector3_count_cells.json")
    cells = [(F(x["G"][0]), F(x["G"][1])) for x in C["cells"]]
    c(C["item"] == "N1'" and C["data"] == data_strings(), "item and data")
    c(len(cells) == 25 and partition(cells), "25 cells partitioning [0, G_MAX]")
    c(all(tuple(F(v) for v in x["rect"]) == RECT_A for x in C["cells"]), "every rectangle is R_A")
    # every cell is one of the 20 equal cells or one of its halves
    base = sector3.count_cells_search()
    halves = [h for (a, b) in base for h in ((a, (a + b) / 2), ((a + b) / 2, b))]
    c(all(x in base or x in halves for x in cells), "cells are the search-mode cells or their halves")
    c(C["parameters"] == {k: (str(v) if isinstance(v, F) else v) for k, v in sector3.COUNT_PARAMS.items()},
      "parameters recorded")
    c.finish()


def test_gap_certificate():
    c = Checks("certificate files: sector3_gap_cells.json")
    C = load("sector3_gap_cells.json")
    cells = [(F(x["G"][0]), F(x["G"][1])) for x in C["cells"]]
    rects = [tuple(F(v) for v in x["rect"]) for x in C["cells"]]
    c(C["item"] == "N2'" and C["data"] == data_strings(), "item and data")
    c(len(cells) == 236 and partition(cells), "236 cells partitioning [0, G_MAX]")
    c(all(r[0] == SIGMA_GAP and r[0] < r[1] and r[2] < r[3] for r in rects), "left edges 211/2500, nondegenerate")
    c(cells == sector3.gap_cells_search(), "cells equal the graded cells of the search mode")
    c.finish()
