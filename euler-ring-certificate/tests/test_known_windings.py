"""Known windings on small rectangles (the sign convention of the winding formula).

G-cell [0, 10^-4], where the sector-3 eigenvalue is lambda_*(G) ~ 0.1220 - 0.4171 i.  The certifier must
report winding 1 for [0.115, 0.13] x [-0.45, -0.40] (lambda_* inside) and winding 0 for
[0.115, 0.13] x [-0.40, -0.35] (lambda_* outside).  The larger cases, and a rectangle whose edge passes
through lambda_*(0) (which must not be certified), are in ``validation/known_windings.py``."""
from fractions import Fraction as F

from testlib import Checks
from ringcert import evans as ev, winding as wd


def test_small_known_windings():
    c = Checks("known windings (small rectangles)")
    g = ev.Grid(8, 16)
    cell = (F(0), F(1, 10000))
    for rect, expect in (((F("0.115"), F("0.13"), F("-0.45"), F("-0.40")), 1),
                         ((F("0.115"), F("0.13"), F("-0.40"), F("-0.35")), 0)):
        res, failed, nev = wd.certify_cell_adaptive(3, rect, cell, g, F(20), 16, 6000, 2)
        w = [r["winding"] for r in res]
        c(w == [expect] and not failed, f"rect {[str(v) for v in rect]}: expected [{expect}], obtained {w}")
    c.finish()
