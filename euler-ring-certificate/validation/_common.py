"""Shared helpers for the validation scripts (run from the source tree; see README)."""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SRC = os.path.join(ROOT, "src")
if SRC not in sys.path:
    sys.path.insert(0, SRC)

_grid = None


def init_worker():
    """Pool initializer: build the integration grid once per process."""
    global _grid
    from ringcert import balls, evans
    balls.set_prec(128)
    _grid = evans.Grid(8, 16)


def grid():
    return _grid
