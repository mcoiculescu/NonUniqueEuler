"""Minimal test helpers: plain Python, also usable under pytest.

Each test function creates ``c = Checks(name)``, calls ``c(condition, message)`` for every check and
ends with ``c.finish()``, which raises AssertionError if any check failed.  ``run_tests.py`` runs every
``test_*`` function of every ``test_*.py`` module and prints the total number of checks."""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SRC = os.path.join(ROOT, "src")
if SRC not in sys.path:
    sys.path.insert(0, SRC)

TOTAL = {"checks": 0, "failures": 0}


class Checks:
    def __init__(self, name):
        self.name, self.n, self.failed = name, 0, []

    def __call__(self, cond, msg):
        self.n += 1
        TOTAL["checks"] += 1
        if not cond:
            self.failed.append(msg)
            TOTAL["failures"] += 1
            print(f"FAIL [{self.name}]: {msg}", flush=True)

    def finish(self):
        print(f"{self.name}: {self.n} checks, {len(self.failed)} failures", flush=True)
        assert not self.failed, f"{len(self.failed)} failures in {self.name}"


def fixture(name):
    return os.path.join(HERE, "fixtures", name)
