"""No floating-point number on the certified path.

python-flint silently accepts Python floats, both in constructors (``arb(0.1)`` is the binary64 number
nearest to 0.1) and as operands (``arb(1) + 1/10`` adds that binary64 number), so this is checked
mechanically in three ways.
(1) Static: an AST scan of the certified modules finds no float or complex literal, no call of
    ``float``/``complex``, no import of math-like float libraries, no ``math`` function other than
    the exact integer/Fraction ones (factorial, ceil, floor), no true division of two integer literals
    (``1/10`` is a float) and no power with a negative literal exponent (``2 ** -3`` is a float).  A
    planted module with each of these must be flagged (failure-path self-test of the scanner).
(2) Dynamic, constructors: the ``arb``/``acb`` constructors used by the certified modules are replaced
    by guards that record a float or complex argument; an Evans evaluation and a winding
    classification must then run without tripping the guard.
(3) Dynamic, every operation: a copy of the package is rewritten so that the value of every binary
    operation, unary operation and call in the certified modules passes through a detector of float
    and complex values.  The exact checks, the cell lists, the certificate loading, the exact output
    checker, and a complete certification of one small rectangle (segments, bisection and indicators)
    are then run in a subprocess with that copy; no float or complex value may occur.  This also
    catches a float produced at run time, for example by ``/`` between two Python integers, and a float
    used as an operand of Arb arithmetic.  A planted ``arb(1) + n / 10`` must be detected.
"""
import ast
import json
import os
import subprocess
import sys
import tempfile
from fractions import Fraction as F

from testlib import Checks, SRC, ROOT

CERTIFIED = ["data.py", "balls.py", "evans.py", "winding.py", "sector3.py", "constants.py", "results.py"]
ALLOWED_MATH = {"factorial", "ceil", "floor"}
FORBIDDEN_IMPORTS = {"numpy", "scipy", "cmath", "decimal", "mpmath", "random"}


def _int_literal(node):
    """True for an int literal, possibly negated (``3``, ``-3``); booleans excluded."""
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
        node = node.operand
    return isinstance(node, ast.Constant) and type(node.value) is int


def _negative_literal(node):
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return _int_literal(node.operand) and node.operand.value > 0
    return isinstance(node, ast.Constant) and type(node.value) is int and node.value < 0


def scan(path):
    with open(path) as f:
        tree = ast.parse(f.read(), filename=path)
    bad = []
    for node in ast.walk(tree):
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div) and _int_literal(node.left) \
                and _int_literal(node.right):
            bad.append(f"true division of two integer literals at line {node.lineno}")
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Pow) and _negative_literal(node.right):
            bad.append(f"power with a negative literal exponent at line {node.lineno}")
        if isinstance(node, ast.Constant) and isinstance(node.value, (float, complex)):
            bad.append(f"float/complex literal {node.value!r} at line {node.lineno}")
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in ("float", "complex"):
            bad.append(f"call of {node.func.id} at line {node.lineno}")
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id == "math" \
                and node.attr not in ALLOWED_MATH:
            bad.append(f"math.{node.attr} at line {node.lineno}")
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            names = [a.name for a in node.names] if isinstance(node, ast.Import) else [node.module or ""]
            for n in names:
                if n.split(".")[0] in FORBIDDEN_IMPORTS:
                    bad.append(f"import {n} at line {node.lineno}")
    return bad


def test_static_scan():
    c = Checks("float-free: static scan")
    for fn in CERTIFIED:
        bad = scan(os.path.join(SRC, "ringcert", fn))
        c(not bad, f"{fn}: {bad}")
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "planted.py")
        with open(p, "w") as f:
            f.write("from flint import arb\nx = arb(0.1)\nimport math\ny = math.exp(2)\nz = float(3)\n"
                    "u = arb(1) + 1/10\nv = 2 ** -3\nw = -1 / 3\n")
        c(len(scan(p)) == 6, f"the scanner flags a planted float literal, math.exp, float(), 1/10, 2 ** -3 and -1/3: "
                             f"{scan(p)}")
    c.finish()


def test_dynamic_guard():
    c = Checks("float-free: constructor guard")
    import flint
    from ringcert import balls, evans as ev, winding as wd
    tripped = []

    def guard(ctor):
        def g(*args, **kw):
            for x in list(args) + list(kw.values()):
                if isinstance(x, (float, complex)):
                    tripped.append((ctor.__name__, x))
            return ctor(*args, **kw)
        return g
    mods = (balls, ev, wd)
    saved = [(m, m.__dict__.get("arb"), m.__dict__.get("acb")) for m in mods]
    try:
        for m in mods:
            if "arb" in m.__dict__:
                m.arb = guard(flint.arb)
            if "acb" in m.__dict__:
                m.acb = guard(flint.acb)
        g = ev.Grid(8, 16)
        E = ev.evans(wd.seg_box((F(1), F(0)), (F(1), F(1, 100))), wd.G_ball((F(0), F(1, 1000))), 3, g)
        c(E.is_finite(), "evaluation succeeded under the guard")
        c(wd.classify(E) in (1, 2), "segment classified under the guard")
    finally:
        for m, a, b in saved:
            if a is not None:
                m.arb = a
            if b is not None:
                m.acb = b
    c(not tripped, f"no float reached an arb/acb constructor: {tripped[:3]}")
    c.finish()


# ------------------------------------------------------------------ (3) every operation
DETECTOR = """
HITS = {}


def __ff_check__(value, module, line):
    if isinstance(value, (float, complex)):
        HITS.setdefault((module, line), repr(value))
    return value
"""

DRIVER = r"""
import json, os, sys
from fractions import Fraction as F
from ringcert import _ffdetect as K
from ringcert import constants, data, evans as ev, winding as wd, sector3, results
root, mode = sys.argv[1], sys.argv[2]
if mode == "planted":
    from ringcert import planted
    planted.f(data.SB_Q.denominator)
else:
    constants.run_checks()
    constants.summary(constants.run_checks())
    sector3.count_cells_search()
    sector3.gap_cells_search()
    for item, fn in (("N1'", "sector3_count_cells.json"), ("N2'", "sector3_gap_cells.json")):
        C, cells, rects = sector3.load_certificate(os.path.join(root, "certificates", fn))
        sector3._jobs(item, cells, rects)
        assert all(sector3.rectangle_ok(item, r) for r in rects)
    results.check(os.path.join(root, "expected"))
    g = ev.Grid(8, 16)
    rect = (F("0.115"), F("0.13"), F("-0.45"), F("-0.40"))
    res, failed, nev = wd.certify_cell_adaptive(3, rect, (F(0), F(1, 10000)), g, F(20), 16, 6000, 2)
    assert [r["winding"] for r in res] == [1] and not failed, (res, failed)
print(json.dumps(sorted([m, l, v] for (m, l), v in K.HITS.items())))
"""


class _Instrument(ast.NodeTransformer):
    def __init__(self, module):
        self.module = module

    def _wrap(self, node):
        self.generic_visit(node)
        call = ast.Call(func=ast.Name(id="__ff_check__", ctx=ast.Load()),
                        args=[node, ast.Constant(self.module), ast.Constant(node.lineno)], keywords=[])
        return ast.copy_location(call, node)

    visit_BinOp = _wrap
    visit_UnaryOp = _wrap
    visit_Call = _wrap


PLANTED = """from flint import arb


def f(n):
    return arb(1) + n / 10          # n is an int, so n / 10 is a Python float
"""


def instrumented_copy(dst, planted=False):
    """Write an instrumented copy of the package ringcert into dst/ringcert (with a planted module
    ``planted.py``, instrumented like the certified modules, if ``planted``)."""
    pkg = os.path.join(dst, "ringcert")
    os.makedirs(pkg)
    src = os.path.join(SRC, "ringcert")
    sources = {}
    for fn in sorted(os.listdir(src)):
        if fn.endswith(".py"):
            with open(os.path.join(src, fn)) as f:
                sources[fn] = f.read()
    if planted:
        sources["planted.py"] = PLANTED
    for fn, text in sources.items():
        if fn in CERTIFIED or fn == "planted.py":
            tree = _Instrument(fn).visit(ast.parse(text, filename=fn))
            tree.body.insert(0, ast.parse("from ringcert._ffdetect import __ff_check__").body[0])
            ast.fix_missing_locations(tree)
            text = ast.unparse(tree) + "\n"
        with open(os.path.join(pkg, fn), "w") as f:
            f.write(text)
    with open(os.path.join(pkg, "_ffdetect.py"), "w") as f:
        f.write(DETECTOR)


def run_instrumented(mode):
    with tempfile.TemporaryDirectory() as d:
        instrumented_copy(d, planted=(mode == "planted"))
        drv = os.path.join(d, "driver.py")
        with open(drv, "w") as f:
            f.write(DRIVER)
        env = dict(os.environ)
        env["PYTHONPATH"] = d
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        p = subprocess.run([sys.executable, drv, ROOT, mode], env=env, capture_output=True, text=True, cwd=d)
    if p.returncode != 0:
        return None, p.stdout + p.stderr
    return json.loads(p.stdout.strip().splitlines()[-1]), ""


def test_every_operation():
    c = Checks("float-free: every operation of the certified modules (instrumented copy)")
    hits, err = run_instrumented("certified")
    c(hits is not None, f"the instrumented run completed: {err[-2000:]}")
    c(hits == [], f"no float or complex value on the certified path: {hits}")
    hits, err = run_instrumented("planted")
    c(hits is not None and [h[:2] for h in hits] == [["planted.py", 5]],
      f"a planted arb(1) + n / 10 is detected at the division: {hits} {err[-500:]}")
    c.finish()
