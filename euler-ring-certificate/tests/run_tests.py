"""Run every test of the package without pytest: ``python tests/run_tests.py``.

Exit status 0 if and only if every check passed."""
import importlib
import os
import sys
import time
import traceback

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import testlib  # noqa: E402


def main():
    if sys.flags.optimize:
        print("refusing to run under python -O (assert statements are part of the checks)")
        return 2
    t0 = time.time()
    mods = sorted(f[:-3] for f in os.listdir(HERE) if f.startswith("test_") and f.endswith(".py"))
    errors = 0
    for name in mods:
        mod = importlib.import_module(name)
        for fn in sorted(k for k in dir(mod) if k.startswith("test_")):
            t = time.time()
            try:
                getattr(mod, fn)()
            except AssertionError:
                errors += 1
            except Exception:
                errors += 1
                print(f"ERROR in {name}.{fn}:", flush=True)
                traceback.print_exc()
            print(f"   ({name}.{fn}: {time.time()-t:.1f} s)", flush=True)
    T = testlib.TOTAL
    print(f"tests: {T['checks']} checks, {T['failures']} failures, {errors} failing test functions "
          f"({time.time()-t0:.0f} s)", flush=True)
    return 0 if (T["failures"] == 0 and errors == 0) else 1


if __name__ == "__main__":
    sys.exit(main())
