"""Environment checks and records.

The verification assumes (i) python-flint 0.9.0 with its bundled FLINT 3.6.0 (the reference
environment), and (ii) that the interpreter runs the code as written: ``assert`` statements are part
of the checks, so running under ``python -O`` is refused.

Only the following are recorded: the Python version, ``platform.platform()``, the python-flint and
FLINT versions, the working precision, and the SHA-256 of each module of this package.  No path,
user name or host name is recorded.
"""
import hashlib
import os
import platform
import sys

REFERENCE_PYTHON_FLINT = "0.9.0"
REFERENCE_FLINT = "3.6.0"


class EnvironmentRefused(Exception):
    pass


def package_dir():
    return os.path.dirname(os.path.abspath(__file__))


def repo_root():
    """The source-tree root (two levels above the package), when running from a checkout."""
    return os.path.dirname(os.path.dirname(package_dir()))


def module_hashes():
    """SHA-256 of every module of the package (sorted by file name)."""
    d = package_dir()
    out = {}
    for fn in sorted(os.listdir(d)):
        if fn.endswith(".py"):
            with open(os.path.join(d, fn), "rb") as f:
                out[fn] = hashlib.sha256(f.read()).hexdigest()
    return out


def describe():
    import flint
    from . import balls
    return {
        "python": platform.python_version(),
        "implementation": platform.python_implementation(),
        "platform": platform.platform(),
        "python_flint": flint.__version__,
        "flint": flint.__FLINT_VERSION__,
        "prec": balls.PREC,
        "modules": module_hashes(),
    }


def refuse_optimized():
    """Refuse to run under python -O (every command calls this)."""
    if sys.flags.optimize:
        raise EnvironmentRefused("refusing to run under python -O: assert statements are part of the checks")


def is_reference(python_flint, flint_version):
    """True if and only if the given versions are those of the reference environment."""
    return python_flint == REFERENCE_PYTHON_FLINT and flint_version == REFERENCE_FLINT


def verify(allow_other_flint=False):
    """Refuse to run under -O; refuse a non-reference python-flint/FLINT unless allowed.

    Returns (reference_environment: bool, messages)."""
    msgs = []
    refuse_optimized()
    try:
        import flint
    except ImportError as exc:
        raise EnvironmentRefused(f"python-flint is not installed ({exc}); pip install python-flint==0.9.0")
    ref = is_reference(flint.__version__, flint.__FLINT_VERSION__)
    if not ref:
        m = (f"python-flint {flint.__version__} / FLINT {flint.__FLINT_VERSION__} is not the reference "
             f"environment (python-flint {REFERENCE_PYTHON_FLINT} / FLINT {REFERENCE_FLINT})")
        if not allow_other_flint:
            raise EnvironmentRefused(m + "; pass --allow-other-flint to run anyway (results then marked non-reference)")
        msgs.append("WARNING: " + m)
    return ref, msgs
