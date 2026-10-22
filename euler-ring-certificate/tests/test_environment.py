"""Environment refusals, run in subprocesses: ``python -O`` is refused (exit 2), and a
non-reference FLINT version is refused unless ``--allow-other-flint`` is given."""
import os
import subprocess
import sys

from testlib import Checks, SRC


def run(args, pre=None):
    env = dict(os.environ)
    env["PYTHONPATH"] = SRC
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    code = "import sys\n" + (pre or "") + "from ringcert.cli import main\nsys.exit(main(sys.argv[1:]))\n"
    return subprocess.run([sys.executable] + args[:1] + ["-c", code] + args[1:], env=env,
                          capture_output=True, text=True)


def test_refusals():
    c = Checks("environment: refusals")
    p = run(["-O", "env"])
    c(p.returncode == 2 and "python -O" in p.stderr, f"-O refused with exit 2 ({p.returncode})")
    pre = "import flint\nflint.__FLINT_VERSION__ = '0.0.0'\n"
    p = run(["-B", "env"], pre)
    c(p.returncode == 2 and "reference" in p.stderr, f"other FLINT refused with exit 2 ({p.returncode})")
    p = run(["-B", "env", "--allow-other-flint"], pre)
    c(p.returncode == 0 and "NON-REFERENCE" in p.stdout, f"other FLINT allowed with the flag ({p.returncode})")
    p = run(["-B", "env"])
    c(p.returncode == 0 and "reference environment" in p.stdout, "reference environment accepted")
    c.finish()
