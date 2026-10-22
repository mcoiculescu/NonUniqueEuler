"""Floating-point reference values of E_3(lambda; G) (NOT certified; optional; needs numpy and scipy,
see requirements-reference.txt).  Regenerates tests/fixtures/dop853_reference.json.

The ODE of ``ringcert.evans`` with chi = 1 on [s_L, s_R] and g(s_L) = 0 (the difference from any
admissible chi is O(e^-50)), integrated by scipy's DOP853 with rtol 1e-12, atol 1e-14, max_step 0.01.
Usage: python validation/reference_dop853.py [OUTPUT]"""
import json
import sys

import numpy as np
from scipy.integrate import solve_ivp

a0 = float.fromhex("-0x1.9f323ecbf984dp-2"); d = 0.02
sL, sR = a0 - 0.6, 0.6


def H(x): return 0.5 * (1 + np.tanh(x))
def sech2(x): return 1.0 / np.cosh(x) ** 2
def f(s): return H((s - a0) / d) * H(-s / d)
def fs(s): return (0.5 / d) * (sech2((s - a0) / d) * H(-s / d) - H((s - a0) / d) * sech2(s / d))


def rhs(s, y, lam, m, G):
    Om = (y[2].real + G) * np.exp(-2 * s)
    return [y[1], (m * m + 1j * m * fs(s) / (lam + 1j * m * Om)) * y[0], f(s) * np.exp(2 * s)]


def Ef(lam, m, G):
    sol = solve_ivp(rhs, (sL, sR), np.array([1 + 0j, m + 0j, 0j]), method='DOP853', rtol=1e-12, atol=1e-14,
                    args=(lam, m, G), max_step=0.01)
    return (sol.y[1, -1] + m * sol.y[0, -1]) * np.exp(-m * (sR - sL))


if __name__ == "__main__":
    out = []
    for G in (0.0, 0.01, 0.02):
        for lam in (0.045 - 0.5j, 0.1 - 1.0j, 0.045 - 1.5j, 1.0 + 0j, 0.12 - 0.417j, 0.0845 - 0.5145j, 2.5 + 2.5j, 0.5 - 4.5j):
            E = Ef(lam, 3, G)
            out.append(dict(lam=[lam.real, lam.imag], G=G, E=[E.real, E.imag]))
            print(G, lam, E)
    path = sys.argv[1] if len(sys.argv) > 1 else "dop853_reference.json"
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1)
