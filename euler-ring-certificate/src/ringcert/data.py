"""Exact data of the ring, and exact formatting of rationals.

Everything in this module is CPython ``int`` / ``fractions.Fraction`` arithmetic.  No floating-point
number is created anywhere in this module.

Notation.  The paper writes xi = log r and uses the points xi_L < xi_a < xi_b < xi_R; the code
calls them s_L, s_a, s_b, s_R (``SL_Q``, ``SA_Q``, ``SB_Q``, ``SR_Q``).  The ring profile is

    wbar(s) = chi(s) H((s - a_0)/d) H(-s/d),        H(x) = 1/(1 + e^{-2x}),

where chi is any admissible cutoff: chi is C^infinity with values in [0, 1], nondecreasing on
(-inf, s_a], equal to 1 on [s_a, s_b], nonincreasing on [s_b, inf), supported in [s_L, s_R].

Definition of the data.  The data are the dyadic rationals below (integer times a power of two).
They are *defined* by these literals.  ``rounding_provenance`` verifies the remark that each of them
is the binary64 number nearest to a short decimal expression; that remark is informational and is
not used by any proof.
"""
from fractions import Fraction

# ------------------------------------------------------------------ the data (definitions)
A0_Q = Fraction(-7304210039150669, 2 ** 54)      # a_0      (~ log(2/3))
DD_Q = Fraction(5764607523034235, 2 ** 58)       # d        (= RN(1/50) > 1/50)
SL_Q = Fraction(-4528212286209965, 2 ** 52)      # s_L = xi_L (= RN(a_0 - 3/5))
SA_Q = Fraction(-4077852323472915, 2 ** 52)      # s_a = xi_a (= RN(a_0 - 1/2))
SB_Q = Fraction(1, 2)                            # s_b = xi_b
SR_Q = Fraction(5404319552844595, 2 ** 53)       # s_R = xi_R (= RN(3/5))
G_MAX_Q = DD_Q                                   # the certified G-range is [0, G_MAX] = [0, d]

# Exact rational thresholds that appear in the statements (N1)-(N3).
SIGMA_COUNT = Fraction(9, 200)                   # left edge of the counting rectangle R_A
SIGMA_GAP = Fraction(211, 2500)                  # left edge of every rectangle of (N2')
RECT_A = (Fraction(9, 200), Fraction(3), Fraction(-5), Fraction(3))   # R_A = [9/200,3] x [-5,3]
G_TARGET = Fraction(1, 50)                       # (N1)-(N2) are stated for G in [0, 1/50]

DATA = dict(a0=A0_Q, d=DD_Q, sL=SL_Q, sa=SA_Q, sb=SB_Q, sR=SR_Q, Gmax=G_MAX_Q)


def data_strings():
    """The data as exact ``"p/q"`` strings (the form used in every output file)."""
    return {k: str(v) for k, v in DATA.items()}


# ------------------------------------------------------------------ binary64 rounding (exact)
def rn_binary64(q):
    """Round the rational q to the nearest binary64 number (ties to even), exactly, with integers.

    Normal range only (asserted).  Returns a Fraction.  Used only to verify the informational
    remark that the data are binary64 roundings of decimal expressions, and to build the grid
    points of the enclosure routine (any strictly increasing partition is admissible there).
    """
    q = Fraction(q)
    if q == 0:
        return Fraction(0)
    sgn = -1 if q < 0 else 1
    a = abs(q)
    # exponent e with 2^e <= a < 2^(e+1)
    e = a.numerator.bit_length() - a.denominator.bit_length()
    if Fraction(2) ** e > a:
        e -= 1
    assert Fraction(2) ** e <= a < Fraction(2) ** (e + 1)
    assert -1022 <= e <= 1023, "normal range only"
    scale = Fraction(2) ** (52 - e)          # a * scale in [2^52, 2^53)
    t = a * scale
    n = t.numerator // t.denominator
    rem = t - n
    if rem > Fraction(1, 2) or (rem == Fraction(1, 2) and n % 2 == 1):
        n += 1
    return sgn * Fraction(n) / scale


def rounding_provenance():
    """Informational: each datum equals RN_64 of the decimal expression quoted in the paper.

    Returns a list of (name, expression, holds) triples.  a_0 is compared with nothing here (it is
    pinned as a literal; its distance to log(2/3) is enclosed in ``constants``).
    """
    return [
        ("d", "RN(1/50)", DD_Q == rn_binary64(Fraction(1, 50))),
        ("sL", "RN(a0 - 3/5)", SL_Q == rn_binary64(A0_Q - Fraction(3, 5))),
        ("sa", "RN(a0 - 1/2)", SA_Q == rn_binary64(A0_Q - Fraction(1, 2))),
        ("sb", "1/2 = RN(1/2)", SB_Q == rn_binary64(Fraction(1, 2))),
        ("sR", "RN(3/5)", SR_Q == rn_binary64(Fraction(3, 5))),
    ]


# ------------------------------------------------------------------ exact decimal formatting

def dec_up(q, n=10):
    """The smallest decimal with n fractional digits that is >= q, as a string (exact)."""
    q = Fraction(q)
    num = q * 10 ** n
    k = -((-num.numerator) // num.denominator)
    return _fmt_scaled(k, n)


def dec_down(q, n=10):
    """The largest decimal with n fractional digits that is <= q, as a string (exact)."""
    q = Fraction(q)
    num = q * 10 ** n
    k = num.numerator // num.denominator
    return _fmt_scaled(k, n)


def dec_near(q, n=10):
    """q rounded to n fractional digits (half up), for display only."""
    q = Fraction(q)
    num = q * 10 ** n + Fraction(1, 2)
    k = num.numerator // num.denominator
    return _fmt_scaled(k, n)


def _fmt_scaled(k, n):
    sgn = "-" if k < 0 else ""
    k = abs(k)
    s = str(k).rjust(n + 1, "0")
    return f"{sgn}{s[:-n]}.{s[-n:]}" if n > 0 else f"{sgn}{s}"


def sci(q, digits=3):
    """Display q in scientific notation with the given number of significant digits (exact
    rounding toward zero of the mantissa; display only)."""
    q = Fraction(q)
    if q == 0:
        return "0"
    sgn = "-" if q < 0 else ""
    a = abs(q)
    e = len(str(a.numerator // a.denominator)) - 1 if a >= 1 else -1
    while Fraction(10) ** e > a:
        e -= 1
    while Fraction(10) ** (e + 1) <= a:
        e += 1
    mant = a / Fraction(10) ** e
    k = (mant * 10 ** (digits - 1)).numerator // (mant * 10 ** (digits - 1)).denominator
    s = str(k)
    return f"{sgn}{s[0]}.{s[1:]}e{e}" if digits > 1 else f"{sgn}{s}e{e}"
