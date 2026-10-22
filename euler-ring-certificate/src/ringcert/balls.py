"""Arb ball helpers: exact conversion of rationals, boxes and hulls.

Every real quantity of the certified computation is an Arb ball ``arb`` (a midpoint and a radius,
representing the closed interval [mid - rad, mid + rad]) and every complex quantity an ``acb``
box (a real ball times a real ball).  The property used throughout is Arb's containment contract:
each operation returns a ball (box) that contains the exact result for every choice of the inputs
in the input balls (boxes).

python-flint silently accepts Python floats in its constructors.  This module, and every module on
the certified path, therefore creates balls only from integers, ``fmpz`` integers and other balls.
"""
from fractions import Fraction
from flint import arb, acb, ctx, fmpz

PREC = 128          # working precision in bits


def set_prec(p=PREC):
    """Set the Arb working precision (bits) for this process."""
    ctx.prec = p


set_prec()


def dy(q):
    """The exact Arb ball (radius 0) of a dyadic rational q.

    q = n / 2^e is built as arb(n) * 2^(-e); both factors are exact at the working precision when
    n fits, and the result is asserted to be exact (radius 0).  Raises if q is not dyadic.
    """
    q = Fraction(q)
    den = q.denominator
    assert den & (den - 1) == 0, "not dyadic"
    e = den.bit_length() - 1
    x = arb(fmpz(q.numerator)) * (arb(2) ** (-e))
    assert x.is_exact(), "dyadic not exact at this precision"
    return x


def qball(q):
    """An Arb ball that contains the rational q.

    Exact (radius 0) when q is a dyadic whose numerator fits in the working precision; otherwise
    arb(numerator) / arb(denominator), which contains q by the containment contract of division.
    """
    q = Fraction(q)
    den = q.denominator
    if den & (den - 1) == 0 and q.numerator.bit_length() < ctx.prec - 2:
        return dy(q)
    return arb(fmpz(q.numerator)) / arb(fmpz(q.denominator))


def box(rho):
    """The acb box [-r, r] x [-r, r] with r = upper(rho) >= rho; rho is an arb ball >= 0.

    The box contains the closed disk of radius rho, which is how disk-shaped error bounds of the
    method (Lemma A.1 perturbations, a priori enclosures, end-region errors) are added to boxes.
    """
    r = arb(0, rho.upper())
    return acb(r, r)


def hull(lo, hi):
    """An arb ball containing the interval [lower(lo), upper(hi)]."""
    return lo.lower().union(hi.upper())


def frac_of_exact(x):
    """The exact Fraction of an exact arb (for example an endpoint ``x.lower()`` or ``x.upper()``)."""
    man, e = x.man_exp()
    return Fraction(int(man)) * Fraction(2) ** int(e)


def lower_q(x):
    """Exact Fraction of the lower endpoint of the ball x (a number <= every point of x)."""
    return frac_of_exact(x.lower())


def upper_q(x):
    """Exact Fraction of the upper endpoint of the ball x (a number >= every point of x)."""
    return frac_of_exact(x.upper())
