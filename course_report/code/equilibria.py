"""Multiplicity, Cardano branches and physical root validation."""
import sympy as s
import numpy as np
from model import Parameters, growth, growth_prime, rhs


def polynomial(x, p):
    return x * (growth(x, p) - p.m) + p.C


def cardano(p):
    """All three algebraic roots, repeated according to multiplicity."""
    p = Parameters(*(s.Rational(str(v)) for v in vars(p).values()))
    a = p.r * p.alpha / p.k
    b = 1 / p.alpha - p.k
    c = (p.m - p.r) / a
    d = -p.C / a
    P = s.simplify(c - b*b/3)
    S = s.simplify(2*b**3/27 - b*c/3 + d)
    disc = s.simplify((S/2)**2 + (P/3)**3)
    zeta = (-1 + s.I*s.sqrt(3))/2
    if disc == 0:
        u = s.real_root(-S/2, 3)
        return [2*u-b/3, -u-b/3, -u-b/3]
    radicand = -S/2+s.sqrt(disc)
    if radicand == 0:
        radicand = -S/2-s.sqrt(disc)
    u = s.real_root(radicand, 3) if disc > 0 else radicand**s.Rational(1, 3)
    return [zeta**j*u-P/(3*zeta**j*u)-b/3 for j in range(3)]


def physical(p):
    """Isolate real roots at 40 digits using rationalized input parameters."""
    q = Parameters(*(s.Rational(str(v)) for v in vars(p).values()))
    x = s.Symbol("x")
    roots = s.Poly(polynomial(x, q), x).intervals(eps=s.Rational(1, 10**40))
    result = []
    for (lo, hi), multiplicity in roots:
        prey = (lo + hi)/2
        if lo <= q.C/q.m <= hi or lo <= q.k <= hi:
            if polynomial(q.C/q.m, q) == 0 or polynomial(q.k, q) == 0:
                continue
            raise ArithmeticError("Root enclosure overlaps a feasibility boundary")
        if q.C/q.m < prey < q.k:
            pred = q.e*q.m*prey/q.d-q.beta
            z = np.array([float(prey), float(pred)])
            if not (0 < z[0] < float(p.k) and z[1] > 0):
                raise ArithmeticError("Floating conversion lost strict feasibility")
            if np.max(np.abs(rhs(0, z, p))) > 1e-9 * (1 + np.max(z)):
                raise ArithmeticError("Equilibrium failed original ODE residual check")
            result.append((z, multiplicity))
    return result


def folds(p):
    """Turning points of m=F+C/x. Use exact inputs for equality tests."""
    a = p.r*p.alpha/p.k
    L = p.k-1/p.alpha
    if L <= 0 or p.C >= a*L**3/27:
        return []
    theta = np.arccos(1-float(54*p.C/(a*L**3)))/3
    xs = [float(L) * (1/6 + np.cos(theta-2*np.pi*j/3)/3) for j in (1, 0)]
    return [(x, growth(x, p)+float(p.C)/x) for x in xs]


def branch_slope(x, p, parameter):
    Qx = x*growth_prime(x, p)-p.C/x
    partial = {
        "m": -x,
        "alpha": p.r*x*x*(1-x/p.k),
        "beta": p.d/p.e,
        "k": p.r*x*x*(1+p.alpha*x)/p.k**2,
        "d": p.beta/p.e,
    }
    return -partial[parameter]/Qx

