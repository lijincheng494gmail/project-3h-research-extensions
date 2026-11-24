"""Analytic and independently differentiated Jacobians."""
import numpy as np
import sympy as s
from model import Parameters, growth, growth_prime

x, y = s.symbols("x y", real=True)
r, k, alpha, m, beta, e, d = s.symbols("r k alpha m beta e d", positive=True)
parameters = Parameters(r, k, alpha, m, beta, e, d)
F = growth(x, parameters)
field = s.Matrix([x*F-m*x*y/(beta+y), e*m*x*y/(beta+y)-d*y])
symbolic = field.jacobian([x, y])


def jacobian(z, p):
    x, y = z
    B = p.beta+y
    return np.array([
        [growth(x, p)+x*growth_prime(x, p)-p.m*y/B, -p.m*p.beta*x/B**2],
        [p.e*p.m*y/B, p.e*p.m*p.beta*x/B**2-p.d],
    ], dtype=float)

