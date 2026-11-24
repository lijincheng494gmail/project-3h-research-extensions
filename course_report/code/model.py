"""Dimensional model, parameters and exact dimensionless embedding."""
from dataclasses import dataclass
import numpy as np


@dataclass(frozen=True)
class Parameters:
    r: float
    k: float
    alpha: float
    m: float
    beta: float
    e: float
    d: float

    @property
    def C(self):
        return self.d * self.beta / self.e

    @property
    def R(self):
        return self.m * self.k / self.C


def from_scaled(A, M, R, D):
    """Use units r=k=beta=1, so e=DR/M."""
    return Parameters(1, 1, A, M, 1, D * R / M, D)


def growth(x, p):
    return p.r * (1 - x / p.k) * (1 + p.alpha * x)


def growth_prime(x, p):
    return p.r * (p.alpha - (1 + 2 * p.alpha * x) / p.k)


def rhs(t, z, p):
    x, y = z[:2]
    loss = p.m * x * y / (p.beta + y)
    return np.array([x * growth(x, p) - loss, p.e * loss - p.d * y])

