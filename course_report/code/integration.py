"""Shared high-order integrator and production tolerances."""
from scipy.integrate import solve_ivp
from model import rhs

RTOL = 1e-10
ATOL = 1e-12
MAX_STEP = 0.08


def integrate(p, z, time, *, events=None):
    result = solve_ivp(lambda t,u: rhs(t,u,p), (0,time), z,
                       method="DOP853", rtol=RTOL, atol=ATOL,
                       max_step=MAX_STEP, events=events, dense_output=True)
    if not result.success:
        raise RuntimeError(result.message)
    return result

