"""Directed section shooting and divergence-based Floquet diagnostics."""
import numpy as np
from scipy.integrate import solve_ivp, quad
from scipy.optimize import root
from model import rhs
from jacobian import jacobian
from integration import RTOL, ATOL, MAX_STEP


def shoot(p, section_x, guess_y, guess_period, *, crossing_sign=-1, tolerance_factor=1.0):
    """Solve equal endpoints with fixed initial X and checked crossing direction."""
    def orbit(y, period):
        result = solve_ivp(lambda t,z: rhs(t,z,p), (0,period), [section_x,y],
                           method="DOP853", rtol=RTOL*tolerance_factor,
                           atol=ATOL*tolerance_factor, max_step=MAX_STEP,
                           dense_output=True)
        if not result.success:
            raise RuntimeError(result.message)
        return result

    def residual(z):
        y, period = z
        return orbit(y,period).y[:,-1]-[section_x,y]

    fit = root(residual,[guess_y,guess_period],tol=1e-10)
    y, period = fit.x
    error = np.linalg.norm(residual(fit.x),ord=np.inf)
    direction = rhs(0,(section_x,y),p)[0]
    if not (error < 1e-9 and y > 0 and period > 0 and crossing_sign * direction > 1e-5):
        raise RuntimeError(f"Invalid return: {fit.x}, {error}, {direction}")
    result = orbit(y,period)
    grid = np.linspace(0,period,2001)
    trajectory = result.sol(grid)
    signed = crossing_sign * (trajectory[0]-section_x)
    crossings = np.flatnonzero((signed[:-1] < 0)
                               & (signed[1:] >= 0))
    # A closing crossing may land numerically on either side of the section.
    if any(grid[i] < period - 2*(grid[1]-grid[0]) for i in crossings):
        raise RuntimeError("Shooting period contains an earlier directed return")
    integral = quad(lambda t: np.trace(jacobian(result.sol(t),p)),0,period,
                    epsabs=1e-10)[0]
    amplitudes = np.ptp(trajectory,axis=1)/2
    return y, period, error, np.exp(integral), amplitudes, trajectory

