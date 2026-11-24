"""Linear equilibrium classification with explicit nonhyperbolic cases."""
import numpy as np
from jacobian import jacobian


def classify(z, p, tolerance=1e-9):
    J = jacobian(z, p)
    trace, det = np.trace(J), np.linalg.det(J)
    discriminant = trace**2-4*det
    if abs(det) <= tolerance:
        kind = "double zero" if abs(trace) <= tolerance else "one zero eigenvalue"
    elif det < 0:
        kind = "saddle"
    elif abs(trace) <= tolerance:
        kind = "imaginary pair"
    else:
        shape = "focus" if discriminant < -tolerance else "node"
        kind = ("stable " if trace < 0 else "unstable ") + shape
    return kind, trace, det, discriminant

