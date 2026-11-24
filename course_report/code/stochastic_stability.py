"""Illustrate exact second moments of two local noise models near coexistence."""

from pathlib import Path
import csv

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import expm, solve_continuous_lyapunov

from jacobian import jacobian
from model import Parameters, rhs


ROOT = Path(__file__).resolve().parents[1]
PARAMETERS = Parameters(r=1, k=10, alpha=0.2, m=1.76, beta=1, e=1/6, d=0.88)
POINT = np.array([6.0, 1.0])
WHITE = np.array([0.35, 0.45])
THETA = 1.2
OU_VARIANCE = 0.12
# Initial displacement measured in the scaled density coordinates x/k and y/beta.
INITIAL = np.array([0.01, -0.02])


def main():
    if np.linalg.norm(rhs(0, POINT, PARAMETERS), ord=np.inf) > 1e-12:
        raise RuntimeError("The reference point is not a coexistence equilibrium.")

    scale = np.diag([PARAMETERS.k, PARAMETERS.beta])
    drift = np.linalg.solve(scale, jacobian(POINT, PARAMETERS) @ scale)
    p = solve_continuous_lyapunov(drift.T, -np.eye(2))
    remainder = np.eye(2) - np.diag(WHITE**2 * np.diag(p))
    p_min = float(np.linalg.eigvalsh(p).min())
    remainder_min = float(np.linalg.eigvalsh(remainder).min())
    lyapunov_residual = float(np.linalg.norm(drift.T @ p + p @ drift + np.eye(2), ord=np.inf))
    a, b, c, d = drift.ravel()
    moment_drift = np.array([
        [2*a + WHITE[0]**2, 2*b, 0],
        [c, a+d, b],
        [0, 2*c, 2*d + WHITE[1]**2],
    ])
    spectral_abscissa = float(np.max(np.linalg.eigvals(drift).real))
    if p_min <= 0 or remainder_min <= 0 or 2*OU_VARIANCE/THETA >= -spectral_abscissa:
        raise RuntimeError("One of the claimed mean-square stability tests failed.")
    moment_abscissa = float(np.max(np.linalg.eigvals(moment_drift).real))
    if lyapunov_residual > 1e-12 or moment_abscissa >= 0:
        raise RuntimeError("The Lyapunov residual or white-noise spectrum failed its check.")

    time = np.linspace(0, 12, 241)
    initial_covariance = np.array([INITIAL[0]**2, np.prod(INITIAL), INITIAL[1]**2])
    white = np.array([expm(moment_drift*t) @ initial_covariance for t in time])
    independently_integrated = solve_ivp(
        lambda _, m: moment_drift @ m, (time[0], time[-1]), initial_covariance,
        t_eval=time, method="DOP853", rtol=1e-11, atol=1e-15,
    )
    if not independently_integrated.success:
        raise RuntimeError(independently_integrated.message)
    white_error = float(np.max(np.abs(white - independently_integrated.y.T)))
    if white_error > 1e-13:
        raise RuntimeError("The matrix exponential and independently integrated moments disagree.")

    deterministic = np.array([np.linalg.norm(expm(drift*t) @ INITIAL)**2 for t in time])
    integrated_variance = 2*OU_VARIANCE*(time/THETA + np.expm1(-THETA*time)/THETA**2)
    check_times = time[::60]
    check_variance = integrated_variance[::60]
    integral = [quad(lambda lag: 2*OU_VARIANCE*(t-lag)*np.exp(-THETA*lag), 0, t)[0]
                for t in check_times]
    variance_error = float(np.max(np.abs(check_variance - integral)))
    if variance_error > 1e-12:
        raise RuntimeError("The closed OU variance disagrees with covariance quadrature.")

    norm0 = np.linalg.norm(INITIAL)**2
    curves = np.column_stack([
        deterministic, white[:, 0] + white[:, 2],
        np.exp(2*integrated_variance)*deterministic,
    ]) / norm0
    (ROOT / "data").mkdir(exist_ok=True)
    (ROOT / "figures").mkdir(exist_ok=True)
    with (ROOT / "data/stochastic_checks.csv").open("w", newline="", encoding="utf-8") as out:
        writer = csv.writer(out)
        writer.writerow(["diagnostic", "value"])
        writer.writerows([
            ("deterministic_spectral_abscissa", spectral_abscissa),
            ("white_moment_spectral_abscissa", moment_abscissa),
            ("lyapunov_matrix_min_eigenvalue", p_min),
            ("white_dissipation_min_eigenvalue", remainder_min),
            ("lyapunov_residual_inf_norm", lyapunov_residual),
            ("white_moment_matrix_exponential_vs_DOP853_max_error", white_error),
            ("OU_variance_closed_form_vs_quadrature_max_error", variance_error),
            ("OU_stationary_variance", OU_VARIANCE),
            ("OU_reversion_rate", THETA),
            ("OU_2q_over_theta", 2*OU_VARIANCE/THETA),
        ])
    np.savetxt(ROOT / "data/stochastic_moments.csv", np.column_stack([time, curves]),
               delimiter=",", comments="", fmt="%.12g",
               header="t,deterministic,independent_white,common_OU")

    with plt.rc_context({
        "font.family": "DejaVu Serif", "font.size": 9, "axes.spines.top": False,
        "axes.spines.right": False, "pdf.fonttype": 42,
    }):
        fig, axes = plt.subplots(1, 2, figsize=(6.85, 2.72), constrained_layout=True,
                                 sharex=True, sharey=True)
        for ax, noise, title, color in zip(
            axes, curves.T[1:], ("(a) Independent white noise", "(b) Common colored noise"),
            ("#006b75", "#a74020"),
        ):
            ax.semilogy(time, curves[:, 0], "--", label="Deterministic", color="#414141")
            ax.semilogy(time, noise, label="With noise", color=color, lw=1.7)
            ax.set_title(title, loc="left", fontsize=10)
            ax.set_xlabel("Time $t$")
            ax.set_xlim(left=0)
            ax.grid(axis="y", color="#e3e3e3")
            ax.legend(loc="upper right", frameon=False, fontsize=8)
        axes[0].set_ylabel(r"$\mathrm{E}\|u(t)\|^2/\|u(0)\|^2$")
        fig.savefig(ROOT / "figures/stoch_moments.pdf",
                    metadata={"CreationDate": None, "ModDate": None})
        plt.close(fig)


if __name__ == "__main__":
    main()
