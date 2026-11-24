"""Reproduce the literature-informed growth-rate sensitivity study and its figure.

Run `python code/literature_cases.py` with the dependencies in requirements.txt.
Prey growth-rate intervals are from Haque (2011), Table 6, citing Tanner (1975).
The common predation and density parameters define a controlled model comparison.
"""

import csv
from dataclasses import asdict, dataclass
from pathlib import Path

import matplotlib

matplotlib.use("Agg")

import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
import numpy as np
from scipy.integrate import solve_ivp

from equilibria import physical
from jacobian import jacobian
from model import Parameters, growth, rhs


@dataclass(frozen=True)
class GrowthBand:
    pair: str
    observed: tuple[float, float]
    maximum: tuple[float, float]
    color: str


BANDS = (
    GrowthBand("Muskrat / mink", (0.806, 1.068), (1.101, 1.366), "#21678a"),
    GrowthBand("Moose / wolf", (0.100, 0.127), (0.171, 0.202), "#a64720"),
    GrowthBand("Snowshoe hare / lynx", (0.545, 0.810), (0.769, 1.033), "#42735a"),
)
PERTURBATIONS = ((0.75, 1.4), (1.25, 0.6))
PLOT_TIMES = np.linspace(0.0, 120.0, 601)


def case_parameters(rate):
    return Parameters(r=rate, k=100.0, alpha=0.04, m=1.20, beta=10.0, e=0.25, d=0.30)


def equally_scaled_distance(trajectory, equilibrium):
    relative = (trajectory - equilibrium[:, None]) / equilibrium[:, None]
    return np.linalg.norm(relative, axis=0)


def equilibrium_summary(p):
    (point, multiplicity), = physical(p)
    if multiplicity != 1:
        raise ArithmeticError("The literature comparison requires a simple coexistence root")
    matrix = jacobian(point, p)
    trace = np.trace(matrix)
    determinant = np.linalg.det(matrix)
    spectral_abscissa = max(np.linalg.eigvals(matrix).real)
    type_name = "stable focus" if trace**2 < 4 * determinant else "stable node"
    return point, trace, determinant, spectral_abscissa, type_name


def convergence_certificate(p):
    a = p.r * p.alpha / p.k
    turning_scale = p.k - 1 / p.alpha
    c_crit = a * turning_scale**3 / 27
    weak_allee = p.alpha * p.k
    dulac_margin = p.d - p.m * (np.sqrt(weak_allee) - 1)**2 / (weak_allee + 1)
    if not (p.R > 1 and p.C > c_crit and dulac_margin > 0):
        raise ArithmeticError("The global convergence certificates do not hold")
    return c_crit, dulac_margin


def trajectory(p, initial, times, refinement):
    result = solve_ivp(
        rhs, (0.0, times[-1]), initial, args=(p,), method="DOP853", t_eval=times,
        rtol=1e-9 / refinement, atol=1e-11 / refinement,
        max_step=0.8 / np.sqrt(refinement),
    )
    if not result.success or result.y.shape[1] != len(times) or np.min(result.y) <= 0.0:
        raise ArithmeticError(f"Trajectory verification failed: {result.message}")
    return result.y


def run_cases():
    baseline_paths = {}
    summary = []
    plotted_samples = []
    sweeps = []
    for band in BANDS:
        for category, interval in (("observed", band.observed), ("Tanner maximum", band.maximum)):
            for rate in np.linspace(*interval, 61):
                p = case_parameters(rate)
                c_crit, dulac_margin = convergence_certificate(p)
                point, trace, determinant, spectral, type_name = equilibrium_summary(p)
                if spectral >= 0:
                    raise ArithmeticError("A local stability check contradicts the convergence certificate")
                sweeps.append({
                    "species_pair": band.pair, "source_category": category, "r_per_year": rate,
                    "Ccrit": c_crit, "dulac_margin_per_year": dulac_margin, "x_star": point[0],
                    "y_star": point[1], "trace_per_year": trace, "det_per_year2": determinant,
                    "spectral_abscissa_per_year": spectral, "linear_type": type_name,
                })

        low, high = band.observed
        for rate_kind, rate in (("observed low", low), ("observed midpoint", (low + high) / 2), ("observed high", high)):
            p = case_parameters(rate)
            point, trace, determinant, spectral, type_name = equilibrium_summary(p)
            c_crit, dulac_margin = convergence_certificate(p)

            horizon = max(float(PLOT_TIMES[-1]), 14.0 / -spectral)
            times = np.unique(np.r_[PLOT_TIMES, horizon])
            for number, perturbation in enumerate(PERTURBATIONS, start=1):
                initial = point * perturbation
                standard_path = trajectory(p, initial, times, 1.0)
                refined_path = trajectory(p, initial, times, 10.0)
                scaled_difference = (standard_path - refined_path) / point[:, None]
                max_disagreement = np.max(np.linalg.norm(scaled_difference, axis=0))
                final_distance = equally_scaled_distance(refined_path[:, -1:], point)[0]
                if max_disagreement >= 1e-7 or final_distance >= 1e-4:
                    raise ArithmeticError("Refinement or terminal-distance check failed")
                summary.append({
                    "species_pair": band.pair, "rate_case": rate_kind, **asdict(p),
                    "R": p.R, "C": p.C, "Ccrit": c_crit, "dulac_margin_per_year": dulac_margin,
                    "x_star": point[0], "y_star": point[1], "trace_per_year": trace,
                    "det_per_year2": determinant, "spectral_abscissa_per_year": spectral,
                    "linear_type": type_name, "initial_condition": number,
                    "x0": initial[0], "y0": initial[1], "horizon_years": horizon,
                    "terminal_scaled_distance": final_distance,
                    "max_scaled_disagreement": max_disagreement,
                })
                if rate_kind == "observed low":
                    plotted = refined_path[:, :len(PLOT_TIMES)]
                    baseline_paths.setdefault(band.pair, (p, point, []))[2].append(plotted)
                    distances = equally_scaled_distance(plotted, point)
                    for time, x, y, distance in zip(PLOT_TIMES, *plotted, distances):
                        plotted_samples.append({
                            "species_pair": band.pair, "initial_condition": number,
                            "time_years": time, "x": x, "y": y, "scaled_distance": distance,
                        })
    return baseline_paths, summary, plotted_samples, sweeps


def write_csv(path, records):
    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=records[0].keys(), lineterminator="\n")
        writer.writeheader()
        writer.writerows(records)


def draw_figure(path, baseline_paths):
    plt.rcParams.update({
        "font.size": 8, "axes.spines.top": False, "axes.spines.right": False,
        "axes.labelsize": 8, "axes.titlesize": 8.5, "axes.linewidth": 0.55,
        "xtick.labelsize": 7, "ytick.labelsize": 7, "pdf.fonttype": 42,
    })
    figure = plt.figure(figsize=(7.6, 4.15), layout="constrained")
    grid = figure.add_gridspec(3, 3, height_ratios=(1.55, 0.24, 1))
    legend_axis = figure.add_subplot(grid[1, :])
    legend_axis.set_axis_off()
    distance_axis = figure.add_subplot(grid[2, :])
    nullclines = ("#56616b", "#959ba0")

    for index, band in enumerate(BANDS):
        p, point, paths = baseline_paths[band.pair]
        ax = figure.add_subplot(grid[0, index])
        xy = np.concatenate(paths, axis=1)
        lower = xy.min(axis=1) - 0.11 * np.ptp(xy, axis=1)
        upper = xy.max(axis=1) + 0.11 * np.ptp(xy, axis=1)
        xs = np.linspace(max(0.0, lower[0]), min(p.k, upper[0]), 600)
        prey_growth = growth(xs, p)
        physical_branch = (prey_growth >= 0) & (prey_growth < p.m)
        prey_line = np.full(xs.shape, np.nan)
        prey_line[physical_branch] = p.beta * prey_growth[physical_branch] / (p.m - prey_growth[physical_branch])
        ys = p.e * p.m * xs / p.d - p.beta
        ax.plot(xs, prey_line, color=nullclines[0], linestyle="--", linewidth=0.9)
        ax.plot(xs, np.where(ys >= 0, ys, np.nan), color=nullclines[1], linestyle=":", linewidth=1.05)

        for plotted in paths:
            ax.plot(*plotted, color=band.color, linewidth=1.02, alpha=0.94)
            ax.scatter(*plotted[:, 0], facecolor="white", edgecolor=band.color, s=19, zorder=4)
            displacement = np.linalg.norm(np.diff(plotted, axis=1) / (upper - lower)[:, None], axis=0)
            shift = np.r_[0, np.cumsum(displacement)]
            for fraction in (0.22, 0.60):
                j = np.searchsorted(shift, fraction * shift[-1])
                end = np.searchsorted(shift, fraction * shift[-1] + 0.025)
                if j < end < plotted.shape[1]:
                    ax.annotate("", xy=plotted[:, end], xytext=plotted[:, j],
                                arrowprops={"arrowstyle": "-|>", "color": band.color, "lw": 0.7,
                                            "mutation_scale": 7, "shrinkA": 0, "shrinkB": 0})
        ax.scatter(*point, color="#15191b", s=19, zorder=5)
        ax.set(xlim=(max(0.0, lower[0]), upper[0]), ylim=(max(0.0, lower[1]), upper[1]),
               xlabel=r"Prey density $x$", ylabel=r"Predator density $y$" if index == 0 else None,
               title=rf"({chr(97 + index)}) {band.pair}, $r={p.r:.3f}$")

        distance = equally_scaled_distance(paths[0], point)
        visible_distance = np.where(distance >= 1e-7, distance, np.nan)
        distance_axis.semilogy(PLOT_TIMES, visible_distance, color=band.color,
                               linewidth=1.2, label=band.pair)

    legend_axis.legend(handles=[
        Line2D([0], [0], marker="o", color="none", markeredgecolor="#303638", markersize=4,
               markerfacecolor="white", label="Initial point"),
        Line2D([0], [0], marker="o", color="none", markeredgecolor="#15191b", markersize=4,
               markerfacecolor="#15191b", label="Equilibrium"),
        Line2D([0], [0], color=nullclines[0], linestyle="--", label="Prey nullcline"),
        Line2D([0], [0], color=nullclines[1], linestyle=":", label="Predator nullcline"),
    ], ncol=4, loc="center", frameon=False, fontsize=7.3)
    distance_axis.set(xlabel="Time (years)", ylabel="Scaled distance", xlim=(0, PLOT_TIMES[-1]),
                      ylim=(1e-7, 1.3), title="(d) Return after the same relative perturbation")
    distance_axis.set_yticks([1, 1e-2, 1e-4, 1e-6])
    distance_axis.grid(axis="y", which="major", color="#e4e7e9", linewidth=0.6)
    distance_axis.legend(loc="lower right", frameon=False, ncol=3, fontsize=7.3)
    figure.savefig(path, metadata={"CreationDate": None, "ModDate": None})
    plt.close(figure)


def main():
    root = Path(__file__).resolve().parent.parent
    figures = root / "figures"
    data = root / "data"
    figures.mkdir(exist_ok=True)
    data.mkdir(exist_ok=True)
    baseline_paths, summary, plotted_samples, sweeps = run_cases()
    write_csv(data / "literature_summary.csv", summary)
    write_csv(data / "literature_trajectories.csv", plotted_samples)
    write_csv(data / "literature_rate_sweep.csv", sweeps)
    draw_figure(figures / "lit_growth_rates.pdf", baseline_paths)
    print(f"Checked {len(summary)} trajectories and {len(sweeps)} equilibrium samples")


if __name__ == "__main__":
    main()
