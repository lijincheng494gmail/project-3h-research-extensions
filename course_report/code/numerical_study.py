"""Reproduce the deterministic numerical figures and data for Project 3H.

The state equations are imported from model.py. The parameter sets illustrate
analytical regimes of that model and are not fitted to population records.
Run from any directory with: python code/numerical_study.py
"""
from dataclasses import asdict, replace
from fractions import Fraction
from pathlib import Path
import csv
import json

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
from sympy import Rational

from bifurcations import dimensional_bt, hopf_coefficient, k_hopf, m_hopf, trace_crossing
from equilibria import folds, physical, polynomial
from integration import ATOL, RTOL, MAX_STEP
from jacobian import jacobian
from model import Parameters, from_scaled, growth, growth_prime, rhs
from periodic import shoot
from phase_portraits import arrow, equilibria, nullclines, INK, RUST, GRAY
from stability import classify

ROOT = Path(__file__).resolve().parents[1]
GREEN = "#00786d"
plt.rcParams.update({
    "font.family": "DejaVu Serif", "font.size": 11, "axes.titlesize": 11,
    "axes.labelsize": 11, "legend.fontsize": 8.5, "pdf.fonttype": 42,
    "xtick.direction": "in", "ytick.direction": "in", "axes.spines.top": False,
    "axes.spines.right": False,
})


def numeric(p):
    return Parameters(*(float(value) for value in vars(p).values()))


def solve(p, start, time, *, tighter=False, events=None, max_step=MAX_STEP):
    factor = 0.05 if tighter else 1.0
    result = solve_ivp(rhs, (0, time), start, args=(p,), method="DOP853",
                       rtol=RTOL * factor, atol=ATOL * factor,
                       max_step=max_step, events=events, dense_output=True)
    if not result.success or not np.isfinite(result.y).all() or np.min(result.y) < 0:
        raise RuntimeError(f"Trajectory did not stay finite and nonnegative: {result.message}")
    return result


def plot_trajectory(ax, result, begin=0, end=None, *, color=INK, alpha=1.0,
                    fraction=0.55, lw=1.0):
    if end is None:
        end = result.t[-1]
    curve = result.sol(np.linspace(begin, end, 1400))
    ax.plot(*curve, color=color, alpha=alpha, lw=lw)
    arrow(ax, curve, fraction=fraction, color=color)


def phase(ax, p, title, xlim, ylim):
    ax.set(title=title, xlabel=r"Prey density $x$", ylabel=r"Predator density $y$",
           xlim=xlim, ylim=ylim)
    nullclines(ax, p)


def save(fig, name):
    fig.savefig(ROOT / "figures" / f"num_{name}.pdf", metadata={"CreationDate": None})
    plt.close(fig)


def write_rows(name, rows):
    with (ROOT / "data" / f"numerical_{name}.csv").open("w", newline="") as file:
        writer = csv.DictWriter(file, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def eq_record(z, p):
    kind, trace, det, discriminant = classify(z, p)
    return dict(x=float(z[0]), y=float(z[1]), type=kind, trace=trace, det=det,
                discriminant=discriminant, rhs_inf=np.linalg.norm(rhs(0, z, p), np.inf))


def invasion():
    fig, axes = plt.subplots(1, 2, figsize=(7.6, 2.7), layout="constrained")
    starts = [(0.17, 0.08), (0.4, 0.72), (1.08, 0.36)]
    records = {}
    for ax, m, label in zip(axes, (0.8, 1.3), ("(a) Predator extinction", "(b) Coexistence")):
        p = Parameters(1, 1, 2, m, 1, 1, 1)
        phase(ax, p, label + fr", $R={p.R:g}$", (0, 1.15), (-0.025, 0.80))
        roots = physical(p)
        target = roots[0][0] if roots else np.array([1, 0])
        ax.scatter(1, 0, s=28, edgecolor=INK, facecolor="white" if roots else INK,
                   zorder=7, label=r"$E_1$")
        equilibria(ax, p, [r"$E^*$"])
        paths = []
        for start in starts:
            path = solve(p, start, 150)
            plot_trajectory(ax, path, end=35, alpha=0.84)
            ax.scatter(*start, s=10, color=GRAY, zorder=5)
            endpoint = path.y[:, -1]
            error = np.linalg.norm(endpoint - target, np.inf)
            if error > 1e-6:
                raise RuntimeError(f"Invasion case did not reach its predicted equilibrium: {error}")
            paths.append(dict(initial=start, time=150, endpoint=endpoint.tolist(),
                              distance_inf=error))
        ax.legend(loc="upper left", frameon=False, fontsize=7.8, handlelength=1.6)
        records[f"R={m}"] = dict(parameters=asdict(p), equilibrium=eq_record(target, p),
                                  paths=paths, dulac_threshold=m * (np.sqrt(2) - 1)**2 / 3)

    p = Parameters(1, 1, 2, 1, 1, 1, 1)
    time = 5000
    path = solve(p, starts[1], time, max_step=1.0)
    check = solve(p, starts[1], time, tighter=True, max_step=0.5)
    np.testing.assert_allclose(path.y[:, -1], check.y[:, -1], rtol=1e-8, atol=1e-12)
    times = [50, 200, 1000, 5000]
    scaled = [float(t * path.sol(t)[1]) for t in times]
    if abs(scaled[-1] - 0.75) > 0.005:
        raise RuntimeError(f"Critical rate did not approach the predicted value: {scaled}")
    records["R=1"] = dict(parameters=asdict(p), initial=starts[1], times=times,
                          time_times_predator=scaled, predicted_limit=0.75)
    save(fig, "invasion")
    return records


def turning_points(p):
    points = folds(p)
    if len(points) != 2:
        raise RuntimeError("Expected two folds")
    return points


def bistability():
    p = Parameters(1, 1, 10, 3, 1, float(Fraction(70, 3)), 1.4)
    folds_here = turning_points(p)
    stationary = [z for z, _ in physical(p)]
    kinds = [classify(z, p)[0] for z in stationary]
    if len(kinds) != 3 or kinds[1] != "saddle" or not all(
        kinds[i].startswith("stable") for i in (0, 2)
    ):
        raise RuntimeError(f"Unexpected linear types for bistability: {kinds}")
    dulac = p.m * (np.sqrt(p.alpha) - 1)**2 / (p.alpha + 1)
    if p.d < dulac:
        raise RuntimeError("Bistability example did not satisfy the Dulac bound")

    fig, (a, b) = plt.subplots(1, 2, figsize=(7.6, 2.85), layout="constrained")
    a.set(title="(a) Equilibrium branches", xlabel=r"Predation coefficient $m$",
          ylabel=r"Prey equilibrium $x^*$", xlim=(1.95, 3.7), ylim=(0, 0.86))
    split = [0.015, *(f[0] for f in folds_here), 0.94]
    branch_data = []
    for i, (lo, hi) in enumerate(zip(split[:-1], split[1:])):
        xs = np.linspace(lo, hi, 400)
        m = growth(xs, p) + p.C / xs
        a.plot(m, xs, "--" if i == 1 else "-", color=RUST if i == 1 else INK,
               lw=1.35, label="Saddle" if i == 1 else ("Sink" if i == 0 else "_"))
        for ms, xsamp in zip(m, xs):
            q = replace(p, m=ms)
            z = [xsamp, q.e * ms * xsamp / q.d - q.beta]
            kind = classify(z, q)[0]
            if kind not in ("one zero eigenvalue", "double zero") and (
                (i == 1 and kind != "saddle") or (i != 1 and not kind.startswith("stable"))
            ):
                raise RuntimeError(f"Unexpected equilibrium branch stability: {ms}, {xsamp}, {kind}")
            branch_data.append(dict(m=ms, equilibrium_x=xsamp, branch=i + 1, type=kind))
    a.scatter(*np.array(folds_here).T[::-1], c=GRAY, s=25, marker="s", label="Fold", zorder=5)
    a.axvline(3.0, ls=":", color=GRAY, lw=0.8)
    a.legend(loc="upper right", frameon=False)

    phase(b, p, r"(b) Basins at $m=3$", (0, 0.68), (0, 32))
    equilibria(b, p, [r"$E_L$", r"$E_S$", r"$E_H$"])

    def boundary(_t, z, _p):
        return min(z[0] - 0.005, z[1] - 0.01, 0.68 - z[0], 32 - z[1])

    boundary.terminal = True
    saddle = stationary[1]
    values, vectors = np.linalg.eig(jacobian(saddle, p))
    if not np.any(values < 0):
        raise RuntimeError("No stable direction for saddle")
    direction = vectors[:, np.argmin(values)].real
    branch_endpoints = []
    for sign in (-1, 1):
        path = solve(p, saddle + sign * 1e-6 * direction, -120, events=boundary)
        curve = path.sol(np.linspace(path.t[-1], 0, 1600))
        b.plot(*curve, color=GREEN, lw=1.2)
        arrow(b, curve, fraction=0.45, color=GREEN)
        branch_endpoints.append(path.y[:, -1].tolist())

    endpoint_records = []
    endpoints = [(0.12, 14), (0.38, 14)]
    for target, start in zip((stationary[0], stationary[2]), endpoints):
        path = solve(p, start, 100)
        plot_trajectory(b, path, color=INK)
        b.scatter(*start, s=12, color=GRAY, zorder=5)
        endpoint = path.y[:, -1]
        error = np.linalg.norm(endpoint - target, np.inf)
        if error > 1e-6:
            raise RuntimeError(f"Basin trajectory mismatch: {endpoint}, {target}")
        endpoint_records.append(dict(initial=start, time=100, endpoint=endpoint.tolist(),
                                     distance_inf=error))
    handles, labels = b.get_legend_handles_labels()
    handles.append(Line2D([0], [0], color=GREEN, lw=1.2))
    labels.append("Separatrix")
    b.legend(handles, labels, loc="upper left", frameon=False)
    save(fig, "basins")
    write_rows("equilibrium_branches", branch_data)
    return dict(parameters=asdict(p), equilibria=[eq_record(z, p) for z in stationary],
                dulac_threshold=dulac, folds=[dict(x=x, m=m) for x, m in folds_here],
                separatrix_plot_endpoints=branch_endpoints, paths=endpoint_records)


def section(x):
    def crossing(_t, z, _p):
        return z[0] - x

    crossing.direction = 1
    return crossing


def fit_cycle(p, x, path):
    times = path.t_events[0]
    events = path.y_events[0]
    if len(times) < 2:
        raise RuntimeError("No repeated positive-direction section crossings")
    start_y = events[-1, 1]
    seed_period = times[-1] - times[-2]
    return verify_cycle(p, x, start_y, seed_period, attracting=True)


def verify_cycle(p, x, start_y, seed_period, *, attracting):
    cycle = shoot(p, x, start_y, seed_period, crossing_sign=1)
    tighter = shoot(p, x, start_y, seed_period, crossing_sign=1, tolerance_factor=0.05)
    y, period, closure, multiplier, amps, curve = cycle
    compare = [y, period, multiplier, *amps]
    compare_tight = [tighter[0], tighter[1], tighter[3], *tighter[4]]
    np.testing.assert_allclose(compare, compare_tight, rtol=1e-7, atol=1e-10)
    first = [x, y]
    independent = solve_ivp(rhs, (0, period), first, args=(p,), method="Radau",
                            rtol=RTOL, atol=ATOL, max_step=MAX_STEP)
    independent_closure = np.linalg.norm(independent.y[:, -1] - first, np.inf)
    if not independent.success or independent_closure >= 5e-9:
        raise RuntimeError(f"Independent Radau closure check failed: {independent_closure}")
    if multiplier <= 0 or (multiplier < 1) != attracting:
        raise RuntimeError(f"Shooting found the wrong transverse stability: {multiplier}")
    stats = dict(section_x=x, section_y=y, period=period, closure_inf=closure,
                 multiplier=multiplier, x_half_amplitude=amps[0], y_half_amplitude=amps[1],
                 x_range=[float(np.min(curve[0])), float(np.max(curve[0]))],
                 y_range=[float(np.min(curve[1])), float(np.max(curve[1]))],
                 independent_radau_closure_inf=independent_closure,
                 max_abs_change_tighter=float(np.max(np.abs(np.array(compare)-compare_tight))))
    return curve, stats


def hopf():
    fig, axes = plt.subplots(2, 2, figsize=(7.6, 5.4), layout="constrained")
    cases = (
        ("m", m_hopf, Fraction(24, 5), (4.65, 4.95), (0.24, 0.26),
         (0.04, 0.40), (0.07, 0.47), Rational(1, 5)),
        ("k", k_hopf, 1, (0.95, 1.05), (0.14, 0.17),
         (0.025, 0.22), (0.015, 0.24), Rational(1, 10)),
    )
    records = {}
    trace_data = []
    for i, (name, base, critical, values, initial, xlim, ylim, exact_x) in enumerate(cases):
        path_base = numeric(base)
        exact_y = base.e * base.m * exact_x / base.d - base.beta
        analytic_eq = (exact_x, exact_y)
        analytic_slope = float(trace_crossing(base, exact_x, name))
        focal_coefficient, _ = hopf_coefficient(base, analytic_eq)
        epsilon = 1e-4
        critical_num = float(critical)

        def equilibrium_at(value):
            p = replace(path_base, **{name: value})
            roots = physical(p)
            if len(roots) != 1:
                raise RuntimeError("The selected Hopf path should have one feasible root")
            return p, roots[0][0]

        for value in np.linspace(*values, 61):
            p, z = equilibrium_at(value)
            trace_data.append(dict(parameter=name, value=value, **eq_record(z, p)))
        p_lower, z_lower = equilibrium_at(critical_num - epsilon)
        p_upper, z_upper = equilibrium_at(critical_num + epsilon)
        num_slope = (np.trace(jacobian(z_upper, p_upper))
                     - np.trace(jacobian(z_lower, p_lower))) / (2 * epsilon)
        np.testing.assert_allclose(num_slope, analytic_slope, rtol=2e-6)
        critical_record = eq_record(tuple(map(float, analytic_eq)), path_base)
        if (abs(critical_record["trace"]) > 1e-12 or critical_record["det"] <= 0
                or critical_record["rhs_inf"] > 1e-12 or focal_coefficient >= 0):
            raise RuntimeError(f"Hopf base point failed trace and determinant checks: {critical_record}")
        record = dict(critical=critical_num, base_parameters=asdict(path_base),
                      critical_equilibrium=critical_record, trace_derivative=analytic_slope,
                      centered_difference=num_slope, focal_coefficient=float(focal_coefficient),
                      scenes=[])
        for j, value in enumerate(values):
            ax = axes[i, j]
            p, z = equilibrium_at(value)
            stability = eq_record(z, p)
            title = f"({chr(97 + i*2 + j)}) " + fr"${name}={value}$"
            phase(ax, p, title + (", before Hopf" if j == 0 else ", after Hopf"), xlim, ylim)
            equilibria(ax, p, [r"$E^*$"])
            time = 2600 if name == "k" and j == 0 else 900
            path = solve(p, initial, time, events=section(z[0]), max_step=0.20)
            plot_trajectory(ax, path, end=35 if name == "m" else 23, alpha=0.56,
                            fraction=0.19)
            ax.scatter(*initial, s=10, color=GRAY, zorder=6)
            scene = dict(value=value, initial=initial, equilibrium=stability, time=time)
            if j == 0:
                error = np.linalg.norm(path.y[:, -1] - z, np.inf)
                if stability["trace"] >= 0 or error > 2e-6:
                    raise RuntimeError(f"Before Hopf convergence not observed: {name}, {error}")
                if name == "k":
                    for begin in (140, 420):
                        plot_trajectory(ax, path, begin=begin, end=begin + 4.7, alpha=0.56)
                scene["endpoint_distance_inf"] = error
            else:
                if stability["trace"] <= 0:
                    raise RuntimeError(f"After Hopf equilibrium not linearly unstable: {name}")
                curve, stats = fit_cycle(p, z[0], path)
                ax.plot(*curve, color=GREEN, lw=1.4)
                arrow(ax, curve, fraction=0.23, color=GREEN)
                scene["cycle"] = stats
            record["scenes"].append(scene)
        records[name] = record
    save(fig, "hopf")
    write_rows("hopf_traces", trace_data)
    return records


def two_parameters():
    fig, (a, b) = plt.subplots(1, 2, figsize=(7.6, 2.8), layout="constrained")
    p = Parameters(1, 1, 10, 3, 1, float(Fraction(70, 3)), 1.4)
    a.set(title="(a) Positive-equilibrium cusp", xlabel=r"Half-saturation density $\beta$",
          ylabel=r"Predation coefficient $m$", xlim=(0, 4.9), ylim=(0.82, 4.75))
    c = 0.3

    def curves(xs):
        beta = p.e / p.d * xs**2 * growth_prime(xs, p)
        m = growth(xs, p) + xs * growth_prime(xs, p)
        return beta, m

    left_x = np.linspace(0.0001, c, 301)
    right_x = np.linspace(0.4499, c, 301)
    left, right = curves(left_x), curves(right_x)
    a.fill(np.r_[left[0], right[0][::-1]], np.r_[left[1], right[1][::-1]],
           color=INK, alpha=0.14, label="Three feasible roots")
    a.plot(*left, color=INK, lw=1.3, label="Fold")
    a.plot(*right, color=INK, lw=1.3)
    cusp_beta, cusp_m = curves(c)
    cusp_p = replace(p, beta=cusp_beta, m=cusp_m)
    if max(abs(polynomial(c, cusp_p)), abs(c * growth_prime(c, cusp_p) - cusp_p.C / c),
           abs(2 * growth_prime(c, cusp_p) - 2 * c * p.r * p.alpha / p.k)) > 1e-12:
        raise RuntimeError("Cusp failed its triple-root check")
    a.scatter(cusp_beta, cusp_m, c=RUST, s=30, marker="s", zorder=5, label="Cusp")
    a.scatter(1, 3, c=GREEN, s=24, zorder=5, label="Bistability example")
    a.legend(loc="lower right", frameon=False)

    q = numeric(dimensional_bt)
    bt_x = 0.2
    bt_z = np.array([bt_x, q.e * q.m * bt_x / q.d - q.beta])
    bt_record = eq_record(bt_z, q)
    J = jacobian(bt_z, q)
    if bt_record["rhs_inf"] > 1e-12 or abs(bt_record["trace"]) > 1e-12 or (
        abs(bt_record["det"]) > 1e-12 or np.max(np.abs(J @ J)) > 1e-12
    ):
        raise RuntimeError(f"BT residual check did not pass: {bt_record}")
    b.set(title="(b) Local Bogdanov–Takens geometry", xlabel=r"Carrying capacity $k$",
          ylabel=r"$10^3(m-m_{\mathrm{fold}}(k))$", xlim=(0.988, 1.010),
          ylim=(-0.12, 2.8))
    table = []
    for k in np.linspace(0.988, 1.010, 151):
        p = replace(q, k=k)
        x_fold = brentq(lambda x: x*x*growth_prime(x, p) - p.C, 0.16, 0.25, xtol=1e-14)
        m_fold = growth(x_fold, p) + p.C / x_fold
        x_trace = brentq(lambda x: (x*growth(x, p)+p.C)*growth_prime(x, p)
                        - p.d*growth(x, p), 0.16, 0.25, xtol=1e-14)
        m_trace = growth(x_trace, p) + p.C / x_trace
        q_trace = replace(p, m=m_trace)
        z = (x_trace, p.e*m_trace*x_trace/p.d-p.beta)
        trace, det = classify(z, q_trace)[1:3]
        if abs(trace) > 1e-11 or np.linalg.norm(rhs(0, z, q_trace), np.inf) > 1e-11:
            raise RuntimeError("Incorrect trace-zero continuation")
        table.append(dict(k=k, x_fold=x_fold, m_fold=m_fold, x_trace_zero=x_trace,
                          m_trace_zero=m_trace, trace=trace, det=det,
                          plotted_hopf_candidate=bool(det>1e-9)))
    b.axhline(0, color=GRAY, lw=1.2, label="Fold")
    b.plot([row["k"] for row in table],
           [1e3*(row["m_trace_zero"] - row["m_fold"]) if row["plotted_hopf_candidate"]
            else np.nan for row in table], "--", color=RUST, lw=1.5,
           label="Trace zero, positive determinant")
    b.scatter(1, 0, marker="*", color=INK, s=70, zorder=5, label="Double-zero point")
    b.set_xticks([0.990, 0.995, 1.000, 1.005, 1.010])
    b.legend(loc="upper right", frameon=False)
    write_rows("bt_locus", table)
    save(fig, "two_parameters")
    return dict(cusp=dict(beta=cusp_beta, m=cusp_m, x=c),
                bt=dict(parameters=asdict(q), equilibrium=bt_record))


def unique_cycle():
    p = Parameters(1, 1, 10, 12, 1, float(Fraction(77, 48)), 3.5)
    roots = physical(p)
    if len(roots) != 1:
        raise RuntimeError("The unique-cycle example must have a single feasible root")
    z = roots[0][0]
    record = eq_record(z, p)
    if record["trace"] <= 0 or record["det"] <= 0:
        raise RuntimeError(f"The equilibrium must be a source: {record}")

    fig, (a, b) = plt.subplots(1, 2, figsize=(7.6, 2.85), layout="constrained")
    phase(a, p, "(a) An attracting periodic orbit", (0.03, 0.65), (0.01, 1.1))
    b.set(title="(b) Repeated section crossings", xlabel="Crossing number",
          ylabel=r"Predator density on the section", xlim=(0.75, 8.25))
    equilibria(a, p, [r"$E^*$"])
    a.axvline(z[0], color=GRAY, ls="-.", lw=0.75)
    rows = []
    stats = {}
    start_details = []
    starts = [(0.20, 0.30), (0.52, 0.72), (0.35, 0.55)]
    for idx, (initial, color, marker) in enumerate(zip(starts, [INK, RUST, GRAY], ["o", "s", "D"])):
        path = solve(p, initial, 65, events=section(z[0]))
        plot_trajectory(a, path, end=5.25, color=color, alpha=0.64, fraction=0.35)
        a.scatter(*initial, s=13, color=color, marker=marker, zorder=5)
        if idx == 0:
            curve, stats = fit_cycle(p, z[0], path)
            a.plot(*curve, color=GREEN, lw=1.55)
            arrow(a, curve, fraction=0.16, color=GREEN)
            b.axhline(stats["section_y"], color=GREEN, lw=1.1, label="Cycle crossing")
        crossing_count = len(path.t_events[0])
        if crossing_count < 8:
            raise RuntimeError("Return section had too few crossings")
        for j, (t, event) in enumerate(zip(path.t_events[0], path.y_events[0]), start=1):
            rows.append(dict(start=idx + 1, crossing=j, time=t, x=event[0], y=event[1],
                             absolute_error=abs(event[1] - stats["section_y"])))
        b.plot(np.arange(1, 9), path.y_events[0][:8, 1], marker=marker, ms=3.2,
               lw=0.9, color=color, label=f"Start {idx + 1}")
        error = abs(path.y_events[0][-1, 1] - stats["section_y"])
        if error > 1e-6:
            raise RuntimeError(f"Numerical convergence to one cycle not observed: {error}")
        start_details.append(dict(initial=initial, crossings=crossing_count, last_distance=error))
    handles, labels = a.get_legend_handles_labels()
    handles.append(Line2D([0], [0], color=GREEN, lw=1.4))
    labels.append("Computed cycle")
    a.legend(handles, labels, loc="upper right", frameon=False)
    b.legend(loc="best", frameon=False)
    write_rows("cycle_returns", rows)
    save(fig, "cycle")
    return dict(parameters=asdict(p), equilibrium=record, starts=start_details, cycle=stats)


def bautin():
    # In this two-parameter unfolding h denotes a scaled equilibrium density.
    s = 0.1
    h_critical = 522 / 449
    h = h_critical + 0.01
    A = 10
    M = 1.8 * (1 + h) / h
    R = (1 + h) / s
    D_hopf = 0.7 * (1 + h) / h
    delta = 2e-5
    p = from_scaled(A, M, R, D_hopf + delta)
    z = np.array([s, h])
    equilibrium = eq_record(z, p)
    if equilibrium["type"] != "stable focus" or equilibrium["rhs_inf"] > 1e-12:
        raise RuntimeError(f"Bautin coexistence point is not a stable focus: {equilibrium}")

    crossing = section(s)

    def first_return(offset):
        y0 = h - offset
        path = solve(p, (s, y0), 13, events=crossing)
        future_returns = np.flatnonzero(path.t_events[0] > 1e-7)
        if len(future_returns) != 1:
            raise RuntimeError(f"Expected one future directed return near Bautin: {offset}")
        index = future_returns[0]
        return path.y_events[0][index, 1] - y0, path.t_events[0][index]

    fig, (a, b) = plt.subplots(1, 2, figsize=(7.6, 2.8), layout="constrained")
    phase(a, p, "(a) Two nested periodic orbits", (0.055, 0.153), (0.72, 1.80))
    equilibria(a, p)
    a.annotate(r"$E^*$", z, xytext=(5, 5), textcoords="offset points",
               color=INK, fontsize=9)
    b.set(title="(b) Displacement on the return section", xlabel=r"Initial offset $h-y_0$",
          ylabel=r"$10^6[\mathcal{P}(y_0)-y_0]$", xlim=(0, 0.305), ylim=(-7.0, 16.0))
    offsets = np.linspace(0.003, 0.33, 94)
    rows = []
    for offset in offsets:
        displacement, period = first_return(offset)
        rows.append(dict(initial_offset=offset, displacement=displacement, period=period))
    b.plot(offsets, 1e6 * np.array([row["displacement"] for row in rows]),
           color=INK, lw=1.2)
    b.axhline(0, color=GRAY, lw=0.7, ls=":")
    orbits = []
    for attracting, bracket, color, style, label in (
        (False, (0.11, 0.19), RUST, "--", "Inner repelling orbit"),
        (True, (0.23, 0.31), GREEN, "-", "Outer attracting orbit"),
    ):
        offset = brentq(lambda offset: first_return(offset)[0], *bracket, xtol=1e-11)
        _, period = first_return(offset)
        curve, stats = verify_cycle(p, s, h - offset, period, attracting=attracting)
        a.plot(*curve, color=color, lw=1.25, ls=style, label=label)
        arrow(a, curve, fraction=0.12, color=color)
        b.scatter(h - stats["section_y"], 0, s=24, color=color, zorder=5, label=label)
        orbits.append(stats | {"type": label, "bracket": bracket})
    handles, labels = a.get_legend_handles_labels()
    a.legend(handles[-2:], labels[-2:], loc="upper left", frameon=False)
    b.legend(loc="upper left", frameon=False)
    write_rows("bautin_displacement", rows)
    save(fig, "bautin")
    return dict(parameters=asdict(p), equilibrium=equilibrium,
                all_positive_equilibria=[eq_record(point, p) for point, _ in physical(p)],
                h_critical=h_critical,
                h_case=h, D_hopf=D_hopf, D_offset=delta, cycles=orbits)


def main():
    (ROOT / "figures").mkdir(exist_ok=True)
    (ROOT / "data").mkdir(exist_ok=True)
    summary = dict(
        method=dict(solver="DOP853", rtol=RTOL, atol=ATOL, default_max_step=MAX_STEP,
                    tighter_factor=0.05),
        invasion=invasion(), bistability=bistability(), hopf=hopf(),
        two_parameters=two_parameters(), unique_cycle=unique_cycle(), bautin=bautin()
    )
    path = ROOT / "data" / "numerical_summary.json"
    path.write_text(json.dumps(summary, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    print(f"Verified all six deterministic figure groups. Diagnostics: {path}")


if __name__ == "__main__":
    main()
