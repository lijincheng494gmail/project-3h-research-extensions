"""Draw the parameter-free equilibrium and local cycle diagrams in Section 8."""
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

FIGURES = Path(__file__).resolve().parents[1] / "figures"


def main():
    plt.rcParams.update({"font.family": "serif", "mathtext.fontset": "stix",
                         "font.size": 10, "pdf.fonttype": 42, "axes.linewidth": 0.7})
    fig, (cusp, branch) = plt.subplots(1, 2, figsize=(6.6, 2.9), layout="constrained")
    ink = "#243e50"
    for ax in (cusp, branch):
        ax.spines[["right", "top"]].set_visible(False)
        ax.tick_params(direction="out", length=3)
        ax.axhline(0, color="0.8", linewidth=0.6, zorder=0)
        ax.axvline(0, color="0.8", linewidth=0.6, zorder=0)
    u = np.linspace(0, 3, 420)
    edge = 2 * (u / 3)**1.5
    cusp.fill_between(u, -edge, edge, color="#e7edf0", linewidth=0)
    cusp.plot(u, edge, color=ink)
    cusp.plot(u, -edge, color=ink)
    cusp.plot(0, 0, "o", color=ink, markersize=4)
    cusp.text(1.6, 0.10, "Three roots", ha="center", va="bottom", fontsize=9)
    cusp.text(0.21, 1.2, "One root", fontsize=9)
    cusp.set(xlim=(-0.6, 3), ylim=(-2, 2), xticks=[0], yticks=[0],
             xlabel=r"$u_c$", ylabel=r"$v_c$")
    cusp.set_title("(a)  Repeated-root locus", loc="left", fontsize=11)
    for lo, hi, style in [(-2.15, -1, "-"), (-1, 1, "--"), (1, 2.15, "-")]:
        z = np.linspace(lo, hi, 300)
        branch.plot(z**3 - 3*z, z, style, color=ink, linewidth=1.7)
    branch.plot([2, -2], [-1, 1], "o", color=ink, markersize=4)
    branch.set(xlim=(-3.7, 3.7), ylim=(-2.3, 2.3), xticks=[-2, 0, 2],
               yticks=[-1, 0, 1], xlabel=r"$V$", ylabel=r"$Z$")
    branch.set_title("(b)  Normalized branch", loc="left", fontsize=11)
    FIGURES.mkdir(exist_ok=True)
    fig.savefig(FIGURES / "analytical_branches.pdf",
                metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)



def draw_periodic_branches():
    """Plot the local Hopf and Bautin radial polynomials in normal-form units."""
    ink = "#243e50"
    fig, (hopf, bautin) = plt.subplots(1, 2, figsize=(6.6, 2.85), layout="constrained")
    for ax in (hopf, bautin):
        ax.spines[["right", "top"]].set_visible(False)
        ax.tick_params(direction="out", length=3)
        ax.axvline(0, color="0.80", linewidth=0.6, zorder=0)
    radius = np.linspace(0, 1.12, 300)
    hopf.plot(radius**2, radius, color=ink, linewidth=1.7)
    hopf.plot([-0.8, 0], [0, 0], color="0.20", linewidth=1.7)
    hopf.plot([0, 1.25], [0, 0], "--", color="0.20", linewidth=1.7)
    hopf.plot(0, 0, "o", markersize=4, color=ink)
    hopf.text(-0.45, 0.08, "Sink", ha="center")
    hopf.text(0.73, 0.08, "Source", ha="center")
    hopf.text(0.09, 0.92, "Attracting cycle", ha="center", fontsize=9)
    hopf.set(xlim=(-0.8, 1.25), ylim=(-0.08, 1.17), xticks=[0], yticks=[0],
             xlabel=r"$\lambda$", ylabel=r"$\rho$")
    hopf.set_title("(a)  Supercritical Hopf", loc="left", fontsize=11)
    for lo, hi, style in [(0, 0.5, "--"), (0.5, 1.18, "-")]:
        z = np.linspace(lo, hi, 200)
        bautin.plot(z**2-z, z, style, linewidth=1.7, color=ink)
    bautin.plot([-0.25, 0], [0.5, 0], "o", color=ink, markersize=4)
    bautin.axvline(-0.25, color="0.8", linewidth=0.6, zorder=0)
    bautin.text(-0.10, 0.28, "Repelling", fontsize=9)
    bautin.text(-0.17, 0.99, "Attracting", fontsize=9)
    bautin.set(xlim=(-0.33, 0.23), ylim=(-0.08, 1.2), xticks=[-0.25, 0],
               xticklabels=[r"$-1/4$", "0"], yticks=[0, 0.5, 1],
               yticklabels=["0", r"$1/2$", "1"], xlabel=r"$U$", ylabel=r"$Z$")
    bautin.set_title("(b)  Bautin cycle fold", loc="left", fontsize=11)
    fig.savefig(FIGURES / "analytical_cycles.pdf",
                metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)


if __name__ == "__main__":
    main()
    draw_periodic_branches()
