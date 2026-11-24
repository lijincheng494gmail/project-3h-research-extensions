"""Rebuild Figure 1.1 from the comparative archive and replay its first 20 time units.

The model, integration, and figure functions below come from the Direction 1
results report. Input and output paths are adapted for the combined appendix.
"""
from pathlib import Path
from zipfile import ZipFile

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
from scipy.integrate import solve_ivp

HERE = Path(__file__).resolve().parent
ARCHIVE = HERE.parent / "research" / "Project3H_Direction1_Comparative_Paper.zip"
MODELS = ["FA_original", "LV_mass_action", "Holling_II", "Beddington_DeAngelis",
          "Ratio_dependent_separate"]
SHORT = ["P0", "P1", "P2", "P3", "P4"]
COLORS = ["#126962", "#52667f", "#c15b32", "#82649a", "#b3923f"]


def load(stem):
    with ZipFile(ARCHIVE) as package:
        with package.open(f"results/{stem}.csv") as data:
            return pd.read_csv(data)


def save(fig, name):
    fig.savefig(HERE / f"{name}.pdf", bbox_inches="tight", pad_inches=.055)
    plt.close(fig)


def feeding(x, y, model, p):
    denominator = x + p.c*y if model==MODELS[-1] else 1+p.b*x+p.c*y
    return p.a*x*y/denominator


def rhs(_, state, model, p):
    x,y = state
    loss = feeding(x,y,model,p)
    return (p.r*x*(1-x/p.K)*(1+p.alpha*x)-loss, p.e*loss-p.d*y)


def simulate():
    params=load("controlled_parameters").query("scenario=='A_moderate'").set_index("model")
    traj=load("comparison_dense_trajectories").query("scenario=='A_moderate'")
    equilibria=load("controlled_equilibria").query("scenario=='A_moderate'").set_index("model")
    fig, axes=plt.subplots(2,2,figsize=(7,4.3),layout="constrained")
    maxerr=0
    for idx,model in enumerate(MODELS):
        p=params.loc[model]
        obs=traj[traj.model==model].sort_values("t")
        first=obs[obs.t<=20]
        sol=solve_ivp(rhs,(0,float(first.t.iloc[-1])),first.iloc[0][["x","y"]].to_numpy(float),
                      args=(model,p),t_eval=first.t.to_numpy(),method="DOP853",rtol=1e-10,atol=1e-12)
        assert sol.success
        maxerr=max(maxerr, np.max(np.abs(sol.y.T-first[["x","y"]].to_numpy())))
        eq=equilibria.loc[model]
        assert max(np.abs(rhs(0,(eq.x,eq.y),model,p))) < 1e-12
        for ax,k in zip(axes[0],("x","y")):
            cut=obs[obs.t<=80]
            ax.plot(cut.t,cut[k],color=COLORS[idx],label=SHORT[idx],lw=1.45)
        if model in (MODELS[0],MODELS[2]):
            ax=axes[1, int(model==MODELS[2])]
            cut=obs[obs.t<=80]
            ax.plot(cut.x,cut.y,color=COLORS[idx],lw=1.45)
            ax.plot(cut.x.iloc[0],cut.y.iloc[0],"o",mfc="white",mec="#1f313b",ms=5)
            ax.plot(eq.x,eq.y,marker="x",color="black",ms=6)
    assert maxerr<1e-5
    axes[0,0].set(title="A   Prey trajectories",xlabel="Time",ylabel="Prey density")
    axes[0,1].set(title="B   Predator trajectories",xlabel="Time",ylabel="Predator density")
    axes[0,1].legend(ncols=3,fontsize=7,handlelength=1.4,loc="lower right")
    for a,title in zip(axes[1],["C   P0  |  Foraging arena","D   P2  |  Holling II"]):
        a.set(xlabel="Prey density",ylabel="Predator density",title=title)
    save(fig,"matched_dynamics")
    return {"replayed_models":len(params),"maximum_absolute_coordinate_difference_t0_20":float(maxerr)}


if __name__ == "__main__":
    plt.rcParams.update({"font.size":8.5,"axes.titlesize":9,"axes.titleweight":"bold","axes.titlelocation":"left","axes.labelcolor":"#263f4b","axes.spines.top":False,"axes.spines.right":False,"pdf.fonttype":42})
    print(simulate())
