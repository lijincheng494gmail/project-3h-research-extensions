"""Recheck the six-model evidence and rebuild every report figure from packaged records."""
from pathlib import Path
import json
import numpy as np
import pandas as pd
import sympy as sp
from scipy.integrate import solve_ivp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

ROOT = Path(__file__).resolve().parent
DATA, FIGURES = ROOT / "data", ROOT / "figures"
IDS = ["M1", "M0", "M2", "M3", "M4", "M5"]
GROWTH = ["Logistic", "Weak", "Strong"]
COLORS = ["#286782", "#1A826C", "#B15B32"]
MODEL_COLOR = dict(zip(IDS, COLORS * 2))
INK = "#172E42"

def table(name):
    return pd.read_csv(DATA / (name + ".csv"))

def growth(x, p):
    base = p["r"] * (1-x/p["K"])
    if p["allee"] == "weak":
        return base * (1+p["alpha"]*x)
    if p["allee"] == "strong":
        return base * (x/p["A"]-1)
    return base

def field(x, y, p):
    interaction = p["m"]*x*y/(p["beta"]+y)
    return np.array([x*growth(x,p)-interaction, p["e"]*interaction-p["d"]*y-p["h"]*y*y])

def verify_math():
    z = sp.symbols("z")
    certify = table("root_classification_examples")
    for row in certify.itertuples():
        inputs = json.loads(row.parameters)
        p = {k:(v if k=="allee" else sp.Rational(v)) for k,v in inputs.items()}
        x = p["beta"]*p["d"]/(p["e"]*p["m"])*(1+z)*(1+p["h"]*p["beta"]/p["d"]*z)
        poly = sp.Poly((1+z)*growth(x,p)-p["m"]*z,z)
        zero = 0
        while poly.eval(0)==0:
            poly = poly.exquo(sp.Poly(z,z))
            zero += 1
        intervals = poly.intervals(eps=sp.Rational(1,10**14))
        positive = [m for (lower,upper),m in intervals if lower>=0 and upper>0]
        assert (len(positive),sum(positive),zero)==(row.distinct_positive,row.positive_with_multiplicity,row.zero_root_multiplicity)
    params = table("extended_parameters")
    ref = params.query("scenario==10 and scaling=='same_r'").set_index("model")
    eqs = table("extended_equilibria").query("scenario==10 and scaling=='same_r'")
    for r in eqs.itertuples():
        p = ref.loc[r.model]
        assert np.linalg.norm(field(r.x_eq,r.y_eq,p))<1e-10
        jac = np.column_stack([field(r.x_eq+1e-24j,r.y_eq,p).imag/1e-24,
                               field(r.x_eq,r.y_eq+1e-24j,p).imag/1e-24])
        np.testing.assert_allclose([np.trace(jac),np.linalg.det(jac)],[r.trace,r.determinant],atol=1e-10)
    trajectories=table("paper_phase_trajectories")
    biggest=0.
    for (model,initial),path in trajectories.groupby(["model","initial"]):
        p=ref.loc[model]
        def rhs(t, log_state):
            x,y=np.exp(log_state)
            return field(x,y,p)/np.array([x,y])
        xy=path[["x","y"]].to_numpy()
        sol=solve_ivp(rhs,(path.time.iloc[0],path.time.iloc[-1]),np.log(xy[0]),t_eval=path.time,
                      method="DOP853",rtol=1e-10,atol=1e-12)
        assert sol.success
        biggest=max(biggest,float(np.max(np.abs(np.exp(sol.y.T)-xy)/(1+np.abs(xy)))))
    assert biggest<1e-6,biggest
    bifs=table("analytical_bifurcation_witnesses")
    assert len(bifs)==12 and set(bifs.model)=={"M0","M2","M4","M5"}
    for r in bifs.itertuples():
        assert np.linalg.norm(field(r.x,r.y,r._asdict()))<1e-10
        J=np.column_stack([field(r.x+1e-24j,r.y,r._asdict()).imag/1e-24,
                           field(r.x,r.y+1e-24j,r._asdict()).imag/1e-24])
        np.testing.assert_allclose([np.trace(J),np.linalg.det(J)],[r.trace,r.determinant],atol=1e-10)
        if r.event=="Hopf":
            assert abs(r.trace)<1e-10 and r.determinant>0 and r.l1*r.l1_complex>0 and abs(r.trace_derivative_wrt_d)>1e-8
        elif r.event=="saddle_node":
            assert abs(r.determinant)<1e-10 and abs(r.scalar_E_xx*r.scalar_E_d)>1e-12
        else:
            assert abs(r.trace)+abs(r.determinant)<1e-10 and abs(r.bt_a20*r.bt_b11*r.bt_unfolding_determinant)>1e-13
    branches=table("matched_branches").query("case=='mixed' and h>0")
    for variable in ("prey","predator"):
        pivot=branches.pivot(index="h",columns="law",values=variable)
        assert ((pivot.S>pivot.W)&(pivot.W>pivot.L)).all()
    shocks=table("extended_shock_recovery")
    assert len(shocks)==48 and shocks.recovered.sum()==45
    print(f"Verified {len(certify)} exact root examples, {len(eqs)} coexistence states, 12 local witnesses, "
          f"the matched-branch ranks, and 48 shock outcomes. Largest scaled discrepancy over 18 reintegrated paths: {biggest:.2g}.")

def verify_forecasts():
    scores=table("real_benchmark_scores")
    preds=table("real_predictions")
    folds=table("real_folds").set_index("held")
    for (held,model),group in preds.groupby(["held","model"]):
        fold=folds.loc[held]
        actual=group[["observed_x","observed_y"]].to_numpy()
        src=pd.read_csv(DATA/"observations"/(held+".csv"),skipinitialspace=True)
        src=src.iloc[:,0:3].dropna().set_index(src.columns[0])
        observations=src.loc[group.time_to].to_numpy()
        observations[:,1]/=20
        np.testing.assert_allclose(actual,observations,atol=1e-12)
        score=scores.query("held==@held and model==@model").iloc[0]
        for col,cols in [("test_nrmse",["predicted_x","predicted_y"]),
                         ("free_trajectory_nrmse",["free_predicted_x","free_predicted_y"])]:
            error=group[cols].to_numpy()-actual
            expected=np.mean(np.sqrt(np.mean(error**2,axis=0))/[fold.train_scale_x,fold.train_scale_y])
            np.testing.assert_allclose(expected,score[col],rtol=2e-11)
    summary=scores.groupby("model")[["test_nrmse","free_trajectory_nrmse"]].mean()
    assert round(summary.loc["M3","test_nrmse"],4)==.8825 and round(summary.loc["M1","free_trajectory_nrmse"],4)==1.0376
    assert round(summary.loc["training_mean","free_trajectory_nrmse"],4)==1.0370
    late=table("real_cycle_metrics").query("model in @IDS and forecast_mode=='free'")
    assert len(late)==48 and not late.late_amplitude_above_floor.any()
    print("Verified 24 conditional and 24 free-running forecast scores against four measured chemostat records.")

def style():
    plt.rcParams.update({"figure.dpi":120,"font.family":"DejaVu Sans","font.size":8,"axes.labelcolor":INK,
                         "axes.edgecolor":"#9CABB2","axes.labelsize":8,"axes.titlesize":9,"axes.titlecolor":INK,
                         "text.color":INK,"axes.spines.top":False,"axes.spines.right":False,"pdf.fonttype":42})
    FIGURES.mkdir(exist_ok=True)

def finish(fig,name):
    fig.savefig(FIGURES/(name+".pdf"),bbox_inches="tight",pad_inches=.04)
    plt.close(fig)

def ref_data():
    eq=table("extended_equilibria").query("scenario==10 and scaling=='same_r'")
    p=table("extended_parameters").query("scenario==10 and scaling=='same_r'").set_index("model")
    return p,eq

def design_and_paths():
    p,eq=ref_data()
    x=np.linspace(0,8,200)
    fig,ax=plt.subplots(figsize=(7.25,2.32),layout="constrained")
    for model,name,color in zip(IDS[:3],GROWTH,COLORS):
        ax.plot(x,growth(x,p.loc[model]),label=name,color=color,lw=2)
    ax.axhline(0,lw=.7,color=INK);ax.axvline(2,color=COLORS[2],ls=":",lw=.8)
    ax.set(xlabel="Prey density, x",ylabel="Per-capita prey growth, g(x)",xlim=(0,8))
    ax.legend(ncol=3,frameon=False,loc="upper center",bbox_to_anchor=(.51,1.25))
    finish(fig,"growth")
    paths=table("paper_phase_trajectories")
    fig,axes=plt.subplots(2,3,figsize=(7.35,3.6),sharex=True,sharey=True,layout="constrained")
    for ax,model in zip(axes.flat,IDS):
        for i,path in paths.query("model==@model").groupby("initial"):
            ax.plot(path.x,path.y,color=COLORS[i],lw=1.1)
            ax.scatter(path.x.iloc[0],path.y.iloc[0],s=9,marker="s",color=COLORS[i])
        for r in eq.query("model==@model").itertuples():
            ax.scatter(r.x_eq,r.y_eq,color=INK,marker="o" if r.stability=="stable" else "x",s=16,zorder=3)
        ax.set_title(model+" · "+GROWTH[IDS.index(model)%3]);ax.set(xlim=(-.2,8),ylim=(-.2,5.5))
    for ax in axes[-1]: ax.set_xlabel("Prey x")
    for ax in axes[:,0]:ax.set_ylabel("Predators y")
    finish(fig,"phase")
    fig,axes=plt.subplots(1,3,figsize=(7.35,1.82),sharey=True,layout="constrained")
    for i,ax in enumerate(axes):
        for j,model in enumerate((IDS[i],IDS[i+3])):
            df=paths.query("model==@model and initial==0 and time<=30")
            ax.plot(df.time,df.y,label=model,color=COLORS[i],ls=["-","--"][j],lw=1.45)
        ax.set_xlabel("Time");ax.legend(frameon=False,ncol=2,fontsize=7,loc="lower right")
    axes[0].set_ylabel("Predators y");finish(fig,"time")

def events_and_shocks():
    df=table("extended_continuation").query("sweep_parameter=='K' and base_scenario==10")
    fig,axes=plt.subplots(1,2,figsize=(7.35,2.35),sharey=True,layout="constrained")
    for j,ax in enumerate(axes):
        for i,m in enumerate(IDS[3*j:3*j+3]):
            part=df[df.model==m].dropna(subset=["y_eq"])
            for stable,rows in part.groupby(part.stability=="stable"):
                ax.scatter(rows.sweep_value,rows.y_eq,s=6 if stable else 9,marker="o" if stable else "x",color=COLORS[i],linewidths=.5)
        ax.set(title=["Without direct competition","With direct competition"][j],xlabel="Carrying capacity, K")
    axes[0].set_ylabel("Predator equilibrium, y*")
    axes[0].legend(handles=[Line2D([0],[0],color=c,label=g) for g,c in zip(GROWTH,COLORS)],frameon=False,fontsize=7)
    finish(fig,"enrichment")
    df=table("matched_branches")
    fig,axes=plt.subplots(1,2,figsize=(7.4,2.3),layout="constrained")
    for ax,case in zip(axes,["mixed","fold"]):
        for g,col,name in zip("LWS",COLORS,GROWTH):
            rows=df.query("case==@case and law==@g")
            ax.plot(rows.h,rows.predator,color=col,label=name,lw=1.8)
        ax.set_xlabel("Direct competition, h")
    axes[0].set(ylabel="Predator equilibrium, y*",title="Mixed initial responses")
    axes[1].set(title="First fold on the strong branch",ylabel="Predator equilibrium, y*")
    e=df.query("status=='fold limit'").iloc[0];axes[1].scatter(e.h,e.predator,facecolors="white",edgecolors=COLORS[2],s=32,zorder=5)
    axes[0].legend(frameon=False,fontsize=7);finish(fig,"ordering")
    fig,axes=plt.subplots(1,2,figsize=(7.4,2.2),sharey=True,layout="constrained")
    df=table("extended_shock_trajectories")
    for ax,m in zip(axes,["M2","M5"]):
        rows=df.query("model==@m and reduction_fraction==.6 and time<=40")
        ax.plot(rows.time,rows.x_over_equilibrium,label="Prey",color=COLORS[1])
        ax.plot(rows.time,rows.y_over_equilibrium,label="Predators",color=COLORS[2])
        ax.axhline(1,color="#A5ABB0",ls=":",lw=1)
        ax.set(title=m+" · 60% prey removal",xlabel="Time after shock")
    axes[0].set_ylabel("Fraction of pre-shock density");axes[0].legend(frameon=False,fontsize=7)
    finish(fig,"shocks")

def interaction_map():
    from matplotlib.colors import ListedColormap, BoundaryNorm
    from matplotlib.patches import Patch
    df=table("paper_interaction_grid")
    assert len(df)==5740
    palette=["#638C9A","#D4AF6C","#AA5842","#E0E5E5"]
    cmap=ListedColormap(palette)
    fig,axes=plt.subplots(1,2,figsize=(7.35,1.91),sharey=True,layout="constrained")
    for ax,scale,title in zip(axes,["same_r","matched_reference_growth"],["Equal growth coefficient r","Growth matched at 0.6K"]):
        r=df.query("growth=='strong' and scaling==@scale")
        a=r.pivot(index="shape_parameter",columns="h",values="interaction_predator")
        nonzero_h=a.loc[:,a.columns>0].to_numpy()
        counts=(np.sum(nonzero_h<0),np.sum(nonzero_h>0),np.isnan(nonzero_h).sum())
        assert counts==((1000,40,360) if scale=="same_r" else (1400,0,0))
        signs=np.where(a.isna(),3,np.where(a<0,0,np.where(a>0,2,1)))
        ax.pcolormesh(a.columns,a.index,signs,cmap=cmap,norm=BoundaryNorm([-.5,.5,1.5,2.5,3.5],4),shading="nearest")
        ax.set(title=title,xlabel="Competition h")
    axes[0].set_ylabel("Threshold A/K")
    axes[1].legend(handles=[Patch(facecolor=c,label=lab) for c,lab in zip(palette,["Negative","Zero","Positive","Undefined"])],
                   loc="upper center",bbox_to_anchor=(-.05,-.28),ncol=4,frameon=False,fontsize=7)
    finish(fig,"interaction")

def observed_forecast():
    df=table("real_predictions").query("held=='C4' and model=='M3'")
    fig,axes=plt.subplots(1,2,figsize=(7.3,2.27),layout="constrained")
    for ax,k,name in zip(axes,["x","y"],["Algae (million cells/ml)","Rotifers (animals/ml)"]):
        scale=1 if k=="x" else 20
        ax.plot(df.time_to,df["observed_"+k]*scale,".",ms=3,color=INK,label="Observed")
        ax.plot(df.time_to,df["predicted_"+k]*scale,color=COLORS[1],lw=1,label="One-step")
        ax.plot(df.time_to,df["free_predicted_"+k]*scale,color=COLORS[2],lw=1.2,label="Free-running")
        ax.set(xlabel="Experiment day",ylabel=name)
    axes[0].legend(fontsize=7,frameon=False,ncol=3,loc="upper left",bbox_to_anchor=(0,1.19))
    finish(fig,"observed")

if __name__=="__main__":
    verify_math()
    verify_forecasts()
    style()
    design_and_paths()
    events_and_shocks()
    observed_forecast()
    interaction_map()
    print("Rebuilt eight vector figures in figures/.")
