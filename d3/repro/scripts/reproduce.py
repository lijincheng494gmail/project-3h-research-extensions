"""Verify the Direction 3 report from saved predictions, replay two ODE fits, and draw the figures."""
import argparse
import json
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
import numpy as np
import pandas as pd
from scipy.integrate import solve_ivp

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
INK, ECO, SPECIAL, NEUTRAL, PALE = "#222936", "#086d68", "#b35a36", "#566477", "#d9e2e3"
plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 9, "axes.titlesize": 10.5, "axes.titleweight": "bold",
    "axes.titlelocation": "left", "axes.labelcolor": INK, "axes.edgecolor": NEUTRAL, "text.color": INK,
    "axes.spines.right": False, "axes.spines.top": False, "axes.axisbelow": True,
    "legend.frameon": False, "legend.fontsize": 8, "pdf.fonttype": 42,
    "xtick.labelsize": 8.4, "ytick.labelsize": 8.4, "savefig.facecolor": "white",
})

def read(stem):
    return pd.read_csv(DATA / f"{stem}.csv")

def close(actual, expected, atol):
    np.testing.assert_allclose(actual, expected, rtol=0, atol=atol)

def save(fig, folder, name):
    fig.savefig(folder / f"{name}.pdf", bbox_inches="tight", pad_inches=.06,
                metadata={"Creator": "Project 3H Direction 3", "CreationDate": None, "ModDate": None})
    plt.close(fig)

def check_ci():
    pbt = read("pbt_example")
    close(pbt[["G7", "G8", "G9"]].mean(axis=1), pbt.observed_mean, 1e-10)
    residual = pbt[["FA_original", "CARRGO", "logistic_fixed_dose"]].sub(pbt.observed_mean, axis=0).iloc[1:]
    assert len(residual) == 225
    close(np.sqrt((residual**2).mean()), [.2678, .3736, .5381], .00005)
    ci = read("ci_by_dose")
    results = []
    for cell, bounds, expected, fixed_dose, wins in [
        ("PBT138","reference",[.288,.336],.637,4), ("HT1080","reference",[.3052,.3736],.3825,5),
        ("HT1080","bounds_control_K",[.1993,.1978],.1981,4)]:
        wide = ci[(ci.dataset == cell) & (ci.variant == bounds)].pivot(index="fold",columns="model",values="rmse_mean")
        avg = wide[["FA_original","CARRGO"]].mean().to_numpy()
        close(avg, expected, .0005 if cell=="PBT138" else .00005)
        close(wide.logistic_fixed_dose.mean(), fixed_dose, .0005 if cell=="PBT138" else .00005)
        n_wins = int((wide.FA_original < wide.CARRGO).sum())
        assert n_wins == wins and len(wide) == 6
        results.append(dict(cell=cell,bounds=bounds,ecological_ci=avg[0],carrgo_ci=avg[1],fixed_dose_ci=wide.logistic_fixed_dose.mean(),ecological_wins=n_wins))
    return results

def check_transfers():
    od = read("od_scores")
    results = {}
    for window, n, expected in [("primary_0_4h",12,1),("open_loop_0_1.0h",3,1),
                                ("open_loop_0_2.0h",3,1),("open_loop_0_4.25h",3,2)]:
        selected = od.loc[od.window == window]
        wins = int((selected.original_rmse < selected.comparator_rmse).sum())
        assert len(selected) == n and wins == expected
        results[window] = dict(conditions=n,ecological_wins=wins)
    frozen = read("frozen_lambda")
    avg = frozen[["original_rmse","comparator_rmse"]].mean().to_list()
    wins = int((frozen.original_rmse < frozen.comparator_rmse).sum())
    assert len(frozen) == 18 and wins == 8
    close(avg,[.0628,.0747],.00005)
    results["frozen_lambda_4h"] = dict(conditions=18,ecological_wins=wins,mean_rmse_od=avg)
    lines = read("frozen_lines")
    for target, expected in [("HT1080",[.587,.519]),("PBT138",[1.700,1.015])]:
        rows = lines.loc[lines.target_dataset.str.contains(target)]
        assert len(rows) == 12
        avg = rows.groupby("model").mean_rmse.mean().loc[["FA_original","CARRGO"]].to_list()
        close(avg,expected,.0005)
        results["frozen_to_"+target] = avg
    return results

STRATEGIES = [
    ("original_FA","target_only","CD33 only"), ("original_FA","near_5pct","5% target-loss band"),
    ("original_FA","joint_1","Equal-weight joint"), ("CARRGO","joint_1","CARRGO joint"),
    ("Shah_BD","joint_1","Shah BD joint"), ("growth_only_timewise","reference","Time-specific reference")]

def score_aml():
    predictions = read("lt6_predictions")
    rows = []
    for (model,strategy,genotype,ratio), group in predictions.groupby(["model","strategy","genotype","held_ratio"]):
        group = group.sort_values("source_day")
        assert group.source_day.to_list() == [3,6,10,16]
        future = group.iloc[1:]
        error = future[["predicted_cd33","predicted_cd3"]].to_numpy()-future[["observed_cd33","observed_cd3"]].to_numpy()
        rms = np.sqrt((error**2).mean(axis=0))
        rise = int(group.predicted_cd3.iloc[1] > group.predicted_cd3.iloc[0]+1e-7)
        assert group.observed_cd3.iloc[1] > group.observed_cd3.iloc[0]
        boundary_error = math.sqrt(np.mean((future.zero_cd33-future.observed_cd33)**2))
        rows.append((model,strategy,genotype,ratio,*rms,rise,boundary_error))
    folds = pd.DataFrame(rows, columns=["model","strategy","genotype","ratio","cd33","cd3","rise","boundary"])
    summary = folds.groupby(["model","strategy"]).agg(cd33=("cd33","mean"),cd3=("cd3","mean"),
                                                       rises=("rise","sum"),conditions=("ratio","size"))
    expected = [(81634,6099,0),(83611,5025,10),(197580,4990,12),(177505,5095,11),(134300,4594,12),(81648,2039,12)]
    for (model,strategy,_),scores in zip(STRATEGIES,expected):
        row=summary.loc[(model,strategy)]
        close(row[["cd33","cd3","rises"]],scores,.5)
        assert row.conditions==12
    band=read("lt6_band")
    close(band.max_allowed_target,1.05*band.best_known_target,1e-10)
    assert len(band)==12 and (band.selected_target<=band.max_allowed_target+1e-10).all()
    joint=folds.query("model=='original_FA' and strategy=='joint_1'").set_index(["genotype","ratio"])
    assert sum(joint.cd33<joint.boundary-.01)==3
    control=folds.query("model=='growth_only_constant'").set_index(["genotype","ratio"])
    assert sum((joint.cd33<control.cd33)&(joint.cd3<control.cd3))==2
    return predictions,summary

def check_certificate():
    cert=read("lt6_certificate").merge(read("target_coefficients"),left_on=["profile","genotype","ratio"],
        right_on=["profile","genotype","held_ratio"],validate="one_to_one")
    for row in cert.itertuples():
        t=json.loads(row.parameters_json)
        r,K,alpha,m,beta,e,d=[t[k] for k in ("r","K","alpha","m","beta","e","d")]
        M=max(K,row.x0)
        gamma=d-e*m*M/beta
        assert gamma>0
        A=alpha*K
        L=r*max(A-1,0)**2/(8*A)
        z=math.exp(13*L)*m/gamma*math.log1p(row.y0/beta)
        count_bound=-100000*M*math.expm1(-z)
        close(count_bound,row.count_bound,2e-7)
        assert row.largest_actual_count_gap <= count_bound + 2e-5
    margins=read("comparator_margins")
    assert len(cert)==24 and len(margins)==72
    assert (margins.absolute_RMSE_margin>margins.pointwise_bound_counts).all()
    assert (margins.full_wins==margins.boundary_wins).all()
    return cert

def replay_wt16(predictions):
    selected=predictions.query("genotype=='WT' and held_ratio=='1:16' and model=='original_FA'")
    output={}
    for row in read("wt16_vectors").itertuples():
        group=selected.loc[selected.strategy==row.strategy].sort_values("source_day")
        p=json.loads(row.parameters_json)
        x0,y0=group[["observed_cd33","observed_cd3"]].iloc[0].to_numpy()/100000
        def rates(time, log_state):
            x,y=np.exp(log_state)
            return [p["r"]*(1-x/p["K"])*(1+p["alpha"]*x)-p["m"]*y/(p["beta"]+y),
                    p["e"]*p["m"]*x/(p["beta"]+y)-p["d"]]
        solve=solve_ivp(rates,(0,13),np.log([x0,y0]),t_eval=[0,3,7,13],method="DOP853",atol=1e-11,rtol=1e-10)
        assert solve.success
        new=np.exp(solve.y.T)*100000
        delta=np.max(np.abs(new-group[["predicted_cd33","predicted_cd3"]].to_numpy()))
        assert delta<.01,delta
        output[row.strategy]=float(delta)
    return output

def line_plot(ax, frame, special, label, title, unit, time="time_h", original="original_FA"):
    ax.scatter(frame[time],frame.observed_mean,facecolors="white",edgecolors=INK,s=12,lw=.8,label="Observed mean",zorder=2)
    ax.plot(frame[time],frame[original],color=ECO,lw=1.9,label="Ecological",zorder=3)
    ax.plot(frame[time],frame[special],color=SPECIAL,ls="--",lw=1.7,label=label,zorder=4)
    ax.set(title=title,xlabel="Hours from onset",ylabel=unit)
    ax.grid(axis="y",color=PALE,lw=.65)
    ax.legend(loc="best",handlelength=1.8)

def cart_figure(folder):
    fig,axes=plt.subplots(1,2,figsize=(7.55,2.75),layout="constrained")
    line_plot(axes[0],read("pbt_example"),"CARRGO","CARRGO","A   PBT138 · 28z, 2,500 held","Cell Index",original="FA_original")
    ci=read("ci_by_dose")
    # A signed difference keeps all twelve conditions on one interpretable scale.
    groups=[("PBT138","reference","PBT138\nprimary"),("HT1080","reference","HT1080\nprimary"),
            ("HT1080","bounds_control_K","HT1080\nrelaxed K")]
    ax=axes[1]
    for i,(cell,bounds,label) in enumerate(groups):
        s=ci[(ci.dataset==cell)&(ci.variant==bounds)].pivot(index="fold",columns="model",values="rmse_mean")
        gaps=(s.FA_original-s.CARRGO).to_numpy()
        ax.scatter(i+np.linspace(-.14,.14,len(gaps)),gaps,s=24,c=np.where(gaps<0,ECO,SPECIAL),edgecolors="white",lw=.6)
        ax.plot([i-.25,i+.25],[np.mean(gaps)]*2,color=INK,lw=2)
    ax.axhline(0,color=NEUTRAL,lw=.8,ls=":")
    ax.set(xticks=range(3),xticklabels=[g[2] for g in groups],xlim=(-.5,2.5),ylabel="Ecological − CARRGO RMSE (CI)",title="B   Six product–dose holds")
    ax.legend(handles=[Line2D([0],[0],lw=2,color=INK,label="Mean difference")],loc="best")
    ax.grid(axis="y",color=PALE,lw=.65)
    save(fig,folder,"cart_held")

def phage_figure(folder):
    fig,axes=plt.subplots(1,2,figsize=(7.55,2.65),layout="constrained")
    for ax,table,special,label,title,limit in [(axes[0],"lambda_example","Geng_r_model","Geng","A   λ · January high input",4),
                                               (axes[1],"t4_example","Eriksen2020_Eq1","Eriksen","B   T4 · high input",4.25)]:
        frame=read(table)
        line_plot(ax,frame[frame.time_h<=limit],special,label,title,"Blank-subtracted OD")
        ax.set_xlim(0,limit)
    save(fig,folder,"phage_held")

def aml_figure(summary,folder):
    fig,axes=plt.subplots(1,3,figsize=(7.65,2.65),layout="constrained",sharey=True,
                          gridspec_kw={"width_ratios":[1.15,1.05,.9]})
    for ax,(column,title) in zip(axes,[("cd33","A   CD33 RMSE"),("cd3","B   CD3 RMSE"),("rises","C   Early rise")]):
        for i,(model,strategy,label) in enumerate(STRATEGIES):
            value=summary.loc[(model,strategy),column]
            if column!="rises":value/=1000
            ax.barh(i,value,height=.53,color=ECO if model=="original_FA" else (NEUTRAL if model=="growth_only_timewise" else SPECIAL))
        ax.set_title(title)
        ax.grid(axis="x",color=PALE,lw=.65)
        ax.set_xlabel("Thousands of cells" if column!="rises" else "Correct / 12")
    axes[0].set(yticks=range(len(STRATEGIES)),yticklabels=[s[2] for s in STRATEGIES])
    axes[0].invert_yaxis()
    axes[2].set(xticks=[0,4,8,12],xlim=(0,12.5))
    save(fig,folder,"aml_tradeoff")

def wt_figure(predictions,folder):
    subset=predictions.query("genotype=='WT' and held_ratio=='1:16' and model=='original_FA'")
    fig,axes=plt.subplots(1,2,figsize=(7.55,2.6),layout="constrained")
    for ax,key,title in zip(axes,["cd33","cd3"],["A   CD33 target","B   Total CD3-positive T cells"]):
        for s,col,line,label in [("target_only",NEUTRAL,"--","CD33-only fit"),("joint_1",ECO,"-","Joint fit")]:
            group=subset.loc[subset.strategy==s].sort_values("source_day")
            ax.plot(group.source_day,group["predicted_"+key]/1000,color=col,lw=1.8,ls=line,label=label)
        ax.scatter(group.source_day,group["observed_"+key]/1000,color=INK,s=24,marker="o",zorder=4,label="Observed")
        ax.set(title=title,xlabel="Experimental day",ylabel="Thousands of cells",xticks=[3,6,10,16])
        ax.grid(axis="y",color=PALE,lw=.65)
    axes[1].legend(loc="upper right")
    save(fig,folder,"aml_case")

def certificate_figure(cert,folder):
    fig,axes=plt.subplots(1,2,figsize=(7.55,2.75),layout="constrained",sharey=True)
    for ax,box,title in zip(axes,["primary","expanded"],["A   Primary bounds","B   Expanded bounds"]):
        rows=cert.loc[cert.profile==box].copy()
        rows["denom"]=rows.ratio.str.split(":").str[-1].astype(int)
        rows=rows.sort_values(["genotype","denom"],ascending=[False,True])
        x=np.arange(1,13)
        ax.vlines(x,rows.count_bound,rows.minimum_absolute_comparator_margin,color=PALE,lw=1.5)
        ax.scatter(x,rows.count_bound,s=21,color=ECO,marker="o",label="Displacement bound",zorder=2)
        ax.scatter(x,rows.minimum_absolute_comparator_margin,s=25,color=SPECIAL,marker="^",label="Nearest RMSE gap",zorder=2)
        ax.set(title=title,yscale="log",xticks=[3.5,9.5],xticklabels=["WT · 6 ratios","KO · 6 ratios"],xlim=(0,13))
        ax.axvline(6.5,color=PALE,lw=.8,ls=":")
        ax.grid(axis="y",color=PALE,lw=.65)
    axes[0].set_ylabel("CD33 count (log scale)")
    axes[1].legend(loc="center right",fontsize=7.3,frameon=True,facecolor="white",edgecolor="none",framealpha=.94)
    save(fig,folder,"ablation_certificate")

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=ROOT/"figures",help="Figure and verification output directory")
    args=parser.parse_args()
    folder=args.output.resolve()
    folder.mkdir(exist_ok=True,parents=True)
    ci=check_ci()
    transfer=check_transfers()
    predictions,summary=score_aml()
    certificate=check_certificate()
    replay=replay_wt16(predictions)
    cart_figure(folder); phage_figure(folder); aml_figure(summary,folder)
    wt_figure(predictions,folder); certificate_figure(certificate,folder)
    report={"ci":ci,"comparisons":transfer,"lt6":summary.reset_index().to_dict(orient="records"),
            "target_only_vectors":len(certificate),"rankings_preserved":72,"max_wt16_replay_error_counts":replay}
    (folder/"checks.json").write_text(json.dumps(report,indent=2)+"\n")
    print(f"Verified the report comparisons, 72 rankings, and both WT 1:16 ODE replays. Wrote five figures to {folder}.")

if __name__=="__main__":
    main()
