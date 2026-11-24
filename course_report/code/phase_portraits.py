"""Shared visual conventions for the paper's phase planes."""
import numpy as np
from equilibria import physical
from model import growth
from stability import classify


INK = "#1d4565"
RUST = "#a14233"
GRAY = "#555555"


def arrow(ax, curve, fraction=0.45, color=INK):
    scale = np.array([np.diff(ax.get_xlim())[0], np.diff(ax.get_ylim())[0]])[:,None]
    increments = np.linalg.norm(np.diff(curve,axis=1)/scale,axis=0)
    length = np.r_[0,np.cumsum(increments)]
    if length[-1] == 0:
        return
    j = np.searchsorted(length,fraction*length[-1])
    target = min(length[j]+0.032,length[-1])
    l = np.searchsorted(length,target)
    ax.annotate("",xy=curve[:,l],xytext=curve[:,j],
                arrowprops=dict(arrowstyle="-|>",color=color,lw=0.9))


def nullclines(ax, p):
    xs = np.linspace(*ax.get_xlim(),1500)
    F = growth(xs,p)
    keep = (F > 0) & (F < p.m) & (xs > 0)
    prey = np.full(xs.shape,np.nan)
    prey[keep] = p.beta*F[keep]/(p.m-F[keep])
    predator = p.e*p.m*xs/p.d-p.beta
    ax.plot(xs,prey,":",color=RUST,label="Prey nullcline",lw=1.25)
    ax.plot(xs,np.where(predator>0,predator,np.nan),"--",
            color=GRAY,label="Predator nullcline",lw=1)


def equilibria(ax,p, labels=None):
    for i,(z,_) in enumerate(physical(p)):
        kind = classify(z,p)[0]
        marker = "D" if kind=="saddle" else "o"
        face = INK if kind.startswith("stable") else "white"
        ax.scatter(*z,s=24,marker=marker,facecolor=face,edgecolor=INK,zorder=6)
        if labels:
            ax.annotate(labels[i],z,xytext=(5,-11 if i == 2 else 5),
                        textcoords="offset points",color=INK,fontsize=9)

