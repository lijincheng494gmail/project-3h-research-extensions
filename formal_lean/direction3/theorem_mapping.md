# Direction 3 | Source-to-theorem map

The primary sources are the November 19 revision, `REVISED_MANUSCRIPT.tex`, and its `supplement.tex` in `zip-zip-zip-zip-2/outputs/Direction3_Writing_Review_20261119/`. The table gives the section or source lines for each declaration in `Direction3.lean`. All declarations use the namespace `Direction3`.

| Source | Lean declarations | Mathematical statement |
| --- | --- | --- |
| Methods, “Unchanged equation and domain-specific candidates,” lines 128–133 | `Params`, `Positive`, `growthRate`, `growth`, `flux`, `target`, `consumer`, `denominators`, `field_eq` | The vector field is exactly the two printed right-hand sides. Target growth is the original weak-Allee law. The same interaction flux is subtracted from target growth and enters the consumer equation with coefficient $e$. The seven printed parameters are strictly positive. For $y\ge0$, both $K$ and $\beta+y$ are nonzero. |
| Methods, line 133, and Supplementary Note 1, first paragraph | `consumerRate`, `consumer_factors`, `target_factors`, `flux_zero`, `target_axis`, `consumer_axis` | The consumer derivative factors as $a(x,y)y$, with $a=emx/(\beta+y)-d$. At $y=0$ the flux and consumer derivative vanish, and the target derivative equals intrinsic growth. |
| Supplementary Note 1, boundary solution $X$ | `Solution`, `axis_invariant`, `lift_scalar` | Every existing regular solution with $y(a)=0$ satisfies $y(t)=0$ throughout $[a,b]$. Conversely, any solution of the scalar growth equation defines a two-dimensional solution on the axis. |
| Methods, state signs checked numerically in line 156 | `nonnegative_quadrant` | Both populations remain nonnegative on any regular solution interval if they start nonnegative. Each coordinate factors as itself times a continuous coefficient. Any crossing from nonnegative to negative would have an intermediate zero, after which the coordinate stays zero. |
| Results, Figure 5 and lines 87–95; Supplementary Note 1 | `Run`, `Runs`, `ablate`, `ablation_inputs`, `ablation_trajectory` | Ablation keeps the entire parameter vector and the starting target, and sets the starting consumer to zero. The interaction vanishes along every resulting regular solution, and its target satisfies the scalar equation on the same interval. |
| Supplementary Note 1, final paragraph | `opposed_rates` | At positive states, instantaneous target decline and consumer growth hold precisely when $g(x)<my/(\beta+y)$ and $d<emx/(\beta+y)$. |
| Supplementary Note 1, first paragraph | `consumer_rate_upper`, `consumer_envelope` | Given $0\le x(t)\le M$ and $0\le y(t)$ on the interval, the per-capita consumer growth rate is at most $-\gamma$, where $\gamma=d-emM/\beta$. Thus $y(t)\le y(a)\exp[-\gamma(t-a)]$. A positive $\gamma$ gives a decaying envelope. |
| Methods, line 142; Supplementary Note 3 | `scaleConsumer`, `scaling_field`, `scaling_solution` | For $f>0$, replacing $(y,\beta,e)$ with $(fy,f\beta,fe)$ leaves the target field unchanged and multiplies the consumer field by $f$. This sends an existing regular solution $(x,y)$ to $(x,fy)$. |
| Methods, “Forecast accuracy, reference criteria, and reproducibility”; Supplementary Note 1 | `rmse`, `rmse_eq_sum`, `rmse_displacement`, `rmse_strict_ranking` | On a common nonempty finite grid, RMSE is the square root of mean squared differences. The change in error against common observations is bounded by the RMS displacement of the predictions. A displacement strictly smaller than the margin to a comparator preserves the strict ranking. |
| Results, line 64; Methods, lines 138–140; archived `LT6.csv` | `observations`, `observed_keys`, `observed_early_rises` | The table covers each of two genotypes and six ratios once. All twelve encoded day-6 CD3 observations exceed their paired day-3 observations. The companion script checks that every integer in this table equals ten times the corresponding source decimal. |

## Solution hypotheses and proof

Time can start at any real $a$, including the forecast origin. A solution is continuous on $[a,b]$ and has the stated right derivatives at all times in $[a,b)$. The statements apply to each finite forward interval on which a solution exists. At its final endpoint, continuity is sufficient. A regular trajectory has $\beta+y(t)\ne0$ throughout the indicated interval. This follows from positivity of $\beta$ and nonnegativity of $y$. The invariance proof also applies to signed solutions with regular denominators.

For a given regular trajectory, its coefficient $a(x(t),y(t))$ is continuous on the compact interval. Its absolute value has an upper bound $C$. The exact ODE then gives $|y'|\le C|y|$. Grönwall’s inequality with $y(a)=0$ gives $|y(t)|\le0$ for every $t\in[a,b]$. This derives invariance for any solution satisfying the equations. The hypothesis does not prescribe the later values of $y$.

The comparison with a separately fitted growth-only reference in Methods uses independently estimated coefficients. The fixed-vector theorem applies to the same coefficients in the original coupled run and its ablation.

## Finite observation input

The archived source is `zip-zip-zip-zip-2/work/Direction3_Robustness_20261118/data/real/independent_cart/LT6.csv`, from Shah et al.'s data deposit, DOI `10.5281/zenodo.12823159`. The byte-identical input is bundled as `data/LT6.csv` with the deposit license. The extract selects `effector=CART` and times 3 and 6 for both genotypes and all six ratios. The recorded CD3 counts have one decimal place. Multiplication by ten preserves their order and represents each selected value as an exact natural number. The Python source check uses decimal arithmetic. Lean checks the keys and all twelve strict inequalities by kernel reduction.

| Archived input | SHA-256 |
| --- | --- |
| Revised manuscript | `1886ad613b03fe7f12d14049645cf512724e2f716dba5a798ec2a62e37f73e72` |
| Supplement | `f34733db02610b6928ac8829b8952ecdbfe308dd0361b0a21f23645003e85fc4` |
| LT6 CSV | `8faaafd4d89fdc98749177fd08db3afece59dc563d37914fcb47afe5f0374eba` |
