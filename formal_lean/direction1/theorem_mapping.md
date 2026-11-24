# Direction 1 theorem map

The source is [the v3 manuscript, Section 2 and Section 5](../../outputs/Direction1_Enrichment_AML_v3/manuscript/AML_MANUSCRIPT.tex). [Supplement S1–S2](../../outputs/Direction1_Enrichment_AML_v3/supplement/SUPPLEMENT.tex) gives a ratio-coordinate calculation and independent checks of the fixed example. These source links use the original research workspace, where `formal_lean` and `outputs` are sibling directories. The formal calculation uses the paper's original time variable and the Cartesian population coordinates.

## Theorem 1 in the manuscript

Fix conversion efficiency $e>0$, predator mortality $d>0$, and a prey density $s$ in an open interval $I\subset(0,\infty)$. The prey growth factor $g$ is twice continuously differentiable on $I$, with $g(x)>0$ and $g'(x)>0$. An admissible intake $p$ is positive, continuously differentiable, and strictly decreasing on the positive ratio axis. The physical equations are

$$\dot x=xg(x)(1-x/K)-yp(y/x),\qquad \dot y=y[ep(y/x)-d].$$

Write $P(s)$ for the following property. For every admissible $p$, every $K_0>0$, and every $v>0$ with $(s,v)$ an equilibrium at $K_0$ and $\det J>0$, the equilibrium trace has strictly negative derivative with respect to $K$ at $K_0$. Only $K$ varies along the branch. The theorem states $P(s)\iff(1/g)''(s)\geq0$. If reciprocal curvature is negative, three Holling II intakes realize negative, zero, and positive derivatives at this same density.

| Mathematical object or step | Lean declaration | Interpretation |
|---|---|---|
| Original physical vector field and equilibrium | `Direction1.q`, `prey`, `predator`, `equilibrium`, `equilibrium_iff` | Both original components vanish. On the positive quadrant the load equation and predator break-even equation follow. |
| Jacobian | `Direction1.jac`, `jac_on_ray`, `trace_det` | Four coordinate partial derivatives of the full vector field are evaluated at equilibrium. Trace and determinant are computed from these entries. |
| Admissible intake | `Direction1.Admissible`, `intake_deriv` | Strict decrease on the whole positive axis implies a nonpositive derivative. Horizontal tangents are allowed by the definition. |
| Feasible loads | `Direction1.reduce_equilibrium`, `upper_iff`, `realization` | Positive determinant forces $D=g-(1+E)Q>0$, where $E=xg'/g$. Every $0<Q<g/(1+E)$ is realized at a positive-determinant equilibrium with a bounded rational intake $p(z)=(2d/e)/(1+z/\rho)$. |
| Trace slope on a ray | `Direction1.capacity_deriv`, `ray_deriv`, `slopeK_neg_iff` | $K(x)=x/(1-Q/g(x))$ has positive derivative at a regular point. Along the ray $dT/dx=QE'-g'$. |
| Local carrying-capacity coordinate | `Direction1.chart_trace_continuous`, `chart_trace`, `branch_trace` | The inverse function theorem produces a continuous branch of the actual equations on a neighborhood of $K_0$. Every continuous equilibrium graph through the point has the same derivative of its actual Cartesian trace. |
| Reciprocal derivatives and endpoint identity | `D1Core.reciprocal_first`, `reciprocal_curvature`, `endpoint`, `criterion` | The Lean second derivative is an iterated `deriv`. The upper load endpoint gives $L(U)=-sg^2(1+E)^{-1}(1/g)''$ for $L(Q)=QE'-g'$. The endpoint is excluded when quantifying positive-determinant equilibria. |
| Universal condition and converse | `Direction1.pointwise_criterion`, `physical_criterion` | The second theorem quantifies directly over continuous graphs satisfying both original equilibrium equations near $K_0$ and differentiates the actual trace along them. The converse constructs Holling II equilibria for the full open load interval. |
| All three signs under negative curvature | `D1Core.all_signs`, `Direction1.holling_slope`, `negative_curvature_three_holling_signs` | For fixed $g,e,d,s$, three strictly ordered interior loads have Holling II witnesses and actual local trace derivatives of the three indicated signs. |
| Affine growth factor | `D1Example.weak_allee_P4` | When $g(x)=r(1+\alpha x)$ with $r,\alpha>0$, the criterion implies strict trace decrease for every positive-determinant coexistence equilibrium and admissible ratio-dependent intake, including P4. The logistic case $\alpha=0$ lies outside this statement. |
| Fixed example at $K=3/2$ | `D1Example.exact_intake_admissible`, `exact_equilibrium`, `exact_matrix`, `exact_trace_det`, `exact_curvature`, `exact_enrichment`, `exact_physical_trace` | For $g=1+x^2$, $p(z)=110/(65+54z)$, and $e=d=1$, the equilibrium is $(1/2,5/12)$, $T=0$, $\det J=3/88$, $(1/g)''=-32/125$, and $dT/dK=1/9$. |

The formal expression for the physical derivative is

$$\frac{dT}{dK}=\frac{QE'(s)-g'(s)}{D/[g(s)(1-Q/g(s))^2]}.$$

Since $1-Q/g(s)=s/K_0$ at equilibrium, this is the paper's $[s^2g(s)/(K_0^2D)]\,[QE'(s)-g'(s)]$. The factor in front of the square brackets is positive.

Lean represents $g$ and $p$ by total functions on the reals. It assumes regularity only on the open domains used in the proof. All derivatives of interest lie inside those domains. The Lean theorem allows any open subset of the positive axis, so it applies in particular to the manuscript's open intervals. Positive determinant includes equilibria with zero trace. One positive trace slope at a negative-curvature point is compatible with the theorem because the necessity direction concerns *all* admissible intakes.

## Scope of the formal statements

The fixed example checks the first crossing point. Theorems about the second crossing, the local stability of a nonlinear system on either side, the general transverse crossing in Corollary 2, extinction basins in Supplement S4, and simulated or empirical results require additional formal work. The five-mechanism paper compares P0–P4. The present Lean project treats the ratio-dependent theorem and its exact example.
