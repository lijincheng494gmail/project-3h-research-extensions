# Direction 1 verification report

On November 23, 2026, `lake build` completed successfully with Lean 4.19.0 and Mathlib v4.19.0. An explicit `#print axioms` check of all 44 public theorem declarations across three files reported only `propext`, `Classical.choice`, and `Quot.sound` for each one. The build checked the general result, the affine-growth application, and the rational example below.

## General theorem

Lean checked both directions of Theorem 1 for general growth and intake functions. `Direction1.physical_criterion` states the equivalence using the derivative of the Cartesian Jacobian trace on continuous graphs of the two original equilibrium equations near the reference carrying capacity. The proof constructs a local graph through each positive-determinant equilibrium and gives the same derivative for every such graph. It keeps the prey growth, intake, conversion efficiency, mortality, and time scale fixed as carrying capacity changes.

The proof also covers the last sentence of Theorem 1. At each density where reciprocal curvature is negative, `Direction1.negative_curvature_three_holling_signs` constructs three interior loads, positive capacities, and corresponding globally admissible Holling II intakes. The original vector field vanishes, the determinant is positive, and the local trace derivatives are negative, zero, and positive, respectively. The witnesses can use different intake parameters.

## Mathematical checks

- The Jacobian consists of four coordinate derivatives of the original differential equations. After differentiation, the equilibrium equations give the trace and determinant in the paper.
- Strict decrease of intake permits a zero derivative. The proof uses the strict positive determinant when deriving the sign of the density derivative of prey growth and the open load interval.
- The carrying-capacity chart has nonzero derivative at the reference density. The inverse function theorem supplies a local continuous equilibrium graph. Differentiation of the actual trace along that graph gives the enrichment derivative.
- The reciprocal second derivative and the affine endpoint identity give strict trace decrease at every admissible interior load even when the curvature is zero.
- The load construction in the converse proves existence of an equilibrium and checks its determinant. The mathematical assumptions require no universal existence of equilibria for every input function.

## Two applications

For the original weak-Allee growth factor $g(x)=r(1+\alpha x)$, $r,\alpha>0$, `D1Example.weak_allee_P4` proves strict local trace decrease on every positive-determinant branch of an admissible ratio-dependent intake. At the exact example with the different growth factor $g(x)=1+x^2$ and fixed intake $p(z)=110/(65+54z)$, the kernel checked the positive equilibrium $(1/2,5/12)$ at $e=d=1$ and $K=3/2$. Its Cartesian Jacobian is

$$J=\begin{pmatrix}9/22&-13/22\\15/44&-9/22\end{pmatrix}.$$

The exact trace is zero, the determinant is $3/88$, and reciprocal curvature is $-32/125$. `D1Example.exact_physical_trace` supplies an equilibrium graph near $K=3/2$ and proves that its Cartesian trace derivative is $1/9$. This calculation uses rational constants interpreted in the real numbers.

## Scope

The theorem assesses a local derivative. The sign of the trace itself, the existence of a limit cycle, and the basins of attraction require separate arguments. Corollary 2 of the manuscript further tunes the intake to give a zero trace and a transverse loss of local stability at arbitrary negative-curvature points. The general tuning and classification in that corollary remain outside this formalization. The paper's second stability crossing, the P0–P3 comparison, and its numerical and empirical findings also remain outside it.

See the [declaration map](theorem_mapping.md), [reproduction instructions](README.md), [Lake build transcript](audit/build.log), and [public theorem axiom audit](audit/axioms.log).
