# Project 3H · Lean verification of three research directions

The projects check distinct parts of three research papers. Start with the [source document inventory](research_documents.md) to identify the original manuscripts, and use the theorem maps to find the exact mathematical statements. The original papers, fitted models, and numerical results are separate research artifacts.

| Direction | Main result checked | What the result says |
|---|---|---|
| [1 · Enrichment](direction1/verification_report.md) | [Theorem 1 and its constructive converse](direction1/theorem_mapping.md) | At a fixed prey density, reciprocal curvature is nonnegative exactly when enrichment strictly decreases the Cartesian Jacobian trace on every eligible coexistence branch. For negative curvature, Holling II responses realize each of the three possible derivative signs. |
| [2 · Competition](direction2/verification_report.md) | [Local and finite comparisons, and equilibrium counts](direction2/theorem_mapping.md) | With a common calibrated starting equilibrium and shared predator parameters, the predator densities satisfy strong Allee > weak Allee > logistic for positive competition throughout a common positive-determinant segment. Each of the four Allee models can attain the sharp upper bound of three positive equilibria. |
| [3 · Cross-domain dynamics](direction3/verification_report.md) | [Original vector field, solutions, ablation, and finite observations](direction3/theorem_mapping.md) | For any regular solution on its stated interval, zero initial consumer density keeps the consumer at zero throughout. Interaction then vanishes and the target follows the scalar growth equation. A separate finite check compares 12 pairs of observed CD3 counts. |

## Three concrete checks

1. **Direction 1.** With growth factor $g(x)=1+x^2$, intake $p(z)=110/(65+54z)$, $e=d=1$, and $K=3/2$, the positive equilibrium is $(1/2,5/12)$. The exact trace is zero, the determinant is $3/88$, and the trace derivative along an actual equilibrium branch is $1/9$. For the original affine factor $r(1+\alpha x)$ with positive parameters, the P4 application instead gives a strictly negative trace derivative. The general theorem concerns the derivative at the prescribed point. Hopf bifurcation and global attraction require additional hypotheses and proofs.
2. **Direction 2.** All three densities agree at zero competition. The proof constructs locally unique regular branches from the initial roots. The theorem orders the predator sensitivities there and their levels at strictly positive competition. It applies to matched and connected branches. The upper bound of three counts multiplicities, including for M4/M5, whose normalized equation has degree five when competition is positive.
3. **Direction 3.** The ablated run keeps all seven model parameters and the target initial condition. The proof follows the consumer along the solution. The source CSV check separately matches 24 recorded values to the Lean inputs, and Lean verifies that each day-6 count exceeds its paired day-3 count. Predictive accuracy, case-specific RMSE values, and fitted biological parameter estimates remain empirical.

## Reproduction

With elan, Python 3.9 or later, Git, and network access for the first dependency download, run the following commands from this folder. Use the pinned Lean 4.19.0 toolchain and Mathlib v4.19.0. The toolchain and manifests in each directory specify the exact versions.

```sh
python3 verify.py --fetch-cache 1 2 3
python3 verify.py 1 2 3
```

Each invocation runs `lake build` for the selected projects. The verifier asks Lean for the axiom dependencies of each public theorem, checks those against the standard foundation, and compares the dependency checkouts with their pinned revisions. Direction 3 also runs the decimal-to-integer source check. Axioms can be inspected directly in each `audit/axioms.log`. The clean-build records describe reproduction with fresh project artifacts and the pinned, already available dependency checkouts.

## Verification record · 23 November 2026

| Project | Public theorem declarations checked | Build evidence | Axiom evidence |
|---|---:|---|---|
| Direction 1 | 44 | [Clean build](direction1/audit/build.log) | [44 declarations](direction1/audit/axioms.log) |
| Direction 2 | 47 | [Clean build](direction2/audit/build.log) | [47 declarations](direction2/audit/axioms.log) |
| Direction 3 | 22 | [Clean build](direction3/audit/build.log) | [22 declarations](direction3/audit/axioms.log) |

All three projects rebuilt with empty project build directories. Each of the 113 public declarations has an explicit axiom report. Across all three reports, the only logical dependencies listed are `propext`, `Classical.choice`, and `Quot.sound`. The two theorems about the finite observation table depend on no axioms. The totals include supporting lemmas.
