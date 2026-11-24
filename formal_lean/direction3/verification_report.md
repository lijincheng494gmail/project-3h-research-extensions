# Direction 3 | Verification report

On November 23, 2026, `lake build` completed successfully on Apple Silicon with Lean 4.19.0 and Mathlib v4.19.0. All 22 public theorems passed. The axiom check reported only `propext`, `Classical.choice`, and `Quot.sound` for the 20 structural, analytic, and error-comparison theorems. The two finite data theorems use no axioms. The complete source has no proof placeholders or added axioms. See the [build transcript](audit/build.log), [axiom transcript](audit/axioms.log), and [source comparison](audit/source_check.log).

## What the mathematical checks cover

The central claim concerns the trajectory produced by fixed-vector consumer ablation. A run stores all seven parameters and both starting populations. The ablation changes the initial consumer to zero. Along a regular solution of the two original equations, the consumer then stays zero, the interaction vanishes throughout the interval, and the target solves the original scalar weak-Allee growth equation. A scalar solution with zero consumer also satisfies the coupled system. This checks the mathematical operation used in Figure 5.

The other trajectory results cover nonnegativity of both populations, a conditional exponential envelope for consumer abundance, and the constant rescaling of consumer units. The envelope assumes an upper bound $M$ on the target and nonnegative populations. The error results apply to two exact forecast vectors evaluated against the same observations on a common, nonempty finite grid. They give the reverse triangle bound for RMSE and a sufficient condition for preservation of a strict ranking. The [theorem map](theorem_mapping.md) gives the assumptions and paper locations.

## Finite arithmetic and data provenance

For the observed day-3 to day-6 comparison, `python3 check_observations.py` checked SHA-256 of the bundled source and matched 24 integers in the Lean table to the corresponding decimal observations. The comparison uses exact tenths of a count. The theorem `observed_keys` checks the twelve distinct genotype-ratio keys, and `observed_early_rises` checks twelve strict increases. The external script connects the frozen CSV to the theorem input. The kernel evaluates the finite comparisons on that input.

## Results outside this verification

Forecasts from fitted parameters, model selection, held-condition RMSE values, the accuracy of predicted CD3 changes, and the three improvements in held target error from Figure 5 remain empirical or numerical results of the paper. No ODE integration or new fitting was required for the observed-value check. The 72 preserved rankings in Supplementary Note 1 also require case-specific estimates. Only the general mathematical ranking implication is part of this project.

The solution theorems quantify over existing regular trajectories. Local existence, maximal continuation, and the existence or uniqueness of all forecast values for each archived parameter tuple are outside their scope. The consumer envelope uses $M$ as a hypothesis. The proof does not derive $M=\max(K,x_0)$, the full finite-horizon target displacement estimate $M(1-e^{-Z_T})$, or its per-fit numerical values.
