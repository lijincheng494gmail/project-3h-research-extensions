# Direction 2 verification report

Lean 4.19.0 rebuilt all four source modules from an empty project build directory. The individual axiom reports for all 47 public theorem declarations contain only standard Lean foundations. [Build transcript](audit/build.log) · [Axiom report](audit/axioms.log)

## Main mathematical result

The original feeding model admits a strict comparison on matched branches. For every positive competition value in the common branch segment, both the prey and predator equilibrium coordinates are largest with strong Allee growth, intermediate with weak Allee growth, and smallest with logistic growth. Their starting coordinates agree. The predator derivatives at the common start follow the same strict order. Individual predator responses can have either sign.

The finite result requires only a positive determinant and the stated conditions on the growth rates and shared parameters. The manuscript's stable version further requires a negative trace. As a result, a common segment of positive sinks satisfies the formal theorem. The conclusion also applies on regular segments where the trace has another sign.

## What is proved

1. The original ODE, with predator loss `−hy²`, has exactly the positive root equations used in the proofs. The additional Cartesian calculation differentiates the original vector field and identifies its determinant at a root.
2. A continuous positive root graph with positive determinant has the stated prey and predator derivatives, one-sided at the endpoints. The proof takes secants of the two undifferentiated equations and uses differentiability of the prey growth law. It supplies the sign of the prey derivative from the equations.
3. For the original feeding law and arbitrary growth functions, a strict growth gap to the right of the matched prey coordinate orders both populations. Equal initial growth slopes are allowed. The three-law calibration supplies the gap and the local derivative order as corollaries.
4. The four named feeding laws in §4 of the general supplement share a rational response function. Lean derives rightward prey motion from a positive Cartesian determinant on the upper branch. A strict growth gap on the reached prey densities then gives both population rankings. The proof checks the Cartesian determinant against the full ODE for this family.
5. Strictly decreasing growth gives at most one positive equilibrium whenever competition is nonnegative. Logistic growth satisfies this condition. For the two Allee laws, the normalized polynomial has at most three positive roots, including multiplicity. In the positive-competition case, four positive linear factors would force incompatible signs for the quadratic and cubic coefficients. At zero competition the polynomial degree is at most three. Exact interval signs for the four published Allee examples show that three distinct positive roots are attainable at both competition settings.

## Interpretation and open steps

Starting from a single positive equilibrium with positive determinant and locally C¹ growth, `Params.exists_local_branch` constructs a regular equilibrium graph on some $[0,H]$ with $H>0$. Both coordinates are C¹ there. Near the initial prey density, every eligible equilibrium lies on this graph. The proof eliminates the predator coordinate, expresses competition as a function of prey density, and applies the inverse function theorem. For the calibrated three-model comparison, `Calibration.exists_three_ordered_branches` constructs all three curves on a common interval and orders their actual right derivatives and equilibrium coordinates. The finite ordering extends over any supplied common positive-determinant branch segment. Calculating its maximal endpoint and classifying all endpoint events remain outside the formalization. The general-predation statement for an arbitrary smooth feeding law, its higher-contact expansion, and its decreasing-nullcline case also remain open here. Global dynamical stability, numerical forecasts, and data fits are separate components of the research.

The Allee count concerns positive roots in the paper's normalized coordinate. It excludes the axis `z=0`. Formal coverage of the count stops with the upper bound, its attainment, and the root correspondence. The parameter-dependent classification by critical values and Sturm certificates in §§S2.3–S2.5 has separate evidence in the original supplement.

## Reproduction

The README gives the pinned Lean and Mathlib versions and the commands. The build log and theorem axiom report are under `audit/`. Lean accepted the checked declarations. Their printed dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
