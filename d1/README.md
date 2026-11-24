# Direction 1. Feeding mechanisms and enrichment

Run the commands below from the top level of the combined appendix package.

## Exact calculations and controlled trajectories

```shell
python3 -m pip install -r d1/repro/requirements.txt
python3 d1/repro/branch_identities.py
python3 d1/repro/plot_matched_dynamics.py
```

The first script is the unchanged v3 supplementary test. It writes 12 exact branch and mixed-model checks to `d1/repro/branch_identities.json`. For that script alone, only SymPy 1.14.0 is required.

The second reads the plotted trajectories from `results/comparison_dense_trajectories.csv` inside the comparative archive, integrates the same five model equations through time 20, and writes the full figure through time 80 to `d1/repro/matched_dynamics.pdf`. Its replay in the appendix build gave a maximum absolute coordinate difference of 1.791e-7 (rounded up). The model, integration, and plotting functions are from the Direction 1 results report. The package uses local archive paths. The supplied copy of the figure is in `d1/figures/`.

## Sources for the results

- The original comparative study is `d1/research/Project3H_Direction1_Comparative_Paper.zip`. Its `paper/PAPER_EN.pdf` and `paper/DETAILED_SUPPLEMENT.pdf` give all five model definitions, nullcline equations, stability conditions, bifurcation checks, and the chemostat evaluation. The supplement sections S1–S3 contain the five-model proofs. S4 describes the empirical comparison. The archive contains the full modeling and benchmark code, raw and processed data, and the commands in `run.sh`.
- The curvature study is `d1/research/Project3H_Direction1_Enrichment_AML_v3.zip`. In its top-level directory, `manuscript/AML_MANUSCRIPT.pdf` contains the pointwise theorem and the fixed-response example. Sections S2–S4 in `supplement/SUPPLEMENT.pdf` verify both crossings, the matched P0/P3 examples, and the invariant extinction region. `python reproduce.py` is the archive's original entry point.
- Figure 1.2 is the archived `figures/stability_crossing.pdf` in the curvature study. Figure 1.3 is its `supplement/figures/03_phase_portraits.pdf`, renamed for this appendix. The source code is `src/crossing.py` and `supplement/src/phase_portrait.py`.
- The three CSV files in `d1/repro/` reproduce Table 1.1 using the scenario A rows of `controlled_parameters.csv` and `controlled_equilibria.csv`, and both protocols in `five_ecology_bound_comparison.csv`. The algae–rotifer data come from [Blasius et al., Figshare](https://doi.org/10.6084/m9.figshare.10045976.v1) and the associated [Nature paper](https://doi.org/10.1038/s41586-019-1857-0).
- Formal theorem correspondence, code, and build evidence are under `formal_lean/direction1/` in the combined package. Set up the Lean 4.19.0 toolchain and run `python3 formal_lean/verify.py --fetch-cache 1` from the package root.

The exact example in Figure 1.2 has growth factor `g(x) = 1 + x²`. Figure 1.3 and the five-model comparison use the coursework's affine Allee factor. The ratio-dependent criterion refers to an equilibrium trace derivative in the original time variable. The Lean source checks the theorem and the first exact crossing, while the plotting scripts replay the trajectories and the separate second-crossing calculation.
