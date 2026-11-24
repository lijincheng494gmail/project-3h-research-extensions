# Direction 2 · Prey growth and predator competition

`chapter.tex` contains the five-page appendix chapter. The three plotted figures come from the original Direction 2 results-report calculation. The replay also outputs five other study figures. All figure inputs are inside `repro/data/`.

| Chapter material | Source in this package |
| --- | --- |
| Growth curves and phase portraits | `repro/data/extended_parameters.csv`, `extended_equilibria.csv`, and `paper_phase_trajectories.csv` |
| Matched competition curves and local sensitivities | `repro/data/matched_branches.csv` and `pdf/COMPETITION_ORDERING_THEOREM.pdf` inside the revised research ZIP |
| Growth-calibration contrasts and disturbance outcomes | `repro/data/paper_paired_comparisons.csv` and `extended_shock_recovery.csv` |
| Algae–rotifer forecasts | `repro/data/real_benchmark_scores.csv`, `real_predictions.csv`, `real_folds.csv`, and `observations/` containing the authors' C1–C4 data, original readme, and license |
| Six-model comparison and proofs | `pdf/REVISED_MANUSCRIPT.pdf`, `pdf/REVISED_COMPARISON_MATRIX.pdf`, and `pdf/REVISED_SUPPLEMENTARY_INFORMATION.pdf` in `research/Direction2_Revised_Complete_20261119.zip` |
| Competition theorem and related generalization | `pdf/COMPETITION_ORDERING_THEOREM.pdf` and `pdf/GENERAL_COMPARISON_THEOREM.pdf` in the same revised ZIP |
| Formal proofs and audit logs | `formal_lean/direction2/` at package level |

With a Python 3.12 environment active, run from the appendix source directory:

```sh
python -m pip install -r d2/repro/requirements.txt
python d2/repro/reproduce.py
```

The replay checks root examples, reference equilibria, bifurcation witnesses, matched branches, recovery outcomes, and archived forecasts. It reintegrates trajectories and regenerates the eight vector plots in `d2/repro/figures/`. `d2/repro/replay.log` records the output for this appendix.

For the full original calculation, extract `research/Direction2_SixModel_Paper_Package_20261118.zip` into a separate directory, then run `bash run.sh reproduce` inside it. That package includes the model-fitting workflow. The later revised ZIP holds the cited manuscript and proof supplements.

The measured algae–rotifer records were published by Blasius et al. in *Nature* 577 (2020), 226–230. [Study](https://doi.org/10.1038/s41586-019-1857-0) · [Data release](https://doi.org/10.6084/m9.figshare.10045976.v1).
