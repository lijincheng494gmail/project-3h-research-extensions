# Direction 3 reproduction

Run the following from the extracted appendix source directory.

```sh
python3 d3/repro/score_lt6.py
python3 -m pip install -r d3/repro/requirements.txt
python3 d3/repro/scripts/reproduce.py --output d3/repro/replay
```

The first calculation requires only standard Python. It reconstructs the LT6 table from the primary forecasts and observations, omits day 3 from both errors, and averages the errors over twelve held conditions. The code uses the original numerical tolerance of 1e-7 counts for a predicted increase.

The figure program comes from the project's Direction 3 results report. It recalculates the CI and OD comparisons, both frozen-transfer summaries, the seven LT6 rows, the finite-horizon bounds and 72 comparator rankings, and the wild-type 1:16 ODE trajectories. It writes five vector figures and a JSON file. The saved results in `checks.json` and the four figures in `../figures/` were checked against a fresh run. The input CSVs contain the precision used by the original reporting code. These commands replay the selected predictions and estimates. The earlier full fitting archive is named `Direction3_DualReadout_Full_Package.zip`.

## Source tables

The tables in `data/` are archived extracts from the Direction 3 results report prepared for Mainul Haque. Their source research edition is `Direction3_DualReadout_20261119`. Its revised paper, including Supplementary Notes 1–5, is supplied as `../research/REVISED_MANUSCRIPT.pdf`.

| Included file(s) | Upstream source in the Direction 3 research archive |
| --- | --- |
| `ci_by_dose.csv`, `pbt_example.csv` | `baseline/results/cart_controlled_held_scores.csv` and `cart_controlled_predictions.csv`. The individual fold keys identify the product and held dose. |
| `od_scores.csv`, `lambda_example.csv`, `t4_example.csv` | `baseline/results/next_stage_model_comparisons.csv`, `phage_predictions.csv`, and `independent_phage_predictions.csv`. The forecasts use the held conditions shown in the figures. |
| `frozen_lambda.csv`, `frozen_lines.csv` | `baseline/results/next_stage_model_comparisons.csv` and `cart_parameter_transfer_held_scores.csv`. The transfer windows are four hours for λ and 24 hours for the two cell lines. |
| `lt6_predictions.csv` | `results/scored/predictions.csv`, primary parameter range, days 3, 6, 10, and 16. Includes both markers for the target-only, joint, and reference comparisons. |
| `lt6_band.csv`, `wt16_vectors.csv`, `target_coefficients.csv` | `results/fit/target_band_audit.csv` and `results/fit/selected.csv`. These include the primary 5% choices, the two wild-type 1:16 ecological vectors, and the target-only vectors across two parameter ranges. |
| `lt6_certificate.csv`, `comparator_margins.csv` | `interpretation/tables/aml_certificate.csv` and `stage_a/results/ranking_certificates.csv`. |

The data sources and comparator models are [Sahoo et al.](https://doi.org/10.1098/rsif.2019.0734), [Shah et al.](https://doi.org/10.1186/s12935-026-04419-8), [Geng et al.](https://doi.org/10.1038/s41467-024-51913-6), [Rajnovic et al.](https://doi.org/10.1371/journal.pone.0216292), and [Eriksen et al.](https://doi.org/10.1038/s41598-020-59635-7). The [Shah data deposit](https://doi.org/10.5281/zenodo.12823159) supplies the LT6 marker table. The accompanying deposit license is retained in `data/LICENSE_LT6.txt`.
