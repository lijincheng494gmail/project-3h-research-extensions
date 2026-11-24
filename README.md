# Project 3H | Research Extensions

[Download the reproducibility ZIP](https://github.com/lijincheng494gmail/project-3h-research-extensions/releases/download/v1.0/Project_3H_Research_Extensions_Source.zip) ·
[Read the 16-page research appendix](https://github.com/lijincheng494gmail/project-3h-research-extensions/releases/download/v1.0/Appendix_Research_Extensions.pdf) ·
[Browse all release files](https://github.com/lijincheng494gmail/project-3h-research-extensions/releases/tag/v1.0)

The authors' research drafts are available below. The appendix ends with links to the published studies and public data used in the analyses.

- Direction 1. [Five-model comparison](https://github.com/lijincheng494gmail/project-3h-research-extensions/releases/download/v1.0/Direction_1_Five_Model_Comparison.pdf) · [Reciprocal-curvature criterion](https://github.com/lijincheng494gmail/project-3h-research-extensions/releases/download/v1.0/Direction_1_Enrichment_Criterion.pdf)
- Direction 2. [Six-model comparison](https://github.com/lijincheng494gmail/project-3h-research-extensions/releases/download/v1.0/Direction_2_Six_Model_Comparison.pdf) · [Competition ordering](https://github.com/lijincheng494gmail/project-3h-research-extensions/releases/download/v1.0/Direction_2_Competition_Ordering.pdf) · [General comparison theorem](https://github.com/lijincheng494gmail/project-3h-research-extensions/releases/download/v1.0/Direction_2_General_Comparison.pdf)
- Direction 3. [Cross-domain prediction and dual readouts](https://github.com/lijincheng494gmail/project-3h-research-extensions/releases/download/v1.0/Direction_3_Cross_Domain_Prediction.pdf)


**Project_3H_Report_with_Appendix_B.pdf** is the 25-page course report. The first page links to Appendix B on page 25. Appendix A is the original formula sheet. The source copy used to build the updated report is under `course_report/`.

**Appendix_Research_Extensions.pdf** is the separate 16-page research companion. Page 1 links to each direction. Each chapter gives its own abstract, results, figures and tables, mathematical proofs, Python calculations, and Lean verification results.

| Research question | Companion pages | Files in this package |
| --- | --- | --- |
| Which results change when the predation law changes? | 2–6 | `d1/README.md` maps the comparison of P0–P4 and the reciprocal-curvature theorem to their papers, figures, code, and data. |
| How do growth and predator competition change coexistence? | 7–11 | `d2/README.md` maps the six models, the branch-ordering proof, population shocks, and algae–rotifer forecasts to their sources. |
| What does the same equation predict in other systems? | 12–16 | `d3/repro/README.md` identifies the observations, archived predictions, coefficient records, and scoring protocols used in the chapter. The full revised paper and its supplement are in `d3/research/`. |

The Version B brief, section 1.3(i), sets a 25-page limit for the written report including research appendices. It separately allows code listings and AI-use documentation. The 16-page companion is additional reading. The course report and this companion together contain two levels of detail.

## Build the PDFs

Start in this folder with a LaTeX installation providing pdfLaTeX, BibTeX, and latexmk.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error appendix.tex
cd course_report
latexmk -pdf -interaction=nonstopmode -halt-on-error Project_3H_Report.tex
```

The outputs are `appendix.pdf` and `course_report/Project_3H_Report.pdf`. Both use `front-results.tex` for the three short summaries. The full chapters are `d1/chapter.tex`, `d2/chapter.tex`, and `d3/chapter.tex`. The original course report's separate deterministic proof supplement is also included in `course_report/`.

## Replay the calculations

The PDF shows one runnable calculation per direction with inputs printed on the page. The full scripts and their datasets are listed below. From the package root, use a Python environment compatible with the chapter requirements.

```sh
python3 -m pip install -r d1/repro/requirements.txt -r d2/repro/requirements.txt -r d3/repro/requirements.txt
python3 d1/repro/branch_identities.py
python3 d1/repro/plot_matched_dynamics.py
python3 d2/repro/reproduce.py
python3 d3/repro/score_lt6.py
python3 d3/repro/scripts/reproduce.py --output d3/repro/replay
```

Direction 1 checks exact identities and five trajectories. Direction 2 checks roots, reintegrates trajectories, and scores forecasts. Direction 3 recalculates the benchmark summaries from observations and archived forecasts, checks 72 ranking margins, and reintegrates a representative pair of fits. The Direction 3 figures and scores can be replayed from the included data. The original large archive for training every Direction 3 fit is separate.

## Rebuild the formal proofs

With Lean 4.19.0 available through elan and Git installed, the first run downloads pinned dependencies. From the package root run

```sh
python3 formal_lean/verify.py --fetch-cache 1 2 3
```

The builds were replayed for this edition from empty project build directories using the pinned dependency cache. Lean accepted 44 public declarations for Direction 1, 47 for Direction 2, and 22 for Direction 3, including supporting lemmas. The audit found only standard Lean foundations. The two Direction 3 theorems about the finite observation table used no axioms. Each chapter identifies which mathematical statements were formalized. Numerical predictions and fit accuracy have separate Python checks.

The transcripts are `lean_rerun.log` and `formal_lean/direction*/audit/`. Each formal project includes a theorem map and verification report. The manuscript inventory in `formal_lean/research_documents.md` records the names and hashes in the original workspaces. Use the chapter directories in this package for local copies.

## Assembly record

Codex assembled the chapters from the existing research papers, mathematical supplements, and archived outputs. It reran selected calculations and the formal builds and inspected the compiled pages. The main course source, numerical scripts, figure map, and AI-use record are in `course_report/`. The updated course PDF adds one contents entry and one page to the prior 24-page report.


## Public release record

The public version includes the scientific inputs used by the listed replay commands. Copies of the instructor handout and its extracted text were omitted. Contact details and host paths in historical records were redacted. Historical hash records for earlier distributions describe those source artifacts. The SHA-256 file attached to this release identifies the public distribution files.

The original algae–rotifer observations are credited to Blasius et al. The [Figshare deposit](https://doi.org/10.6084/m9.figshare.10045976.v1) carries CC BY 4.0. The upstream MIT notice distributed with the observations and the MIT notices distributed with the [Shah et al. data and code](https://doi.org/10.5281/zenodo.12823159) are also included.
