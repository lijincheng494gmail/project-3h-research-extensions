# Project 3H (Version B)

**Coexistence, stability and bifurcation in a predator–prey model with weak Allee growth and a foraging-arena response**

- **../Project_3H_Report_with_Appendix_B.pdf** is the English report with the one-page research appendix. Building the editable source here produces **Project_3H_Report.pdf**. Its formula sheet lists the Python entry point for every figure.
- **Project_3H_Report.tex** is the editable LaTeX driver. The other .tex files supply its sections.
- **Proof_Supplement.pdf** and **Proof_Supplement.tex** retain the longer deterministic derivations as a separate study companion. Numbering inside the companion follows those derivations.
- **FIGURE_MAP.csv** connects figure numbers and pages to the generated PDFs and entry points.
- **data/** contains the parameters and numerical diagnostics, including directed return results, equilibrium and bifurcation branches, the three prey-growth scenarios, and stochastic moment checks.
- **AI_Use.md** records the role of AI assistance and the limits of the checks.

The model follows the displayed equation (1.1) in the supplied Version B brief and the h = 0 case in the group's earlier Task 1–3 notes. The brief's prose mentions a separate quadratic predator self-competition term. The analysis throughout this project uses the displayed system, with predator loss dy and the interference denominator β + y. The symbol h* = Y* in the main report, called h in the proof companion and some scripts, denotes a scaled equilibrium density.

The examples in Sections 8.1–8.5 are constructed model cases. Section 8.6 uses the observed and maximum prey growth rates reported in Haque (2011), Table 6, which credits Tanner (1975). The shared parameters in those three scenarios support a controlled model comparison. Section 9 states the specific local linear noise models.

## Regenerate the figures and data

Use Python 3.12 or a compatible version and run from this directory. A virtual environment is recommended.

~~~sh
python3 -m pip install -r code/requirements.txt
python3 -B code/numerical_study.py
python3 -B code/analytical_diagram.py
python3 -B code/literature_cases.py
python3 -B code/stochastic_stability.py
(cd code && python3 -B -m unittest -v verify verify_analytical)
~~~

Each figure script writes its named files into **figures/** and, where applicable, computes the corresponding diagnostics in **data/**. Runs fail if their declared residual or stability checks fail. The verified environment used Python 3.12.13, NumPy 2.5.5, SciPy 1.18.1, SymPy 1.14.0, and Matplotlib 3.11.2. The numerical checks concern the given cases and tolerances. Theorems in the text carry their own hypotheses, and the proof companion contains the detailed derivations.

## Rebuild the PDFs

Use a current LaTeX distribution with pdfLaTeX and BibTeX. The PDFs use New TX text and math fonts, the standard AMS packages, and the author–year bibliography style supplied by the Elsevier Article package.

~~~sh
latexmk -pdf Project_3H_Report.tex Proof_Supplement.tex
~~~

The report follows the parameter-to-figure organization of Haque's 2011 article. The trajectories and diagrams in this package are generated for the Project 3H model. Read the original comparison through [Haque 2011](https://doi.org/10.1016/j.mbs.2011.07.003) and the growth-rate reference through [Tanner 1975](https://doi.org/10.2307/1936296).
