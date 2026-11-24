# Competition on matched equilibrium branches

The primary sources are the 19 November revisions of *Competition responses across three prey growth laws*, *Comparing predator responses to competition*, and the six-model paper and supplement.

Start with `Direction2.lean` for the population comparisons and counts. `D2Jacobian.lean` differentiates the original vector field, `D2Feeding.lean` covers four feeding laws, and `D2LocalExistence.lean` constructs the local branches. A comparison at positive competition is conditioned on the specified equilibrium branches. At zero competition the starting densities agree.

## Reproduce

Use Lean 4.19.0, Lake 5.0.0, and Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The `lean-toolchain` and `lake-manifest.json` files pin the toolchain and dependency revisions. With Lean installed through elan and Python 3.9 or later, run these commands from this directory:

```sh
python3 ../verify.py --fetch-cache 2
lake build
```

On this Mac, the installed toolchain can also be selected with `export PATH="$HOME/.cache/project3h-lean419/toolchain/bin:$PATH"`. The first build on another computer needs network access to obtain the pinned dependencies. Subsequent checks can use `python3 ../verify.py 2` once the dependencies are available.

## Evidence

Read [theorem_mapping.md](theorem_mapping.md) for the correspondence with the research manuscript. [verification_report.md](verification_report.md) describes the checked statements and their scope. The [build log](audit/build.log), [public theorem axiom report](audit/axioms.log), and [dependency revisions](audit/dependencies.json) record the verification run.
