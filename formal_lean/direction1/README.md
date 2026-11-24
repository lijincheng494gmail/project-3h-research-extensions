# Reciprocal curvature and enrichment

The target is Theorem 1 of *A curvature criterion for enrichment under ratio-dependent predation*, in the v3 manuscript. The exact example uses the original-time Cartesian vector field, with the carrying capacity as its varying parameter.

`D1Core.lean` contains the reciprocal-derivative and interval calculations. `Direction1.lean` defines the vector field, Jacobian, equilibrium, and local branch. `D1Example.lean` specializes them at the rational example.

## Reproduce

Use Lean 4.19.0, Lake 5.0.0, and Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The `lean-toolchain` and `lake-manifest.json` files pin the toolchain and dependency revisions. With Lean installed through elan and Python 3.9 or later, run these commands from this directory:

```sh
python3 ../verify.py --fetch-cache 1
lake build
```

On this Mac, the installed toolchain can also be selected with `export PATH="$HOME/.cache/project3h-lean419/toolchain/bin:$PATH"`. The first build on another computer needs network access to obtain the pinned dependencies. Subsequent checks can use `python3 ../verify.py 1` once the dependencies are available.

## Evidence

Read [theorem_mapping.md](theorem_mapping.md) for the correspondence with the research manuscript. [verification_report.md](verification_report.md) describes the checked statements and their scope. The [build log](audit/build.log), [public theorem axiom report](audit/axioms.log), and [dependency revisions](audit/dependencies.json) record the verification run.
