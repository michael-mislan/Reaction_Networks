# Lean sources for "Exact common-activity compatibility of autocatalytic cores"

`lean_sources.zip` contains every `.lean` file under `proofs/ThermoCoreCompatibility/`
(77 modules: this paper's modules and the companion developments they import), the
toolchain pin, the Lake manifest that pins Mathlib, and the strict compilation
receipts for the modules cited in Table 3 of the paper.

## Toolchain

* Lean `leanprover/lean4:v4.30.0` (file `lean-toolchain`)
* Mathlib at the revision recorded in `lake-manifest.json` (input revision `v4.30.0`)

## Modules cited in the paper

| Directory | Modules |
|---|---|
| `GeneralCompatibility/` | `ClosedMargin`, `ActiveSupport`, `Interaction`, `CycleBranches`, `CycleJump`, `FiniteProgress`, `SourceImplications`, `StrictDecision`, `CandidateTransport`, `Root`, `Inventory`, `RobustExample`, `MonotoneElimination`, `Consequences` |
| `BeyondJunction/` | `MarginTransfer` (and its imports) |
| `MultiInterface/` | `WeightedPair`, `WeightedSource` |

`MonotoneElimination.lean` (vertex elimination with next-maps, the core of the
fixed-parameter algorithm) depends on Mathlib only. `Consequences.lean` (one-sided
rounding, capacity ceiling, ratio monotonicity and robustness obstruction, order-d band)
depends on `BeyondJunction/MarginTransfer.lean`.

## Checking

Module names are of the form `proofs.ThermoCoreCompatibility.<Dir>.<Module>`, so the
`proofs/` directory must sit at the source root of a Lake package that requires the pinned
Mathlib. A minimal `lakefile.toml` for that purpose:

```toml
name = "thermo_core_compatibility"
defaultTargets = ["proofs"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.30.0"

[[lean_lib]]
name = "proofs"
globs = ["proofs.+"]
```

then `lake exe cache get` and `lake build`. This scaffold is provided for convenience and
was not exercised when the archive was packed; the receipts in `receipts/` were produced by
the project's own verifier (`scripts/verify_proof.py`), which compiles each module against the
same pinned Mathlib with warnings promoted to errors, records the source hash, and checks the
axioms of requested declarations. No module contains `sorry`, an added axiom or `native_decide`.

## What is and is not formalized

Formalized: source identities and the response band; explicit inverse and the two
implications; min-closure and least state; tight-support coverage; forced cycle root and
no-root rejection; finiteness of cycle roots under analyticity; the token argument for finite
progress; the policy counterexample; candidate transport; strict productivity iff weak
feasibility at a stable threshold (root theorems); vertex elimination with next-maps; one-sided
rounding; capacity ceiling `(3-2*sqrt 2)`; ratio monotonicity and the `r+ >= 2 r-` obstruction;
order-d band; least inventory; example arithmetic.

Not formalized (conventional proofs in the paper): graph traversal and cycle extraction,
analyticity of composed maps, quantifier elimination and cylindrical decomposition, branch
stability, Davenport-Schinzel envelope bounds, and both complexity theorems.
