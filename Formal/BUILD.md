# Building the formal proofs

Run the Python commands below from `Formal/`, using Python 3.11 or newer.

## Source checks

```text
python scripts/check_integrity.py
python scripts/test_migration_inventory.py
```

These check source hashes, local imports, claim inventories, PDF hashes and links.
They do not compile Lean or validate numerical experiments.

## Lean environment

Install the Lean version named in `mathlib4_project/lean-toolchain` through Elan.
From `Formal/mathlib4_project/`, obtain the pinned dependencies and Mathlib cache:

```text
lake exe cache get
```

Do not run `lake update`: the checked-in manifest fixes the dependency revisions.
All Lake commands must run from `Formal/mathlib4_project/`. The library source root
is `Formal/`, and all project modules use the `proofs.*` namespace.

## Verify a paper

From `Formal/`, this example compiles a bounded batch for P049, then audits its
declarations once its complete dependency closure has compiled:

```text
python scripts/verify.py --paper P049 --max-modules 40 --max-seconds 3600 --threads 1
python scripts/audit_claims.py --paper P049 --threads 1
```

Repeat the compilation command as needed. The runner uses one worker, treats
warnings as errors and reuses results only when source, dependency, environment
and artifact fingerprints match. Use `--help` for memory and time controls.
An unrestricted full `lake build` may require substantial time and memory.

Compilation and axiom auditing are separate checks. See [verification scope](VERIFICATION.md)
for the existing evidence and trust assumptions. To reproduce independently, use
a fresh checkout and the pinned dependency cache, without copying compiled project
artifacts from another checkout.

## Manuscripts and computations

Paper directories contain manuscript sources and, where applicable, numerical
companions. Their individual notes describe build entry points and dependencies.
Original source-machine scripts are archival unless identified as portable entry
points. [Portable-script records](migration/portable-scripts.json) identify the
explicit adaptations supplied here.
