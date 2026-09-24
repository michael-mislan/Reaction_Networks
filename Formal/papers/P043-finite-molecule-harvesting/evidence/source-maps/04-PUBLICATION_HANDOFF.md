# C2 postproof and publication handoff

## Delivered paper

**Reliable Repeated Harvesting in a Finite-Molecule Autocatalytic Reactor**

- PDF: `Reliable_Repeated_Harvesting.pdf` in this workspace's root.
- Editable source: `Reliable_Repeated_Harvesting.tex` in the same directory.
- 16 pages, including the technical supplement, full error formula, dimensional coefficient table, declaration map and references.
- Figures and exact tables: `publication/`; producer: `publication_assets.py`.
- Formal root: `../../proofs/FiniteCopyReactor/PublicationResolution.lean`.
- Strict receipt: `PublicationResolution.verify.json`.
- Claim correspondence: `PUBLICATION_CLAIM_MAP.md`.
- Current source/PDF/proof hashes: `PUBLICATION_AUDIT.json`.
- Page review: `publication/QA.md`.

The paper presents the final proof path and its direct quantitative consequences. It excludes abandoned correctors, diagnostic ODE campaigns, optional lower-volume research, mechanism attribution, randomized handling extensions and discovery transcripts. Those historical records remain in the existing research ledger, not in the paper.

## Strongest established statement

For every integer V >= 200,000,000,000, every admitted restart state, every fixed r in [19,21] and d in [1/50,1/25], every controller depending on the complete preceding returned-population/five-counter list, and every finite horizon m, the full normalized literal source law has joint success probability at least (1-e(V))^m >= 1-m e(V). The event includes successful return and each individual cycle's output/cost constraints, cumulative bounds, physical-trace existence and synthesis accounting for every realizing trace.

The sharper error envelope is e(V) <= 101 exp(-V/10^10). Natural integer scale

    max(200000000000, ceil(10^10 log(101 m / delta)))

therefore gives joint success at least 1-delta for m>0 and delta>0. The paper uses 0<delta<1 for an informative reliability target. At V=200,000,000,000:

- 48,000 cycles have joint success probability at least 99%.
- 100 cycles have joint success probability at least 99.9979%.
- Final retained inventory is at least ceil(V/28).
- Net synthesis is at least m ceil(V/56)+ceil(V/28)-I_initial, hence at least the same expression with floor(161V/160) replacing I_initial.
- Every admitted start has positive net synthesis after 55 successful cycles.
- The richer compatible witness has positive net synthesis after two successful cycles.
- Exact hundred-cycle net synthesis lower bounds are 163,035,714,343 uniformly and 351,485,714,343 for the displayed richer witness.

The full joint-event product bound is constructed for the concrete list-history law. A separate product theorem applies to every measurable PhysicalHistory satisfying the literal conditional-law and actual-return equations. It assumes no success bound. The manuscript distinguishes this interface from constructing every possible raw-path feedback controller.

## What was proved and tested in this follow-up

1. The original strict root receipt and all 234 local dependency hashes were current. Event definitions, actual-return transitions, normalization, nonvacuous trace existence and source-law bridge were read and compared to the proposed publication claims.
2. Exact rational pilot checks verified the exp(4980) polynomial endpoint, the exp(20) Taylor sum through degree 36 and the stronger integer synthesis totals.
3. `LogarithmicScale.lean` proves residual absorption on the entire V>=V0 domain, the single exponential, natural logarithmic sizing, exact exponential certificate and sharp fixed-scale budgets. The absorption proof uses a sixth-degree Taylor term and an exact linear comparison, avoiding a new calculus development.
4. `SynthesisCorollaries.lean` proves the final inventory ceiling, integer/real synthesis bounds, the 55-cycle and richer-witness consequences and exact hundred-cycle arithmetic.
5. `OperationalCorollaries.lean` derives the conditional product bound from the actual one-cycle source premise, transfers it to the full normalized OperationalSuccess event, and proves all operating ratios after establishing positive denominators.
6. `PublicationResolution.lean` exports full-history logarithmic sizing, 48,000-cycle and sharper hundred-cycle theorems, plus the certified mission budget.
7. Compilation remained serial. Initial failures in LogarithmicScale and PublicationResolution were unnecessary tactic sequencing/linter issues, with one redundant tactic after a solved goal; they were corrected without weakening any statement. Every final strict receipt is successful with empty compiler diagnostics.
8. The original root and all four original exported declarations remain intact. Publication verification authenticates six interfaces; only Classical.choice, Quot.sound and propext occur in their axiom lists. Final audit finds all 238 local dependency source hashes current.
9. The scale table uses outward sufficient integers with exact Fraction Taylor certificates, not floating ceilings. Amount conversion uses exact count arithmetic and the exact SI Avogadro constant. Figures evaluate the actual error formula in logarithmic form, including the otherwise underflowing residual.
10. Source-to-prose review corrected the recovery narrative from the earlier deterministic 3/5 comparison to the actual stochastic 5/8 exponential drift. The paper now states the explicit capped tilt schedule, material barriers, terminal contraction, positive phase weights and marked counter arithmetic.
11. The PDF was built using the existing MiKTeX installation, rendered with Poppler, and all 16 final pages inspected. Protocol-box clipping and declaration-table spacing found on the first render were fixed. Final log has no overfull/underfull boxes or unresolved-reference/LaTeX warnings. No toolchain or package upgrades were made.

No large numerical campaign or full-scale SSA was launched. Canonical Python and numerical smoke checks passed. The repository Python lacks pypdf; the final audit uses existing native Poppler for PDF structure/text checks instead of modifying the locked environment.

## Reproduction commands

From `E:\Erdos Problems`:

```powershell
.\.venv\Scripts\python.exe scripts/check_python.py --quiet
.\.venv\Scripts\python.exe scripts/smoke_numerics.py
& .\problem_workspaces\RAF_C2_finite_copy_reactor_result\publication_verify.ps1
.\.venv\Scripts\python.exe problem_workspaces/RAF_C2_finite_copy_reactor_result/publication_assets.py
```

`publication_verify.ps1` records the exact six-interface invocation of `scripts/verify_proof.py`. Its wrapper enforces the pinned `mathlib4_project` working directory and warnings-as-errors. To build/render, from this workspace:

```powershell
pdflatex -interaction=nonstopmode -halt-on-error Reliable_Repeated_Harvesting.tex
pdflatex -interaction=nonstopmode -halt-on-error Reliable_Repeated_Harvesting.tex
pdftoppm -scale-to 1400 -png Reliable_Repeated_Harvesting.pdf publication/page
```

Then from the repository root:

```powershell
.\.venv\Scripts\python.exe problem_workspaces/RAF_C2_finite_copy_reactor_result/publication_audit.py
```

Publication proof source SHA-256:

    bc121e4ac55b1022a47fbff4c0f942740410709fb12aecf6f19483117260c72f

## AGC disposition and lessons

AGC was invoked at entry, new structure, compilation failures and delivery gates. Its new-proof freshness detection was useful: the final checkpoint requested the exact self-service `authority reconcile-frontier` command, which acknowledged the new strict publication receipt and its six authenticated interfaces without changing the theorem graph. Mathematical suggestions continued to point to historical already-closed source work; they did not guide the new probability proof.

The post-proof docking attempt returned exactly:

    AGC-POST-PROOF-E001: no synchronizable live frontier: NO_OPEN_FRONTIER

This is publication metadata, not a failed Lean proof. No fictitious open node, forced graph mutation or modified verification check was introduced. Logs are `postproof-reconcile.log`, `postproof-publish.log` and `postproof-final-checkpoint.log`. No generated evidence was staged or committed.

## Model boundaries

The reactor is a specified maintained schematic source, not an independently named literature conjecture or calibrated molecular apparatus. Reservoir activities stay fixed; catalyst is initially established. Resource allowances apply on the joint successful event. Pulse outcomes are conditionally independent across molecules. Within-cycle rates are uncontrolled and parameters fixed. Gross driven counts do not measure total apparatus dissipation. Initial preparation, pulse handling time and purification are outside the operational budgets. No assertion of indefinite survival, pathway necessity or autonomous finite-bath operation is made.

The optional guide extensions A-D were not activated; none is needed to deliver the requested publication package. Final completion status and task evidence are in `POSTPROOF_TASKS.json` and `STATUS.md`.
