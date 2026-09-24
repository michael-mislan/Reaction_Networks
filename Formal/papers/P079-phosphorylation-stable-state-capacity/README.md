# Sharp equilibrium and stable-state capacities of multisite phosphorylation

[Read the paper](../../../Applications/Phosphorylation/P079-phosphorylation-stable-state-capacity.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Exact equilibrium and stable-state capacities for sequential distributive multisite phosphorylation, with a rational construction, stability analysis and explicitly scoped algebraic formalization.

**Reproduction:** Build from manuscript/ with pdflatex main.tex, bibtex main and two more pdflatex passes; the vector figures and bibliography are included. Optional check_paper.py uses only Python standard-library rational arithmetic and local phos_sharp.py/phos_capacity.py; --full extends its finite range, not the theorem scope. Figure regeneration needs NumPy and Matplotlib. Use an explicit time/resource bound for optional replay. Original source-repository verification commands in archived README files are historical; use the public shared pinned environment described in BUILD.md.

**Formalization:** The current 34-page manuscript establishes equilibrium capacity 2n-1 and stable-state capacity n by a combination of conventional mathematics and compiled algebra. Lean proves the literal positive mass-action equilibrium lower-bound construction and selected coalescence, source-preserving retuning, feedback-gap and diagonal identities. The full stable-state capacity theorem is not a Lean endpoint. Its ceiling, interlacing and positivity arguments, determinant/slope formulas, loaded matrix derivations and limiting identities, M-matrix/Gershgorin arguments, and spectral perturbation are conventional. Conditional algebra does not establish its analytic premises. The exact finite witnesses and operational/recovery computations are not kernel-checked. Strict original console receipts bind the complete unchanged module closure and pinned environment; the equilibrium lower-bound root has a saved elaborated standard-axiom interface, while the diagonal-algebra receipt has no declaration probes.

[Historical verification review](../../papers/P079-phosphorylation-stable-state-capacity/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 10 selected modules, including shared dependencies. 25 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [StructuralAlgebra.lean](../../proofs/PhosphorylationStableCapacity/StructuralAlgebra.lean)
- [KineticFreedom.lean](../../proofs/PhosphorylationStableCapacity/KineticFreedom.lean)
- [Assembly.lean](../../proofs/PhosphorylationStableCapacity/Assembly.lean)
- [DiagonalAlgebra.lean](../../proofs/PhosphorylationStableCapacity/DiagonalAlgebra.lean)
- [Resolution.lean](../../proofs/PhosphorylationSharpness/Resolution.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
