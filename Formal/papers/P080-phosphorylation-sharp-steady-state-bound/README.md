# The 2n − 1 steady-state bound is sharp for sequential distributive phosphorylation

[Read the paper](../../../Applications/Phosphorylation/P080-phosphorylation-sharp-steady-state-bound.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A sharp lower-bound construction for positive steady states of sequential distributive multisite phosphorylation, with supporting algebra, conventional nondegeneracy analysis and exact finite stability examples.

**Reproduction:** Build from manuscript/ with pdflatex main.tex, bibtex main and two further pdflatex passes. The bibliography and vector figure are included. Optional check_paper.py uses standard-library rational arithmetic and local phos_sharp.py; --full is a substantially longer finite Routh census, so give it an explicit resource limit. Figure regeneration uses Matplotlib. Archived source-machine commands are provenance; use public BUILD.md for the pinned Lean environment.

**Formalization:** The 19-page manuscript includes a Lean theorem constructing 2n-1 distinct positive equilibria of the literal full mass-action system in one compatibility class for every positive n. Resolution and PublicationAlgebra have strict source/environment-matched receipts and saved elaborated standard-axiom interfaces. The construction uses the sufficiently-large-r coefficient estimate. The external upper bound, arbitrary prescribed ratios and rationality, interlacing and sharper positivity region, full slope/determinant formulas, openness and stability analysis are conventional. Finite Routh and substrate-window computations are not kernel proofs. The all-n stability conjecture printed here is historical: P079 establishes general stable-state capacity with different kinetics; the stronger standard-kinetics family is not thereby settled.

[Historical verification review](../../papers/P080-phosphorylation-sharp-steady-state-bound/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 6 selected modules, including shared dependencies. 8 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [Resolution.lean](../../proofs/PhosphorylationSharpness/Resolution.lean)
- [PublicationAlgebra.lean](../../proofs/PhosphorylationSharpness/PublicationAlgebra.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
