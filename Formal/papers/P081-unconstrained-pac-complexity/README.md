# Unconstrained detection of productive autocatalytic cores is NP-complete

[Read the paper](../../../Theory/Algorithms/P081-unconstrained-pac-complexity.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

NP-completeness of unconstrained productive-autocatalytic-core detection for finite reversible sources with binary-encoded literal nonnegative integer complexes, including formal polynomial-time reduction and NP membership.

**Reproduction:** From manuscript/, run pdflatex --disable-installer -interaction=nonstopmode -halt-on-error -jobname=unconstrained_pac_paper paper.tex twice. Bibliography is embedded, with paper.bib included for editing; no external figures or numerical inputs are required. Original source-specific build/audit scripts are preserved only as archival source maps, and should not be run as public build commands. The public integrity checker revalidates receipt-bound source hashes without relying on old .olean locations. See repository BUILD.md for optional Lean verification using the pinned shared environment.

**Formalization:** The current eight-page focused paper is supported by the hypothesis-free Lean theorem UnconstrainedPACDetection.complexity_root. The strict receipt binds its full 638-module transitive source closure, the frozen environment and four saved elaborated standard-axiom interfaces: the NP-completeness root, actual total FP compilation, all-string reduction correctness and NP membership. Cook-Levin is proved in the included dependency closure rather than assumed as a hardness axiom. The language uses literal left/right integer matrices, signed real flows and no designated target or food set; malformed strings are rejected. This structural classification does not establish kinetic realizability, elemental conservation, elementary reaction arity or performance on particular networks. Older broad reports and discovery experiments are not the selected publication.

[Historical verification review](../../papers/P081-unconstrained-pac-complexity/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 638 selected modules, including shared dependencies. 18 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [ComplexityRoot.lean](../../proofs/UnconstrainedPACDetection/ComplexityRoot.lean)
- [FormulaTotalWriter.lean](../../proofs/UnconstrainedPACDetection/FormulaTotalWriter.lean)
- [FormulaPACEncoding.lean](../../proofs/UnconstrainedPACDetection/FormulaPACEncoding.lean)
- [VerifierNPPolynomial.lean](../../proofs/UnconstrainedPACDetection/VerifierNPPolynomial.lean)
- [FormulaLinkage.lean](../../proofs/UnconstrainedPACDetection/FormulaLinkage.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
