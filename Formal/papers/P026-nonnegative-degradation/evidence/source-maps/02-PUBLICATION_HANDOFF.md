# Publication handoff: mixed-degradation unistationarity

The publication consists of a mathematical paper presenting only the final
uniqueness path and a separate companion supplement containing the requested
postproof consequences and reproducibility material. Both are saved in this
workspace root. No journal submission, public announcement, or repository
commit has been made.

Final status: **Postproof 16/16 PASS**; original uniqueness **2/2 PASS**;
historical guide **43/48** with five bypassed helpers. The main paper has
9 pages and the companion supplement has 7 pages. Every final rendered page
has been visually inspected. Final LaTeX logs contain no overfull/underfull
boxes or unresolved references. The final AGC checkpoint is CURRENT after
the requested proof-neutral same-cut reconciliation.

## Files

- `Unistationarity_Nonnegative_Degradation.pdf`: main research paper.
- `Unistationarity_Supplement.pdf`: quantitative and derivative consequences,
  continuation and small-degradation stability proofs, exact examples, scope.
- `manuscript.tex`, `supplement.tex`, `references.bib`: editable sources.
- `figures/`: three editable-script-produced vector figures.
- `experiments/publication_figures.py`: figure producer.
- `experiments/build_publication.py`: reproducible bounded typesetting producer.
- `publication_examples.tex`: table generated from the original exact records.
- `verification/publication.verify.json`: new strict publication receipt.
- `verification/type_v_derivative.verify.json`: new tangent-kernel receipt.
- `POSTPROOF.md`, `POSTPROOF_GRAPH.yaml`: separate postproof ledger and score.
- `results/publication_qa.json`: final artifact hashes and QA evidence.

## Exact mathematical and formal scope

The main theorem states at most one strictly positive stationary concentration
vector for source-minimal Type II_l (l>=3) and Type V reversible diluted cores,
with positive reversible rate constants and arbitrary nonnegative linear
degradation. Equality includes internal path species. Active weighted Type II
mass-action monomials remain intact; only source-minimality-forced return
paths are treated as unit chains. Type V includes every permitted pair
identification and every finite unit path.

The two original roots are **2/2 PASS**. The historical guide remains
**43/48**, with five bypassed helper tasks; this is not five mathematical gaps.
The publication receipt separately verifies:

1. `MixedDegradation.paper_mixed_degradation_unistationarity`;
2. `MixedDegradation.TypeV.tangentMatrix_nonsingular`.

It reports exit 0, no warnings, 90 authenticated local dependency modules,
and exactly `Classical.choice`, `Quot.sound`, `propext` for both declarations.
The run took 77.578 seconds. The tangent-kernel proof separately compiled in
153.875 seconds. The frozen toolchain is Lean 4.30.0; no Lean dependencies
or repository package locks were changed.

The newly formalized result is the algebraic three-row tangent coefficient
class and its determinant nonsingularity. The analytic derivative formula,
its literal source-model identification, full Schur-complement lifts, and
other postproof consequences are conventional mathematical proofs in the
supplement. They are not presented as additional fully Lean-verified source
theorems. The classification-wide five-family corollary also uses Nandan,
Nghe and Unterberger's published remaining cases and classification.

## What the follow-ups established

The diagonal determinant hypothesis forces all principal minors to be
nonnegative: large complementary shifts isolate a selected principal minor,
then a zero-shift limit removes its regularization. Expansion in the remaining
diagonal shifts gives det(A+diag(t)) >= product(t). The stationary admissibility
identity t_i=min(p_i,q_i) consequently gives

    det(-H) >= det(N)^2 product_i min(p_i,q_i) > 0.

The bound is asserted only for the retained separated Type II scope certified
by SourceBoundary. In physical coordinates the right side is divided by
product_i x_i. No bound for an expanded determinant or condition number is
asserted.

The Type V ratio extremum has an infinitesimal counterpart. At a minimum
direction with nonnegative median, all derivative-row terms are nonnegative
and the positive quadratic coefficient makes one term strictly positive.
The opposite median selects a maximum with a strictly negative row. This
annihilates every possible nonzero kernel vector for all nonnegative leakage
coefficients. The same mechanism also covers the conventional coincident
Type II derivative: its extra weight contributes B(m-1)z_j with nonnegative
coefficient, and the inverse stoichiometric matrix has positive off-diagonals.

Two exact derivative transformations matter. The linked Type V source block
has diagonal pivots -D_i<0. The endpoint transformation uses
Q=11^T-2I and the invertible multiplier 2Q^-1; at a root its derivative is
-diag(u)DG(u). For every passive chain, detailed-balance weights give a
strict Dirichlet energy identity at fixed endpoints. This proves the internal
block invertible even if all internal losses vanish. Block differentiation
then gives the usual Schur complement and determinant lift.

Local smooth continuation follows conventionally by the implicit-function
theorem, including at zero loss coordinates. Global continuation still needs
compactness away from the concentration boundary and infinity. Nonsingularity
does not imply attraction or exclude Hopf bifurcations.

At zero degradation, the square-invertible source matrix gives a unique
detailed-balanced positive state by N^T log(x*)=log(a/b). Its physical Jacobian
is similar to a symmetric negative-definite matrix. IFT and openness of the
Hurwitz condition give a locally stable positive state for every sufficiently
small nonnegative degradation vector; the uniqueness theorem makes it the
only positive state. Finally, zero concentration propagates backward along
the strongly connected forward split graph, so a nonnegative stationary state
is either the origin or strictly positive.

## Tests, failures, and what was learned

The attached follow-up and the original guide were read in full. The primary
article's classification, undegraded theorem, degradation theorem and mixed
remark were checked. The manuscript restricts its scope to reversible
extensions of diluted cores and identifies which claims use published work.

The small exact postproof experiment passed 64 derivative-support formulas,
7936 nonzero direction-sign checks, and 30 passive-chain blocks for lengths
one through four and every binary loss support. It used exact rational
arithmetic after the canonical runtime check and numerical smoke suite.
The full job was bounded by a 120-second process lease. These are diagnostics,
not proof certificates. The ten original exact stationary examples remain
available in full and are summarized in the supplement.

The first Lean tangent attempt exposed an unavailable lemma name and cyclic
Fin-index simplification issues. Explicit index conversion and a direct
positive-product argument resolved these. A deterministic heartbeat limit
required a bounded larger allowance; a declaration-comment placement error
was corrected. No theorem hypothesis was weakened and no warning was accepted.
The final receipt confirms the general coefficient result, rather than only
the finite tested directions.

MiKTeX first built both PDFs successfully, then failed to overwrite some
existing auxiliary files. A fresh temporary build directory made repeated
typesetting reliable. Vector figures use an atomic replacement to avoid the
same observed overwrite failure. The final outputs keep stable names in the
workspace root. No environment repair or dependency update was required.

Visual review found a figure-label collision and cramped rational fractions
in the example table. The label was moved clear of its arrow; the table now
uses readable slash fractions. A long formal declaration was given its own
line. Final QA is recorded separately, bound to the output PDF hashes.

AGC entry, structure, derivative and handoff gates are preserved. AGC is useful
for freshness and scope bookkeeping; its route hint still describes an
already completed historical boundary bridge and supplied no mathematical
ingredient for this sprint. Its canonical publication status is distinct
from the strict proof receipts. No protected authority graph was changed.

## Reproduction

Run from the repository root using the canonical interpreter:

```powershell
.venv/Scripts/python.exe scripts/verify_proof.py proofs/MixedDegradation/Publication.lean --timeout 600 --declaration MixedDegradation.paper_mixed_degradation_unistationarity --declaration MixedDegradation.TypeV.tangentMatrix_nonsingular --output problem_workspaces/RAF_mixed_degradation_TypeIIL_V_unistationarity/verification/publication.verify.json
.venv/Scripts/python.exe problem_workspaces/RAF_mixed_degradation_TypeIIL_V_unistationarity/experiments/publication_figures.py
.venv/Scripts/python.exe scripts/process_guard.py run --timeout 480 --owner-label mixed-publication-build -- "E:\Erdos Problems\.venv\Scripts\python.exe" problem_workspaces/RAF_mixed_degradation_TypeIIL_V_unistationarity/experiments/build_publication.py
```

The verifier enforces the pinned mathlib working directory. The PDF build
requires the already installed MiKTeX executables; Poppler supplies rendering
and text checks. The main proof remains independent of the numerical scripts
and the publication tooling.

No additional theorem is required for the main uniqueness conclusion. Further
formalization of the conventional supplement would strengthen the formal
coverage, but does not supply a missing uniqueness implication. Global
stability, persistence, global existence thresholds, and arbitrary coupled
networks remain outside the requested result.
