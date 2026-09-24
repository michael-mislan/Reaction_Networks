# Publication handoff — 14 September 2026

**Original DET/NEG/POS guide: 48/48 PASS. Postproof/publication phase: 24/24 PASS.**
The original source theorem remains closed and unchanged. The attached review's
required follow-ups have been completed at their stated evidence levels.

## Deliverables

The 12-page paper is saved directly in this workspace root:

`Child_selection_determinants_and_unstable_cores.pdf`

Title: **Child-selection determinants and unstable cores in sequential futile
cycles**. The PDF contains four vector figures, explicit matrices and exact
certificates, conventional proofs of the quantitative and kinetic extensions,
and an appendix separating formal verification from exact algebra and numerical
illustrations. It excludes discovery subcase inventories and optional work.
No human author or affiliation was invented, and the document includes a short
preparation disclosure. It has not been submitted or published externally.

PDF SHA256:
`05f8f178640ca78af447ba3c40591c3fd8dad211b434b913d91231ab810c9860`.

The editable and reproducible package is in `publication/`:

- `paper.tex`, `references.bib`, and four vector PDFs under `figures/`;
- `postproof_checks.py`, `figures.py`, and `exact_certificates.json`;
- `PUBLICATION_CLAIM_MAP.md`, with every central claim's actual evidence;
- `README.md`, with exact verification, numerical and PDF build commands;
- `POSTPROOF_LEDGER.md`, including hypotheses, tests, failures and lessons;
- final strict Lean receipts, AGC checkpoints, and `publication_qa.json`.

## What is proved

The determinant theorem is structural: eliminate selected intermediates by a
unit-determinant block operation, then reverse enzyme-row signs. Every remaining
column becomes a restricted incidence column with at most one positive and one
negative entry. Cofactor induction proves determinant 0 or ±1. This applies to
the stated elementary enzyme-conversion class, including singular and empty
children, without enumerating all children or imposing a bound on n.

For every n≥3, the source contains the six-species ordinary unstable-negative
core with determinant 1. Its quintic has a right-half-plane root by a reciprocal
root-sum contradiction, with an explicit eigenvector linking that root to the
matrix. Proper restrictions are handled by short-cycle decomposition and one
positive-definite Lyapunov certificate. This is principal minimality, not a
claim of global smallest size.

The five-species restriction B is strictly stable at unit scaling but becomes
unstable at D*=diag(1,1,2,1,2). Its exact characteristic polynomial is
`z^5+7z^4+15z^3+13z^2+4z+4`. Its rational Routh column has exactly two sign
changes, and positive coefficients exclude positive real roots: the unstable
roots form a nonreal conjugate pair. Every proper restriction is nonunstable
under every positive scaling. The source embedding holds for every n≥3.
Consequently the six-species core is not minimal for D-instability.

For every n≥2, the positive child has dimension 2n+1 and determinant 1. Its
positive determinant and odd order imply a positive real eigenvalue under every
positive column scaling. The existing all-rate proper-restriction theorem makes
each scaled matrix principal-minimal. Its sign-conjugate graph consists of two
positive cycles sharing a hub; this sign conjugacy is not a biochemical
autocatalysis claim.

The scalar return equation identifies the spectral abscissa, gives strict
individual-rate monotonicity, homogeneous scaling and min/max rate bounds, and
gives a sharp threshold for independent diagonal losses. At unit rates,
`y(1+y)^(n−1)=1`, where `y=(1+α)^2−1`. Finite Lambert-function brackets prove
`α=W(n−1)/(2(n−1))+O(W(n−1)^2/(n−1)^2)~log(n)/(2n)`.
Thus unbounded minimal feedback size need not provide a uniform instability
margin. The exact n=10 example has three unstable roots despite a unique
positive real eigenvalue.

The complete n=3 kinetic example includes every species and reaction. Balanced
positive fluxes and explicit saturating factors realize the stated derivative
matrix at concentrations one. The full Jacobian has three right-half-plane
eigenvalues and three exact conservation zeros. Its nonzero modes lie in the
stoichiometric subspace. ATP/ADP/phosphate activities are implicit externally
maintained quantities in this effective driven model. It is neither an
elementary mass-action realization nor a proof of nonlinear oscillations or
thermodynamic realizability.

## What was checked and what changed

The original `Resolution.lean` was reverified once, including four exported
interfaces, in 32.890 seconds. Its source hash is unchanged. Two additions now
have strict exported proofs:

| Target | Exports | Verification |
| --- | --- | --- |
| `proofs/FutileCycle/PositiveAllRates.lean` | `positive_all_rates`, `positive_all_rates_minimal` | PASS, 91.187 s |
| `proofs/FutileCycle/NegativeFiveMinimality.lean` (imports `NegativeFive.lean`) | `negativeFive_core_all_n`, `negativeFive_scaled_unstable` | PASS, 104.766 s |

All exports use only `Classical.choice`, `Quot.sound` and `propext`. Warnings
were treated as errors. No `sorry`, new axiom, native computation premise,
dependency update or edited mathlib package was used. The five-species exact
determinant sign and exact root count are separately reproduced algebraic
certificates; they are not described as additional exported Lean declarations.
The quantitative return-law and Lambert results and the full kinetic example
have conventional proofs in the paper, as permitted by the adopted follow-ups.

The small exact-check script reproduces source ownership, determinants, both
explicit eigenvectors, the Lyapunov identity and positive minors, the five-root
polynomial, rational Routh columns, full kinetic polynomial, conservation/rank,
flux balance and the derivative identity. It verifies illustrated finite
Lambert bounds and computes rounded spectral values. Runs took about four
seconds under a 120-second process guard. Vector-figure runs took about eight
seconds. Only one Lean target ran at a time; no bulk enumeration was launched.

The main new formal insight was the logarithmic-derivative certificate:
`Re(p'(3i/5)/p(3i/5))=−24183425/1544506`.
If every root had nonpositive real part, this expression would be nonnegative.
This supplied a short Lean route using existing factorization machinery instead
of building a general Routh library. Initial proof-code failures involved
complex-power simplification, row reassociation, finite-index normalization and
an unused simp argument; each was resolved without changing the theorem or
weakening strict verification. The ledger records them to prevent repetition.

AGC was helpful in detecting new unconsumed proof receipts. Exact same-frontier
reconciliation restored freshness and the final checkpoint is `CURRENT`.
Historical authored-route guidance still refers to old DET/NEG/POS tasks and is
not mathematical evidence. Neither that guidance nor the prior publisher's
`NO_OPEN_FRONTIER` limitation reopens a kernel-verified theorem. No protected
theorem graph or generated-evidence commit was changed.

## Final 24-item completion table

| Group | Item 1 | Item 2 | Item 3 | Item 4 | Total |
| --- | --- | --- | --- | --- | --- |
| Source/evidence | Root recheck PASS | Definitions PASS | Source comparison PASS | Claim map PASS | 4/4 |
| Positive scaling | Full-scaling Lean theorem PASS | Scalar equation PASS | Rate bounds PASS | Loss criterion PASS | 4/4 |
| Negative scaling | Polynomial PASS | Instability certificate PASS | Proper-restriction proof PASS | Minimality distinction PASS | 4/4 |
| Quantitative behavior | Monotonicity/limit PASS | Finite bounds PASS | Asymptotic proof PASS | Numerical/spectral examples PASS | 4/4 |
| Kinetic example | Source S,R PASS | Rate-law realization PASS | Exact spectrum PASS | Conservation/energy interpretation PASS | 4/4 |
| Publication | Manuscript PASS | Figures/examples PASS | Inspected PDF PASS | Reproducible handoff PASS | 4/4 |

All twelve pages were rendered and visually inspected. An overlapping diagram
label, overfull lines, a lemma reference and a draft root-sign transcription
were corrected. The final LaTeX log has no warnings or overfull/underfull boxes;
references resolve. The workspace-root PDF is byte-identical to the final build.

There are no remaining obligations for the adopted proof and publication scope.
Classification up to subdivision, all-n unstable-mode counts, elementary
mass-action realization and nonlinear oscillations remain separate unclaimed
questions. The optional tree-recognition corollary was intentionally omitted.
