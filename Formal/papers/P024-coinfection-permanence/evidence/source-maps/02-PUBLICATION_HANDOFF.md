# Publication handoff

Date: 2026-09-14. Final paper: `paper.pdf`, saved in this problem workspace root.
Length: 11 pages. Editable sources: `paper.tex`, `paper.bib`. Build instructions:
`REPRODUCE_PAPER.md`. Detailed successor deductions: `PUBLICATION_FOLLOWUPS.md`.

## Delivered result

The paper explains exactly the completed selected root: a full-cover,
same-boundary-state overlap characteristic-polynomial identity, and uniform
individual-species permanence for the literal fourteen-reaction source under
positive rates, existence of both single-strain residents, and strict mutual
invasion. It includes the entire necessary conventional proof and a compact
mapping to the formal declarations. Discovery-only lemmas, optional parameter
examples, trajectory plots and bifurcation extensions are excluded from the
manuscript, as requested. One vector diagram explains the shared compartment
and the critical proof implication.

The source is explicitly attributed to the reduced coinfection reaction model
in Section 6 of arXiv:2510.26526v2, with constant recruitment. Densities and rate
units are specified; loss may aggregate death and permanent removal, while the
four-compartment source has no tracked recovery or immunity compartment.
Permanence does not imply convergence of the interior dynamics or a desired
health outcome.

## Completed follow-ups and their evidence

1. `PublicationEndpoint.lean` adds `publication_permanence`, combining a common
   floor for every positive trajectory with global positive existence and
   forward uniqueness for each positive initial state. It imports the unchanged
   `Root.lean`. The new uniqueness proof obtains a common total-count bound and
   applies the existing Gronwall comparison. Strict receipt:
   `PublicationEndpoint.verify.json`, 51 current source files checked.
2. `PublicationCertificates.lean` proves the negative positive-covector
   criterion, the resident quadratic Lyapunov identities, the forbidden-entry
   implication for a regular splitting, the exact beta threshold determinant,
   and the entire independent one-percent parameter-box covector certificate.
   Strict receipt: `PublicationCertificates.verify.json`, seven sources checked.
3. `UncertaintyPermanence.lean` proves `one_percent_permanence`, applying those
   rational bounds to the actual source's invasion hypotheses and then the
   existing all-trajectories permanence theorem. Strict receipt:
   `UncertaintyPermanence.verify.json`, 53 sources checked. Its epsilon can
   depend on the constant parameter vector; it is not one common epsilon for
   the whole parameter box.
4. The existing fixed-witness certificate was inspected and its explicit floor
   extracted: exp(-5)/(7000^2*259200). It is a certified but conservative
   concentration bound, not a simulation minimum. It is outside the general
   proof's necessary path and therefore outside the manuscript.
5. The follow-up memo supplies conventional derivations for nonlinear local
   attraction under negative invasion, the resulting strict classification,
   source-interpretable NGM matrices, regular-splitting threshold transfer,
   realized-signature factorization and inclusion-exclusion. These deductions
   are identified as conventional and not substituted for missing Lean theorem
   declarations. The stronger unchanged-entire-DFE-Jacobian obstruction is
   preserved there as well.

## What was tested and learned

The canonical Python entry check and full numerical smoke suite passed. The
guarded `publication_followups.py` diagnostic completed in about one second.
It checked two Lyapunov identities, exact rational uncertainty margins and
resident bounds, the threshold determinant, and the proposed projected
threshold coefficients. There was no large search or new ODE simulation.

The one-percent result is robust to independent variation of all fourteen
rates because the resident coordinates were bounded symbolically, not frozen
at nominal values or checked only at sampled corners. Expanding the weighted
columns before interval bounding retains the gamma cancellation. The exact
normalized margins are 5601/101000 and 8701/25250. Lean now verifies these
inequalities and their implication to source permanence.

The negative-resident Lyapunov matrix has an exact positive determinant and
strict quadratic tangent drift. Combined conventionally with a contracting
missing-species covector, it yields a local attracting positive neighborhood.
This identifies a concrete path to the missing formal reverse implication,
without confusing local attraction with global competitive exclusion.

The threshold projection coefficients are 7/20 and -158/175. They support the
recorded conventional implicit-function calculation, but the full bifurcation
statement is not formally certified. A common parameter-neighborhood floor
also requires a parameterized compact-flow extension. Neither is needed for
the released paper, and the attachment explicitly permits their deferral.

Initial certificate compilation exposed finite-vector reduction, redundant
post-`field_simp` tactics, and a syntactic rational-normalization mismatch. These
were corrected in place. An expensive arithmetic tactic was narrowed to the
two product bounds and one loss bound it actually needed; the local heartbeat
allowance was made explicit. All final compiles have zero warnings and errors.
Failed receipts remain recorded as failed attempts, not as mathematical
counterexamples. Lean jobs were serial and other agents' processes untouched.

## Literature and limits

Both cited preprints were inspected, including the original source reaction
table in the full arXiv PDF and the 2026 two-siphon theorem's actual assumptions.
The paper distinguishes a source-specific direct proof from the existing
conditional framework. Publisher pages for Mathematics 14(1),23 and
14(18),3271 were inaccessible, so final-version novelty comparison remains
open. No claim that the general literature problem is solved is made.

`PUBLICATION_STATUS.json` records **12/20 successor PASS, eight OPEN**. PASS
uses explicitly labeled evidence levels (compiled proof, conventional
deduction, audit or artifact). The eight open items are:

- Final-version literature comparison.
- Full nonlinear local-attraction Lean theorem.
- Full strict permanence-equivalence Lean theorem.
- Complete threshold/obstruction compilation bundle.
- General inverse and regular-splitting threshold transfer in Lean.
- Full finite-family characteristic factorization in Lean.
- Common parameter-neighborhood floor in Lean.
- Local threshold asymptotics in Lean.

The original ledger remains **42/48 PASS**, with its six broader bundles open.
These lists are not claims that eight mathematical counterexamples or blockers
have been found. They identify remaining successor scope accurately. The
selected root and publication endpoint have no remaining proof-critical
obligation.

## Artifact and formal QA

`PUBLICATION_AUDIT.json` checks the unchanged Root receipt and all three new
receipts against their current source hashes. All authenticated interfaces
use only propext, Classical.choice and Quot.sound. There are no compiler
warnings, `sorry`, extra axioms or unchecked native proof computations in the
verified endpoints. Dependencies were not updated and no proof-package source
was edited.

The PDF was built with installed MiKTeX, automatic installation disabled, and
BibTeX references resolved. All eleven pages were rendered with Poppler and
visually inspected. The formal mapping table's spacing was corrected, the
latest affected pages rechecked, and geometric bounds verified for every
extracted word. The final LaTeX log contains no overfull or underfull boxes or
unresolved references. Poppler's text extraction emitted legacy math-font
control codes; the audit strips only XML-invalid controls from its in-memory
parser input, leaving page geometry and the actual PDF unchanged.

AGC checkpoints were used at entry, new structures, compiler failures and
handoff. Same-frontier reconciliation bound the new saved proof inputs without
changing theorem status. Its final freshness status is CURRENT, while its
mathematical-next-action still quotes an obsolete already-completed route.
It was useful for freshness and receipt binding, not for the mathematical
choice of the publication proof. Protected theorem graphs were not edited;
no generated evidence was staged or committed.
