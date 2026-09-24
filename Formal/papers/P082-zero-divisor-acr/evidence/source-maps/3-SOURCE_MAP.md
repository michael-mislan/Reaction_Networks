# Source and environment map

Accessed 2026-09-19, America/Whitehorse (UTC-07).

Primary text: https://arxiv.org/html/2401.00078v3 (12 November 2024).
Final journal PDF located through Oxford's repository:
https://ora.ox.ac.uk/objects/uuid:54279304-7bb0-4afc-a242-b91f4300512c/files/r1j92g886z
Journal of Symbolic Computation 128 (2025), 102398.
Direct DOI access failed, but the institutional PDF is journal typeset.

Source anchors: Definition 2.3 gives deterministic mass action; Definition 2.11
defines ACR, and Definition 2.12 defines vacuous ACR; condition (13) asks uniqueness of the positive coordinate value
giving ideal membership or a zero divisor. Question 3.13 (journal p.11) asks
both necessity and sufficiency for at-most-bimolecular networks. Section 4.1
(journal p.18) defines an elimination order by the pure-coordinate leading
monomial property. Algorithm 1 (p.21) permits such an order and reads leading
coefficients using its restriction. Conjecture 4.7 is the coverage claim.

The final PDF retains the broad elimination definition and the restricted
coefficient order. Therefore the guide's nonblock example applies to the
unrestricted-order reading of the final text as well as v3. This does not
refute existence of a successful order. The present substantive results require
a positive equilibrium; vacuous cases must remain separate. Further comparison
of the vacuity wording and Suzuki–Sato's original assumptions remains pending.

Applicable instructions: root AGENTS.md and the user-supplied identical rules.
Workspace was empty at entry, with no child instructions or workstream registry.
Pinned Lean: mathlib4_project/lean-toolchain = leanprover/lean4:v4.30.0.
Runtime check and scripts/smoke_numerics.py passed using .venv/Scripts/python.exe.
Use scripts/verify_proof.py for every proof build. Existing relevant API:
mathlib4_project/.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/Groebner.lean
provides MonomialOrder.div (unit leading coefficients, arbitrary commutative ring).
Do not modify that package. Reusable proofs belong in proofs/ACRZeroDivisors/.

AGC checkpoint exists but fails AGC-LAUNCH-E005: no problem.yaml or unique
*AGC_SPEC.yaml. Actual saved diagnostic: verification/agc_entry_structure.txt.
No authority, focus hash, or proof status has been invented. Independent
mathematics and Lean work can continue; AGC has not provided mathematical help.

Later-resolution check, 2026-09-19: queries on the exact title and Question 3.13,
the title and Conjecture 4.7, and `"zero-divisor ACR" "conjecture" resolution`
returned the source, institutional mirrors, a database entry and unrelated
work, but no later primary-source resolution. This is a bounded negative
search result, not evidence of priority or an exhaustive literature review.

The final PDF initially returned extracted text confirming the broad order
definition at journal p.18 and Algorithm 1 at p.21. Subsequent requests for
its vacuity section failed (ultimately HTTP 403). The v3 Definition 2.12
explicitly includes vacuous ACR. Accordingly the vacuity comparison remains
bounded by access: retain v3 scope and assert only nonvacuous substantive
results. This bounded access record is the alternative completion evidence
expressly permitted for task 1.2.

Located Suzuki–Sato (2003), DOI 10.1016/S0747-7171(03)00098-1, at
https://www3.risc.jku.at/Groebner-Bases-Bibliography/gbbib_files/publication_273.pdf.
Its text develops comprehensive bases over regular coefficient rings. The
exact theorem cited by the ACR paper still needs reference-level matching;
do not attribute the broad-order defect to Suzuki–Sato on this evidence.
Intermediate-elimination attribution (task 7.6) is complete; see
paper/INTERMEDIATE_ATTRIBUTION.md for the primary-source comparison. In particular,
the singleton-intermediate definition does not automatically cover our mixed
product complexes. The paper cites Suzuki–Sato for context only and does not
assume or attribute an unverified specialization theorem.
