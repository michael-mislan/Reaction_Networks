# Publication handoff: complete irreducible autocatalytic families

**PROOF 16/16 PASS; R0 GREEN locally verified. PUBLICATION 16/16 PASS.**

The final research paper is saved in the requested project workspace root:

`E:/Erdos Problems/problem_workspaces/RAF_polynomial_enumeration_irrRAFs/Complete_Irreducible_Autocatalytic_Families.pdf`

It is eight pages, 340,163 bytes, built from editable LaTeX and BibTeX. SHA-256:

`85c1bc4c43888d6f6da8ed5718d5015975fff98900bb3d6182c3268ad1f71ff6`

The publication-directory `paper.pdf` is byte-identical. `paper.tex`, `references.bib`, and `build.ps1` reproduce the typesetting; timestamps can change a rebuilt PDF hash. Nothing was submitted or published externally. Author names and affiliations were not invented.

## What the paper proves

The main result is the exact equivalence between uniform output-polynomial enumeration of all ordinary irreducible RAFs and P=NP. The paper defines nonempty ordinary RAFs, explicit independent reaction identifiers, dense original-input encoding, exact duplicate-free output, unary count, fixed-width masks, and the single-machine/single-polynomial quantifier order.

Its lower bound is the SAT source actually consumed by the compiled negative classification. The mandatory catalytic cycle forces all auxiliary reactions into any RAF. A first-enablement argument shows the reset cannot generate its own prerequisite. This gives an exact correspondence between the entire RAF family and a monotone choice predicate. Its minimal accepted sets are conflict pairs and consistent satisfying assignments. Unsatisfiable instances therefore have a known polynomial-size complete baseline family. The count-based deadline decides SAT without waiting for a satisfiable instance's possibly enormous output.

Its upper bound gives the full supported-trace SAT clauses, proves soundness by induction into real food closure, and completeness by the canonical closure witness. A filtered deletion sweep retains avoidance of every known output and produces a new irreducible RAF. Each round increases the known-family size, a negative query proves exhaustion, and all costs are polynomial in N+B under P=NP. The paper includes the actual original-input initializer polynomial and the byte-preserving finite-identifier transport needed by the machine contract.

The root source, successful strict receipt, and all 378 recorded local dependency source/artifact pairs were rechecked for freshness in this publication pass. The root still has no outer hypotheses and only propext, Classical.choice, and Quot.sound as recorded axioms. No proof file, frozen Lean dependency, or successful receipt was altered. See `theorem_concordance.md` for exact declaration mapping and `reproduce.md` for the command that can produce a separate fresh compilation receipt.

## Scope of the requested follow-ups

The attached guide was read in full. The user's narrower manuscript instruction governs the main PDF: it contains the correct final critical proof path and omits optional discovery results. The guide's other requested work was completed as companion material.

- `followups.md`: deletion survival and structural essentiality, model-assisted minimization/blocking invariant, exact completed-run solver-call count, and carefully scoped conventional completeness/certificate consequences. These are explicit proofs using existing finite Lean results; no new machine-level corollary is falsely claimed.
- `experiments/publication_completion.py` in the project workspace: small supported-trace Z3 adapter, incremental blockers, independent closure/maxRAF output checks, input validation, duplicate known-family handling, and complete/unknown/invalid-input outcomes with new-irrRAF events.
- `benchmarks/inputs.json`, `results.json`, and the pinned raw Hordijk example: exact inputs, events, resource provenance, solver-call and maxRAF counters, completed versus censored runs.
- `benchmarks.md` and `benchmarks/discovery.svg`: actual comparison table and vector plot, with `summarize_benchmarks.py` as their source.
- `LEDGER.md`: the ordered attempts, corrections, outcomes, and learned limitations, separate from the proof-campaign ledger.

No streaming, parameterized, or counting refinement was needed. No new biological curation, GUI, large numerical campaign, or machine optimization was undertaken. Formal source construction and original-input details are integrated into the main PDF; the concordance supplies repository-specific supplemental information without creating another optional PDF.

## What was tested and learned

The canonical Python check and numerical smoke suite passed. Z3 4.15.4 was already available; no solver package was installed. The guarded demonstration used one process and completed in roughly 27 seconds. There are 50 new exact checks/check groups and 57 recorded comparison runs. The original 89 tiny reference checks remain available from the proof campaign; they are a distinct record, not relabeled as new experiments.

Fixtures cover no reactions, no RAF, self-catalyzed singleton, minima of unequal sizes, overlapping minima, and distinct equal-incidence reaction identifiers. All methods that claimed completeness agreed on the exact family. Tests include every known subfamily on the tiny fixtures, duplicate known outputs, every tiny deletion set, invalid supplied members, and a zero-budget unknown result. The final adapter smoke also checked duplicate identifier rejection and reuse of the pinned source commit.

The principal experiment supported the solver-call hypothesis: for the n=3, seed47 polymer instance, model-assisted minimization required 8 SAT checks while decision-only minimization required 148; both returned all 7 cores. Timings were about 0.208 versus 0.420 seconds. Fewer calls did not universally improve time: two n=2 cases were slightly slower in the model-assisted variant. Sampling on the seven-core case returned 6, 7, and 7 cores for its three fixed seeds, while all three correctly retained unknown status.

The larger published example is a deliberate retained limitation. Both SAT variants spent their four-second budget in base construction, before a solver check, and reported unknown with zero discoveries. Exhaustive search likewise remained unknown. Sampling found three independently checked cores for each seed; no complete family size was established. This identifies setup cost as a limitation of the small Python routine rather than providing a reason to scale the experiment. All source reactions were split into separately selectable forward/reverse IDs and their annotated catalysts copied to both directions; that convention is explicit and is not asserted equivalent to grouped reversible minimality.

No result constitutes biological validation. Food availability, reaction selection, and catalyst annotations define the structural question. Structural essentiality is not measured organism essentiality, and neither sampled nor complete combinatorial frequencies are kinetic probabilities. The companion proofs explain why screening all minimal structural cores does not necessarily characterize productive larger RAFs.

## Evidence and unresolved boundaries

The compiled theorem is machine-level Lean evidence. The companion complexity corollaries are conventional mathematical proofs based on verified finite semantics. The Python implementation is not extracted from Lean. SAT completeness outcomes trust Z3 UNSAT and the Python chemistry-to-CNF translation; no checked UNSAT proof or verified Python compiler is claimed. The benchmarks are small single-run pilots, not a general performance study. Peak memory is a sequential process lifetime high-water mark, not isolated method memory.

AGC was invoked at entry and handoff. Its final result is CURRENT / current_with_unbound_authored_closure. It is helpful for identifying the separate authority-integrator record-binding action and avoiding a return to superseded historical repair guidance. Local proof closure is authenticated; the protected canonical theorem graph was not changed by the publication task. That bookkeeping action is not an unresolved mathematical premise and is not required for local publication checklist credit.

## Final PDF quality assurance

The final LaTeX passes and BibTeX exited successfully. MiKTeX's installed update-check advisory is preserved in logs; no dependency update was performed. The final LaTeX log contains zero warnings, undefined references, overfull boxes, or underfull boxes. Text extraction retained the headline theorem, all lemma titles, initializer polynomial, and bibliography. Font inspection confirmed embedded fonts with Unicode mappings.

Every final rendered page was visually inspected by the assistant:

| Page | Inspected content | Outcome |
|---|---|---|
| 1 | Title, abstract, introduction, classification | PASS: readable, aligned, no clipping |
| 2 | Closure equations, RAF definition, exact encodings | PASS: mathematical symbols and delimiters intact |
| 3 | Quantifiers, completion equivalence, support variables | PASS: links and set relations legible |
| 4 | All support clauses, proof, monotone predicate, minimal-choice lemma | PASS: equation numbers aligned; complete lemma statement on one page |
| 5 | Rule table, catalytic cycle/reset, exact normal form | PASS: table and dimensions fit cleanly |
| 6 | Reset reasoning and small-output deadline | PASS: formulas and proof transitions legible |
| 7 | Filtered deletion, total-time argument, formal root | PASS: long declaration and exact type fit |
| 8 | Initialization, identifier transport, trust boundary, references | PASS: both references together; no orphan page |

The companion plot was also inspected: its actual time series, status markers, legend, axis labels, and censoring note are readable. The automated checks and source hashes are in `qa/qa.json`. The superseded ninth-page render was removed, leaving only the eight current page images.

## Completed publication checklist

| ID | Status | Deliverable |
|---|---|---|
| P01 | PASS | Frozen root scope, existing strict receipt, current freshness audit |
| P02 | PASS | Deletion/essentiality identities proved from existing finite theorem |
| P03 | PASS | Model-assisted invariant and exact solver-call count proved |
| P04 | PASS | Selected conventional consequences written; optional streaming omitted |
| P05 | PASS | Small Z3 reference completion adapter implemented |
| P06 | PASS | Input conventions, output checks, terminal states, provenance validated |
| P07 | PASS | 50 exact checks and 57 bounded runs; timeouts retained |
| P08 | PASS | Actual comparison table, vector plot, interpretation and limits |
| P09 | PASS | Main final-path mathematical narrative and proofs |
| P10 | PASS | Companion practical method, examples, and limitations |
| P11 | PASS | Integrated formal detail, declaration concordance, reproducibility |
| P12 | PASS | Primary-source attribution and explicit evidence levels |
| P13 | PASS | Native LaTeX/BibTeX build from editable sources |
| P14 | PASS | Logs, extracted text, equations, references, font checks |
| P15 | PASS | Every final page and companion plot visually inspected |
| P16 | PASS | Final root PDF, identical publication copy, hashes and handoff saved |

There is no remaining required publication work within the user's stated scope. The larger benchmark's completeness remains unknown; it is reported as such and is not needed for the classification proof.
