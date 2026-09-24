# Publication handoff

## Delivered result

`Permanence_and_Composition_Control.pdf` is the publication-style research paper in the problem workspace root. Its matching `.tex` and `.bib` files are beside it. It presents the final donor-load -> bounded-corrector -> species-recovery proof, with a complete conventional donor appendix, rather than the discovery chronology or superseded boundary enumeration route.

The original campaign remains **60/60 PASS**, with five compiled source endpoints and 82 matching source hashes. The separate post-proof checklist is recorded in `POST_PROOF_LEDGER.md`. A completed conventional proof or investigation is not counted as a new Lean theorem.

## What changed mathematically

1. **Sharp recovery, compiled in Lean.** `SharpRecovery.lean` retains variable-speed damping. `SharpSourceRecovery.lean` instantiates it for both reference sources and both full independent-rate cubes. The explicit species floors improve to `s/(2n)` and `s/[8(n+1)]`. The source assertions reuse actual positive global existence from the original roots.
2. **Correct order in the number of consumers, conventional proof.** Coarse permanence first gives composition restoration; then `nQ/S² -> 1` improves the aggregate corrector coefficient. The resulting `c/n` floor has `c` independent of n. This avoids circularity. It is not yet a compiled new quantifier-strengthening theorem.
3. **Composition and stability, conventional proofs.** The normalized composition equation uses accumulated abundance as its clock. Quantitative ratio recovery follows, and the full equilibrium Jacobian splits into the reduced environmental block and n-1 stable composition modes.
4. **Prescribed unequal proportions, conventional source theorem.** Arbitrary fixed positive self-limitation coefficients give target proportions proportional to their reciprocals. The proof includes global bounds, the actual donor load, aggregate persistence, and resident floors under the enlarged load ceiling. This is beyond the original small cube and is explicitly not described as Lean-compiled.
5. **Supply consequences, conventional proofs.** Exact finite-time variance and uptake balances give average-abundance and uptake ceilings and zero-supply finite activity budgets. The existing compiled extinction and necessary-floor results remain intact.
6. **Small-supply branch, exact rational plus conventional proof.** A scalar polynomial encloses the unloaded donor equilibrium and proves a nonzero derivative. Explicit elimination gives donor-Jacobian nonsingularity; the reduced implicit-function theorem then gives the positive branch and its linear abundance scale.
7. **A local operating certificate.** Exact rational arithmetic proves a full seven-dimensional invariant ellipsoid for all 21 independent rates within 1e-14 of the worked reference point. It guarantees a consumer floor of 0.0203270509477 inside that initial-condition set. It also isolates a unique nearby equilibrium and proves convergence from the ellipsoid. This is a conventional certified-numerics result, not a Lean certificate.

## Tests and lessons

- Canonical repository Python entry check and numerical smoke suite passed.
- Three exact rational damping fixtures supported the sharp comparison before formal compilation.
- All four explicit source recovery declarations strictly compiled; warnings were rejected. The failures were an omitted multiplication of an equality, rational normalization, multiplication order, and unnecessary tactic sequencing. No mathematical counterexample was found.
- The initial donor test requiring all positive shifted derivative coefficients failed. A narrow-interval lower bound succeeded; the failure was a sufficient-bound failure, not a stationary-state counterexample.
- The Lyapunov radius 1e-3 failed both contraction and derivative bounds. Radius 1e-4 passed contraction but failed the quadratic derivative bound. Radius 1e-5 passed the derivative test; tolerances 1e-10 and 1e-12 still failed the inward-boundary margin. Tolerance 1e-14 succeeded. This identifies region size and forcing error, not instability, as the barriers for this chosen certificate.
- Three small ODE examples and a 25-point stationary continuation took roughly 3.3 seconds total on one BLAS thread, under a 120-second guard. They reproduce the rare-consumer, depleted-reservoir and 1:3 composition examples. Field residuals are below 2e-14; these residuals are not convergence proofs.
- `verify_publication.py` checks the manuscript's rational center, matrix, reported certificate bounds, donor interval, symbolic variance and composition identities, formal root hashes, and clean LaTeX diagnostics.
- All original five source receipts remain valid and their 82-source endpoint audit passes.

## Scope that remains open

- A global all-trajectory floor proportional to supply d as d approaches zero is not proved. The stationary branch has that scale, but a global dynamical estimate would be needed to transfer it to all trajectories.
- The added n-uniform floor, spectral factorization, arbitrary-rho source theorem, integral supply refinements and implicit-function/local-certificate arguments are conventionally proved in the paper, not fully formalized in Lean.
- The whole numerical stationary continuation is not interval-certified. The branch theorem certifies a neighborhood of zero supply; the local operating certificate treats the separate fixed d=0.05 region.
- No certified entrance time into the local ellipsoid is claimed for the rare/depleted initial states.
- No atom-balanced realization, finite-population survival theorem, autonomous apparatus, global reactor convergence, or general RAF permanence result is claimed.

## Physical and literature checks

The completed common-physical-realization workspace uses a different labelled source and different operating assumptions; it does not instantiate this donor. The paper states this source mismatch. Dimensionalization uses explicitly illustrative scales, and reservoir exchange, gross copying uptake, loss, and collection are kept distinct.

The three cited primary sources were checked through the publisher/arXiv/UCL author-repository records. The density-dependent chemostat comparison uses the publisher abstract and bibliographic record; the general feedback and experimental community-control comparisons use their primary texts. No claim of first discovering self-regulation-mediated coexistence is made.

## Reproduce

From the repository root:

```powershell
powershell -NoProfile -File problem_workspaces/RAF_permanence_with_multiple_extinctions_dynamic_limiting_reservoirs/build_paper.ps1 -ReproduceExperiments
.\.venv\Scripts\python.exe problem_workspaces/RAF_permanence_with_multiple_extinctions_dynamic_limiting_reservoirs/verify_publication.py
```

For PDF-only rebuilding, omit `-ReproduceExperiments`. MiKTeX/pdflatex and BibTeX are required. This does not update repository or Lean dependencies. The PDF build emits a MiKTeX update-check notice, but the manuscript itself has no overfull/underfull boxes, undefined citations or references after the final build.

`publication/` holds the vector figures, CSV data, rational certificates, build log, publication audit, and rendered review pages. The stable Lean files are the authoritative formal sources; `derive_sharp_sources.py` is a historical extraction helper, not part of the reproduction command and should not overwrite the finalized source file.

## AGC

AGC was helpful for identifying the current declaration failure and requesting proof-neutral freshness reconciliation after successful new evidence. It supplied no new mathematical suggestion. The exact suggested reconciliation was used, followed by a checkpoint. Original authority files and theorem status were not rewritten to manufacture closure. Final diagnostic and visual-review status are recorded in the ledger and `publication/PUBLICATION_QA.json`.
