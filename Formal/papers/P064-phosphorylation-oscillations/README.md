# Attracting oscillations in sequential distributive multisite phosphorylation: dynamic enzyme sequestration and what static elimination cannot see

[Read the paper](../../../Applications/Phosphorylation/P064-phosphorylation-oscillations.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

For every n ≥ 3, the formalization constructs positive nonconstant periodic orbits of the sequential distributive phosphorylation mass-action system with orbital asymptotic stability relative to their compatibility class.

**Reproduction:** Build from manuscript/ with pdflatex main.tex, bibtex main and two further pdflatex passes; all five vector figures, bibliography, certificate JSON and two original orbit-block NPZ files are included. Optional Python replay needs SymPy, NumPy, SciPy and Matplotlib; local phos.py and interval_arithmetic.py are included. check_paper.py --quick omits the higher-site and pulse stages; full check_paper.py invokes the copied workspace pulse checker. validate_orbit.py 7/5 and validate_orbit.py 1 regenerate finite-orbit certificates and can run for many minutes. Use explicit overall time and memory limits before any optional numerical replay. Scripts resolve inputs within manuscript/ or workspace_certificates/; no source checkout is required. The original certify_reduction.py helper, omitted from the publication bundle but imported by three certificate scripts, is supplied from the original workspace.

**Formalization:** For every n ≥ 3, `ThreeSitePhosphorylation.AllSiteAttractingFamily.all_site_attracting_hopf` proves an existential affine family of the literal mass-action system with positive rates, positive nonconstant periodic solutions, fixed conserved totals, supercritical parameter selection and whole-orbit orbital asymptotic stability relative to the compatibility class. The theorem has no hypotheses beyond n ≥ 3. Its saved strict receipt matches every included dependency and the pinned environment; its declaration uses only standard Lean axioms. This strengthens the earlier three-site periodic-existence result. Arbitrary-parent inheritance with fixed unit added-site rates, the n=1/2 exclusions, quantitative manuscript constants and the separate 2n−1 sharpness theorem are outside this result. Finite-amplitude orbit certificates remain numerical evidence; a connection of the isolated certified orbits to the Hopf branch is not asserted.

[Historical verification review](../../papers/P064-phosphorylation-oscillations/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** The all-site theorem and its receipt-matched local dependency closure are included alongside the earlier formal results. See the claim map and evidence records for their respective scopes.

Selected entry points:

- [AllSiteAttractingFamily.lean](../../proofs/ThreeSitePhosphorylation/AllSiteAttractingFamily.lean) — all-site attracting Hopf family

- [Resolution.lean](../../proofs/ThreeSitePhosphorylation/Resolution.lean)
- [ResourceAccounting.lean](../../proofs/DynamicSequestration/ResourceAccounting.lean)
- [InventoryThreshold.lean](../../proofs/DynamicSequestration/InventoryThreshold.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
