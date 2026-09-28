# Granularity paper: research and verification handoff

Date: 27 September 2026.

## Deliverable and scope

The publication source is `Granularity_and_Coordinate_Interfaces.tex`; its PDF
is saved alongside it in this workspace root. The central result concerns a
D-stable finite real core, positive first-order leaves attached at one coordinate,
and arbitrary positive rates. It is not a solution of general D-stability.
R-GENERAL and R-MOVING-PLANE-COVERAGE remain parked under the user's scope change.

The exact threshold is the infimum of nonnegative static coordinate loads
admitting strict D-instability. Below it every partition is stable; at equality
the endpoint determinant alone decides stability, and every nonzero eigenvalue
is strictly left-half-plane; above it every sufficiently fine positive partition
has a strictly unstable finite positive scaling. The tolerance is uniform over
the number of leaves and the partition. This is a static reduction, not an
arbitrary-dimensional decision procedure.

## What changed in our understanding

1. **Safety has a direct spectral proof.** For z=sigma+i omega in the closed
   right half-plane, set d=(1+sigma t)^2+omega^2 t^2,
   alpha=rt/d and x=r(1+2 sigma t)/d. Then
   r/(1+zt)+z alpha=x. For nonzero z, 0<x<r. The free rate at the same
   coordinate absorbs the imaginary response and maps the actual attached
   eigenpair to a static core eigenpair. A continuation theorem is unnecessary
   for this central implication.
2. **The converse is finite and constructive.** Split a sufficiently fine
   partition at the first partial sum above a known unstable static load.
   Give the two groups suitable common finite inverse rates. Their effective
   static load is exactly the desired load; their total inverse-rate correction
   is smaller than the original port inverse rate. Reversing the identity
   preserves the original unstable eigenvalue exactly. There is no hidden
   infinite-rate witness or contour-limit step.
3. **Marginality cannot hide below the threshold.** The determinant/cofactor
   quotient is continuous near a contact and has nonzero denominator because
   the unloaded core is D-stable. A small real displacement of the eigenvalue,
   together with a small port-rate and load correction, creates strict growth.
   The same proof handles zero frequency. No stability assumption on the
   deleted principal block is needed.
4. **Partition geometry explains the contrast.** At fixed real response, a
   partition has a lower protective height given by a minimum of semicircles
   indexed by subset sums. Fragmentation can lower that height even at unchanged
   total load. A sampled core trace cannot certify the supremum envelope.
5. **Four states are necessary for this fixed-core phenomenon.** The cubic
   principal-minor gap is concave along coordinate loading, precluding static
   reentry for cores of order at most three. The four-state example attains
   the minimum. This rules out the suggested three-state fixed-core Goodwin
   application; changing a nonlinear equilibrium is a different comparison.

## Exact experiments and diagnostics

`experiments/publication_followups.py` first reproduces the established B(5)
strict-growth witness. It then certifies the moderate B(6) equal-split witness
using exact rational arithmetic. Rates are

    (617/1000, 617/1000, 617/1000, 35, 158/5, 4/125).

The exact Routh first-column signs are +,+,+,+,-,+,+, so there are two
right-half-plane roots. All polynomial coefficients are positive, excluding
positive real roots. The achieved rate spread is 4375/4=1093.75. This is an
upper bound on the spread needed by this example, not an optimality claim.
The full characteristic coefficients and Routh column are saved in
`evidence/publication_followups.json`.

The same script checks the absorption identity, a 60-leaf finite-realization
control by its exact Schur equation, and a two-level reciprocal-chain control.
The latter has response 2/5-3i/10 and DC gain 2/3. This bounded tree pilot
supports the recursive Schur formula; it is not a general tree decision theorem.

`experiments/partition_edge_certificates.py` proves the stable (19/10,1/10)
verdict through four exact terminal-edge certificates and stable corners.
Literal characteristic polynomials are checked before the ordered-variable
positive-coefficient Hurwitz certificates are accepted. Output is
`evidence/partition_edge_certificates.json`. Thus the stable unequal split
and unstable equal split are exact results at the same total, not inferences
from a numerical plot.

`experiments/publication_geometry.py` produces the paper figure. The plotted
core response is explicitly only a sampled equal-inner-rate trace, not the
unknown full envelope. The exact certificates, not that trace, prove the verdicts.
All experiments used the canonical repository Python, small calibrated models,
and bounded process guards. No brute-force campaign was launched.

## Follow-up dispositions and attribution

`PUBLICATION_FOLLOWUP_AUDIT.md` records each reviewer item and the corrections.
The hub theorem needs stable modules, so it does not subsume the arbitrary
coordinate-core theorem. Its positive DC margin supplies a stable base point
by slowing the hub; an additional base-point assumption is unnecessary.

The multiport result uses the entire open static box. The reciprocal result
is a safety theorem for a fixed relaxation subnetwork, not a converse allowing
independent adjustment of its modal rates. The explicit two- and three-state
threshold prescriptions use classical small-dimensional criteria.

Negative-imaginary theory (Lanzon and Petersen), relaxation systems (Willems),
classical value-set/zero-exclusion methods, and the prior decoy/retroactivity
literature are credited. The arbitrary core need not be negative imaginary
under every scaling, so that theory does not already supply our threshold.
The paper claims no priority for decoy-induced oscillations. It also avoids
claiming that a maximum response height alone determines the full rate spread.

The loss/return formula for a degrading bound site is r=ku/(u+delta), with
port loss k. Stable endpoints are extra assumptions for a literal reentry
interpretation. The example is a linear interface mechanism, not a calibrated
biochemical clock, and proves no nonlinear Hopf bifurcation or limit cycle.

## Formal scope and reproduction

The final assembly is strictly verified:
`DStabilityCharacterization.Granularity.granularity_threshold` in
`proofs/DStabilityCharacterization/Threshold.lean`.
The source-matched receipt reports `verified: true`, exit code 0, empty
diagnostics, and a 117-second verification run. The source SHA-256 is
`2e515988238c2dcb4d8b0143f1aa510ca90c7d1bc90421633a24014a70055520`.
The exported axiom list is exactly `propext`, `Classical.choice`, `Quot.sound`.
Its content uses the existing literal `DStable`, `DUnstable`, `rightScale`,
and `HasEigenpair` definitions. Its premises do not include a spectral bridge,
coverage oracle, assumed marginality theorem, or assumed realization theorem.

The critical chain is Granularity (actual matrix safety), StaticMarginality
(contact perturbation), FiniteRealization (uniform finite partitions),
TraceGrowth/DiagonalGrowth (finite sharp upper bound), ZeroEndpoint (actual
zero eigenpairs at every scaling), and Threshold (all branches together).
The separate SpectralContinuation module supplies a verified no-crossing
bridge but is not an assumed input to the main threshold theorem.

Reproduce from repository root:

```powershell
& '.venv/Scripts/python.exe' scripts/verify_proof.py proofs/DStabilityCharacterization/Threshold.lean --timeout 600 --declaration DStabilityCharacterization.Granularity.granularity_threshold --output problem_workspaces/RAF_D_stability_characterization/evidence/threshold.verify.json
```

The verifier uses the frozen mathlib environment and treats warnings as errors.
The source-matched receipt, exported statement and axiom report are authoritative;
mere arithmetic certificates or a successful dependency import are not substitutes.

The additional multiport, reciprocal, exact-envelope and minimum-dimension
theorems are conventional proofs, independently reviewed. Their complete Lean
formalization is outside the completed central theorem: it needs multiaffine
propagation, positive-residue spectral decomposition, convex slice geometry,
and the cubic optimization/concavity bridge. The rational example's generic
quintic/sextic Routh spectral consequences are likewise not claimed as Lean
theorems. These are explicitly distinguished in the paper.

No general-problem theorem graph is closed by these results. AGC receipt
reconciliation is proof-neutral and must not be read as resolution of the
parked original conjecture. No generated evidence has been staged or committed.

## Remaining application and document QA

The bounded F2 audit is saved in `F2_PORT_AUDIT.md`. For the realized
B0(1/100,5) network, port 0 has the existing sharp threshold
(857-125 sqrt(13))/1296 and a buffering safety consequence. The other three
ports have exact necessary upper bounds, not safe-load certificates. No
permutation or transpose symmetry transfers the port-0 proof. Three new
contact-envelope analyses would be required for sharp all-species indices;
they remain open and are not presented as solved in the paper.

The final PDF has 11 pages. It was compiled twice from the same open source
with the installed MiKTeX `pdflatex`, and every page was rendered with Poppler
and visually inspected. All equations, the figure, tables and bibliography
are legible; there are no overfull boxes or unresolved references. One harmless
underfull paragraph warning remains. The built-in compiler was also called
as requested, but failed before reading the source with `Unable to find
standard directories for platform`. The editor was kept open. The exported
PDF itself compiled successfully and is verified separately from that preview
initialization failure.

PDF SHA-256:
`cf939d5998d574865131a5d8cfcf2144e165515eb628131d092cc49dfe38b030`.

The completion criterion used here is the actual central theorem and its
end-to-end formal dependencies, not a count of certificates. Additional
application and extension formalizations are explicitly outside that closed
critical path. The full disposition of the reviewer's proposals is retained
in `PUBLICATION_FOLLOWUP_AUDIT.md` rather than adding discovery history to
the publication.
