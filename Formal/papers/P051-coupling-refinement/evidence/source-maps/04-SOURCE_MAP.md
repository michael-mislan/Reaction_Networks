# Literal source map

The authoritative requested statements are Sections 3–6 of SOURCE_GUIDE.md. The user additionally requires full Lean proofs, beyond the guide's conventional delivery criterion.

| Component | Existing source | Binding / limitation |
|---|---|---|
| Six-species exporter | proofs/ProductiveRecovery/Source.lean | Exact epsilon, eta, fluxes and field match. New Refinement/Source.lean imports it and proves free_field against it. |
| Thermochemical exporter | proofs/CommonPhysicalRealization/ExporterThermochemistry.lean | Transitive dependency of the existing exporter. No new claim of empirical calibration. |
| Resident reservoir polynomial | proofs/CoreCouplingCAC/Source.lean and Creation.lean | Rates 6,27,16,2,1/100000,1/10000 match guide. |
| Consumers and precursor reservoir | proofs/MultiConsumerPermanence/ReservoirRateLiteralSource.lean and ReservoirRateFlow.lean | Heterogeneous rho_i supports prescribed q_i; the equal-consumer ReservoirSource specialization alone does not. Reduced six-dimensional R19 certificate still needs formal docking and analytic existence/stability. |
| Network donor | proofs/RAF1314/StrictMargins.lean; problem_workspaces/Medical_Sept16Plan_13_14/THEOREM.md and FORMAL_BOUNDARY.md | Deterministic selected support exists. Donor martingale mission is NOT a fully formal Lean theorem. |
| New seven-species extension | proofs/RAF1519/Refinement/Source.lean | Reuses original five fluxes and replaces the driven pair with the two explicit intermediate pairs, including D washout. |
| Count correction | proofs/RAF1519/Refinement/CountSource.lean | Fourteen oriented chemical labels grouped as seven reversible pairs plus two feeds and seven washouts. Drift algebra is separate from existence of the random history law. |

No source mismatch was found in the six-species exporter. New analytic stochastic proof work cannot be discharged by importing the donor's finite arithmetic modules. The original reservoir source was located, but the complete R19 docking item remains open until the lift is formally connected.
