# Reliable autocatalytic operation with a finite fuel–waste bath: joint mission guarantees, reservoir sizing and a sharpened certificate

[Read the paper](../../../Theory/Production/P076-finite-fuel-waste-bath.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

An explicit finite reactor-and-bath count process supports repeated recovery and collection under history-dependent interventions, with joint mission guarantees, inventory accounts and sufficient reservoir sizing.

**Reproduction:** Build from `manuscript/` with pdflatex main.tex, bibtex main and two further pdflatex passes. The included diagnostic_table.tex and three vector figures are required build inputs. check_paper.py uses exact standard-library arithmetic; make_figures.py requires NumPy/SciPy/Matplotlib. Paths in these scripts are local. The archival build.ps1 assumes the old interpreter and scratch layout and reruns computations; direct LaTeX commands build from saved inputs. All eight packaged refinement receipts are preserved alongside the two original root receipts, without rerunning Lean or numerical producers.

**Formalization:** The current 25-page publication extends the 19-page workspace draft with both refinements propagated through the mission and sizing theorems. The formal chain includes the literal finite-bath source, nonexplosion and chronological-law identification, joint cycle and returned-history bounds, directed inventory and prefix tolerance, net synthesis, neighbouring-state detailed balance, and refined general/pure-bath mission and inverse-design results. Saved strict receipts bind the selected source closures under the frozen environment; four original-root declaration interfaces have saved standard-axiom probes, while the newer receipts certify compilation without saved elaborated interface probes. All theorem hypotheses and the specified externally clocked interventions remain in the source statements. Endpoint free-energy simplifications, force-budget inversion, the metered-food common-randomness coupling, tilt optimality and unit conversions are conventional. ODE plots are diagnostics, not count-process evidence. The theorem certifies finite missions with established catalyst, not positive net fuel consumption or the whole operating apparatus.

[Historical verification review](../../papers/P076-finite-fuel-waste-bath/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 351 selected modules, including shared dependencies. 97 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [SharpService.lean](../../proofs/FiniteReservoir/SharpService.lean)
- [SharpCycle.lean](../../proofs/FiniteReservoir/SharpCycle.lean)
- [SharpPhase.lean](../../proofs/FiniteReservoir/SharpPhase.lean)
- [SharpPhaseCycle.lean](../../proofs/FiniteReservoir/SharpPhaseCycle.lean)
- [SharpEnvelope.lean](../../proofs/FiniteReservoir/SharpEnvelope.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
