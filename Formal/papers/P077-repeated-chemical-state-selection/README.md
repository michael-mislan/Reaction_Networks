# Repeated selection of inherited chemical states: finite-population guarantees and a logarithmic horizon law

[Read the paper](../../../Theory/Evolution/P077-repeated-chemical-state-selection.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A specified compartment model supports a prescribed finite sequence of transfers with joint gain and minority-representation guarantees; sufficient and necessary bounds give a logarithmic horizon law for that operating event.

**Reproduction:** Build from `manuscript/` using pdflatex main.tex, bibtex main and two further pdflatex passes, with the included figures. check_paper.py uses exact fractions alongside explicitly labelled mpmath/numerical diagnostics; make_figures.py requires Matplotlib and mpmath. Both resolve outputs relative to their files. The archived build.ps1 also reruns the computations and assumes the old environment; direct LaTeX commands avoid that dependency. The complete selected Lean import closure and saved receipts are preserved without replay.

**Formalization:** The current 26-page manuscript distinguishes the compiled baseline from its conventional refinement. Source-matched strict receipts cover the publication root, the earlier aggregate containing normalization bounds, and the displayed scalar minority-growth barrier. They support the original history/all-prefix mission, logarithmic sufficient horizon, compiled ten-cycle instance and terminal interpretation, transfer loss and inventory/target algebra. Ten declarations have saved elaborated standard-axiom interfaces. The lifting of the minority scalar barrier to a batch population theorem, weighted-sampling Chernoff refinement, exact finite-population variance result, improved mission and smaller-population witness, and corresponding refined horizon statements are conventional. The 4-billion-population refined witness is not the 10-trillion compiled witness. Diagnostics are not proofs. Finite-horizon selection and coexistence do not establish indefinite coexistence, innovation or open-ended adaptation.

[Historical verification review](../../papers/P077-repeated-chemical-state-selection/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 210 selected modules, including shared dependencies. 41 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [PublicationResolution.lean](../../proofs/SerialTransferSelection/PublicationResolution.lean)
- [SourceHorizonDesign.lean](../../proofs/SerialTransferSelection/SourceHorizonDesign.lean)
- [HorizonScaling.lean](../../proofs/SerialTransferSelection/HorizonScaling.lean)
- [StrongShareInstance.lean](../../proofs/SerialTransferSelection/StrongShareInstance.lean)
- [EnrichmentDesign.lean](../../proofs/SerialTransferSelection/EnrichmentDesign.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
