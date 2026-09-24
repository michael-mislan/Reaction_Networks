# Rest–rhythm bistability and single-rate switching in the sequential distributive three-site phosphorylation cycle

[Read the paper](../../../Applications/Phosphorylation/P078-rest-rhythm-phosphorylation.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

The three-site phosphorylation mechanism supports certified coexistence of rest and rhythm, with a local single-rate switching theorem near a generalized Hopf point and separately validated finite-amplitude witnesses.

**Reproduction:** Build from `manuscript/` with pdflatex main.tex, bibtex main and two further pdflatex passes; included tables/*.tex and figures/*.pdf permit building without Python. All supplied .npz seeds/data are included. Optional computational replay requires NumPy, SciPy, mpmath, SymPy and Matplotlib. Use `python reproduction/replay.py` from the dossier for the earlier certificate chain: its only change is resolving the public checkout and copied workspace paths. It retains bounded 240-second child stages; wrap longer work in an explicit overall resource limit. The 190 MB generated finite_fourier_inverse.npz is intentionally not bundled, matching the source release: sparse_fourier_pilot.py --certify regenerates it before geometry/attraction checks. The external preparation_pilot.py dependency, finite-path seed and source-control receipt omitted from the original publication bundle have been copied into the expected local locations.

**Formalization:** The current manuscript proves its bifurcation, periodic-orbit and control results conventionally with interval/error-bounded certificates. Three Mathlib-only Lean modules provide thirteen elementary source/control/Lyapunov algebra statements; their strict source- and environment-matched receipts have no saved elaborated declaration probes. These algebra facts do not formalize the dynamical theorems. The switching theorem selects suitable baselines sufficiently near the Bautin point for each prescribed duration and positive modulation bound; the finite-witness switching demonstration is numerical. No finite-copy clock or loaded reusable processor is established. Exact source data, interval checkers, saved reports and numerical seeds are preserved with their separate roles.

[Historical verification review](../../papers/P078-rest-rhythm-phosphorylation/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 3 selected modules, including shared dependencies. 13 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [SourceControlAlgebra.lean](../../proofs/SwitchablePhosphorylation/SourceControlAlgebra.lean)
- [SingleInputColumn.lean](../../proofs/SwitchablePhosphorylation/SingleInputColumn.lean)
- [CaptureInequality.lean](../../proofs/SwitchablePhosphorylation/CaptureInequality.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
