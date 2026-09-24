# Exact common-activity compatibility of autocatalytic cores: finite cycle acceleration, monotone elimination, and fixed-parameter tractability in the longest path

[Read the paper](../../../Theory/Algorithms/P073-common-activity-algorithms.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

For weighted two-reaction cores on arbitrary finite graphs, exact cycle acceleration and monotone elimination decide static shared-activity compatibility under a fixed kinetic model, with structural complexity bounds and rational witnesses.

**Reproduction:** Build from `manuscript/` with pdflatex main.tex, bibtex main and two further pdflatex passes. check_paper.py uses SymPy; make_figures.py uses NumPy/Matplotlib; sanity_elimination.py is a NumPy floating-point prototype, not a certificate. Paths are local. lean_sources.zip is preserved byte-for-byte: all 77 archived sources, 15 receipts and both environment pins were compared with the selected source snapshot. Use this repository's pinned shared build environment for Lean, rather than the untested standalone scaffold in the archived lean_README.md.The supplied computational examples do not constitute complete implementations of both algorithms.

**Formalization:** The current 28-page manuscript includes the later FPT result; the earlier workspace handoff and the opening of its claim map predate that extension. Fifteen archived strict receipts match the source files and pinned environment. Formal components include least-state existence, support and cycle-root lemmas, finite progress under finite token data, source implications, candidate transport, threshold bridges, next-map elimination, inventory and quantitative/example algebra. The two root declarations explicitly assume stability of weak feasibility across a positive margin interval; the real-algebraic argument establishing that stability is conventional. Graph traversal, analyticity of composed maps, quantifier elimination/CAD, branch stability, envelope bounds and both complexity theorems are conventional. There is no end-to-end verified solver or full algorithm benchmark, and static productive compatibility does not establish long-time persistence. The original archive contains 77 modules including companion developments; the production inventory records the exact selected receipt closure.

[Historical verification review](../../papers/P073-common-activity-algorithms/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 27 selected modules, including shared dependencies. 52 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [ActiveSupport.lean](../../proofs/ThermoCoreCompatibility/GeneralCompatibility/ActiveSupport.lean)
- [CandidateTransport.lean](../../proofs/ThermoCoreCompatibility/GeneralCompatibility/CandidateTransport.lean)
- [ClosedMargin.lean](../../proofs/ThermoCoreCompatibility/GeneralCompatibility/ClosedMargin.lean)
- [Consequences.lean](../../proofs/ThermoCoreCompatibility/GeneralCompatibility/Consequences.lean)
- [CycleBranches.lean](../../proofs/ThermoCoreCompatibility/GeneralCompatibility/CycleBranches.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
