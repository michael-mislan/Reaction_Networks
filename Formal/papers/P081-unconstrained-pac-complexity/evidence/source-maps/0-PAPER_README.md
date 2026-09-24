# Final critical-path paper

The current publication-style paper is `paper.tex`. Its eight-page PDF is
saved at the project subfolder root as `../unconstrained_pac_paper.pdf`.
`unconstrained_pac_report.pdf` and `manuscript.tex` remain the earlier,
broader research report and are not the current focused paper.

The paper contains only the main classification and its necessary proof:
literal definitions; square witnesses; NP certificates; weighted linkage
with the universal partial-support converse; the explicit SAT switch and
global wiring argument; total binary FP execution; and formal reproducibility.
Discovery history, the optional balanced example, strengthening bounds,
future adapters, and AGC workflow are excluded from the paper.

Build from the repository root:

```powershell
& 'problem_workspaces/RAF_unconstrained_PAC_detection_complexity/publication/build_paper.ps1'
```

The script uses installed MiKTeX with automatic installation disabled, runs
two passes, and copies the final PDF to the project root. Bibliography is
embedded in `paper.tex`, with matching editable entries in `paper.bib`.
Authorship and affiliations have not been invented. Nothing was submitted.

Verification for this revision was a successful strict-receipt and current
source/artifact hash audit (`audit_evidence.py`, `evidence_audit.json`), not
a new clean Lean build. All 777 checks passed, including 638 in the root
receipt's source closure. The root and all mathematical source files were
unchanged. The original successful strict compilation and authenticated
root/FP/equivalence/NP interfaces remain in the campaign receipt.

All eight final pages were rendered at 100 dpi and visually inspected;
see `qa_paper/INSPECTION.md`. The final log has no overfull boxes or
undefined-reference warnings. The MiKTeX update advisory was not addressed
by changing the frozen environment.

The 18 September continuation brief's required proof gate, balanced example,
and one bounded useful strengthening were completed in the earlier handoff.
The user clarified that there is no additional attachment requiring work.
Guide score remains 43/43 PASS. General conservation-preserving hardness
and elementary-chemistry extensions remain unclaimed optional research.

AGC was run at entry and handoff. It remains useful for freshness and for
distinguishing formal proof evidence from administrative publication state.
Registration of the prepared root route in the protected legacy authority
graph is still the canonical authority integrator's responsibility; this
revision does not claim that administrative action was performed.
