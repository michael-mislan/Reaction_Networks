# C4 publication package

## Result

Final register: C4-PUB **24/24 PASS**; inherited baseline **49/49 PASS**.
The 14-page PDF was rendered and every page inspected. All required postproof
items are complete; no optional extension has been activated.

The defined-family C4 theorem is preserved and strengthened. Strict Lean
verification proves free-X concentration and collection at least **1/209 per
node per routine cycle**, compared with the baseline 1/540. Template output
remains 1/28. Conditioning, routine timing, parameter boxes and food/service
allowances are unchanged. The strengthened actual-history root and closed
nonzero path and ring applications compile. Ready-start net synthesis is now
packaged, with positivity from cycle 28; the existing conditioned result gives
positivity from cycle 30.

The paper is `C4_Conservative_Exchange_Paper.pdf` in this workspace root;
editable source is `C4_Conservative_Exchange_Paper.tex`, with `references.bib`
and three vector figures in `figures/`. It contains the final conventional
proof and direct operational consequences, not the discovery ledger or failed
tactics. No optional matrix optimization, unequal-volume, stochastic,
switching, or autonomous-bath branch was activated.

## Evidence and reconciliation

`audit_completion.py` passed for the baseline `Examples.verify.json`. Its
successful current proof hash differs from the older failed hash
`050259c82226f5073180612a60935dfaad2cb7c1dbbaffe75178dc59296320dc`
identified in the supplied review. Local status prose already reflected the
successful baseline. This package contains the current successful files;
no claim is made that a remote GitHub branch was updated or a paper submitted.

`Publication.verify.json` is the new strict receipt. It has verified=true,
exit_code=0, empty compiler diagnostic streams, five authenticated exported
interfaces and only propext, Classical.choice and Quot.sound.
`publication_audit.json` checks all 66 dependency source/artifact pairs, the
root hash and frozen manifest. The root SHA-256 is
`b53986f749f96c4e33ad38132e9d29d47bd8030ebb164755fd63787a6480d014`.
The toolchain is Lean 4.30.0. Baseline proof files and dependencies were not
modified; the improvement is in small additional modules.

The core mathematical change is the correlated bound u+x<=11/10, yielding
common phase loss 48. The existing polynomial adjoint, evaluated at 1/24,
has minimum Y-coefficient ratio 725/1008. An exponential upper bound gives
1/209. `sharp_preflight.json` records exact rational checks; the Lean theorem
is the decisive universal evidence. The full root adapter reuses the same
actual trajectories and resources rather than constructing an unrelated
successful history. Ready-start synthesis reuses the actual inventory telescope.

AGC is used as a freshness/scope gate, separately from Lean proof evidence.
The new strict receipt requires its prescribed proof-neutral same-cut
reconciliation. This workspace still has no synchronizable formal frontier;
the previously failing post-proof-publish command was not repeated. The final
checkpoint result is saved in `current_checkpoint.json`.

## Formal boundary

Compiled: local rate-48 comparison; backward phase propagation; actual-source
collection; arbitrary history-dependent repeated operation with common
accounts; closed path/ring instances; ready-start synthesis.

Conventional proofs in the paper: mission ceiling/floor inversion, endpoint
liminf/limsup rates, undirected-edge/dense/bounded-degree cost deductions,
dimensional conversions and multi-pulse material ceiling. These are direct
consequences, not separately exported Lean claims. The four distinct phase
losses are derived in the text; the formal phase theorem states the sufficient
common-48 weakening. Selective-X failure is exact rational source substitution,
with only the limited minimum-drift conclusion.

Numerical illustrations: the existing four-run pilot (uncoupled, path, ring,
star), Radau rtol=1e-9, atol=1e-12, integral states and no clipping. Rerunning
was necessary only to retain missing time traces for figures. Saved scalar
metrics reproduced within 1e-10. All data and the source hash are in
`figures/figure_data.json` and `figures/trajectory_data.npz`. Figure 3 and
the comparison table separate simulated outputs from analytic allowances.

Physical limits remain explicit: equal volumes, common species-independent
exchange, fixed kinetics, synchronous instantaneous pulses, maintained F/P
activities and a schematic effective source. Gross service and handling are
not total energy. The work identifies no molecule or experimentally calibrated
reactor and does not resolve an unrestricted literature conjecture.

## Reproduction

From `E:/Erdos Problems`:

```powershell
.venv/Scripts/python.exe scripts/check_python.py --quiet
.venv/Scripts/python.exe problem_workspaces/RAF_C4_composition_on_defined_assemblies/audit_completion.py
.venv/Scripts/python.exe problem_workspaces/RAF_C4_composition_on_defined_assemblies/audit_publication.py
.venv/Scripts/python.exe scripts/verify_proof.py proofs/C4Assemblies/Publication.lean --declaration C4Assemblies.sharp_conservative_assembly_operation --declaration C4Assemblies.sharp_path_operation --declaration C4Assemblies.sharp_ring_operation --declaration C4Assemblies.ready_mission_synthesis --declaration C4Assemblies.sharp_assembly_routine_free_export --output problem_workspaces/RAF_C4_composition_on_defined_assemblies/Publication.verify.json
.venv/Scripts/python.exe scripts/process_guard.py run --timeout 120 --owner-label C4-paper-figures -- .venv/Scripts/python.exe problem_workspaces/RAF_C4_composition_on_defined_assemblies/publication_figures.py
```

From this workspace directory:

```powershell
powershell -NoProfile -File build_paper.ps1
```

This runs the existing MiKTeX pdflatex/bibtex workflow in `tmp/pdfs`, copies
the final PDF to the workspace root and renders every page with Poppler.
The intermediate output directory avoids an observed root-log sharing lock.
The build log is retained as `PDF_BUILD.log`; it has no overfull boxes or
undefined references. MiKTeX's generic update reminder did not affect the
successful build and no package/toolchain updates were performed.

`PUBLICATION_MANIFEST.json` and `C4_Publication_Snapshot.zip` bind the PDF,
editable sources, figure data, local proof-source closure and successful
receipts. This is a publication-source snapshot for use with the existing
frozen repository environment, not a standalone vendored mathlib installation.
No dependency updates, staging, commits, external posting or submission were
performed. `PDF_QA.json` records the final page-level visual review and checks.

Literature inspection used primary arXiv records for Baez--Pollard and
Rao--Esposito and the publisher's first-page PDF for Chueh--Conley--Smoller.
The complete classical invariant-region article was not accessible; the paper
therefore makes only a broad foundational attribution and no theorem-containment
claim. C0/C1 citations are to the actual local manuscript sources, not invented
external publications. C2 is not needed on this deterministic proof path.
