# Formal supplement and reproducibility record

This supplements the main paper, *Certifying complete families of irreducible
autocatalytic sets is co-W[P]-complete*, dated 7 September 2026. The main paper
contains the complete mathematical critical path. This record supplies the
local reproduction interface, not additional assumptions or optional lemmas.

## Terminal certificate

- Lean: `leanprover/lean4:v4.30.0`.
- Frozen lake-manifest SHA-256:
  `a8df0b606ec258561c226df89856884be433c19b49fb0a27335d69bb2b6e9fac`.
- Final `Publication.lean` SHA-256:
  `15fb4b803e47f11378625ff94031395e18e221c46916f531f506a0403ff3bcdf`.
- Updated `Main.lean` SHA-256:
  `839834fe70898599e7acf4df55eb7f5951400c89f9a82260fde83beac35b134e`.
- Four-declaration interface hash:
  `sha256:ce140931191300fd967f1674205ce2d153e69b63b051f5c548c2a915ed6e02cc`.
- Receipt: `../results/postproof_terminal_verification.json`.
- Strict final compile: exit zero; empty compiler stdout and stderr; warnings
  treated as errors. Final successful run: 70.141 seconds, 36 dependencies.
- Audited declarations: `AllIrrRAFCert.axiom_iff_not_exactCertification`,
  `AllIrrRAFCert.axiom_reduction`,
  `AllIrrRAFCert.extra_iff_preservingTransversal`, and
  `AllIrrRAFCert.clique_iff_not_exactCertification`.
- Every audited declaration reports only `Classical.choice`, `Quot.sound`,
  and `propext`. No `sorryAx` or custom axioms.

The old `results/terminal_verification.json` authenticates the pre-strengthening
Main source, not its current hash. It is a historical receipt. The current
post-proof receipt authenticates the updated Main as an imported dependency
and explicitly probes `axiom_reduction`.

## Owned proof-module inventory

All paths below are relative to `proofs/AllIrrRAFCert/` in the repository.

| Module | Role in the final proof |
|---|---|
| WPHardness/Source.lean | Finite implication system; inductive derivability; literal molecules, reactions, food, and catalysts; unique production provenance |
| WPHardness/GuardPromise.lean | Each guard is an irrRAF; guards are distinct; a no-close irrRAF is a listed guard |
| WPHardness/Omissions.lean | Extra irrRAFs contain close and omit exactly one selector per slot |
| WPHardness/NoSpurious.lean | Selected decoder identity; induction on staged closure; extracted axioms generate all statements |
| WPHardness/Forward.lean | Finite derivations give closure reachability; a common stage for finite inputs; the witness is a RAF; minimal extraction gives an extra irrRAF |
| WPHardness/Reduction.lean | Ordinary at-most-k set semantics, repeated slots, final equivalence, list parameter, molecule/reaction counts |
| WPHardness/Encoding.lean | Computable dense Boolean representation and correctness of each row kind |
| Main.lean | Existing Clique package plus the strengthened `axiom_reduction` package |
| Publication.lean | Exact total predicate, generic transversal/one-deletion results, public axiom and Clique exact-certification equivalences |

The existing `Hardness/` modules implement the separate ordinary Clique
reduction retained for the ETH follow-up. They are not a second proof route
recounted in the main paper. Imported RAF core files provide staged closure
and the RAF predicate; existing enumeration files provide finite cyclic
successor and minimal-subset extraction. Transitive imports are fully listed
and hashed in the strict receipt. A transitive import does not make its every
theorem part of the manuscript's critical path.

## Scope of the checked statements

The source universe has size `n+2`, the slot type is `Fin k`, and rules are
indexed by `Fin q`. `SmallGenerating A k` quantifies over finite sets B with
`B.card ≤ k` and derivability of every statement. No source-instance truth
predicate is taken as an axiom. The generic preserving-transversal result
requires valid listed sets, while `ExactIrrRAFCertification` explicitly
conjoins validity with completeness on all finite inputs.

The conventional parts are: the cited external completeness of Minimum Axiom
Set; finite-derivation/staged-closure equivalence for its standard source
definition; harmless tiny-universe preprocessing; polynomial implementation of
the maxRAF oracle; construction-time analysis; and complexity-class transfers.
These are proved or specified in the paper and are not claimed to be formal
Turing-machine complexity results in Lean.

## Reproduction commands

Run the following in PowerShell from `E:/Erdos Problems`. No dependency update
is needed or permitted for routine verification. The bridge automatically
enforces `mathlib4_project/` as Lean's working directory.

```powershell
$rafPython = 'C:/Users/researcher/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
& $rafPython scripts/agc.py checkpoint problem_workspaces/RAF_fixed_param_tractability_irrRAFs
& $rafPython scripts/verify_proof.py proofs/AllIrrRAFCert/Publication.lean --timeout 600 --output problem_workspaces/RAF_fixed_param_tractability_irrRAFs/results/postproof_terminal_verification.json --declaration AllIrrRAFCert.axiom_iff_not_exactCertification --declaration AllIrrRAFCert.axiom_reduction --declaration AllIrrRAFCert.extra_iff_preservingTransversal --declaration AllIrrRAFCert.clique_iff_not_exactCertification
& $rafPython scripts/process_guard.py run --timeout 60 --owner-label RAF-AXIOMS -- $rafPython problem_workspaces/RAF_fixed_param_tractability_irrRAFs/experiments/axiom_preflight.py
& $rafPython problem_workspaces/RAF_fixed_param_tractability_irrRAFs/publication/build_paper.py
```

The axiom preflight covers 768 cases and 624 positives. The independent
historical graph diagnostics can be reproduced with `guard_preflight.py`
(120-second lease, 4,176 graphs) and `dense_preflight.py` (60-second lease,
56 cases), using the same guarded command pattern. These experiments do not
substitute for the universal Lean proof.

## PDF and LaTeX reproduction

`build_paper.py` is a single manuscript source exporting `manuscript.tex` and
the workspace-root PDF. It uses embedded Times New Roman text and Segoe UI
Symbol for missing mathematical glyphs, with no raster equations or images.
`BUILD_REPORT.json` records structural checks and metadata. The final visual
QA record is `VISUAL_QA.json`. `SHA256SUMS.json` binds the sources and artifacts.

No TeX engine was found on this workstation, and the attempted official
Tectonic download was denied by socket permissions. Therefore the delivered
PDF is ReportLab-rendered, **not LaTeX-compiled**. The exact two-pass TeX build
from the review remains blocked. On a machine with XeLaTeX and the named
fonts, the exported source can be tested with two `xelatex manuscript.tex`
passes; those passes have not been executed here and are not certified.

The PDF was built, rendered at 200 dpi, visually inspected page by page,
corrected for subscript placement and the semantic-convention box, rebuilt,
and rendered again. The final PDF is in the requested project subfolder root;
render intermediates are under `publication/`, not mixed with final outputs.
