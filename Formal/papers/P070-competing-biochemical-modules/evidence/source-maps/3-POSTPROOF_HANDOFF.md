# Final follow-up handoff: operational recovery and finite donor service

Date: 19 September 2026. The attached follow-up scope and the user-authorized
finite donor extension are complete. Score: **24/24 guide items plus 4/4 finite
extension items PASS**, with no FAIL or BLOCKED item. The original guide remains
36/36 PASS. These counts measure the contracted deliverables, not the number of
open conjectures solved. No historical literature conjecture is identified as
solved by this declared-model result.

## Delivered paper

`dynamic_shared_resource.pdf` is the final 12-page research paper in this
workspace root, as requested. Its title is **Certified transient recovery and
finite donor operation in a shared-NADPH model**. It contains the final proof
path, explicit equations and units, a readable continuum barrier argument,
three reproducible figures, exact resource accounting, finite donor operation,
the repair-clock obstruction, a worked example, primary literature comparison,
and a claim-to-evidence appendix. Discovery detours are retained here and in
the ledger rather than inserted into the scientific argument.

Editable source: `publication/main.tex`. Figures and their numerical data:
`publication/figures/`. Builder: `publication/make_figures.py`. Exact rational
supplement: `certificates/modal_box.json`. The PDF SHA-256 is recorded in
`verification/POSTPROOF_AUDIT.json`; it is
`32ee7b2d2d8ed2f0baaeac1650d92422ba41903d546ea7f51c8da45c343c3258`.

All pages were rendered and inspected. The review corrected long-path overflow
and a clipped numerical Trx curve, then rechecked the changed pages. The final
LaTeX log has no overfull boxes, undefined references, or LaTeX warnings. A
MiKTeX update notification is unrelated to document correctness; dependencies
were not updated.

## Strongest compiled result

`DynamicSharedResource.Certificate.fast_joint_service` in
`proofs/DynamicSharedResource/OperationalMain.lean` has strict successful
verification, saved in `verification/OperationalMain.json`. The root and all
27 local dependencies match their authenticated source hashes (28/28 files).
The successful root compilation took 61.813 seconds with verified dependencies
reused. Its only reported axioms are Classical.choice, Quot.sound, and propext.
No warnings, `sorry`, nonzero exit, unchecked generator, or sampled trajectories
are accepted as proof.

The field and nominal parameters are unchanged from the original result:
eight states, source scale 3/25, repair scale 1. In the fixed modal coordinates,

    R = (.9,.834,.7,.7,.7,.7,.7,.7)
    S = (.9,.7,.7,.7,.7,.7,.7,.7).

For **every** initial state in the reconstruction of R, the theorem produces
an actual unique global forward solution of the literal field. It proves
physicality and continued membership in R, capture in S by 1/250 second, and
HG>=10.35 always, HT>=3.91 always, HT>=4.01 after 4 ms. It also proves, on the
same continued solution, zero GPx quota shortfall, Trx quota shortfall at most
9/25000 on every prefix, both service integrals on every later window, and
regeneration expenditure at least14.36 T-.1 on each window of length T.

The independent concentration box centered at p=c+(5/6)M[:,1], halfwidth
1/2000000 micromolar, lies inside R. Every point is physical and HT-deficient.
The tolerance is0.5 pM per independent coordinate. Its full dimensionality is
not represented as broad practical preparation tolerance. The new terminal
rectangle is not the old halfcube; its output and storage bounds were checked
directly. Main.lean and the old20-source root receipt were preserved and
re-audited successfully.

## What was tested and what we learned

1. **Baseline integrity and scope.** All20 original source hashes matched the
   original receipt. The old theorem already supplied actual evolution,
   uniqueness, and same-trajectory service. No reopening of its completed
   mathematics was necessary. The old2,000-second deadline was conservative
   because it shrank every modal coordinate at a slow common rate.
2. **Frozen rectangular hypothesis.** The supplied exact refinement checker
   was run against the local certificate before Lean work. Both endpoint face
   budgets, preparation inclusion, direct service bounds, and storage range
   passed. The local certificate hash differs from the attachment's historical
   hash; all asserted rational calculations and reported values matched. We
   did not regenerate the certificate or pretend the files were byte-identical.
3. **Service recovery versus full relaxation.** Shrinking only modal coordinate1
   from.834 to.7 while retaining the other radii removes the slow-repair
   bottleneck from this preparation. Its moving speed is-33.5; the tighter
   endpoint face budget is approximately-34.34346. The affine dependence of
   every signed face budget on the radius supplies the entire continuum of
   intermediate rectangles, not just two sampled states. This is the decisive
   improvement from2,000 seconds to4 ms.
4. **Costs on the actual terminal region.** Direct coordinate enclosures give
   service floors exceeding10.35 and4.01. The exact terminal storage range is
   2430664273305669/25000000000000000<.1. Combining that range with W'=R-HG-HT
   gives expenditure. The shortfall bound is simply.09 times.004. No trajectory
   quadrature is trusted for these all-time integral results.
5. **Source uncertainty.** The changed field differs only in its x component.
   R1<=130 and the inverse-matrix first column bound the modal perturbation.
   Both robust face checks pass for |s-.12|<=1e-6, even with this coarser source
   bound. This is an exact sufficient uncertainty band, not an empirical noise
   model or necessary threshold. `SourcePerturbation.lean` compiled strictly
   in37.875 seconds; its17 source files match the receipt.
6. **Actual finite donor coupling.** We tested the explicit extension
   u'=F_(Q/V,1)(u), Q'=-R_(Q/V)(x), Q0=.12V. For horizon H>=.004 and
   V>=16,000,000H, simultaneous modal and donor barriers prove that the source
   remains in the robust band, the donor stays positive, and the actual coupled
   solution provides service for the entire mission. This is a sufficient
   operation theorem, not a necessary budget bound applied to a nominal run.
7. **Small finite pilot.** A bounded Radau job for H=1.004 completed in about
   two seconds. With V=16,064,000 and Q0=1,927,680, the prepared-center pilot
   consumed14.9500106 micromolar over the whole mission and ended at source
   .11999906935. Its first Trx quota crossing was near1.67739918 ms. The script
   integrates spent donor to avoid cancellation against a huge initial stock.
   These values are numerical diagnostics, not uniform guarantees.
8. **Stock cost and impossibility.** The sufficient stock is enormous compared
   with consumption because of the narrow source band and the chosen Q/V law.
   It is not a proved necessary stock or an efficient physical design. The exact
   identity(Q+W)'=-HG-HT instead gives a genuine obstruction: finite nonnegative
   Q and physical W cannot support perpetual positive service without input.
9. **What stationary data discard.** Scaling the hyperoxidation and repair
   rates by the same positive sigma leaves all full stationary states unchanged.
   Yet w'>=-.003 sigma w implies a necessary quota-recovery delay proportional
   to1/sigma for a fixed sufficiently hyperoxidized preparation. The earlier
   numerical comparisons and the exact lower bound illustrate distinct
   information: the lower bound does not certify an upper deadline. This
   heavily damaged preparation is not inside the fast recovery certificate.
10. **Verification performance.** One local Lean job ran at a time. Most repairs
    were simplification/indexing/derivative conversions, not changes in the
    mathematics. A componentwise proof of stationary equivalence hit the kernel
    limit; a second expensive attempt was stopped after its exact process was
    identified. Replacing it by direct cancellation of the matched repair terms
    produced a strict pass in53.765 seconds. No unrelated process was stopped,
    no package environment changed, and no growing replay campaign was launched.

The original discovery tests are comprehensively recorded in
`HANDOFF_REPORT.md` and `journal/2026-09-19.md`. In particular, positive spectral
abscissae for absolute comparisons in physical/account coordinates were failed
sufficient estimates, not dynamical counterexamples. Transforming reaction
vectors before taking absolute values preserved the cancellations needed for
the successful modal certificate. That distinction remains important for any
later extension. The complete running deliverable ledger is
`POSTPROOF_SCORE.json`; the updated evidence graph is `POSTPROOF_GRAPH.md`.

## Evidence boundaries and remaining scope

The full nominal operational theorem is Lean verified. The exact source
perturbation identities and robust endpoint inequalities are also Lean
verified. `RepairObstruction.lean` verifies stationary equivalence, the repair
velocity lower bound, and the integrating-factor derivative inequality.

The full continuous-source global evolution theorem and the full nine-state
finite donor theorem are **complete conventional proofs using those checked
inequalities**, not fully formalized Lean evolution statements. Their proofs
are in `SOURCE_ROBUSTNESS_PROOF.md`, `FINITE_RESERVOIR_PROOF.md`, and the paper.
The logarithmic repair-clock consequence and the finite-fuel impossibility
argument are conventional proofs as well. These evidence levels satisfy the
follow-up scope and are exposed in the paper, not hidden behind a generic
"verified" label.

The donor extension makes regeneration fuel finite, while peroxide and the
phenomenological repair pathway remain maintained. It is not a thermodynamic
completion of all chemical inputs. V is a stock-to-source concentration scale,
not geometric volume. The numerical coefficients are those of the declared
reduced model; they are not individually attributed to the primary redox paper
or claimed as clinical calibration. We prove no global attraction, optimal
deadline, minimal donor stock, or success for the source-.1 equilibrium or
95%-hyperoxidized preparations.

No required positive mathematical red node remains. Potential future work
would be full Lean formalization of the changed-field extensions, broader
source certificates yielding useful stock sizes, or a calibrated model with
all energetic inputs accounted for. None is silently included in the completed
claim, and no additional bulk computation is authorized by this handoff.

## Reproduction and validation

Use the repository's canonical `.venv/Scripts/python.exe`. The runtime check
and numerical smoke suite passed at follow-up entry. Lean4.30.0 and Mathlib
revision c5ea00351c28e24afc9f0f84379aa41082b1188f remain frozen.
From the repository root:

```powershell
.\.venv\Scripts\python.exe scripts/verify_proof.py proofs/DynamicSharedResource/OperationalMain.lean --declaration DynamicSharedResource.Certificate.fast_joint_service --timeout 600 --output problem_workspaces/RAF_dynamic_compatibility_modules_sharing_resources/verification/OperationalMain.json
```

The bridge enforces the Mathlib working directory, strict warnings policy,
dependency source checks, and bounded process. For repair lemmas substitute
`RepairObstruction.lean` and omit the root declaration option. Figure generation
uses the bounded process guard around `publication/make_figures.py`; the finite
pilot is `experiments/finite_reservoir_pilot.py`. Solver tolerances and source
data remain in the saved scripts and JSON records.

From this workspace's `publication` directory, run the following twice:

```text
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex
```

Copy `build/main.pdf` to the workspace root as `dynamic_shared_resource.pdf`.
The final audit record checks source-receipt correspondence, key exact numbers,
layout warnings, evidence scope, and the PDF hash. Its source counts are
20/20 baseline,28/28 strengthened nominal,17/17 perturbation,2/2 repair.
No files or generated evidence were staged or committed by this agent.

## AGC assessment and final gate

The saved final checkpoint is `verification/POSTPROOF_FINAL_AGC.yaml`:
exit0, CURRENT, `current_with_authored_route_refinement`, with proof-admissible
false and no node-status effect. It still proposes original obligations and
an earlier authored refinement now completed. The template successor has no
bound live authority frontier; the prior publication attempt returned
NO_OPEN_FRONTIER. We did not invent a frontier, edit protected authority,
claim canonical docking, or reopen the proof to obtain a dashboard label.

AGC helped preserve the distinction between stationary and dynamical targets
and between exact arithmetic and actual flow. Its repeated late-stage guidance
was less useful than the current compiler receipts and explicit theorem
contracts. It did not discover the modal argument or prove a lemma. The saved
CURRENT status is a workflow diagnostic, not mathematical evidence. The
stopping criterion is completion of the attached scope and the requested paper,
with the nominal strengthened theorem strictly compiled and the finite donor
extension proved at its openly stated conventional level.
