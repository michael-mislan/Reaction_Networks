# Publication follow-up handoff

## Delivered result and scope

The final paper is **inherited_family_decisions.pdf** at this workspace root;
editable source is **paper/main.tex**. It gives the literal model, actual-law
probability bridge, source-specific decision reversal, decision-preservation
criterion, selected decision consequences, strongest proved scalar feedback
floor, and two separate continuation refinements. Its appendix explains the
exact numerical enclosure and conventional/exact/kernel evidence boundary.

Baseline guide: **60/60 preserved**. Postproof brief: **32/32 selected task
items discharged**, including the explicitly permitted, advance scope decision
to defer optional unfolding (tasks7.1–7.2). This does not mean that the deferred
theorem has been proved. The task register and final daily entry are the
authoritative record of completion times and evidence. No canonical AGC
authority status was changed to obtain these counts.

The latest user requested only the final critical path. Accordingly the paper
omits the rare-mutation expansion and finite-amplitude response derivations,
which are valid retained baseline work but are not required for its certified
decision or selected follow-up claims. It also omits diagnostic pilot tables,
the failed coarse-remainder route, the superseded weaker barrier and the optional
local unfolding theorem. These remain in the research record, not the paper.

## Exact new conclusions

1. **Continuum reversal (R1, C/E).** With all other baseline quantities fixed,
   complementary inheritance prefers BA and independent-marginal inheritance
   prefers AB throughout **0.120545 <= c_B <= 0.120561**. The certificate is an
   inner interval, not a maximal region. The central one-founder margins exceed
   1.6e-6; the full-interval margins are smaller. Four extra enclosed flows plus
   the analytic curvature bound |G_D''|<=6912 prove decreasing signed gaps and
   the required endpoint signs. Floating roots are not certified brackets.
2. **Decision cost and founder scaling (R2, C/E/K).** A rule with only the
   common mean information has two-world minimax extinction regret
   ab/(a+b), enclosed in (8.67636512e-7,8.67636514e-7). The rule selects an
   entire deterministic course, independently of population outcomes. Both
   identical-AA-founder advantages have a unique integer maximum at n=32,
   established from exact signs of consecutive increments, not rounded logs.
   Values at32 are about2.0895095323e-5 (J) and2.1774502812e-5 (I).
3. **Improved universal floor (R3, C/E/K).** For fixed division b=.1,
   d_i<=.421, acquisition probability mu_i>=.01 and the declared post-course
   endpoint, the scalar envelope gives a20 in
   (.002472578295567906,.002472578295567911). Every admitted predictable
   feedback course from n molecular and m mutant founders has eventual survival
   >=1-(1-a20)^n(.2)^m. No founder independence under feedback is assumed.
   This is about5.2 times the old simple floor, still far below the exhibited
   one-founder risk about.03041843. No near-optimality is proved.
4. **Continuation sensitivity (R4, C/E).** Residual acquisition mu=eta*kappa
   after the course has one-sided errors at most eta*U_s, with U_AB<.050002
   and U_BA<.053172. Thus eta<=1e-5 preserves both central decisions. This
   does not make the original terminal vector exact under residual mutation.
   Separately, mutation-free clearing for H162, then a source satisfying the
   stated coupling assumptions, gives total two-order error<1.343e-6 and
   preserves both central preferences. Its added erasure exposure46.98 is
   substantial. Neither simultaneous perturbations nor optimal H is claimed.

## Tests, evidence, and what was learned

| Test or argument | Result | Evidence |
|---|---|---|
| Pinned Python runtime and numerical smoke | PASS | Session entry checks; prior baseline runtime retained |
| Exact source and preserved central enclosures | PASS | results/postproof/publication_audit.json; campaign/postproof/baseline_inputs.json |
| Small variational boundary diagnostic | Slopes near-.149, separated approximate ties; N only | results/postproof/boundary_diagnostic.json |
| Four additional exact endpoint flows | PASS; approximately14s first run | results/postproof/boundary_certificate.json |
| Regret and founder exact arithmetic | PASS; no new original flows needed | results/postproof/decision.json |
| Scalar exact enclosure and independent closed-form diagnostic | PASS; agree at floating precision | results/postproof/scalar_floor.json |
| Exact resolvent identity and enclosed linear rewards | PASS; correct backward-column/forward-row orientation | results/postproof/continuation.json |
| New scalar algebra | Strict Lean PASS | verification/scalar_barrier.json |
| New regret inequalities | Strict Lean PASS after syntax-only linter repair | verification/regret.json |
| Expanded thin root | Strict Lean PASS, warnings treated as errors | verification/postproof_main.json |
| Bounded full selected reproduction | PASS in45.50s, one native numerical thread | results/postproof/reproduction.json and its command logs |
| Final editorial build and all11 rendered pages | PASS; no clipping, overlaps, missing references or LaTeX warnings | results/postproof/paper_build.json; paper/qa_postproof/; final daily entry |

The productive structural step was to turn a diagnostic slope into an analytic
curvature bound, then combine exact secants with four small endpoint solves.
This closed a whole interval without a larger validated sensitivity system.
The regret and founder conclusions used the existing central certificate;
rerunning the baseline would not add mathematical information. A scalar
Riccati supersolution tightened the feasibility obstruction cheaply. The
continuation calculations exposed the actual limitation: small certified
residual acquisition and expensive finite clearing, rather than broad biological
robustness. There was no need to launch a large search.

Two compiler attempts failed on an unnecessary tactic-sequencing linter, not
an unproved mathematical step. Explicit goal branches resolved this, with no
statement changes or disabled linter. The PDF viewer briefly held the old root
PDF mapped; atomic replacement succeeded and is now used by the build. No
environment or dependency repair was needed.

One final TeX subprocess transiently returned nonzero despite reporting a
complete PDF and no TeX error. A diagnostic rerun returned zero, followed by
a clean two-pass editorial build with both exit codes zero. The MiKTeX update
reminder was not treated as a reason to update dependencies. Final acceptance
uses the clean build, not the earlier nonzero invocation.

## Reproduction and preservation

Follow **REPRODUCE.md**. The single bounded driver rebuilds only selected
publication outputs. Default operation preserves the original four-flow
certificate and checks it before deriving consequences. The optional
--replay-baseline argument recomputes all original intervals and compares them
without replacing that certificate. It was not needed for this follow-up,
since the baseline had already passed its own full reproduction.

After the successful scientific reproduction, editorial changes removed
noncritical material, added the state/evidence tables, and eliminated a TeX
fraction-style warning. **paper/build.py** rebuilds that final manuscript and
first verifies that every recorded mathematical input and proof file is
unchanged. Its paper_build.json supersedes only the manuscript/PDF hashes in
the scientific reproduction record. Numerical or Lean work is not silently
rerun or relabelled after those editorial changes. All final pages were rendered
with Poppler and visually inspected. Baseline HANDOFF.md, original task register,
central certificate and original main verification receipt remain available.

## Formalization, AGC, and remaining limits

The probability bridge, curvature analysis, feedback supermartingale argument,
and continuation coupling/occupation proofs are conventional. Exact interval
arithmetic certifies numerical inequalities under the documented enclosure
proof. The integrator and stochastic process are not formally verified in Lean.
The root imports the selected new algebra modules in the frozen mathlib
environment. This is **not an end-to-end Lean proof of the probability theorem**.

AGC checkpoints at entry, structure, compiler failure, results and handoff are
saved under verification/agc_postproof_*.json. They report current diagnostic
content with an unbound authored route; proof-admissibility limitations are
authority/integration limitations, not mathematical refutations. AGC was helpful
for freshness and scope discipline, but did not provide the key estimates or
certify these conventional/exact results. No protected authority was edited.

Optional unfolding remains deferred. To instantiate it one would need a simple
baseline tie, a nonzero schedule derivative, a nonzero difference of transported
covariance corrections, and controlled mixed derivatives/remainders. Global
schedule optimization, a maximal reversal region, combined endpoint perturbations,
empirical calibration and full stochastic Lean formalization are outside the
delivered scope. The acquisition probabilities are coarse-grained synthetic
assumptions, not per-base mutation rates; no clinical recommendation follows.

Primary-literature claims remain restricted to the accessible Gunnarsson
sources cited in the paper. The earlier source inventory records version/page
differences and inaccessible material; no unseen full text or exhaustive
historical-priority review is newly claimed.
