# Postproof research and publication handoff

Date: 20 September 2026, America/Whitehorse (UTC-07:00).
The earlier FINAL_HANDOFF.md is the historical 80/80 baseline. This report
describes the new 40-task continuation and the revised publication.

**Final continuation score: 40/40 PASS. U1–U5 GREEN in the precise C/R scope,
with separately compiled K components. Historical baseline remains 80/80.**

## What changed mathematically

The question is no longer merely whether one two-site example differs.
The conventional comparison theorem now covers every finite site count,
all nonnegative reader–writer constants, a constant division rate and any
mortality map decreasing with activating/increasing with repressive state.
It proves extinction and scalar population-PGF order. It extends to finite
Erlang phase clocks independent of molecular state. It does not prove size
stochastic dominance or order every first-passage event.

The proof uses a boundary-checked nearest-neighbor molecular coupling,
ordered allocation of common/extra marks, and association of independent
allocation bits after reversing repressive bits. This identifies the
monotone risk cone on which complementary daughter covariance is negative.

The exact response h=delta+Bh separates molecular continuation-risk
covariance from its propagation through the population. A positive weight
certifies kappa<.796 on an actual enclosing risk box. Narrower rational
boxes then bound the all-A extinction difference by
(.1144144057984627, .11443304520509548); outward simpler bounds are used
in the paper. Both signs and enclosures are tied to source rates, not
inferred from a fitted eigenvalue or a small floating residual.

The threshold identity avoids any large population-composition chain.
The new independent supersolution gives eventual hit-300 gap >.059.
Two validated microscopic PGFs give hit-300-by-300 gap >.054.
At N=16, a continuous monotone hazard with slope anywhere in
[7.999,8.001] has an extinction gap >.01427 at (9,7), an all-A gap
<.000122, and an eventual hit-2000 gap >.013 at (9,7).

## What was tested and learned

1. Exact six-state residuals and response boxes: canonical SymPy rational
   arithmetic reproduced every supplied independent supersolution residual.
   250 downward rational iterates and checked upper residuals gave useful
   forcing/response bounds. Weight components are
   (2.148,2.011,1.997,4.880,2.882,4.895).
2. Finite deadline: ordinary floating integration was not accepted as proof.
   Degree-20 Taylor steps of 1/50 used integer outward intervals at 10^40.
   A complex analyticity radius 1/4 gives a uniform local tail; real
   logarithmic norm .09 controls propagation. The total two-solve runtime
   was about 76 seconds, with error <1.81e-7 per solve. No local-stability
   hypothesis was needed: high order made even the global exp(27) bound
   sufficiently sharp. AA intervals are in deadline_validated.json.
3. Bounded sizes N=2,4,8,16,32: reproduced the review's step/smooth all-A
   gaps. Interior error decreases dramatically; near-balanced preparation
   can have much larger error at the same N. Finite sizes do not prove a
   nonvanishing asymptotic boundary gap.
4. N=16 smooth certificate: rational exponential bounds enclose the whole
   slope interval. Positive-map lower iterations (466/474) and exact
   supersolution residuals enclose all 153 coordinates. Maximum interval
   widths are 3.5763e-5 (joint) and 3.5408e-5 (independent). The complete
   diagnostic plus certificate campaign took less than ten seconds.
5. Preparation: all-A, a specified O(N^-1/2) contrast family, and a one-unit
   predivision molecular hold were compared. The hold suppresses death and
   division by explicit experimental assumption; it is not a treatment
   protocol. No convenient states were selected after evolving its law.
6. Mean-matched clocks: m=1,2,4 at rate m/10. At N16 smooth, founder (10,6),
   joint extinction increases .327685 -> .349397 -> .360826; gaps decrease
   .012498 -> .008331 -> .005601. These magnitudes remain N evidence.
   The conventional phase coupling guarantees the sign for every finite m.
7. Observation: prospective separated sister-clone extinction is the
   relevant risk-weighted observation. Parental mixing adds Var(m_X), so
   a pooled covariance sign is not an identified partition effect. A
   sensitivity interval explicitly includes within-stratum risk range,
   per-daughter classification error and missing pairs.
8. Matched-growth reproduction: a final bounded 13-second diagnostic fixed
   chronological growth at .005. At N=2,8,16,32, erasures were respectively
   .0818143818, .4354538223, .6043663843, .7428712700, and all-A gaps
   .0413662892, .0082280269, .0053119887, .0036819401. This reproduces the
   review's second table. It changes molecular erasure to control growth;
   unlike the fixed-source size comparison it is not a single-parameter
   size limit, and it does not prove global erasure monotonicity. Retained
   in the handoff/data rather than added as a nonessential paper result.

## Failures and corrected endpoints

- Small total variation is mathematically false: conservation-graph TV is
  1-C(2a,a)C(2r,r)/4^(a+r), tending to one for all-A. Do not retry it.
- Negative covariance for arbitrary vectors is false: (1,0,1) at two marks
  gives +1/4. The decreasing state-order cone is indispensable.
- A uniform approximation inferred only from all-A preparation is false
  already at N16 with a smooth hazard: the certified contrast exceeds .01.
  The corrected scaling law retains L_N^2/[N(1-kappa_N)].
- A near-critical expansion with a certified uniform second-order remainder
  was not pursued after the brief's allowed positive-vector margin endpoint
  closed the quantitative role. No expansion is claimed in the paper.
- Direct Lean arithmetic with powers 299/300 timed out; block-power bounds
  were substituted. Generic scalar lemmas isolate the final arithmetic
  from huge rational power expressions. Reusable algebra also triggered
  warning-as-error linters for unreachable/unnecessary tactic sequencing;
  those are compilation issues, not failed mathematical propositions.
- A first attempt to send the entire manuscript through a single Windows
  shell command exceeded the process command-line limit. The write was
  split into bounded chunks. PDF rendering then exposed long monospace
  filenames and a declaration name overflowing margins; line-breaking
  file paths and a separate declaration line repair them.

## Scope and evidence boundary

The paper keeps only the final critical path. The earlier killed-memory,
three-cell erasure comparison and optional DNA-carrier pilot remain in
historical artifacts, not in this paper's theorem chain. The old .389 gap
compared erasure rates; it is not repurposed as an inheritance gap.

The full all-N probability argument is conventional C evidence. The fixed
six-state algebra, reusable inequality steps and short assembly have a
separate warning-as-error Lean receipt. The integer ODE enclosure and
153-state checker are reproducible validated R evidence with conventional
soundness proofs, not kernel-checked stochastic processes. Diagnostic size
and phase-clock curves are labeled N. No unchecked native evaluation,
target axiom or admitted proof is used to claim formal closure.

Mortality, locus size and clock parameters are exploratory. No clinical
calibration, global erasure monotonicity, state-dependent birth extension,
universal size asymptotic or quantitative clock invariance is claimed.
Future biological questions do not reopen the selected mathematical root.

## Reproduction and delivery

Use REPRODUCE.md from the repository root. The final source bundle makes
the exact local Lean files available without relying on an absent remote
directory. No remote publication, push, dependency update or protected
generated-evidence commit was performed. The source archive is a local
delivery artifact, not a claim that GitHub now contains these files.

The main paper is molecular_memory_population.pdf, edited in place from
molecular_memory_population.tex in the project subfolder root. The task
register and local graph are CONTINUATION_TASKS.json and
CONTINUATION_GRAPH.md. The chronological ledger continues in
campaign/logs/2026-09-20.md.

AGC was helpful for distinguishing current authored evidence from canonical
authority and highlighting failed verification attempts. It did not supply
new mathematics. A CURRENT checkpoint is not a ClosedRoot theorem receipt;
the unbound canonical route remains distinct from the local C/R/K result.

## Strict compilation result

The final continuation Main.lean compiled successfully with all 14 imported
dependencies, warning-as-error, exit code zero and empty stdout/stderr.
The receipt verification/continuation_main.json reports 160.782 seconds.
Its elaborated declaration exports the actual independent source residual,
upper range, weighted source-Jacobian bound, hit300 arithmetic and deadline
arithmetic. Only standard Lean axioms propext, Classical.choice and Quot.sound
occur; there are no target axioms or sorry admissions. The reusable order,
association-step, iteration, response and threshold modules also compiled.
Earlier standalone failed attempt receipts are historical and superseded
by this content-bound successful dependency/root compilation.

## Final delivery gate

The final PDF has 12 pages, all rendered and visually inspected. Layout
and reference checks pass without overfull boxes or undefined references.
The current source and PDF hashes and proof-source freshness are recorded
in results/final_publication_check.json. A transient Windows lock on root
LaTeX auxiliary files was resolved by building in tmp/pdfs/tex-build and
copying only the completed PDF/log to the project root. No dependency repair
or update was needed. The source archive is regenerated after the final
register and handoff update, so it contains the delivered source state.

The stopping condition is the completed postproof brief with its expressly
allowed corrected endpoints, plus the finished paper. No selected implication
remains red. Unproved size asymptotics, a near-critical remainder expansion,
clinical calibration and full stochastic Lean formalization are named limits,
not advertised achievements or directions to start a new campaign.
