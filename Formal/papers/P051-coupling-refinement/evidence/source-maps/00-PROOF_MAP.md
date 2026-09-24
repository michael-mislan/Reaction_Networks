# Claim-to-source map

Paths here are relative to the original `Erdos Problems` repository root. The manuscript is
self-contained for its conventional arguments; the formal source is separately identified below.
All RAF1519 refinement names have namespace `RAF1519.Refinement` unless explicitly qualified.

| Printed claim | Exact source / declaration | Assumptions and conclusion | Evidence |
|---|---|---|---|
| Literal seven-species chemistry | `proofs/RAF1519/Refinement/Source.lean`: `field`, `firstFlux`, `secondFlux`; `CountSource.lean`, `CountNetwork.lean` | 23 local labels; positive r,d, fixed beta/theta for count law; falling-factorial propensities, feeds, washouts, common exchange | Formal source definitions and identities |
| Theorem 2: local deterministic operation | `proofs/RAF1519/Refinement/Repeated.lean`: `R15_D` | r in [19,21], d in [.02,.04], beta=.01, 0<theta<=.01; protocol takes cycle index and current state; ready seed; existence of actual global segments, return, product, food and service over every finite prefix | Formal, existing strict `evidence/Repeated.verify.json`; conventional explanation in Appendix A |
| Theorem 3: refined mission | `proofs/RAF1519/Refinement/RelaxedMission.lean`: `Relaxed.R15_S` | n>0, V>=10000, symmetric nonnegative exchange with row sums<=Delta; ready seed and empty history log; `PhysicalHistory` interface; probability >=max(0,1-29nm exp(-V/[2e12(1+Delta)^3])) | Formal, existing strict `evidence/Publication.verify.json` |
| Inhabited history interface | `ReturnedHistory.lean`: `returnedPhysicalHistory`, `returnedHistoryStep_markov`; `RelaxedMission.lean`: `Relaxed.returned_mission` | Arbitrary policies on complete lists of returned count states and five physical counters; conditional law is the literal pulse-plus-flow law; no success assumption, censoring of failures or reset | Formal; dependency closure of publication receipt |
| Physical marks and success event | `CycleOutputLaw.lean`, `RelaxedOperating.lean`: `Relaxed.integerCycleSuccess_of_operating` | QI,QX on (3,4]; food/service on (0,4], integer refill; original ceilings/floors and actual ready endpoint | Formal |
| Improved probability budget | `NoiseBudget.lean`, `RelaxedCorridors.lean`, `RelaxedStock.lean`, `RelaxedProbability.lean`: `Relaxed.pulseFlow_integer_failure` | Pulse 5n, coordinates 14n, marks 10n; tolerance 1/[10000(1+Delta)]; unrestricted literal law | Formal; readable concentration/comparison derivation in main text |
| Connected witness | `RelaxedInstance.lean`: `Relaxed.connected_hundred_cycle_mission` | n=2, edge weight 1, V=224000000000000, m=100, literal integral seeds | Formal; arithmetic gives >.99; displayed decimal is numerical evaluation |
| Corollary 5: sizing and food ratios | `MissionAccounting.lean`: `Relaxed.mission_size`, `Relaxed.successful_cycle_yield` | Positive constants for log inequality; integer cycle success for food ratios | Formal plus conventional derivation |
| Theorem 4: donor mission | `problem_workspaces/Medical_Sept16Plan_13_14/paper/reliable_exchange.tex`, `THEOREM.md` | Literal six-species process, donor service mark, common event, V>=10000; 27nm exp(-V/[2e14(1+Delta)^3]) | Conventional, complete estimates in Appendix B; not a fully formal probability root |
| Proposition 6: exact donor reduction | Same donor manuscript; `proofs/RAF1314/MaterialReduction.lean` supports reconstruction identities | Four phases plus exact material histories, nonnegative reconstruction domain and literal deterministic pulse updates | Conventional proof, selected formal algebra; no autonomous frozen-material stochastic claim |
| Proposition 7: storage and nonclosure | Seven forward increments in Table 1 and `Source.lean` field; two explicit ready states | theta=beta=.01 for witness; identical six coordinates but different food/x rates; V divisible by 200 for count witness | Conventional; exact arithmetic checked by reproduce.py |
| Proposition 8: augmented synthesis | J weights (0,0,1,1,1,2,1); chemical J increments (1,0,0,1,0,0,-1) | Every finite physical path: telescope; successful mission implies S_J>=nV(m/56+1/28-161/160), positive at m>=55 | Conventional, source-bound pathwise proof; no new Lean declaration claimed |
| Service ratios and inverse duration | Integer success event and Theorem 3 | G<=56QI/5, G<=216QX; sufficient duration at a risk allowance | Conventional algebra |
| Figures 2--4 | `reproduce.py`, `data/operation.csv`, `data/cycles.csv`, `data/checks.json` | Exact fixed source parameters and literal deterministic carryover; tighter numerical repeat | Numerical illustration; no proof or empirical probability claim |

## Strict evidence audit

The original receipt is:
`problem_workspaces/Medical_Sept16Plan_15_19_preserving_function_thru_inheritence/evidence/Publication.verify.json`.
It reports `verified: true`, exit 0, and `-DwarningAsError=true`. Publication target source,
all 430 recorded dependency sources, the Lean toolchain pin and the lake manifest were compared
with current files. The printed mission/witness/sizing/food declaration interfaces were inspected;
all report only `propext`, `Classical.choice`, `Quot.sound`. The concrete returned-history
construction was read directly. No unchanged proof was rebuilt merely for a second receipt.

The donor workspace explicitly distinguishes compilation-only receipts from failed declaration
probes. This manuscript relies on the donor conventional proof, not on those failed probes.
The donor AGC checkpoint reports `AGC-LAUNCH-E005` (no canonical specification). The refined
checkpoint reports CURRENT with proof-neutral authored-route guidance. Neither AGC outcome
is mathematical evidence or a substitute for Lean.

No general intermediate-elimination theorem, fully formal donor probability root, arbitrary-theta
stochastic statement, calibrated chemistry or experimental validation is asserted.
