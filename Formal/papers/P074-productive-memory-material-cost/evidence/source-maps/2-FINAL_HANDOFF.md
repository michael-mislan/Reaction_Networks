# Productive chemical memory: comprehensive research handoff

## Result and exact scope

The selected guide scope is a source-bound robust material frontier, not a
universal theorem about all chemical memory. For the guide's literal reversible
binding source, fixed reference volume/count-rate convention, complete restart
set, terminal product quota 4, deadline 5, and target 999/1000, the least material
budget guaranteeing success at every release parameter kappa in [10,20] is 32.

The decisive lower probability is 2145514420/2147483648 = approximately
0.9990830067545. The guarantee is uniform over every admitted preparation and
the entire real interval of release parameters, not just its endpoints. All
smaller budgets are excluded at the admitted parameter kappa=10: budgets 2-14
by the material/partition ceiling, and 15-31 by exact finite upper certificates.
The largest exclusion upper value is 2144298834/2147483648 at 31. Therefore the
same robust minimum holds for every reliability target strictly above that
upper value and at most the robust lower value. This is an actual family result.

The concrete frontier is **C/E**, conventional proof plus exact integer
computation. The general envelope and source/accounting implications have **K**
evidence from strict Lean compilation. **No end-to-end Lean proof of the
3384-state numerical certificate or the full CTMC probability theorem is claimed.**
This is the guide's explicitly permitted C/E publication with K decisive lemmas
(guide section 11.5), satisfying the user's alternative of completing guide
scope. It is not advertised as settling a separately named literature conjecture.

## What is new beyond the supplied guide

The guide supplied the nominal minimum32 and first-release obstruction. The new
step is a nonlinear lower envelope of endpoint stochastic kernels, which
certifies a factor-of-two continuous release interval with one finite
calculation. Affinity is used at the one-step kernel, not at the terminal
probability. Its exact exclusion argument reuses the already established
constant-rate witness. There is no monotonicity assumption in material, release,
or deadline, and no wide parameter sweep.

Let P10 and P20 be the common-clock kernels and Mv=min(P10v,P20v), rowwise.
For every kappa in the interval, Mv <= Pkappa v. Positivity gives monotonicity;
induction gives M^j v <= Pkappa^j v. Positive truncated Poisson sums preserve
this order. Repeated rounded lower blocks therefore remain below the actual
finite-time payoff. The full proof, floors, clock, overflow bounds and coverage
are in the manuscript, sections 1 and 3 and appendices A/B.

This is a finite certificate theorem with a general uniformity implication, not
an unproved dimension-reduction ansatz. STRUCTURAL_REVIEW.md explains why two
robust pilots close the exact selected obligation and why additional bulk replay
is unnecessary. It compares structural bounds, proved checkers, generator
soundness/coverage and explicit replay as required by the repository.

## Experiments, failed routes, and what we learned

1. **Entry and source adoption.** Read the entire attached guide and local
   AGENTS.md. Canonical Python preflight and numerical smoke passed. Adopted all
   23 supplied preparation items, with their existing C/E/N distinctions.
   The user renamed the workspace during entry; all files survived under the
   current RAF_Origin path. Existing factory Lean source is a different fueled
   repair mechanism; only its general uniformization module was reused.
2. **Nominal exact replay (PASS, C/E).** The 18 budgets 15-32 reproduced every
   guide numerator. About 27 seconds initially, maximum 3384 states. No rounding,
   transpose or source mismatch. Saved as experiments/benchmark_two_sided.json.
3. **HC-008 preparation/release diagnostic (N).** Four small backward solves:
   (K,kappa)=(31,10),(32,10),(32,1),(32,100), each comparing resident-heavy,
   free-seed and bound-seed starts plus the stationary payoff. About 24 seconds.
   At (32,10), resident-heavy quota failure is 0.000900058131 and partition
   failure 0.000004581103. Free-seed quota failure is 0.000004674551, while
   partition failure is 0.000169826294. Food-poor startup is the useful
   explanation for the nominal quota tail, with the causal claim explicitly
   limited to a controlled preparation comparison. The entire 17-unit gap is
   not assigned to sequestration or to any single cause.
4. **Failed universal worst-start hypothesis (N counterexample).** At (32,1)
   bound-seed success is 0.939455 versus resident-heavy 0.967111. A universally
   resident-heavy worst preparation is false. This does not refute its role at
   the nominal parameter. We did not use that hypothesis for certificate coverage.
5. **Rejected partition-only explanation.** Over 99% of nominal resident-heavy
   failure at budgets31/32 is missed product quota. Refining partition alone
   cannot fix the failed31 point. Separately multiplying success marginals was
   never used.
6. **Stationary-only route not accepted.** The stationary distribution has
   tiny residuals (~1e-14), but stationary payoff is not a deadline bound. A
   mixing theorem was not proved or assumed. No expensive spectral search was
   launched; the robust envelope supplied the needed transient comparison.
7. **HC-009 robust pilots (PASS, C/E).** [10,11] yields lower numerator
   2145517682; [10,20] yields 2145514420, common denominator2^31. About seven
   seconds each. The interval calculation permits a stronger rowwise adversary
   than a fixed unknown rate; its conservatism still leaves enough margin.
   The broader band loses only3935/2^31 relative to the nominal lower certificate.
8. **Certificate conservatism diagnostic.** At32 the nominal floating success
   exceeds its rigorous lower bound by about1.0522e-5. At31 the exact upper
   already falls below target, so certificate loss is not the reason31 fails.
9. **One actual source trace (N illustration).** SSA seed20260917, start
   (31,0,0,1), terminal(25,0,7,0), channel counts(24,30,40,33,28,21).
   Net collected product is28-21=7. Actual daughters retain13 and12 residents,
   refill19 and20 food. Ledger32+39=7+32+32. The complete event record is saved;
   this is not a Monte Carlo reliability estimate.
10. **Formalization failures and repairs.** Initial Source compilation exposed
    a Lean notation ambiguity (unspaced <= followed by s parsed as graph
    notation). Spacing repaired it. MaterialBound needed a separate refill
    lemma and a common reciprocal normal form. These were implementation/proof
    elaboration failures, not mathematical counterexamples. Failed receipts
    remain historical; the successful root receipt imports current files.
11. **Publication QA.** Seven-page LaTeX PDF built with local pdflatex; all pages
    rendered with Poppler and inspected. Fixed an overlong workspace path and
    a figure legend hiding certified points. The final quota plot also marks
    exclusion inherited by larger quotas. No interpolated region is called
    certified. No runtime/dependency lock changes were made.

## Source, returns and cost

The six literal rates are nf, n(n-1)/100, 2nf, kappa c, kappa c, np/50.
The invariant n+2c+p+f=K charges two units to a bound complex, while intact
partition counts n+c carriers. Both daughters are outcomes of one fair
complementary partition, not independent daughter simulations. Product is
terminal stock starting at zero, not the number of forward release firings.

Successful daughters have 1 <= resident count <= parent count-1 <= K-1.
Their nonproduct retained mass does not exceedK; food refill returns them to the
actual B_K restart set with product zero. Total refill is K+p. Conditional
iteration gives at least L^G successful inspected divisions along a preselected
lineage, even if kappa varies between cycles within the band. Ten cycles exceed
99% reliability, yield at least40 product units, and consume at least392 initial
plus newly supplied material units when both daughters are refilled. Unoperated
siblings retain inventory and remain in the account. This is not a full binary
family-tree guarantee or autonomous protocell demonstration.

The admitted bound seed has only two enabled exits, each rate kappa. Thus
p_* <= 1-exp(-2 kappa T), for everyK and positivequota. For T5 and target0.999,
kappa < log(1000)/10 is impossible regardless of added food. This proof is C;
the literal enabling/rate calculation is K in Source.lean. No CTMC holding-time
probability theorem is silently claimed formalized.

## Exact evidence map

| Claim | Evidence | Artifact / declaration |
|---|---|---|
| Literal source and conservation | K | Source.lean: rates, jump_conserves, final_resident_survives |
| Quota charges material | K | Source.lean: quota_limits_carriers |
| Source is affine in release | K | Source.lean: release_affine |
| Bound seed is admitted and only releases | K | Source.lean: bound_seed_admitted, bound_seed_rates |
| Actual first-exit probability obstruction | C + K source facts | Manuscript Theorem2 |
| Refilled complementary daughters restart | K | MaterialBound.lean: complementary_daughter_return |
| Food replenishment identity | K | MaterialBound.lean: actual_refill_account |
| Carrier/material necessity | K deterministic implication, C probability docking | MaterialBound.lean: reliability_requires_carriers, material_necessary |
| Uniform endpoint-envelope comparison | K | RobustEnvelope.lean: envelope_le_kernel, envelope_iterates_lower, robust_poisson_lower |
| Complement converts lower to upper | K | RobustEnvelope.lean: complement_upper |
| Repeated lower blocks | K reused, C integer realization | TinyProgrammableChemicalFactory.UniformizationLower.block_iteration_lower |
| Exact robust minimum32 | C/E | benchmark_two_sided.json, robust_release.json, manuscript Theorem1 |
| Threshold and ten-cycle arithmetic | K | Frontier.lean: exact_frontier_margins, ten_cycle_margin |
| Robust exclusion and coverage logic | K conditional lemmas | Frontier.lean: robust_exclusion, exact_minimum_from_coverage |
| Short formal root and axiom reports | K | Resolution.lean, verification/Resolution.verify.json |
| Preparation mechanisms/stationarity | N | mechanism_pilot.json |
| Counter ledger/trajectory | N, exact integer material identities | source_trace.json |

All Lean paths in this table are under proofs/UsefulChemicalMemoryCost unless
otherwise specified. The root's dependency list and hashes are the authoritative
record of the final compiled files; an earlier failed Source.verify.json or
earlier stale standalone envelope receipt is not a current failure of the root.
Only ordinary Lean logical axioms are allowed; no sorry or numerical-answer
axiom is used. The Python producers and CTMC semantic docking remain outside K.

## AGC usefulness and integration boundary

AGC was invoked on entry, after the envelope structure, after implementation
failure, and before stopping. Entry correctly reported missing specification;
the prescribed start action made the local specification CURRENT. No protected
theorem graph or generated-evidence commit was made. The specification has no
canonical frontier authority; AGC's automatic route reader selected the literal
guide-template phrase 'the remaining gap:' rather than the new mathematical
lemma. Its freshness classification is useful, but its suggestions did not
discover the envelope or validate the concrete theorem. The local ledger and
evidence map therefore carry the actual scoped C/E result.

The final AGC checkpoint is saved separately. A future canonical integrator may
bind the result into a protected theorem graph at its honest C/E+K scope.
An AGC CURRENT or proof_admissible field is not a proof and is not used as one.
Unbound global-authority integration is separate from completing this local
guide scope; no claim of a kernel-closed canonical CTMC root is made.

## Reproduction and deliverables

Canonical workspace:
`E:\Erdos Problems\problem_workspaces\RAF_Origin_material_cost_of_useful_chemical_memory`.

Run from `E:\Erdos Problems`:

```powershell
.\.venv\Scripts\python.exe problem_workspaces/RAF_Origin_material_cost_of_useful_chemical_memory/reproduce.py
.\.venv\Scripts\python.exe scripts/verify_proof.py proofs/UsefulChemicalMemoryCost/Resolution.lean --timeout 600 --output problem_workspaces/RAF_Origin_material_cost_of_useful_chemical_memory/verification/Resolution.verify.json
```

The first is bounded published replay, with one numerical worker and guard per
subprocess, not a discovery campaign. Numerical source uses the canonical
Python3.11 environment and no altered packages. The second compiles the formal
spine in the frozen mathlib workspace. Saved results allow reading the paper
without rerunning either.

- Paper and focused technical supplement: output/pdf/material_cost.pdf.
- Editable paper: output/pdf/material_cost.tex; figures alongside it.
- Attached guide preserved in full: GUIDE.md.
- Experiment outputs: experiments/*.json, with scripts alongside.
- Running history: ledger/2026-09-17.md; seed history HC001-HC007 in GUIDE.md.
- Scope/route decision: STRUCTURAL_REVIEW.md.
- Task-by-task evidence: TASKS.md and tasks.json.
- Local outcome graph: HYPOTHESIS_GRAPH.md.
- Strict root receipt: verification/Resolution.verify.json.
- Reproduction output: reproduction.log.

## Remaining limits, not hidden obligations

The selected robust frontier is closed at its declared mixed evidence level.
Full kernel replay, arbitrary quotas/rates/budgets, optimal physical preparation,
common-support correction, packaging kinetics, autonomous reset and empirical
calibration remain outside this theorem. We did not treat two failed optimizers
as impossibility, require another campaign to finish, or create a larger target
after closing the scoped one. The proof does not claim allK>32 succeed, nor that
the stationary payoff is a finite-time upper bound, nor that32 is a universal
material cost of useful memory.
