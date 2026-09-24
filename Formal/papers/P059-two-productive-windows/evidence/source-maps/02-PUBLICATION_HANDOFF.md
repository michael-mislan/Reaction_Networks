# C6 publication handoff — 16 September 2026

The research paper is `C6_Two_Window_Productive_Operation.pdf` in this project
subfolder root. It has 14 pages, three figures, two numerical tables, the
explicit probability constants, and a formal-scope appendix. Editable LaTeX,
bibliography, source scripts, raw numerical data, a theorem map, and build
instructions are in `paper/`. The manuscript uses only the final proof chain
and the consequences/example requested in the publication attachment.
Discovery attempts remain in the ledger rather than becoming paper lemmas.

## What was established

The accepted finite-horizon root remains unchanged: one food-only initialized
trajectory has endpoint stock at times 1, 100, and 199, nonfood monomer export
greater than V/10 in each of (1,100] and (100,199], mass at most 11V throughout,
and at most 1195V food arrivals. On this event, net internal nonfood synthesis
exceeds V/5. The source is the literal capped, shifted Zipf row sampler and
the count process uses falling-factorial propensities, the admitted shared
marks, food feed, and washout. The two windows are not independently reset.

The final critical proof path is the selected food-silent witness, its
startup/coordinate controls, the interval potential bound, both actual export
windows plus stock/supply, simultaneous actual-law noise control, exact source
averaging, inherited event converse, and signed material identity. The paper
states and credits the inherited estimates before applying the interval
extension. It does not claim that endpoint stock proves uniform restart from
every state in the stock region.

The follow-up consequences are:

1. There are 224 productive incidences: 32 ordered food-to-nonfood splits,
   each with six possible food catalysts and its own product. The productive
   predicate is identified exactly, not replaced by the 15480-element short
   rectangle. The source union bound sharpens the upper coefficient to 224.
2. Along the admitted volume sequence, the full lower limiting coefficient
   is gamma=(6/pi²)^6=0.0504788009, and the selected source witness has posterior
   liminf at least gamma/224=0.00022535179. This is a liminf, not an asserted
   eventual bound at the exact endpoint.
3. The exact source gives 2^n p_n -> 9/(2pi²)=0.4559453264. Mission success and
   the population of highly reliable environments are Theta(2^-n). Independent
   complete-experiment screening therefore needs Theta(2^n) trials at fixed
   confidence. Repeating one fixed environment has a different mixture law.
4. The event inclusion transfers local singleton dominance and the disabled
   baseline suppression, supplies a positive repeated-given-first-window
   liminf, and permits RAF conditioning using the same-source structural
   theorem. It does not identify relative weights of the 224 mechanisms.
5. A new stopped first-birth proof gives food-silent mission probability at
   most 1-exp[-(484/3) epsilon V]. Corridor exits are safely absorbed in the
   survival comparison; they are not counted as births or conditioned away.
   The finite-state uniformization proof and Poisson mixing are written in
   full. With epsilon=2e-9, 99% reliability necessarily requires
   V >= 14,272,221.6508, so the integer count scale must be at least 14,272,222.
6. The compatible material account gives recovered nonfood monomer fraction
   Q/(10V+B)>1/12000. Gross food arrivals and monomer input are not conflated.

## Finite utility and what the experiment taught us

Tracing the constants identifies the selected-product absolute noise tolerance
1/(3e20) as the dominant conservative bottleneck. The inherited direct
conditional theorem permits a real improvement over the convenient
V_*(n)=1e60(n+1)² envelope: V >= max(2n/d, (n/c)log(24/eta)) suffices for
witness reliability 1-eta. At eta=.01 the second term is approximately
2.24157e50 n; at n=4 it is 8.9663e50 rather than 2.5e61. Both remain impractical.
This does not silently weaken the assumptions of other converse statements.

The fixed-cutoff converse has a separate obstruction. At n=4 its local
rectangle includes the whole source, and the probability of at least two
incidences is almost one. We computed its exact independent-row formula;
its complement is about 10^-11.446. A smaller census prefactor cannot repair
that residual. An informative accessible-incidence converse would need a
bound on integrated adverse drift from occupied catalysts under the exposed
dependent row law. No bulk simulation can substitute for that inequality.

We first tested a 10-replicate pilot, then ran 200 trajectories per row, with
single-thread numerical settings and a 180-second process lease. The chosen
n=4 source uses all 30 molecules and 68 split identities, all marks one,
and one catalytic incidence on 00+11 <-> 0011. The interventions change its
catalyst from 0011 to food 0 or delete it, preserving all basal chemistry.
These are explicit chosen environments, not conditional random samples.

The deterministic full-catalogue self trajectory eventually reaches selected
product concentration about .2753 and exports about 102.8V and 109.0V in the
two windows. Yet at V=100 the rigorous food-silent mission ceiling is only
3.22661e-5, and at the prospectively specified V=200 it is 6.45313e-5.
Neither self row had a first birth in 200 deadline-one paths; the deleted
V=100 row also had none. All 200 food-catalyst paths had a first birth.
There were five corridor exits in each V=100 row and none in self V=200;
the raw records retain them. A zero-in-200 two-sided 95% binomial interval
extends to .01828, so these runs cannot measure a probability of order 10^-5.
The experiment illustrates the initiation distinction, not the precision of
the analytic ceiling. The largest deterministic mass-account discrepancy
was about 3.7e-13.

The dimensional example is explicitly illustrative: V=N_A Omega c_* and
physical time is tau times model time. At c_*=1 micromolar the necessary
99% startup scale is about 23.7 pL, not a sufficient reactor size. The huge
sufficient scale remains huge after conversion. No calibrated chemistry or
purified functional output is claimed.

## Verification and formal scope

The root receipt `c6_resolution.verify.json` remains valid. Its root source
hash is a18c376680dce935c51a305c3dde1f8e7e25b5fe1cbd479657e70c7aef523060.
The initial audit checked 428 items, including 425 dependency sources, the
root, toolchain and manifest, without mismatch.

The new `publication_bundle.verify.json` passed strict Lean 4.30.0 verification
in 522.344 seconds with empty compiler output and 428 dependency entries.
It checks `ProductiveCensus.lean` and `StartupNecessary.lean`, including the
literal predicate equivalence, kernel census/injection, food-pair maximum,
rate consequence, finite-kernel survival induction, logarithmic necessary
scale, and scalar material fraction. The transitive axioms of the probed
declarations are exactly propext, Classical.choice, and Quot.sound.
The final publication audit checks both receipts against current source
content, with 853 dependency entries across them; these are not 853 independent
mathematical achievements.

The first auxiliary census compile failed on dependent-equality elaboration
and a deprecated tactic. The finite 224 computation already succeeded.
The transport proof was repaired in place, without weakening its predicate,
adding assumptions, or using native computation. The successful bundle is
the evidence used by the paper; the failed receipt is historical diagnostics.

The paper does not describe every added consequence as a new Lean export.
The 224 source union bound, limiting arguments, screening/reliability/event
transfers, and physical stopped-generator identification plus Poisson mixing
have conventional proofs in the manuscript. The finite-kernel auxiliary
theorem alone is not asserted to be the actual-law first-birth theorem.
The theorem map records this distinction claim by claim.

## AGC, delivery, and remaining boundaries

AGC was invoked on entry, after mathematical structure, after the new proof,
and at handoff. It detected new content-bound proof inputs and requested
same-frontier reconciliation. That authorized proof-neutral reconciliation
bound the root and new auxiliary interfaces; it did not change the theorem
graph or create mathematical evidence. AGC helped with scope/freshness and
receipt handling. The mathematical improvements came from direct source
inspection, algebra, and the small diagnostic experiment.

The PDF has been built with resolved citations/references and no overfull
boxes. All pages were rendered and visually reviewed, including equations,
tables, plot labels, the formal-scope table and bibliography. Page images
are in `paper/rendered`; the final fingerprint and checks are in
`paper/theorem_map.json` and `paper/QA_REPORT.md`. Nothing was submitted to a
journal, uploaded publicly, or committed as generated evidence.

The publication follow-up register is complete at 24/24 PASS; the final AGC
checkpoint succeeded after reconciliation. It is separate from the historical 38/60
guide tally. The latter is not retroactively relabeled as 60/60. The requested
publication follow-ups close with this paper/package; arbitrary-state restart,
infinite-horizon persistence, exact operational weights, practical sufficient
volumes, and a fully formalized terminal export for every conventional
corollary remain outside its claims. No bulk campaign is queued.
