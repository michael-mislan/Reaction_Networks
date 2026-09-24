# General fixed-factor common-activity compatibility: theorem and handoff

19 September 2026, Sprint 11. This report assembles the unrestricted result at the **mixed conventional/Lean boundary explicitly allowed by the attached guide**. It is not a claim that the complete algorithm or CAD has been implemented and verified in Lean. The final status and requirement audit are maintained in `general_campaign/COMPLETION_AUDIT.md` and `TASKS.json`.

## The theorem

For every finite oriented simple graph with fixed positive rational edge factors and independent rational closed species boxes 0<l_v<=u_v<=1, there is a complete exact algorithm deciding whether one common activity vector makes both original production residuals positive on every edge. It returns a rational common productive vector, or correctly excludes every such vector. Singleton boxes, empty graphs, weakly feasible but strictly infeasible boundaries and directed cycles are included.

For n species, maximum input coefficient bit length B, and maximum undirected simple-path edge count h, the algorithm and output admit the upper bound

    (n+2)^{O(h+1)} (B+log(n+2)+1)^{O(1)} 2^{2^{O(h+1)}}.

This algorithm accepts all source graphs; h is not an input restriction. A generic complete exact algorithm can be dovetailed with it to retain the better guarantee. The result is polynomial on fixed-h slices, including all-size cyclic graphs with unbounded junction count. It is not polynomial time on unrestricted graphs.

The source contract is unchanged: food activity 1, two original reversible channels per oriented edge, fixed factors a,b>0, one activity per shared species, and each edge's two residuals positive separately. This is a static compatibility statement, not a dynamical persistence theorem.

No authenticated named published conjecture equivalent to this exact programme has been identified. Accordingly this report claims the guide's unrestricted algorithm/resource result, not resolution of an unspecified named literature conjecture or priority over every structural algorithm.

## Complete proof chain

The proof is contained in three companion documents, with no remaining algorithmic oracle assumed beyond standard complete real-algebraic CAD:

1. [PATH_CYCLE_TERMINATION.md](notes/PATH_CYCLE_TERMINATION.md), sections 2–7, specifies and proves the exact weak-margin algorithm for every rational t>=0. Every feasible state dominates its anchors and all simple-path consequences. A violated edge appended to an attaining path necessarily closes a simple cycle. The least next root is forced by the intermediate value theorem; no root gives a valid rejection. Fixed nonidentity cycle-root values cannot be consumed twice, yielding finite termination and the least state on success.
2. [LOCAL_TEMPLATE_STRICTNESS.md](notes/LOCAL_TEMPLATE_STRICTNESS.md), sections 2–6, proves complete finite candidate coverage for each positive t. Every output coordinate is one fixed-cycle root or rational endpoint transported along one simple path. Local finite-fiber CADs stabilize all candidate box/edge tests near zero. An effective positive rational threshold therefore decides strict feasibility. Binary dyadic rounding inside boxes recovers a rational witness; no enormous grid is enumerated.
3. [LOCAL_TEMPLATE_STRICTNESS.md](notes/LOCAL_TEMPLATE_STRICTNESS.md), section 7, bounds local dimension, template counts, coefficient sizes, comparisons, jump counts and output bits. [RESOURCE_COMPARISON.md](notes/RESOURCE_COMPARISON.md) demonstrates the structural improvement over the specified inherited/generic guarantees and states its limits.

For a returned weak-margin state z at the computed t0>0, let eta<=t0/4. Box-preserving coordinate rounding loses at most 3eta in either normalized residual because each response is 2-Lipschitz on [0,1]. All residuals remain positive. The same rounded coordinate is used on every incident edge, so reconstruction never gives conflicting copies of a species. Multiplication by the positive original denominators converts normalized positivity to the two original production inequalities.

For a negative output, suppose a productive source state existed. Finitely many edges give it a positive uniform margin. Candidate stability then implies feasibility at t0. This contradicts the proved negative verdict of the fixed-margin algorithm. Thus rejection excludes every original productive state, not merely a sampled grid or chosen support.

## What Lean verifies

All modules are stable files in `proofs/ThermoCoreCompatibility/GeneralCompatibility/`; the pinned Mathlib environment and strict verification bridge were used. No warnings or admissions are accepted.

| Module | Verified content | Conventional interface still visible |
|---|---|---|
| ClosedMargin | Compact/min-closed least-state existence | Finite source input encoding |
| ActiveSupport | A least coordinate is lower-box anchored or incoming-tight | Source implication instantiation |
| Interaction | Tight-subsystem leastness counterexample | Stronger six-species counterexample has exact conventional proof |
| CycleBranches | Finiteness of analytic fixed roots under a nonidentity witness | Analyticity of full source compositions is elementary conventional analysis |
| CycleJump | Least-root domination, no-root rejection, lifted violation | Graph path splitting and actual cycle enumeration |
| FiniteProgress | Fixed root tokens cannot repeat; jump-count bound; actual single-anchor update semantics forbid an infinite successful run | Identifying the finite token set with graph cycle roots |
| SourceImplications | Explicit nonnegative quadratic inverse, inverse correctness, monotonicity/continuity, boxed margin iff actual bidirectional implications | Finite composition analyticity |
| StrictDecision | Uniform positive margin, downward closure, stability-to-strictness transfer | Local CAD constructs the threshold and proves stability |
| CandidateTransport | Local label tests transport a whole feasible state; literal productivity equivalence | Candidate coverage and parameter branch construction |
| Root | Both directions of the terminal source/threshold equivalence and negative-source conclusion | Explicit stable-threshold premise discharged by the conventional theorem |

The root is a thin assembly importing the actual new core. Its statement is conditional on threshold stability, openly and intentionally: the conventional CAD proof supplies that premise. Neither an unproved exact solver nor termination is postulated as an axiom. The finite-progress theorem derives termination of successful updates from local update semantics. This is stronger evidence than merely compiling a checker or an existential reformulation, but it is still **not a fully Lean-verified decision procedure**.

The guide permits a complete conventional general theorem with its genuinely new core and source bridge compiled. Full formalization of CAD, path enumeration, arithmetic complexity and machine execution remains optional future strengthening, not a hidden claim of this result.

## Experiments and failure-driven development

| Experiment/result | What was learned | Consequence |
|---|---|---|
| Five-species disconnected domain | Competing nonlinear paths can exchange order. | Abandon interval-only messages. |
| Repeated modules and independent copies | Component counts can grow; connected-piece covers can be exponentially large. | Decide feasibility without describing every component. |
| Unit single-edge cycle | Ordinary iteration can converge forever; arbitrary root selection is unsound. | Use least admissible exact root jumps. |
| Three-species tight-support counterexample | A selected tight subsystem can have a smaller inadmissible solution. | Retain all original inequalities. |
| Six-species unique tight-support counterexample | Even unique support does not remove the inactive-constraint problem. | Prove complete branch coverage rather than least-policy correctness. |
| Six tiny path/cycle runs | Exact results agree with independent full-system queries, including a zero identity. | Preserve these as branch and boundary regression fixtures. |
| Six-species 60-second execution timeout and two changed 20-second diagnostics | Delay occurred before any cycle jump, in exact algebraic comparison. | Change arithmetic representation instead of increasing the search budget. |
| Rational interval filter | The stalled comparison has an easily certified nonzero sign. | Avoid eager construction of merged algebraic fields. |
| Exact winning-path extensions | Four remaining phase-zero comparisons are structural equalities. | Use identities when available; retain a general exact fallback. |
| Unit-edge parametric margin | Critical margin exactly 1/48; roots coalesce at the endpoint. | Include singular parameter events. |
| Matched diamond | Zero-margin identity becomes impossible at every positive margin. | Separate positive-margin finite fibers from t=0 continua. |
| Windmill k=1,2,3,5 | Exact source validity, h=4 for k>=2, junction count k+1. | Support the symbolic all-size resource comparison. |

Pilot success is not the proof of a universal theorem. The conventional arguments are parametric and finite; the compiled statements have their own quantified scopes. Failed/UNKNOWN runs remain recorded. The full six-species algebraic prototype was not made fast by this campaign; only its diagnosed phase-zero bottleneck was resolved. The complexity theorem is for the specified CAD-based exact primitives, not Z3's implementation.

The central insight is **fixed ancestry**. Resetting derived labels to fixed cycle-root anchors plus simple paths simultaneously supplies a finite progress set and bounds the dimension of every arithmetic comparison. Positive-margin candidate families then permit local sign stability to control global feasibility. This avoids both moving-clamp critical values and Cartesian-product enumeration of candidate states.

## Resource comparison: what is and is not established

The growing windmill family has arbitrarily many undirected cycles and at least k+1 required junctions in the inherited path representation, yet h=4. The new uniform theorem guarantees polynomial bit complexity for arbitrary fixed rational factors and boxes on these graphs. The inherited junction bound and the full-dimensional generic existential-real bounds do not give that polynomial guarantee. The forest theorem does not apply.

This is a comparison of proved guarantees, not a runtime lower bound for competitors. Windmills also admit specialized block reasoning; the report makes no exclusive tractability claim. Further literature work may locate related structural results. The claimed advance is the guide's specific one: a source-preserving all-input exact algorithm with a structural resource bound improving the inherited generic elimination guarantee on an explicit all-size regime.

## Reproduction and operational limits

Run commands from the repository root. Use the canonical interpreter; no dependency updates are needed.

```powershell
& .\.venv\Scripts\python.exe scripts/check_python.py --quiet
& .\.venv\Scripts\python.exe scripts/smoke_numerics.py
& .\.venv\Scripts\python.exe scripts/verify_proof.py proofs/ThermoCoreCompatibility/GeneralCompatibility/Root.lean --timeout 180 --output problem_workspaces/RAF_thermo_compatibility_beyond_junction-path_assemblies/verification/GeneralRoot.json
& .\.venv\Scripts\python.exe scripts/process_guard.py run --timeout 30 --owner-label RAF-parametric -- 'E:\Erdos Problems\.venv\Scripts\python.exe' problem_workspaces/RAF_thermo_compatibility_beyond_junction-path_assemblies/experiments/parametric_margin.py
& .\.venv\Scripts\python.exe problem_workspaces/RAF_thermo_compatibility_beyond_junction-path_assemblies/experiments/path_interval_filter.py
& .\.venv\Scripts\python.exe problem_workspaces/RAF_thermo_compatibility_beyond_junction-path_assemblies/experiments/windmill_regime.py
```

The verifier automatically uses `mathlib4_project` as Lean's working directory and materializes checked local dependencies. A practical solver timeout remains UNKNOWN. Do not rerun the unchanged expensive six-species prototype, launch bulk certificate replay, or update Mathlib to reproduce this result.

The running score, evidence paths, failed attempts and timestamped Sprint history are in `general_campaign/` and `daily/2026-09-19.md`. AGC was run at entry, new structures, failed proof attempts and handoff gates. It was useful for proof-neutral freshness checks but its historical closure suggestion did not provide the mathematical route. Local completion does not require an authority integrator; protected publications remain untouched.

## Future work beyond this declared result

Stronger ambitions include a substantially better h-dependence, polynomial time for unrestricted graphs, a practical implementation of the complete local-CAD method, and full Lean verification of graph/CAD execution. None is asserted here. The completion audit must check the actual guide's mixed-boundary theorem, rather than silently substituting any of these stronger or weaker targets.
