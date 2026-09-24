# C2 claim-to-declaration map

The root is proofs/FiniteCopyReactor/Resolution.lean. Every listed stochastic
claim is a Lean theorem or definition in its verified dependency closure.
DeterministicMargins and ErrorBottleneck are separately verified diagnostic
results; numerical pilots are not premises of the root.

| Claim | Declaration/module | Exact boundary |
|---|---|---|
| Literal20-label source | Source; CommonPhysicalRealization.ExporterSource.marked_projection | Falling factorials, both driven labels, fixed reservoir activities1 |
| Actual source trajectories | ActualSource; JointTrajectory.joint_actual_events | Positive-rate physical updates, available reactants, literal integer counter increments |
| Nonexplosion | CountNonexplosion; joint_trajectory_nonexplosion | All count starts, V>0, r,d>=0; no global rate-bound assumption |
| Full molecular pulse | Pulse.pulseMass_total; PulseInventory | Independent retained/withdrawn/lost categories, every outcome, integer food refill |
| Restart set | Restart; all_free_restart | Exact integer stock inequality; nonempty at every integer scale |
| Material drift and pulse tails | Source; PulseMaterialProbability; MaterialModel; MaterialReturn | Exact source identities and uniform exponential bounds |
| Stock recovery | StockExponential; EntryProbability.seeded_recovery_deadline | Prepared seed3V/250, target3V/50, deadline11/4; paid material exits |
| Residence and actual return | CollectionResidence; StateRestart | Actual intermediate and terminal states; strict activity retained for transfer |
| Free-X occupancy/output | PhaseProbability; Occupation; FreeCollection; FreeThreshold | Source-specific phase transport; actual free-X washout, integer ceiling |
| Template and supply counters | Template; SupplyBudget; RoundedService | Template equivalents; both foods including pulse; forward-plus-reverse service |
| Same joint law | JointMarks; JointCycle; JointCounterBudget; PreparedCycle | Five accumulated counters and actual state pass all phase boundaries |
| Safe stopping | SafeCycle; StoppingSemantics | Closed Restart alone is insufficient; strict terminal activity implies no earlier exit |
| Unrestricted transfer | StoppedAgreement.stopped_clock_eq_killed_chronology | Killed path equality from renewal/resolvent and local rate bound |
| Chronological composition | SourceSemigroup.chronological_endpoint_semigroup | Poisson convolution, killed semigroup and increasing-region exhaustion |
| Literal cycle identification | JointTimeComposition.joint_source_cycle_kernel_literal | Eliminates11/4 analysis split; collection marks switch at3 |
| Original count endpoint | JointPhysicalEndpoint.joint_cycle_count_projection | Counter erasure gives the original unrestricted count source at physical time4 |
| One-cycle joint probability | LiteralCycleBound.literal_cycle_success_bound | V>=10^6, all Restart starts, all admissible Intervention choices, r in[19,21], d in[0,1/25] |
| Explicit full history process | returnedHistoryStep; returnedPhysicalHistory | Normalized literal transition; prepends actual count/counter outcome; arbitrary policy on previous list |
| General conditional histories | PhysicalHistory; physical_history_success_lower; finite_copy_reactor_adapted_history | Arbitrary measurable history space with explicitly specified literal conditional endpoint law; success is derived |
| All-cycle full-law event | full_returned_history_success | Success submeasure domination plus support on exactlym good records; no conditioning/renormalization of process |
| Cumulative accounting | returned_joint_totals | Both outputs and all three expenditure coordinates on that same event |
| Physical inventory | joint_endpoint_has_trace; literal_cycle_has_trace; full_history_has_trace | Almost-sure finite supported physical traces; all pulse removals included |
| Net synthesis | HistoryTrace.inventory_lower, net_lower, certified_net_lower | Every physical realization of a certified history; sum of literal synthesis marks |
| Effective error/scale | one_cycle_error_envelope; volume_times_error; sufficient_volume_error | e(V)->0 with explicit inverse-volume sizing envelope |
| Root finite-horizon theorem | finite_copy_reactor_horizon | Probability of OperationalSuccess >=ofReal(1-m e(V)) |
| Root sizing/existence theorem | finite_copy_reactor_result | delta>0; V=max(2e11,ceil(5e6m/delta)); actual restart witness; requested parameter rectangle and policies |
| Concrete benchmark | finite_copy_reactor_hundred |100 cycles, probability>=99/100 at V=2e11 |
| Deterministic check | deterministic_interior_return; deterministic_collection_margins | Stock>=.06 after2.75; actual C1 output, food, service and return margins |
| Certificate bottleneck | one_cycle_error_phase_lower; error_certificate_volume_limit | V>=1e10 log(100m/delta) is necessary for this error certificate, not for a physical reactor |

## No unproved probability input

The main result quantifies m and delta>0, constructs V and N, and proves the
probability bound for the concrete literal process. It does not take a success
bound, martingale estimate, finite-case generator, global rate cap, clipped pulse,
or reset population as an input. The general-history extension takes a model's
literal conditional-law equation, which is the definition of its admissible
transition law; its probability-of-success estimate is proved.

## Scope of observations

The concrete normalized process records the complete preceding list of joint
count/counter outcomes. The general measurable-history theorem is stated over
PhysicalHistory. It can express additional continuous observations through the
history space and conditional-law equation. The exported interface does not
silently equate a finite count list with the entire continuous-time path.

## Verification boundary

Resolution.verify.json records the root source hash, pinned toolchain/manifest,
verified local dependency artifacts, warning-as-error flag, exact elaborated
interfaces and axiom reports. The final audit summary is ROOT_AUDIT.json.
Numerical JSON files and AGC checkpoints are diagnostics; neither replaces kernel
verification. Final AGC publication status is tracked separately in STATUS.md.
