# Publication handoff

Completed 2026-09-14T18:52:29.861460-07:00. Historical campaign **48/48 PASS** is preserved.
Post-proof follow-ups **24/24 PASS**. This counts conventional proofs where
identified below, not 24 independently kernel-verified statements.

## Delivered paper

`finite_count_inheritance.pdf`, ten pages, in this project workspace root.
Title: *Finite-count chemical inheritance with reversible interactions and
bounded food supplies*. The paper contains the final source, conventional
probability proof, actual partition/refill event, parameter region, restricted
minimum budget, composition margin, lineage bounds, stationary law and physical
limitations. Three vector figures and two complete-cycle examples are included.
Failed discovery lemmas, SSA results and the old wedge certificate are excluded.
The earlier controlled source is mentioned only to identify the structural change.

PDF SHA256: `d5fd83a2617e9b0edcbe1ff10f6d2bb2e25a9e90e758acb8301f1ea4ea110541`.
All delivery source/receipt hashes are in PUBLICATION_DELIVERY.json.

## Main results

For each module, the pure selected resident count n and food f obey n+f=K.
The same reversible channels S+F <-> 2S and S+U+F <-> 2S+U act on every word.
There is no count-triggered quench, maintained food pool or event quota.
Nominal coefficients are a=1000, b=1, gamma=1/10. The time-20 complete cycle
fairly partitions all molecules, requires both daughters to receive each selected
resident, refills food by module total, and resets solvent/clock externally.

* K=9: newborn resident cap 16; parent resident cap 18; exactly 18 modelled
  residents plus food per compartment. Uniform joint return is at least
  8046297159/8112104000, greater than 0.99188782.
* K=20: newborn resident cap 38; parent/modelled-total cap 40. Uniform joint
  return is at least 7077818258231/7077927321600, greater than 0.99998459.
* K=9 parameter box 500<=a<=1500, 1/2<=b<=2, 1/20<=gamma<=2/9:
  uniform joint return is at least 114080769/115203200, greater than 0.99025694.
  Catalytic coefficients are a*gamma and b*gamma; uncertainty is within this
  compatible family, not independent arbitrary errors in every channel.
* Composition regions have a uniform lower separation 2/K. The conventional
  boundary example proves this global minimum is sharp. Nearest-region readout
  tolerates L1 measurement error strictly below 1/K.
* Replenishing both daughters consumes exactly K new food molecules per module,
  or 18 across both modules at K=9. Solvent and apparatus are excluded.

## What is formally verified

`proofs/SmallResidentCompositionCopying/Publication.lean` is the short final root.
The authenticated exported declarations are:

1. `SmallResidentCompositionCopying.FiniteFood.publication` (nominal K=9,
   parameter-box return, geometry and count budgets).
2. `SmallResidentCompositionCopying.FiniteFood.return20` (nominal K=20).
3. `SmallResidentCompositionCopying.FiniteFood.literal_next` (every positive-rate
   channel has the literal resident stoichiometry).

Source modules are FiniteFoodSource, FiniteFoodInvariants, FiniteFoodDrift,
FiniteFoodRobustness, FiniteFoodPartition and FiniteFoodGeometry. Key source
identification declarations are channel_sum, generator_identification and
word_law. Conservation reconstructs food; food_transition, refill, food_refill
and admitted_daughters record the restart arithmetic. single_return sums the
actual complementary resident allocations. The manuscript explains why summing
independent food allocations contributes a factor one.

The final receipt publication.verify.json has exit code zero, verified=true,
warnings treated as errors, and only Classical.choice, Quot.sound and propext.
Duration: 60.031 seconds. PUBLICATION_AUDIT.json checks all
18 dependency source/artifact hashes, root source/artifact,
toolchain and manifest. Root SHA256: `d111998ed2fd273a3f9794be353cd05f74d24b0559175174d33a55286159cb62`.
No predecessor quenched probability theorem is in the final dependency graph.

The sharper predecessor bound 1/10 compiled in SharpComposition.lean without
editing the original theorem. Its source/artifact hashes are checked against
the saved publication_predecessor_context.verify.json dependency receipt. That
receipt is historical context; its previous Publication source is not passed
off as the current root. The original resolution/iteration receipts remain valid.

## Conventional consequences and exact diagnostics

The manuscript proves the restricted 17-molecule impossibility by balancing
fair allocations and integrating the pointwise ceiling over arbitrary parent
laws. It constructs the actual successful restart kernel W(x,y), proves row
bounds and conditional iteration q^N<=S_N<=u^N, and derives zero eternal
error-free survival of a selected lineage. It also proves binomial product-form
stationarity by edge balance, word-permutation symmetry, the sharp geometry
example and the single-contaminant obstruction. These are explicit conventional
proofs, **not separately Lean-verified consequences**. No unresolved conjectural
extension is presented as established.

postproof_preflight.py reproduced the review's exact 81/400 nominal state checks,
648 state/parameter-vertex checks, stationary edge identities and the maximum
partition reward under peak17. All use exact rational/integer arithmetic.
The symbolic Lean parameter proof covers the entire box. No SSA or large
finite certificate campaign was needed. Numerical preflight is evidence for
discovery and error detection; it is not the basis of formal proof acceptance.

## Physical and scientific scope

The four labels have different exact species supports. A previously absent
alternative cannot be generated by the base table; a present species' last
molecule cannot disappear. One contaminant therefore prevents joint return to
the original pure-label regions in that cycle. This is not contamination repair,
mixed-support memory, autonomous reproduction, a universal minimum molecule
theorem, or experimental calibration. The time unit is hypothetical. Split,
replenishment and volume reset are instantaneous ideal external operations.
Thermodynamic compatibility does not quantify controller work or feasibility.

The primary literature was checked, including Matsubara et al., arXiv:2211.03155v2,
21 July 2026; the paper positions its explicit budgets and probability bounds
without claiming the first demonstration of chemical heredity. References also
include Segre et al. (2000) and Anderson, Craciun and Kurtz (2010).

## Reproduction

From E:/Erdos Problems, use the canonical repository interpreter:

```powershell
.venv/Scripts/python.exe scripts/check_python.py --quiet
.venv/Scripts/python.exe scripts/smoke_numerics.py
.venv/Scripts/python.exe problem_workspaces/RAF_small_resident_budget_interacting_copying_mechanism/postproof_preflight.py
.venv/Scripts/python.exe scripts/verify_proof.py proofs/SmallResidentCompositionCopying/Publication.lean --timeout 600 --declaration SmallResidentCompositionCopying.FiniteFood.publication --declaration SmallResidentCompositionCopying.FiniteFood.return20 --declaration SmallResidentCompositionCopying.FiniteFood.literal_next --output problem_workspaces/RAF_small_resident_budget_interacting_copying_mechanism/publication.verify.json
.venv/Scripts/python.exe problem_workspaces/RAF_small_resident_budget_interacting_copying_mechanism/publication_audit.py
& problem_workspaces/RAF_small_resident_budget_interacting_copying_mechanism/build_paper.ps1
```

The builder uses the local MiKTeX installation (automatic package installation
disabled) and Poppler; mathematical figures use canonical Python with a 60-second
process lease. No lock, toolchain, dependency or verification-bridge changes
were made. No subagents or generated-evidence commits were used.

Every page was rendered and visually inspected. Repaired an overflowing path,
an overlong schematic label and a cross-page command block. Final LaTeX has no
overfull boxes or undefined references. PDF metadata and ten-page count checked.

AGC entry, new-structure/repair and stopping records are retained. New interfaces
required the exact proof-neutral same-frontier reconciliation; final checkpoint
is CURRENT. Its authority graph remains unbound, separately from strict proof
evidence. AGC helped with freshness and scope, not the mathematical discovery.
