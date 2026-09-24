# Evidence map

GUIDE.md is an instruction/reference document, not campaign evidence.
The inherited sequential capacity theorem is an ordinary proof in ../RAF_exact_stable-state_capacity_n-site_phosphorylation_system/{ORDINARY_PROOF,SPECTRAL_PROOF}.md. Its modular Lean receipts do not formalize the full capacity theorem.

## Proof dependency order and root scopes

| Order | Document | Established interface |
|---|---|---|
| 1 | SOURCE_AND_CONTRACT.md | Literal reactions, inventories, class rank, finite lattice and operational quantifiers |
| 2 | SYMMETRIC_BRIDGE.md | Exact equilibrium/stability correspondence and aggregate path laws, all n |
| 3 | FINITE_MEMORY_THEOREM.md | Quadratic generator, stopped retention, recovery, readout, explicit common two-label source |
| 4 | SCALING_PROOF.md | Smooth dynamic factorization and full-source local action asymptotic |
| 5 | LOCAL_EXIT_THEOREM.md | Source-generator and Poisson-tilting quantiles; iterated local-domain scaling |
| 6 | TREE_REDUCTION.md | General exact parameterization, exceptional ratio, degree upper bound |
| 7 | POLE_OBSTRUCTION.md | Selected circulating square: two poles but at most two sinks uniformly over its declared totals |
| 8 | UNIFORM_CAPACITY_PROOF.md | Exponential interpolation rank, normal stable continuum, full-source lift; C_n=Theta(2^n) |
| 9 | ARCHITECTURE_MEMORY_COMPARISON.md | Exact symmetric equality and a common-constraint four-versus-three finite-memory comparison |

R3-FINITE, R3-SCALING, R6-SYMMETRIC, R6-GENERAL and R-JOINT are GREEN as **ordinary** theorems at these exact scopes. R3-SCALING uses a local inward tube and an iterated limit. R6-GENERAL uses the growth-classification alternative; the exact sharp formula is not claimed. Finite operating thresholds are sufficient, not optimal or practical.

## Strict Lean components

| File under proofs/PhosphorylationMemory | Verified declarations and boundary | Receipt |
|---|---|---|
| SymmetricAggregation.lean | association_multiplicity, association_level, quadratic_jump; algebra only | certificates/aggregation_lean.json |
| TreeTotals.lean | denominator_split, ratio_loading, exceptional_derivative; scalar reconstruction algebra only | certificates/tree_totals_lean.json |
| UniformLoading.lean | stationary_loading_kernel, saturated_current_numerator, programmed_center_numerator, square_numerator_determinant | certificates/uniform_loading_lean.json |

All three completed with exit zero, no warnings and no sorry in the pinned toolchain. They do not formalize center manifolds, Perron–Frobenius, singular perturbation, degree theory, probability, or the complete capacity theorem. No conditional Lean assembly is relabeled as the full source theorem.

## Exact finite certificates

- certificates/symmetric_pilot.json: 14 rational intertwining checks, n=2,3.
- certificates/finite_memory.json: rational source, two sink Lyapunov inequalities and explicit probability bounds.
- certificates/pole_bound.json: exact parameter-dependent Descartes certificate for the selected square.
- certificates/loading_rank.json: exact positive loading kernel and rank-seven three-site design.
- certificates/cube_four_sinks.json and cube_four_sinks_replay.json: four exact root intervals and integer interval Lyapunov checks for the full 31-dimensional source.
- certificates/cube_memory_bound.json and cube_integer_preparations.json: common four-label operating threshold, noise/readout intervals and actual integer preparations.
- certificates/uniform_pilot.json: small exact rank checks; its normal-mode values are floating diagnostics only.

The IEEE-double spectra in cube_many_poles.json are explicitly rejected for stability inference because the fast/slow scale separation is too severe. The 65-digit spectra guided the exact certificates but are not themselves proofs. Negative discriminants in tree_root_pilot.json, rather than small complex parts in floating roots, refute the tree real-rootedness hypothesis.

AGC checkpoint files are freshness and scope diagnostics. They are never theorem evidence. The canonical source spec remains proof-neutral and was not rewritten to manufacture a closed authority graph. Local tasks and root statuses use the proof paths above.
