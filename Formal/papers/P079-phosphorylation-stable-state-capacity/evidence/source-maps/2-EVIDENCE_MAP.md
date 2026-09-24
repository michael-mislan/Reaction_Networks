# Evidence map

## Mathematical endpoint

H_n=C_n=n for every n>=1, in the positive literal full mass-action source and
one common compatibility class. Status GREEN-C: a complete ordinary proof.
ORDINARY_PROOF.md gives the upper bound; SPECTRAL_PROOF.md gives the new
uniform spectral lemma and attainment. PAPER_DRAFT.md assembles the source
construction and these arguments into one manuscript draft.

The full capacity theorem is **not** a Lean endpoint. The analytic bridges
remain ordinary mathematics: real-rooted coefficient inequalities, the path
maximum principle, Gershgorin, finite-dimensional spectral perturbation,
degree theory, and parameter transversality. The proof explicitly derives
the model-specific matrices and their needed inequalities. These are not
unproved red assumptions in the ordinary theorem.

## Strict compiled components

All paths below are relative to the repository root. Verification uses the
frozen mathlib environment, warning-as-error, and no `sorry`.

| Module / declarations | Exact scope | Receipt in this workspace |
|---|---|---|
| proofs/PhosphorylationStableCapacity/StructuralAlgebra.lean: coalesced_identity | Repeated-root product identity for all m | certificates/structural_algebra_verify.json |
| Same: relaxation_balance, relaxation_positive | Exact source-preserving fast-relaxation algebra and positivity | Same |
| Same: feedback_ratio_step | Monotone coefficient-ratio product implication; its real-rooted inputs are proved ordinarily | Same |
| Same: loaded_feedback_elimination | Exact elimination giving the loaded feedback functional | Same |
| Same: slow_link_charpoly | Zero final current produces exactly the polynomial factor X times the prefix characteristic polynomial | Same |
| Same: feedback_vector | Rank-one matrix acting on its positive test vector reduces to scalar gain | Same |
| Same: feedback_gain_identity, feedback_gap_positive, feedback_gain_lt_one | Closed gap formula and strict positivity for every natural n>=2, 0<v<1 | Same |
| proofs/PhosphorylationStableCapacity/KineticFreedom.lean: retune_positive, retune_equilibrium | One retuned rate list stays positive and preserves every balanced source state, using the literal inherited source definitions | certificates/kinetic_freedom_verify.json |
| proofs/PhosphorylationStableCapacity/Assembly.lean: large_r_block_certificate | Assembles the derived matrix identities and all-n gap into a strict negative-vector certificate; does not assume or claim capacity | certificates/assembly_verify.json |

Inherited count/source algebra is credited to proofs/PhosphorylationSharpness.
The verification bridge reused its pinned compiled dependency artifacts and
records their source hashes. No old compiled count theorem is relabeled as a
stability theorem. Ordinary source nondegeneracy is inherited from the prior
publication manuscript, with its derivative hypothesis supplied by splitting.

## Exact finite evidence

| Artifact | What it establishes |
|---|---|
| certificates/coalesced_preparation_replay.json | Exact rational coalesced n=2,3,4,5 simple-zero/Hurwitz-complement checks; exact standard-kinetics n=4 split pattern 0,1,0,1,0,1,0 |
| certificates/loaded_structure.json | Exact loaded matrices and proper leading minors; counterexample to all-admissible-r Metzler claim at n=4,r=100 |
| certificates/large_r_structure.json | Exact small limiting matrices, supporting the derivation rather than asserting all-n coverage |
| certificates/gain_check.json | Exact rank-one and gain identities in n=2,3,4,5; floating convergence-error diagnostics separately labeled |
| certificates/kinetic_lift.json | Exact new-kinetics full-source coalesced n=2,3 certificates |
| certificates/new_route_split.json | One common new-kinetics n=3 realization with exact Routh counts 0,1,0,1,0 |
| certificates/base_case.json | Literal n=1 equilibrium, restricted cubic and Hurwitz Routh column |

These rational calculations are conventional exact computation (GREEN-I),
not kernel-checked Routh certificates. The all-n proof does not extrapolate
from them. The floating asymptotic errors are diagnostics only.

## AGC boundary

The initial missing spec was repaired with a source-faithful new specification
and the checkpoint-supplied start action. Later checkpoint files are preserved
under certificates/agc_*.json. A CURRENT label is freshness, not proof status.
The published specification still lists the initial mathematical obligations;
protected authority was not mutated to manufacture a closed root. Local
hypothesis_graph.json records GREEN-C with actual proof paths.

The checkpoint heuristics also classified a prospective milestone table in
GUIDE.md as an authored closure claim. That is a false positive: guide
instructions are not evidence. The actual ordinary closure is SPECTRAL_PROOF.md.
Canonical publication/integration is distinct from mathematical completion.

2026-09-20T10:59:53.597450-07:00 Final declaration audit: assembled block certificate, all-n positive gap and loaded elimination passed using only propext, Classical.choice and Quot.sound. No extra mathematical axiom or sorry. Final checkpoint: certificates/agc_final.json, CURRENT / current_with_unbound_authored_route. Task score remains 64/64.
