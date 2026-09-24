# Theorem-to-evidence concordance

All declaration names below have prefix `ThermoCoreCompatibility.Hypergraph.`.
Proof directory: `proofs/ThermoCoreCompatibility/Hypergraph/`.
Strict compilation does not itself establish novelty, chemical interpretation, or algorithmic complexity.

| Paper claim | Declaration / artifact | Evidence level |
|---|---|---|
| Theorem 1: PACs, unbounded-domain incompatibility, every proper subfamily, physical directions, common complex assignment and individual bounds | `Shortcut.unbounded_monomial_order`, UnboundedMonomialOrder.lean | Compiled source theorem |
| Response interval and composition | `PairResponse.interval_iff`, `composition_identity`, `composition_lt`, `path_incompatible`, PairResponseBounds.lean | Compiled universal real/Nat lemmas |
| Literal signed PAC integration and every deletion | `Shortcut.arbitrary_order`, `source_proper`, `rank_edge`, ShortcutPathSource.lean; `PairAssembly.source_isPAC`, GradedSource.lean | Compiled source theorems |
| Exactly n distinct chemical cores/channels, incidence cycle, molecularity, acyclicity | Explicit architecture and counting in Section 3 | Conventional finite combinatorial proof; source uses finite indexed types |
| Fixed-order-test corollary | Theorem 1 plus n > k | Conventional deduction |
| Lemma 2 and graded source correctness | `Graded.edge_productive`, `graded_common_state`; `PairAssembly.graded_source_compatible` | Compiled |
| Theorem 2, including singleton boxes and reconstruction | `private_interval_box_iff`, `privateTriangle_box_iff_polynomial`; `FanData.sourceCompatible_univariate_iff` | Compiled exact source equivalence |
| Lemma 3 negative margin | `MonomialTriple.negative_margin`, `source_coordinate_margin` | Compiled; formal tau is any common lower bound, so applies to the finite minimum |
| Theorem 3, seven factors and ten endpoints: full incompatibility and every deletion | `MonomialTriple.simultaneous_perturbation`, TripleRobustSource.lean | Compiled source theorem under `Near`; gains fixed |
| Current/production perturbation control and stable source witnesses | `MonomialTriple.current_perturbation`, `production_perturbation`, `residual_error`, `stable_source_witness` | Compiled |
| Theorem 3 additional perturbed direction and complex witnesses, induced complex box bounds | Explicit witnesses and coefficient estimate in Section 5; review_exact.py | Conventional universal perturbation proof plus exact rational witness checks; not included in simultaneous_perturbation's type |
| Positivity/nonemptiness of all perturbed factors and boxes | Reference values and rho in Section 5 | Conventional immediate inequalities; formal FanData includes these validity conditions |
| Theorem 4 recognition/complexity and bit bounds | Section 6; review_exact.py `graded` | Conventional algorithm proof + exact implementation checks; algorithm is not Lean-verified |
| Food adapter | Section 7 | Conventional mass-balance/current calculation, not a change to the effective source predicates |
| Original package | `tcch_resolution : TCCHResolution`, Main.lean | Original strict root retained unchanged |
| Strengthened package | `reviewed_resolution : ReviewedResolution`, Reviewed.lean | Strict root composing original + both new source statements |

## Important semantic details

- Shortcut `Compatible` explicitly asks for source productivity in the fixed species box. For gain-two pairs productivity implies both displayed currents positive, as proved by the response inequalities; no direction condition is missing mathematically.
- Fan `SourceCompatible` includes retained source production and current signs explicitly. Omitted motifs do not retain requirements; global boxes remain fixed.
- `LinearComplexCompatible` alone has no box fields. The shortcut root includes separate singleton and doubled-complex bounds on the same `complexValues` function.
- The harmless unused value at `2X_L` is `a_L - 7 delta/4`, rather than `a_L^2` suggested in the review. It is still in [81/100,1], enters no current, and lets one formula cover every nonzero vertex. The paper matches the implementation.
- Triple `Near` quantifies independent absolute deviations bounded by 1/1000000, with one shared factor. It does not identify the full cube with the older two-endpoint parameter window.
- The generic Sturm routine and discovery experiments are not used to claim a verified decision algorithm. They are omitted from the main proof path.

Source and receipt hashes are in `data/evidence_manifest.json`. Strict root interfaces record the standard axioms, compiler exit status, and frozen toolchain/manifest.
