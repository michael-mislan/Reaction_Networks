# Overlap-corrected Kauffman RAF emergence — final handoff

Date: 2026-09-01

## Result landed

The warning-free Lean root is
`OverlapCorrectedRAF.correctedEmergenceResolution` in
`proofs/OverlapCorrectedRAF/CorrectedEmergenceResolution.lean`.

It joins three source-faithful conclusions.

1. **Exact finite RAF probability.** On the literal repository molecule type
   `Molecule n` and reversible-channel quotient `RepositoryChannel n`, the
   catalogue is now derived rather than assumed: it contains every nonempty
   food-generated reversible support. Lean proves that its activation union is
   exactly `exists S, IsRevRAF (repositoryCRS n t) C S`. Two nested
   inclusion--exclusion layers then give the literal event probability. The
   fixed-`Q` law is the cardinality of actual RAF configurations of total size
   `Q`, divided by `choose (|X_n||J_n|) Q`; the Bernoulli law is the sum of
   their product weights.
2. **Literal gateway necessity.** Every RAF in `repositoryCRS n t` contains a
   catalysed reversible seed reaction. For binary food horizon two, the source
   gateway quotient has exactly 34 channels.
3. **Corrected negative asymptotic resolution.** Define the actual RAF
   probability by the exhaustive repository catalogue at
   `p_n=f_n/|RepositoryChannel n|`. Lean derives—rather than assumes—that
   this probability is nonnegative and dominated by the literal gateway
   event. If `f_n=o(n)`, it tends to zero; quantitatively, for `n>=3`, it is
   bounded above by `272 f_n/n`. Thus the finite-size
   constant-`f` transition in the source data cannot be an asymptotically
   positive constant-`f` phase transition.

This is a corrected negative resolution, not a claim that the RAF law at the
first nondegenerate scale `f_n=lambda n` has been determined.

## Exact finite formula

For a selected family `S` of cores and channel `j`, let
`W_{k,j}` be the eligible food-closure molecules for core `k` on `j`, omitting
empty/unused requirements. The Bernoulli channel factor is

`H_{j,S}(q) = sum_{T subseteq {W_{k,j}:k in S}} (-1)^|T| q^|union T|`.

The selected-core intersection probability is

`P(intersection_{k in S} E_k) = product_j H_{j,S}(1-p)`.

Therefore

`P(RAF) = sum_{nonempty S subseteq cores} (-1)^(|S|+1)
          product_j H_{j,S}(1-p)`.

For fixed total catalysis `Q`, the local subset-counting factor is

`G_{j,S}(z) = sum_T (-1)^|T| (1+z)^(|X|-|union T|)`.

The exact numerator is the degree-`Q` coefficient of the outer
inclusion--exclusion sum of `product_j G_{j,S}(z)`.

## Why these formulas are actual RAF probabilities

The completion audit found that the earlier algebraic formulas were not, by
themselves, semantic probability theorems. The repaired proof supplies every
missing bridge:

1. `fibreHitConfigurations` is the finite family of actual molecule subsets
   hitting every requested set. `localFixedQHitPolynomial` is proved equal to
   its ordinary cardinality-generating polynomial.
2. `jointFibreHitConfigurations` is a dependent product with one subset for
   each channel. Its polynomial counts total catalytic-coordinate cardinality,
   and its Bernoulli mass is the product of the local masses.
3. `catalogueFibreHitConfigurations` is the actual union of singleton support
   events. Outer inclusion--exclusion is proved equal to its generating
   polynomial and to its Bernoulli mass.
4. `repositoryCoreSupports n t` enumerates all nonempty food-generated source
   supports. For such a support, the finite core (food plus all support
   reactants and products) equals the set of molecules reachable at some
   closure step. Consequently, hitting its core on every support channel is
   equivalent to `IsRevRAF`.

The source-specialized conclusions are
`repository_rafFixedQProbability_eq_actual_raf_ratio` and
`repository_rafBernoulliProbability_eq_actual_raf_mass`.

The final missing bridge is now also source-specialized. Every actual RAF
configuration contains a catalysed seed channel. These seed channels inject
into the exact 34-element binary-food gateway catalogue, and their diagonal
open event has probability
`1-(1-p)^(|Molecule n|*|repositorySeedChannels n 2|)`. This proves
`repositoryRAFBernoulliProbability_le_gateway` without an event-containment
assumption supplied by the caller.

## The central overlap insight

Pairwise overlap data are not sufficient. Two compiled three-core fixtures,

- `{{0,1},{0,2},{0,3}}`, and
- `{{0,1},{0,2},{1,2}}`,

have the same member sizes (all 2) and the same distinct pair-intersection
sizes (all 1). Their complete union sizes are 4 and 3, however, and their
channel hit probabilities are

- `1 - 3q^2 + 3q^3 - q^4`, and
- `1 - 3q^2 + 2q^3`.

They differ by `q^3-q^4`. Hence a pair-corrected scalar theory cannot be exact;
the sufficient statistic is the full channel-indexed closure-union trace.

## Nonoverlap recovery

`Nonoverlap.lean` constructs genuinely coordinate-disjoint core blocks using
dedicated channels `(core, fibreLabel)`. It proves, rather than assumes, that
all selected-core intersections factor. The exact overlap law then collapses
to

`1 - product_k (1 - (1 - (1-p)^w_k)^m)`,

which is the source independent-core expression term by term. This identifies
precisely what the published nonoverlap formula assumes and how overlap
corrects it.

## Source and numerical checks

- The source reaction quotient was reconstructed exactly. The literal
  repository has 18 reversible channels at `n=3` and 34 food-gateway channels
  at binary food horizon two.
- All 111 rows of the source `raf_results.csv` were preserved and overlaid with
  the exact gateway curve.
- The source `single_solutions.json` was preserved verbatim and audited. Its 96
  objects are catalyst witnesses on exactly 34 reversible singleton gateway
  channels, not 96 independent reaction-support cores.
- The exact gateway curve under `f_n=lambda n` approaches
  `1-exp(-34 lambda)` numerically. At `lambda=.03`, it moves from about
  `0.78484` at `n=6` to `0.65108` at `n=64`, against the candidate gateway
  limit `0.639405`. This is a gateway result only, not an RAF-limit theorem.
- At the published finite transition points the gateway is nearly always open;
  for example, the recorded `n=6, f≈1.3158` RAF frequency is `0.84`, while the
  gateway probability is about `0.9999869`. Thus the gateway explains the
  asymptotic impossibility of constant `f`, but not the shape of the observed
  finite transition.
- The pairwise-insufficiency fixture was exhaustively kernel evaluated with
  `native_decide`, avoiding a large catalysis search.

Numerical assumptions were kept explicit: binary words of length at most `n`,
fixed food horizon two for the 34-channel gateway, the displayed-reaction
quotient used by the public repository, molecule--reversible-channel random
coordinates, and Bernoulli parameter `p=f/|J_n|`.

## Strict Lean receipts

All listed files compiled with Lean 4.30.0, `-DwarningAsError=true`, exit code
zero, and no `sorry`.

| Module | Source SHA-256 | Artifact SHA-256 |
|---|---|---|
| `FiniteCoreEvent.lean` | `26fc298751074a6c7f8621070d22f157f561e7aae8647f8487c2943c20beb650` | `11f37a76d37493dfc9ba4c780f8768526d0392beafbd540af8d1b52118e82061` |
| `OneCoreProbability.lean` | `79e686431875662cc723c606e8a6420c5b41fdefd3b5f9763e93d6ab65e9eeac` | `da916a9ab52c2bf4d90524825976e562a8790c16d2775d4f92d305dc7bf2d2d2` |
| `ChannelHit.lean` | `906f940960d0578a0289c1e92d16d9fabf91f3061cc31ec121669ce94bc42e6d` | `7c7c1c35b40a3057731eaa022ce65ea1727a17125d602544d44e1a4c8d8a4655` |
| `TriplePairwiseFailure.lean` | `9622c13de8d246fb7354099666d47dc8d553f0bb8d1d5b7c25c42b6e8703f8a8` | `40fd1d100a89eb1544b886242085f0dc02d53c91fa12d35c3c9447f3181f9897` |
| `FinitePartition.lean` | `a3c94dced502d88cb612b0cc079e56764290e2cf09c604ae003e466dde2e5768` | `21113c5713af01174f7d453f902d0a78995864d6557332ed897077fe64a95f62` |
| `Nonoverlap.lean` | `3bd660e9ccd9d6882b67354b9c11b0a11775245ab09e32e11b34093c324e643b` | `42b28a1d9f013ecb3114c5d1d9d5434d2187ff86c5844d6c7c300782d9ff29fe` |
| `ActualGatewayDock.lean` | `7c22a10632f2201ab67e03293b2593614f9172fba6a197760b42b4a819781fa3` | `827f33ad5ccff87a5ab07620ad5189056bbd92c3183e1ffe495bf18488a9a9ac` |
| `SublinearCatalysis.lean` | `ec241b57f7766fee591ada3b7435dc25fd23990994c85c7cdd589d444d9c7e32` | `dd94a0946dfaf8ca4fe4df98b18039e5ac04a67039a10332f9c9007b317df2d8` |
| `SemanticCounting.lean` | `d091c8ceca281272e4c6f3fa80bda8ee88f7d7afbf2563135795964b10e06bd1` | `0105b89a98eb287a74b9b032cbf41aa198626104aa70fa74c3b19d1d8fac2493` |
| `RepositorySemanticCounting.lean` | `4929e5fe8f5d8318cf870462cffc68ccc58ff8adedde542e1bc1fd733d8f801c` | `83d27e083680a59ee26e47f183a4d74c1ecd45ef4504c227d002a38527c8811b` |
| `CorrectedEmergenceResolution.lean` | `7aa9018c0c15aadbfa959cdd91eb1df4db5846161c25f9064b1ee2a384a928f0` | `27ec5bbe0e46db17d7313255a4e6cc617fc7941b2246914df1348af1c942f8bb` |

Reproduction command, from the repository root:

`python scripts/verify_proof.py proofs/OverlapCorrectedRAF/CorrectedEmergenceResolution.lean`

## Failed routes and lessons

- Treating the 96 source witness objects as independent cores overcounts: they
  collapse to 34 reversible singleton supports.
- Pairwise overlap summaries lose triple-union information exactly.
- A constant-`f` positive limiting transition contradicts the finite gateway
  obstruction.
- Local Lean failures were all representation issues (unused strict simp
  arguments, dependent-channel witnesses, concrete `Finset.card`
  normalization, polynomial-map distribution, integer scalar signs, product
  orientation, and powerset empty-term bookkeeping); none invalidated a
  mathematical route.
- Large brute-force catalysis enumeration was unnecessary for the critical
  path. Small exact censuses and the four-coordinate triple witness supplied
  the discriminators before formalization.
- The actual gateway dock initially failed at a symbolic finite-product
  rewrite. The diagnostic showed no mathematical failure: replacing brittle
  `Finset.prod_subset` argument inference with `Fintype.prod_subset` closed the
  diagonal factorization and reduced subsequent strict builds to about 34
  seconds.

## Scope and nonclaims

- The generic finite interface still accepts a catalogue, but the terminal
  theorem no longer assumes one: the source adapter finitely enumerates every
  nonempty food-generated support and proves that its union is exactly RAF
  existence. This is mathematically exhaustive, though not intended as a fast
  large-instance enumerator.
- The root does not claim a positive RAF limit at `f_n=lambda n`, a transition
  width, a Poisson law, or connected-cluster decay. Those remain follow-on
  questions (`H2b`) rather than assumptions hidden in the theorem.
- The proved asymptotic endpoint is the exact negative statement for every
  sublinear scale, including fixed `f`.
- The asymptotic endpoint is about the actual exhaustive repository RAF
  probability; no arbitrary numerical probability sequence or assumed
  gateway containment remains in the root theorem.
- Fixed-`Q` and Bernoulli laws are both retained; no unproved
  equivalence-of-ensembles replacement is used.

## AGC assessment

AGC was useful as a discipline and scope controller. It consistently retained
the canonical red node, forced checkpoints after failed proof routes, and
required hash-bound publication refreshes before frontier changes. Its
mathematical route extraction was occasionally distracted by older ledger
lines and then supplied stale local advice, but this never altered theorem
content. On the critical path it was most valuable for preventing premature
promotion of the conditional nonoverlap theorem and for recognizing the exact
negative replacement theorem as the admissible `OKR-APPROX` exit. During the
semantic repair it repeatedly returned the correct local counting cut; because
its advice is ledger-content-bound, it continued to show that action until the
successful semantic receipts were recorded here and in the ledger. Most
importantly, the final completion audit reopened the conditional root and AGC
focused the proof on the actual-event gateway dock; this prevented a false
terminal declaration. The final hash-bound checkpoint at authority
`sha256:9a614662f5242c7a181248ed7f47249f964ac27ccbf7f439c51a556df9deb697`
returned `CURRENT`, `TERMINAL_NO_OPEN_CUT`, and an empty minimal cut.
