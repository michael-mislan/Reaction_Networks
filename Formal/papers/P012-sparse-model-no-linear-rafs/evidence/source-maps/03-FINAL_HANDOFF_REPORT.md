# Sparse-model linear-size RAF: negative resolution

## Result and verification

The requested mathematical stopping criterion is met. A fully compiled Lean proof establishes, for every fixed food horizon t, every fixed nonnegative intensity lambda, and every real constant C,

    Pr[there exists a nonempty RAF with at most C*n channels] -> 0

as n tends to infinity in the sparse reversible split-position binary-polymer model. In particular, the proposed high-probability linear-size assertion is false in this model. The conclusion covers all catalyst ranks, not just single-catalyst or bounded-rank RAFs.

Terminal source: `proofs/SparseLinearRAF/LiteratureResolution.lean`.

Terminal declarations:

- `SparseLinearRAF.sparse_linear_raf_literature_resolution`
- `SparseLinearRAF.no_high_probability_linear_raf`

The verifier-authenticated receipt is `problem_workspaces/RAF_sparse_model_O_n/LiteratureResolution.verify.json`. It records `verified=true`, exit code 0, empty stdout and stderr, warning-as-error compilation, and elaborated interfaces for both terminal declarations. The only reported axioms are `Classical.choice`, `Quot.sound`, and `propext`; there is no `sorryAx` or additional mathematical axiom.

Terminal source SHA256: `efd35752a2a21690776a4acd17a69f7e77e3dd314d2a6adb1e5bee3d4f5c787b`.

Pinned toolchain: `leanprover/lean4:v4.30.0`. Manifest SHA256: `a8df0b606ec258561c226df89856884be433c19b49fb0a27335d69bb2b6e9fac`. The final verification, including dependency materialization and declaration export, took 120.895 seconds. Its receipt records all 48 local dependency sources and their authenticated compiled artifacts.

This is a local formal proof and research handoff, not a claim of publication or independent peer review.

## Exact source and quantifiers

The literature source reviewed was Hordijk and Steel, *Autocatalytic Sets in Polymer Networks with Variable Catalysis Distributions*, especially the model, sparse distribution, and open questions in sections 2, 3, and 7: [arXiv:1605.03919](https://arxiv.org/html/1605.03919).

Molecules are all nonempty binary words of length at most n. Food consists of all such words of length at most the fixed horizon t; the literature instance uses t=2. A channel is indexed by a product word and a split position. Its two orientations are ligation of the ordered factors and cleavage of their product. Both orientations share the channel's catalytic coordinate. Equal factors, repeated endpoint values, and different split positions are retained according to this literal source.

The source counts are

    |X_n| = 2^(n+1)-2,
    |R_n| = (n-2)*2^(n+1)+4  (n>=2).

For each molecule x, an independent activity bit has probability p_n. Conditional reaction bits have probability q_n=1/n, independently across molecule-channel coordinates and independently of activity. Catalysis is the conjunction of activity and the corresponding conditional bit. At fixed intensity lambda,

    p_n = lambda*n^2/|R_n|,
    p_n*q_n*|R_n| = lambda*n.

The formal probability space uses `activityParameter`, clamped to [0,1] to make the definition total at small n, and `channelParameter`. `activity_eq_raw_eventually` proves that this clamp disappears eventually for every nonnegative fixed lambda. Thus the limit theorem uses the exact literature normalization in its asymptotic regime. The mean-normalization equation above is the direct algebraic interpretation of these parameters; no alternative marginal-independent catalysis model is substituted.

The theorem first handles natural C in `Resolution.lean`, then arbitrary real C by comparison with its natural ceiling. The formal negation chooses epsilon=1/2 and contradicts eventual probability at least 1/2 using the zero limit. Parameters lambda and C are fixed before taking n to infinity.

## The decisive insight: divide labelled encodings by m!

The initial productive-prefix approach successfully excluded fixed catalyst ranks. Its constants, however, grew quadratically in the logarithm of the prefix count and did not resolve every logarithmic-rank window. The successful change was to count supports through dependency encodings, rather than count their ordered executions.

Let A_m be the set of m-channel supports admitting a productive program from food. A productive step is enabled in one orientation and adds at least one endpoint to the available state. A selected channel cannot be productive twice: after its first productive firing, all its endpoints are available.

Give the m distinct channels arbitrary labels. For each support choose one productive order as an existence certificate. Every input molecule can be referenced either by its food index or by one of the three endpoints of an earlier channel. There are at most f+3m references, where f is the food cardinality. A ligation instruction records two ordered references. A cleavage instruction records one product reference and a split position, with at most n choices. Thus each node has at most

    B_m = (f+3m)^2 + (f+3m)*n

possible instructions.

The encoding does not contain the productive order. Its dependency graph is acyclic, and its equations uniquely determine the labelled reaction assignment. Lean proves this uniqueness by induction on a rank certifying acyclicity. Ordered factors determine a literal channel; alternatively, the product and split position determine it. Repeated endpoint values do not compromise uniqueness.

Every support has at least m! distinct encodings, one for each arbitrary labelling. Distinct supports cannot share a valid code. This is not the false claim that every support has m! productive execution orders. The verified theorem is

    |A_m| * m! <= B_m^m.

Using the exponential-series bound m^m/m! <= exp(m), for m<=C*n the proof obtains

    |A_m| <= (D*n)^m,

where D depends only on t and C. This factorial saving is what permits the all-rank conclusion.

## From supports to the actual sparse probability

A productive support's final universe contains food and its endpoints, at most f+3m molecules. Choose k catalysts inside this finite universe. For a specified catalyst set and a specified assignment of its catalysts to the m distinct channels, the activity coordinates and conditional channel coordinates are disjoint. The exact cylinder mass is p^k*q^m. Union over assignments gives the verified bound

    Pr[specified k-set active and covering specified m channels]
      <= p^k*k^m*q^m.

This retains the shared activity dependence. Multiplying by the number of supports and catalyst subsets yields

    Pr[productive support of size m with a k-catalyst cover]
      <= |A_m|*(f+3m)^k*k^m*p^k*q^m.

For m<=C*n and q=1/n, the verified linear support count cancels the n^m factor:

    probability <= (D*k)^m * [(|X_t|+3*C*n)*p_n]^k.

For sufficiently large fixed K, all k>K satisfy `(D*k)^C <= (4/3)^k`. Independently, for sufficiently large n, the polynomial prefactor in the activity probability is dominated so that

    (|X_t|+3*C*n)*p_n <= (9/16)^n.

Consequently, uniformly over m<=C*n and k>K, the probability is at most `(3/4)^(n*k) <= (3/4)^n`. There are at most `C*n*(|X_t|+3*C*n)` size/rank pairs. Their total upper bound tends to zero.

## Why every RAF is covered

An arbitrary RAF can include channels that are not needed for productive construction. The proof extracts a saturated productive program using a subset of the original channels. Its final state contains the entire closure of the original support. Thus it contains every original reachable catalyst. All channels of the extracted support remain covered by those catalysts.

Inactive members of a catalyst cover are removed without losing coverage. If the productive subset is empty, an active catalyst must be food; that event has probability at most `|X_t|*p_n`, which tends to zero. Otherwise the extracted support has positive size no greater than the original linear budget, and the preceding support-universe bound applies.

The remaining case, catalyst rank at most fixed K, was already resolved by a separate compiled theorem. A far reachable catalyst forces a productive prefix of depth d. Such prefixes have distinct channels, a count P_d independent of ambient n, and a finite shallow universe H_d. The finite bound is

    H_d*p + choose(|X_n|,k)*P_d*k^d*p^k*q^d.

For fixed k choose d=k+1. Since `|X_n|*p_n/n -> lambda`, the second term tends to zero, and the first does too. A finite union handles k<=K. The root proof combines active food, bounded rank, and the uniform large-rank tail.

## Experiments, failures, and what they taught us

All experiments and raw results are retained in this workspace. Numerical evidence was used to select and audit routes; it was never substituted for a Lean proof.

| Experiment | Domain and result | What changed in the proof |
|---|---|---|
| `frontier_preflight.py` | Exact source at n=3..9, t=2. 196 channels at n=5; 32 productive first channels; one-step universe of 30 molecules. Ordered productive pairs stabilize at 1424 for n=8,9. | Locked the literal source. An initial incorrect n=7-to-8 saturation assertion was repaired: 16 length-four doublings first fit at n=8. |
| `parameter_preflight.py` | 315 exact rational checks at n=2..64 and lambda=0,0.1,1,10,100. All stated normalization inequalities passed. | Confirmed p's exponential decay and the extra inverse-n factor for rank one. Coarse constants often exceeded one at modest n, so they were treated only as asymptotic bounds. |
| `prefix_preflight.py` | Exact lazy prefixes through depth 3, maximum length 16. Counts 1,32,1424,84704. At depth 3: 79340 with three ligations, 5336 with two, 28 with one. No productive repeated channel. | Confirmed cleavage must be retained and that only ligations increase maximum length. A sharper orientation-count hypothesis was recorded but was not needed for the terminal proof. |
| `sparse_law_preflight.py` | Exact weighted enumeration for k,d=1..3 at p=1/3,q=1/4, up to 4096 atoms. Active coverage matched `p^k*[1-(1-q)^k]^d`. | Detected the wrong independent-edge shortcut: two same-molecule edges have mass 1/48, whereas the product of their marginals is 1/144. |
| `growing_rank_preflight.py` | Logarithmic evaluation of the proved prefix majorant over log n=20..1000 and several k/log n ratios. This was a bound diagnostic, not simulation of RAF probabilities. | Exposed the finite constant barrier of prefix counting alone. Its leading optimized coefficient approaches `alpha-1/(2 log 2)` for k~alpha log n. This directed work toward support encoding. |
| `support_encoding_preflight.py` | Exact t=2,n=6 supports through size 3. Counts 1,32,920,23780. Distinct labelled codes 1,32,1840,142680, exactly m! per support. At size 3, 17316 codes involve cleavage. All decoded correctly without the original order; no collisions. | Validated the proposed factorial fibre mechanism before formalizing it. The universal result is now compiled in SupportCounting. |

The encoding test completed in under three seconds under a 60-second process lease. The other enumerations were similarly small. No large ambient catalysis matrix, long brute-force search, or competing numerical worker was launched. Lean verification ran one job at a time because this PC was also serving other proof tasks.

There were ordinary formalization failures: unavailable or deprecated lemma names, explicit ENNReal-to-real conversion requirements, native/classical decidable-equality differences in finite images, simplifier expansion of source cardinalities, and strict-linter complaints about redundant tactics. These were repaired in place. A rank-one compilation also exceeded 600 seconds under resource contention; the successful retry was verified separately. A timeout was never treated as mathematical evidence or as a proof. Attempt receipts retain the failures.

One substantive guide correction was necessary: `Build` must require a nonempty support. Otherwise an active food molecule with empty support satisfies the proposed construction condition but supplies no nonempty RAF. The compiled equivalence includes this repair.

## Theorem and reproduction index

All proof files below are under `proofs/SparseLinearRAF/` and share the frozen `mathlib4_project/` environment.

| File | Main role |
|---|---|
| `Source.lean`, `Parameters.lean`, `SparseLaw.lean` | Literal source counts, exact eventual normalization, independent activity/channel probability space. |
| `CatalystRank.lean` | Corrected nonempty Build/RAF equivalence. |
| `TwoFrontier.lean` through `SelfConstructionLimit.lean` | Separate single-catalyst negative resolution, including cleavage. |
| `ProductiveProgram.lean`, `PrefixFamily.lean`, `PrefixCounting.lean` | Productive normalization, finite prefix family, ambient-independent counts. |
| `CoverProbability.lean`, `LowRankBound.lean`, `LowRankLimit.lean`, `BoundedRank.lean` | Actual sparse assignment law and bounded-rank zero limit. |
| `AssemblyCode.lean`, `ProgramEncoding.lean`, `SupportCounting.lean` | Deterministic acyclic encoding, arbitrary labellings, factorial count. |
| `SaturatedProgram.lean`, `RAFReduction.lean` | Productive subset extraction and exhaustive RAF event decomposition. |
| `LinearSupportCount.lean`, `SupportProbability.lean`, `GrowthBounds.lean`, `LargeRankEstimate.lean` | Linear-budget support count and uniform all-large-rank probability estimate. |
| `Resolution.lean` | All-rank zero limit for natural linear-budget constants. |
| `LiteratureResolution.lean` | Arbitrary real budget constants and explicit falsification of the positive assertion. |

From `E:\Erdos Problems`, reproduce the terminal verification with:

```powershell
& 'D:\miniconda3\python.exe' scripts/verify_proof.py proofs/SparseLinearRAF/LiteratureResolution.lean --timeout 900 --declaration SparseLinearRAF.sparse_linear_raf_literature_resolution --declaration SparseLinearRAF.no_high_probability_linear_raf --output problem_workspaces/RAF_sparse_model_O_n/LiteratureResolution.verify.json
```

The bridge enforces the Lean working directory. No dependency update, package edit, toolchain change, or generated-evidence commit was made. Small numerical scripts can be rerun with the same interpreter; the encoding test should retain its process guard:

```powershell
& 'D:\miniconda3\python.exe' scripts/process_guard.py run --timeout 60 --owner-label SLR-ENCODING -- D:\miniconda3\python.exe problem_workspaces/RAF_sparse_model_O_n/support_encoding_preflight.py
```

The final root receipt is the authoritative compiled dependency inventory. Older individual receipts may describe earlier source snapshots; do not infer that an older standalone receipt is the final dependency version. `RankOneDock.lean` and `LengthBarrier.lean` are unused exploratory drafts and are not claimed as terminal dependencies or verified deliverables.

## Scope, nonclaims, and variants

| Question or variant | Status |
|---|---|
| Literal sparse split-position model, fixed t, lambda>=0, fixed real C | Zero-probability limit proved. |
| Single-catalyst self-construction with cleavage | Separately proved to have probability tending to zero. |
| Fixed bounded catalyst rank, without a linear support restriction | Probability tends to zero. |
| Growing catalyst rank with support size <=Cn | Covered uniformly by the terminal proof. |
| Independent marginal catalysis without shared activity | Not the model proved here. |
| Quotienting ordered factors or split positions | Not silently substituted; counts can differ. |
| Intensity lambda growing with n | Not covered by the fixed-intensity theorem. |
| Optimal superlinear RAF size, such as n log n | Not established. |
| Conditional-on-RAF size theorem | No separate conditional theorem is claimed; the terminal statement is unconditional. |
| Practical finite-n threshold or optimized constants | Not supplied. The proof is asymptotic. |

## AGC and campaign accounting

The complete supplied attachment was read. The initially empty workspace was initialized, and AGC checkpoints were used at entry, structure discoveries, failed routes, stronger-theorem transitions, and the terminal gate. AGC helped enforce freshness and preserve failure diagnostics; it did not supply the factorial-encoding insight.

The final checkpoint identified unconsumed proof-neutral inputs and requested `authority reconcile-frontier`. That exact action was attempted and failed with `AGC-FRONTIER-BIND-E004: compiler emitted no current frontier authority identity`. The campaign was initialized without a frontier authority binding. This is an AGC publication/binding limitation, not a failed Lean proof. No canonical AGC graph closure or authority integration is claimed. The strict terminal declaration receipt independently establishes the mathematical result. No further mathematical work is needed to meet the user's compiled-proof criterion.

Final conservative guide score: **39/72 complete; mathematical root PASS; zero blocking mathematical red nodes**. Complete items are A01-A05; B01,B05; C01,C03-C06; D06; E01-E06; F01,F02,F06; J01-J06; K01-K06; L01-L03,L05-L06. L04's freshness/publication gate is BLOCKED by the unbound authority described above. The remaining 32 exploratory or alternate-route items were not claimed complete and were not pursued after the terminal proof settled the root. The requested stopping criterion was a compiled solution, not completion of every proposed experimental route.

`HYPOTHESIS_CYCLE_LEDGER.jsonl` is the chronological record of tested hypotheses, failures, and changes of direction. `RESEARCH_NOTES.md`, `SUPPORT_ENCODING_ROUTE.md`, and the raw experiment outputs retain the supporting research history. This report supersedes their provisional statements that the terminal theorem was pending.
