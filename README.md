# Reaction networks

Mathematical papers, scientific code and formal proofs on autocatalytic networks, reaction dynamics, chemical inheritance and biochemical observation.

[Full paper catalogue](CATALOGUE.md) · [Browse topics](TAGS.md) · [Scientific examples](Examples/README.md)

## Selected results

These entry points address explicit literature questions or connect reaction structure to dynamics and useful operation. Links lead to the papers and their evidence scope.

| Question | Result and scope | Read |
|---|---|---|
| How small can an autocatalytic network be? | No constant-factor polynomial-time approximation of the minimum RAF exists for the stated finite-CRS encoding unless P = NP. | [P001: minimum RAF](Formal/papers/P001-min-raf-inapproximability/README.md) |
| Does linear catalysis produce a sharp RAF threshold? | Every finite positive linear intensity has a limiting RAF probability strictly between zero and one in the specified reversible binary-polymer models, replacing the proposed step law. | [P002](Formal/papers/P002-critical-window/README.md), [P036](Formal/papers/P036-channel-quotient-emergence/README.md) |
| Which families can be realized as RAFs? | Same-ground RAF families are exactly intersections of antimatroids with digraph support families. | [P005: realizability](Formal/papers/P005-raf-realizability/README.md) |
| Does gross stoichiometry bound optimal affinity? | An exact reversible two-species counterexample has exp(A*) = 7/4 < 2. The response-profile capacity gives a replacement under stated hypotheses. | [P004: optimal affinity](Formal/papers/P004-optimal-affinity/README.md) |
| Can sequential distributive phosphorylation oscillate? | An attracting Hopf family exists for every n ≥ 3 in the literal mass-action system. The formal existential construction and finite-amplitude numerical examples have distinct scopes. | [P064: phosphorylation oscillations](Formal/papers/P064-phosphorylation-oscillations/README.md) |
| How can stability under diagonal scaling be decided? | A PARTITION reduction establishes weak coNP-hardness of D-stability; a critical-point criterion characterizes it in every dimension. Numerical decision tools and generic finiteness arguments have separate scope. | [P086: hardness](Formal/papers/P086-deciding-d-stability-conp-hard/README.md), [P087: criterion](Formal/papers/P087-d-stability-contact-critical-points/README.md) |
| Does autocatalytic structure ensure repeated output? | Finite-molecule operating guarantees follow withdrawal, recovery, output and supply on one finite-horizon stochastic law under explicit operating conditions. | [P043: repeated harvesting](Formal/papers/P043-finite-molecule-harvesting/README.md) |

For measurement and biological inference, [P063: How to design an assay](Formal/papers/P063-assay-design/README.md) is a perspective connecting eight companion case studies. Its formal references belong to those companions; the examples are model results.

## Theory

Theory and Applications are parallel, overlapping ways to browse. Each artifact has one location; tags connect it to other subjects.

[Structure](Theory/Structural/README.md) · [Algorithms](Theory/Algorithms/README.md) · [Kinetics](Theory/Kinetics/README.md) · [Thermodynamics](Theory/Thermodynamics/README.md) · [Production](Theory/Production/README.md) · [Inheritance](Theory/Inheritance/README.md) · [Memory](Theory/Memory/README.md) · [Persistence](Theory/Persistence/README.md) · [Evolution](Theory/Evolution/README.md) · [Emergence](Theory/Emergence/README.md)

[D-stability](Theory/D-Stability/README.md) is a related mathematical strand. The [theory guide](Theory/README.md) explains the categories.

## Applications

[Phosphorylation](Applications/Phosphorylation/README.md) · [Assays](Applications/Assays/README.md) · [Cell Memory](Applications/Cell-Memory/README.md) · [Metabolic and Redox Function](Applications/Metabolic-and-Redox-Function/README.md) · [Chemical Computation](Applications/Chemical-Computation/README.md) · [Origin of Life](Applications/Origin-of-Life/README.md)

The [applications guide](Applications/README.md) connects model questions to domains. [Scientific examples](Examples/README.md) provide small exact-arithmetic calculations with links to their public sources.

## Literature problems and resolutions

The [literature guide](LITERATURE.md) records conjectures, questions, resolutions and remaining qualifications, with paper and proof links.

## All papers

The [full catalogue](CATALOGUE.md#all-papers) lists every public paper by stable ID. The [topic index](TAGS.md) cross-links subjects; [catalogue.json](catalogue.json) provides the same discovery information for scripts and agents.

## Proofs and supporting material

[Formal proofs](Formal/README.md) include Lean sources, a pinned build environment and per-paper claim maps. Formal statements, conventional arguments, computational evidence and inherited tools have different scopes: consult the [verification notes](Formal/VERIFICATION.md), [research notes](RESEARCH_NOTES.md) and [errata](ERRATA.md).

## Reuse

Proofs and software are available under [Apache-2.0](LICENSE); papers and explanatory material under [CC BY 4.0](LICENSE-CC-BY-4.0.txt), subject to existing third-party notices. See [licensing](RIGHTS.md) and [citation guidance](CITATION.md).
