# Scientific examples

[Research overview](../README.md) · [Full catalogue](../CATALOGUE.md)

These small Python examples use exact rational arithmetic and existing public-paper companions. Python 3.11 or later and its standard library are sufficient. Run from the repository root:

```sh
python -B Examples/fresh_conversion.py
python -B Examples/phosphorylation_equilibria.py
python -B -m unittest discover -s Examples -p "test_*.py" -v
```

| Example | Scientific question | Public source and scope |
|---|---|---|
| [Fresh conversion](fresh_conversion.py) | How much fresh material must a two-window product record contain after accounting for retained inventory and reserve? | [P062 paper and notes](../Formal/papers/P062-fresh-microbial-conversion/README.md), [original calculator](../Formal/papers/P062-fresh-microbial-conversion/manuscript/companion/calculator.py). Reuses the source's synthetic observations and shows positive, unresolved, threshold-boundary and incompatible outcomes. The certificate is conditional on the declared material model and calibration; it does not establish viability or future function. |
| [Phosphorylation equilibria](phosphorylation_equilibria.py) | Can one mass-action compatibility class contain 2n − 1 distinct positive equilibria? | [P079 notes](../Formal/papers/P079-phosphorylation-stable-state-capacity/README.md), [P080 notes](../Formal/papers/P080-phosphorylation-sharp-steady-state-bound/README.md), [original exact toolkit](../Formal/papers/P079-phosphorylation-stable-state-capacity/manuscript/phos_sharp.py). For n = 3, constructs five equilibria and checks the full vector field and all conserved totals. This finite example does not prove the general stability-capacity theorem. |

The wrappers import these source modules directly and print JSON without writing reports or changing manuscript data. In a sparse checkout, include the linked source modules. [Tests](test_examples.py) check the material threshold boundary, incompatible observations, positivity, distinct equilibria, exact mass-action residuals and conservation away from equilibrium for n = 1 through 4.

The original companion code and these wrappers are covered by [Apache-2.0](../LICENSE), as described in [Licensing](../RIGHTS.md). Attribute the paper ID, title and repository revision using the [citation guidance](../CITATION.md), and retain existing source notices. The wrappers are introductory adaptations; the scientific formulas and model assumptions come from the linked public manuscripts. Their computations illustrate finite instances and do not replace formal or conventional proofs.
