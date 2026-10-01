# SPDX-License-Identifier: Apache-2.0
"""P079/P080: exact finite witnesses from the public sharpness toolkit.

Source: Formal/papers/P079-phosphorylation-stable-state-capacity/manuscript/phos_sharp.py
See also P080's manuscript/phos_sharp.py and the per-paper proof notes.
This wrapper illustrates equilibrium construction, not an all-n stability proof.
"""
from fractions import Fraction as Q
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "Formal/papers/P079-phosphorylation-stable-state-capacity/manuscript/phos_sharp.py"


def load_toolkit():
    spec = importlib.util.spec_from_file_location("public_phos_sharp", SOURCE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def construct(n=3):
    if isinstance(n, bool) or not isinstance(n, int) or not 1 <= n <= 4:
        raise ValueError("This introductory exact-arithmetic demo supports 1 <= n <= 4")
    toolkit = load_toolkit()
    roots = [Q(j + 2) for j in range(2 * n - 1)]
    enzyme_ratio = Q((4 * n * n - 1) // 8 + 1)
    record = toolkit.build(roots, enzyme_ratio)
    if not record["positive"]:
        raise ArithmeticError("The public construction did not give positive coefficients")
    return toolkit, record


def demo(n=3):
    toolkit, record = construct(n)
    return {
        "paper_ids": ["P079", "P080"],
        "scope": "finite exact equilibrium witnesses; no general stability conclusion",
        "sites": n,
        "expected_equilibria": 2 * n - 1,
        "enzyme_and_substrate_totals": [str(v) for v in record["totals"]],
        "positive_rates": all(v > 0 for row in record["rates"] for v in row),
        "equilibria": [
            {"enzyme_ratio": str(state["u"]),
             "all_species_positive": all(v > 0 for v in state["z"]),
             "zero_mass_action_residual": all(v == 0 for v in toolkit.vector_field(record["rates"], state["z"])),
             "same_conserved_totals": toolkit.totals(state["z"]) == record["totals"]}
            for state in record["states"]
        ]
    }


if __name__ == "__main__":
    print(json.dumps(demo(), indent=2))
