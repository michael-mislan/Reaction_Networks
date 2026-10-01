# SPDX-License-Identifier: Apache-2.0
"""P062: reuse the public two-pool certificate on synthetic observations.

Source: Formal/papers/P062-fresh-microbial-conversion/manuscript/companion/calculator.py
The public paper and its proof notes define the model and evidence scope.
This wrapper changes no source formula and writes no files.
"""
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "Formal/papers/P062-fresh-microbial-conversion/manuscript/companion/calculator.py"


def load_calculator():
    spec = importlib.util.spec_from_file_location("public_p062_calculator", SOURCE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def demo():
    calculator = load_calculator()
    cases = calculator.examples()
    return {name: calculator.calculate(cases[name])
            for name in ("positive", "unresolved", "boundary", "incompatible")}


if __name__ == "__main__":
    print(json.dumps(demo(), indent=2))
