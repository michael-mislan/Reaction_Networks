# SPDX-License-Identifier: Apache-2.0
"""Scientific checks for the introductory public-paper examples."""
from fractions import Fraction as Q
import json
from pathlib import Path
import subprocess
import sys
import unittest

from fresh_conversion import calculate, load_calculator
from phosphorylation_equilibria import construct


class FreshConversionTests(unittest.TestCase):
    def setUp(self):
        self.calculator = load_calculator()
        self.cases = self.calculator.examples()

    def test_measured_reserve_bound_and_threshold_boundary(self):
        result = self.calculator.calculate(self.cases["positive"])
        # Hand-accounted bound: .05*5.8 + 3.8 - .05*10 - .85*2 - .2.
        expected = Q(169, 100)
        self.assertEqual(Q(result["lower"]), expected)
        self.assertEqual(result["active_constraints"], ["measured_reserve"])
        self.assertEqual(result["outcome"], "certified-above")
        self.assertEqual(self.calculator.calculate(self.cases["boundary"])["outcome"], "certified-above")
        just_above = {**self.cases["positive"], "threshold": "1.690001"}
        self.assertEqual(self.calculator.calculate(just_above)["outcome"], "unresolved")

    def test_less_reserve_information_and_incompatible_upper_bound(self):
        relaxed = self.calculator.calculate(self.cases["unresolved"])
        self.assertEqual(Q(relaxed["lower"]), Q(0))
        self.assertEqual(relaxed["outcome"], "unresolved")
        self.assertEqual(self.calculator.calculate(self.cases["incompatible"])["outcome"], "incompatible")
        self.assertEqual(self.calculator.calculate(self.cases["negative_interval"])["outcome"], "incompatible")

    def test_retention_hypotheses_are_required(self):
        with self.assertRaises(ValueError):
            self.calculator.calculate({**self.cases["positive"], "e": ".95", "s": ".9"})

    def test_wrapper_exact_threshold_equality_and_nearby_cases(self):
        for threshold, expected in (
            ("1.5", "certified-at-or-above"),
            ("1.69", "certified-at-or-above"),
            ("1.690001", "unresolved"),
        ):
            with self.subTest(threshold=threshold):
                result = calculate({**self.cases["positive"], "threshold": threshold})
                self.assertEqual(result["lower"], "169/100")
                self.assertEqual(result["threshold"], str(Q(threshold)))
                self.assertEqual(result["outcome"], expected)

    def test_wrapper_upper_boundary_and_incompatible_regressions(self):
        boundary = calculate({**self.cases["boundary"], "fresh_upper": "1.69"})
        self.assertEqual(boundary["lower"], boundary["threshold"])
        self.assertEqual(boundary["upper"], boundary["threshold"])
        self.assertEqual(boundary["outcome"], "certified-at-or-above")
        for upper, expected in (("1.5", "unresolved"), ("1.499999", "certified-below")):
            with self.subTest(upper=upper):
                result = calculate({**self.cases["unresolved"], "fresh_upper": upper})
                self.assertEqual(result["outcome"], expected)
                self.assertEqual(result["threshold"], "3/2")
        for name in ("incompatible", "negative_interval"):
            with self.subTest(name=name):
                result = calculate(self.cases[name])
                self.assertEqual(result["outcome"], "incompatible")
                self.assertEqual(result["threshold"], "3/2")

    def test_cli_json_distinguishes_equality_from_positive_case(self):
        script = Path(__file__).with_name("fresh_conversion.py")
        output = subprocess.check_output([sys.executable, "-B", str(script)], text=True)
        cases = json.loads(output)
        self.assertEqual(cases["positive"]["threshold"], "3/2")
        self.assertEqual(cases["boundary"]["threshold"], "169/100")
        self.assertEqual(cases["boundary"]["lower"], cases["boundary"]["threshold"])
        self.assertGreater(Q(cases["positive"]["lower"]), Q(cases["positive"]["threshold"]))
        for name in ("positive", "boundary"):
            self.assertEqual(cases[name]["outcome"], "certified-at-or-above")
        self.assertEqual(cases["unresolved"]["outcome"], "unresolved")
        self.assertEqual(cases["incompatible"]["outcome"], "incompatible")


class PhosphorylationTests(unittest.TestCase):
    def test_distinct_positive_equilibria_in_one_compatibility_class(self):
        for n in range(1, 5):
            with self.subTest(n=n):
                toolkit, record = construct(n)
                self.assertEqual(len(record["states"]), 2 * n - 1)
                self.assertEqual(len({tuple(state["z"]) for state in record["states"]}), 2 * n - 1)
                self.assertTrue(all(v > 0 for row in record["rates"] for v in row))
                for state in record["states"]:
                    self.assertTrue(all(v > 0 for v in state["z"]))
                    self.assertTrue(all(v == 0 for v in toolkit.vector_field(record["rates"], state["z"])))
                    self.assertEqual(toolkit.totals(state["z"]), record["totals"])

    def test_conservation_away_from_equilibrium(self):
        toolkit, record = construct(3)
        perturbed = list(record["states"][0]["z"])
        perturbed[0] += Q(1, 7)
        derivative = toolkit.vector_field(record["rates"], perturbed)
        self.assertTrue(any(v != 0 for v in derivative))
        # totals() is linear, so on a derivative it gives the three conserved rates.
        self.assertEqual(toolkit.totals(derivative), (Q(0), Q(0), Q(0)))

    def test_demo_range_is_bounded(self):
        for bad in (0, 5, True, 2.5):
            with self.assertRaises(ValueError):
                construct(bad)


if __name__ == "__main__":
    unittest.main()
