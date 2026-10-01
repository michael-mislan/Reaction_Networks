# SPDX-License-Identifier: Apache-2.0
"""Scientific checks for the introductory public-paper examples."""
from fractions import Fraction as Q
import unittest

from fresh_conversion import load_calculator
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
