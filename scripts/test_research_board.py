#!/usr/bin/env python3
"""Fail-closed registry/derived-doc unit tests; Python stdlib only."""
import copy
from collections import Counter
import json
from pathlib import Path
import unittest

import research_board as rb


class BoardRegistryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(rb.REGISTRY.read_text(encoding="utf-8"))
        cls.evidence = rb.validate(cls.data)

    def test_expected_gate_counts(self):
        self.assertEqual(len(self.data["gates"]), 10)
        self.assertEqual(len(self.evidence), 14)
        stats = Counter(x["status"] for x in self.data["gates"])
        self.assertEqual(stats["passed"], 0)
        self.assertEqual(stats["sample_verified"], 2)
        self.assertEqual(stats["partial"], 4)
        self.assertEqual(stats["open"], 4)

    def test_derived_docs_are_exact(self):
        generated = (
            rb.board_text(self.data, self.evidence),
            rb.context_text(self.data),
            rb.cards_text(self.data, self.evidence)
        )
        for path, content in zip(rb.OUTPUTS, generated):
            with self.subTest(path=path.name):
                self.assertEqual(path.read_text(encoding="utf-8"), content)

    def test_retrieval_cards_are_rag_ready(self):
        cards = [json.loads(line) for line in rb.cards_text(self.data, self.evidence).splitlines()]
        self.assertEqual([x["id"] for x in cards], [f"G{i:02d}" for i in range(1, 11)])
        for card in cards:
            self.assertTrue(card["content"])
            self.assertTrue(card["source_paths"])
            self.assertTrue(card["evidence_ids"])
            self.assertIn("acceptance:", card["content"])
            self.assertIn("blockers:", card["content"])

    def test_exactly_one_source_of_truth(self):
        self.assertEqual([g["slug"] for g in self.data["gates"]],
                         [f"G{i:02d}" for i in range(1, 11)])
        self.assertTrue(all(g["closure"] is None for g in self.data["gates"]))

    def test_missing_file_is_rejected(self):
        d = copy.deepcopy(self.data)
        d["evidence"][0]["path"] = "docs/this_file_must_not_exist.md"
        with self.assertRaises(AssertionError):
            rb.validate(d)

    def test_false_pass_without_closure_is_rejected(self):
        d = copy.deepcopy(self.data)
        d["gates"][0]["status"] = "passed"
        with self.assertRaises(AssertionError):
            rb.validate(d)

    def test_dependency_cycle_is_rejected(self):
        d = copy.deepcopy(self.data)
        d["gates"][0]["depends_on"] = [5]
        with self.assertRaises(AssertionError):
            rb.validate(d)

    def test_sample_without_source_runtime_is_rejected(self):
        d = copy.deepcopy(self.data)
        g = d["gates"][1]
        g["evidence_ids"] = ["EV-010"]
        with self.assertRaises(AssertionError):
            rb.validate(d)

    def test_original_aftercode_query(self):
        found = rb.search_gates(self.data, self.evidence, "afterCode", top=10)
        self.assertIn("G04", [g["slug"] for _, g in found])
        self.assertIn("G01", [g["slug"] for _, g in found])

    def test_resource_model_query(self):
        found = rb.search_gates(self.data, self.evidence, "TM2", top=10)
        self.assertIn("G09", [g["slug"] for _, g in found])


if __name__ == "__main__":
    unittest.main()
