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

    def test_action_queue_moves_on_to_full_preparation(self):
        board = rb.board_text(self.data, self.evidence)
        self.assertIn("G05 的完整原版准备命令单程序运行", board)
        self.assertNotIn("G04 的原版 afterCode 完整执行", board)

    def test_full_halt_evidence_does_not_close_global_gate(self):
        g04 = self.data["gates"][3]
        g05 = self.data["gates"][4]
        self.assertEqual(g04["status"], "sample_verified")
        self.assertEqual(g05["status"], "open")
        self.assertIn("EV-015", g04["evidence_ids"])
        self.assertIn("EV-016", g05["evidence_ids"])
        note = (rb.ROOT / "research/evidence/G04_AFTERCODE_HALTED_20261029.md").read_text()
        self.assertIn("290,560,512", note)
        self.assertIn("8323964865602a50b772ecb82b42d5a0d6c14e16", note)

    def test_stage5_lean_axioms_and_runtime_samples(self):
        import re
        proof = (rb.ROOT / "research/evidence/G05_FULLPREP_CERTIFICATE_AXIOMS_20261029.raw.txt").read_text()
        found = re.findall(r"'([^']+)' depends on axioms: \[([^]]+)\]", proof, re.S)
        self.assertEqual(len(found), 4)
        for name, axioms in found:
            self.assertTrue(name.startswith("IndependentFullPreparationDirectCertificate."))
            self.assertEqual({a.strip() for a in axioms.split(",")},
                {"propext","Classical.choice","Quot.sound"})
        run = (rb.ROOT / "research/evidence/G05_LAZY_ORIGINAL_OPCODE_20261029.raw.txt").read_text()
        self.assertIn("FULL_NATIVE_LAZY_SAMPLE_PASS", run)
        self.assertEqual(len(re.findall(r"^FULL_NATIVE_LAZY_SOURCE_OPCODE ",run,re.M)), 9)
        self.assertIn("FULL_NATIVE_SOURCE_LABELS=12539 entry=3",run)

    def test_expected_gate_counts(self):
        self.assertEqual(len(self.data["gates"]), 10)
        self.assertEqual(len(self.evidence), 17)
        stats = Counter(x["status"] for x in self.data["gates"])
        self.assertEqual(stats["passed"], 0)
        self.assertEqual(stats["sample_verified"], 3)
        self.assertEqual(stats["partial"], 3)
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
