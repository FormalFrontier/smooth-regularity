#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Invented-fixture checks for the bounded Conormal documentation extractor."""
import json
import unittest
from unittest.mock import patch

import update_conormal_api as api

SOURCE = """namespace Example
universe u v
variable {K : Type u} [CommRing K]
/-- Hidden helper. -/
private def hidden := 3
/-- An identity law. -/
@[simp] theorem identity (x : K) : x = x := by
  rfl
end Example
"""


class ExtractorTests(unittest.TestCase):
    def setUp(self):
        self.inventory = patch.object(api, "EXPECTED", {"Example": {"identity"}})
        self.inventory.start()
        self.addCleanup(self.inventory.stop)

    def test_context_and_private_boundary(self):
        rows = api.extract(SOURCE)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["name"], "Example.identity")
        self.assertEqual(rows[0]["universes"], "u v")
        self.assertEqual(rows[0]["variables"], "{K : Type u} [CommRing K]")
        self.assertEqual(rows[0]["doc"], "An identity law.")
        self.assertNotIn("rfl", rows[0]["signature"])

    def test_inventory_refusal(self):
        with self.assertRaises(ValueError):
            api.extract(SOURCE.replace("theorem identity", "theorem another"))
        with self.assertRaises(ValueError):
            api.extract(SOURCE.replace("@[simp] theorem", "private theorem"))

    def test_distinct_provenance_and_idempotence(self):
        old_api = b"# Original\n## SmoothRegularity.AlgClosed\nPreserve this native tail.\n"
        old_manifest = dict(format=1, api_sha256="old", inputs={"old.lean": "old-hash"},
                            display_entries=[dict(path=api.PATH, name="old-conormal"),
                                             dict(path="Other.lean", name="other")])
        output, raw = api.render(SOURCE.encode(), old_api, old_manifest)
        manifest = json.loads(raw)
        self.assertEqual(manifest["historical_native"]["inputs"], old_manifest["inputs"])
        self.assertEqual(len(manifest["historical_native"]["display_entries"]), 1)
        self.assertEqual(len(manifest["source_signatures"]["entries"]), 1)
        self.assertTrue(output.endswith(b"Preserve this native tail.\n"))
        self.assertEqual(api.render(SOURCE.encode(), output, manifest), (output, raw))
        self.assertFalse(manifest["proof_certification"])


if __name__ == "__main__":
    unittest.main()
