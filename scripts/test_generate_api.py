#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Smooth adaptation of the accepted finite-etale renderer tests (d0d6b479).
Requires independently retained Smooth native data; no finite display-count transfer.
"""
import argparse
import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
import generate_api as g

ROOT = Path(__file__).resolve().parent.parent
MANIFEST_RAW = (ROOT / g.MANIFEST).read_bytes()
MANIFEST = json.loads(MANIFEST_RAW)
SOURCES = {p: (ROOT / p).read_bytes() for p in g.INPUTS}
RECORDS = None
NATIVE_DATA = None


class RendererTests(unittest.TestCase):
    def fixture(self, repository=False):
        temp = tempfile.TemporaryDirectory(prefix="smooth-doc-test-")
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        for path, raw in SOURCES.items():
            target = root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
        (root / "docs").mkdir()
        (root / g.MANIFEST).write_bytes(MANIFEST_RAW)
        if repository:
            self.command(root, "init", "-q")
            self.command(root, "config", "user.name", "Documentation Test")
            self.command(root, "config", "user.email", "documentation-test@example.invalid")
            self.commit(root)
        return root

    def command(self, root, *args):
        result = g.git(root, list(args))
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        return result.stdout.decode().strip()

    def commit(self, root):
        self.command(root, "add", ".")
        self.command(root, "commit", "-qm", "fixture inputs")
        return self.command(root, "rev-parse", "HEAD")

    def bind(self, root, manifest=MANIFEST, source_only=False):
        return g.bind_sources(root, manifest, g.encoded(manifest), source_only)

    def bad_record(self, change):
        records = copy.deepcopy(RECORDS)
        row = records[g.MODULES[0]]["declarations"][0]
        change(records, row)
        with self.assertRaises((ValueError, KeyError)):
            g.render(records, MANIFEST, SOURCES)

    def test_native_golden_outputs(self):
        api, manifest = g.render(RECORDS, MANIFEST, SOURCES)
        self.assertEqual(api, (ROOT / "docs/API.md").read_bytes())
        self.assertEqual(manifest, (ROOT / "docs/api-manifest.json").read_bytes())
        self.assertEqual(len(json.loads(manifest)["display_entries"]),
                         sum(len(r["entries"]) for r in MANIFEST["native_records"].values()))
        self.assertGreater(len(json.loads(manifest)["display_entries"]), 0)
        self.assertNotIn(b"https://github.com/FormalFrontier", api)
        self.assertNotIn(b"forgejo", api.lower())
        self.assertIn(b"[Field K]", api)
        self.assertIn(b"[IsLocalRing R]", api)
        self.assertIn(b"cotangentSpaceEquivTensorKaehlerOfSection_apply_toCotangent", api)

    def test_full_implicit_text(self):
        header = g.Header('<div><span class="decl_kind">def</span> '
                          '<span class="decl_name">x</span><span class="impl_arg">'
                          ' {K : Type u} [Field K]</span><div class="decl_type">K → K</div></div>')
        self.assertEqual(header.rendered(), "def x {K : Type u} [Field K] K → K")

    def test_bad_markup(self):
        for value in ('<script>bad</script>', '<div>', '<div></span>',
                      '<div onclick="x">y</div>', '<!-- comment -->', '<?bad?>'):
            with self.subTest(value=value), self.assertRaises(ValueError):
                g.Header(value)

    def test_missing_entry(self):
        self.bad_record(lambda records, _: records[g.MODULES[0]]["declarations"].pop())

    def test_duplicate_entry(self):
        self.bad_record(lambda records, row: records[g.MODULES[0]]["declarations"].append(row))

    def test_wrong_module(self):
        self.bad_record(lambda records, _: records[g.MODULES[0]].update(name="Wrong"))

    def test_wrong_kind(self):
        self.bad_record(lambda _, row: row["info"].update(
            kind="theorem" if row["info"]["kind"] == "def" else "def"))

    def test_missing_doc(self):
        self.bad_record(lambda _, row: row["info"].update(doc=""))

    def test_wrong_url_revision(self):
        self.bad_record(lambda _, row: row["info"].update(
            sourceLink=row["info"]["sourceLink"].replace(MANIFEST["analyzed_source_revision"], "0" * 40)))

    def test_wrong_source_fragment(self):
        self.bad_record(lambda _, row: row["info"].update(
            sourceLink=row["info"]["sourceLink"].split("#")[0] + "#L0-L999999"))

    def test_wrong_doc_link(self):
        self.bad_record(lambda _, row: row["info"].update(docLink="https://example.invalid"))

    def test_wrong_header_name(self):
        def change(_, row):
            # Native names contain nested spans. Replacing the first full name
            # can touch only an href, which the renderer intentionally discards.
            before = row["header"]
            row["header"] = before.replace('<span class="decl_name">',
                '<span class="decl_name">wrong_', 1)
            self.assertNotEqual(row["header"], before)
            self.assertNotEqual("".join(g.Header(row["header"]).names), row["info"]["name"])
        self.bad_record(change)

    def test_fence(self):
        self.bad_record(lambda _, row: row["info"].update(doc="```unclosed"))

    def test_native_byte_hash(self):
        temp = tempfile.TemporaryDirectory(prefix="smooth-native-test-")
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        for m in g.MODULES:
            (root / ("declaration-data-" + m + ".bmp")).write_bytes(b"{}")
        with self.assertRaisesRegex(ValueError, "native bytes"):
            g.decode_records(root, MANIFEST)

    def native_fixture(self):
        temp = tempfile.TemporaryDirectory(prefix="smooth-native-inventory-")
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        for module in g.MODULES:
            name = "declaration-data-" + module + ".bmp"
            shutil.copyfile(NATIVE_DATA / name, root / name)
        self.assertEqual(g.decode_records(root, MANIFEST), RECORDS)
        return root

    def test_extra_native_record(self):
        root = self.native_fixture()
        (root / "declaration-data-Extra.Module.bmp").write_bytes(b"{}")
        with self.assertRaisesRegex(ValueError, "declaration-file inventory differs"):
            g.decode_records(root, MANIFEST)

    def test_missing_native_record(self):
        root = self.native_fixture()
        (root / ("declaration-data-" + g.MODULES[0] + ".bmp")).unlink()
        with self.assertRaisesRegex(ValueError, "declaration-file inventory differs"):
            g.decode_records(root, MANIFEST)

    def test_source_only_requires_flag(self):
        root = self.fixture()
        with self.assertRaisesRegex(ValueError, "source-only"):
            self.bind(root)
        self.assertEqual(self.bind(root, source_only=True)[1], "explicit-source-only-content-continuity")

    def test_parentless_committed_manifest(self):
        root = self.fixture(repository=True)
        self.assertEqual(self.bind(root)[1], "missing-historical-object-content-continuity")

    def test_parentless_dirty_manifest(self):
        root = self.fixture(repository=True)
        manifest = copy.deepcopy(MANIFEST)
        manifest["extra"] = "uncommitted"
        (root / g.MANIFEST).write_bytes(g.encoded(manifest))
        with self.assertRaisesRegex(ValueError, "exact committed manifest"):
            self.bind(root, manifest)

    def test_present_history(self):
        root = self.fixture(repository=True)
        manifest = copy.deepcopy(MANIFEST)
        manifest["analyzed_source_revision"] = self.command(root, "rev-parse", "HEAD")
        manifest["analyzed_source_tree"] = self.command(root, "rev-parse", "HEAD^{tree}")
        self.assertEqual(self.bind(root, manifest)[1], "historical-git-bytes-matched")

    def test_present_history_mismatch_never_falls_back(self):
        root = self.fixture(repository=True)
        manifest = copy.deepcopy(MANIFEST)
        manifest["analyzed_source_revision"] = self.command(root, "rev-parse", "HEAD")
        manifest["analyzed_source_tree"] = self.command(root, "rev-parse", "HEAD^{tree}")
        path = g.INPUTS[0]
        raw = SOURCES[path] + b"\n-- altered\n"
        (root / path).write_bytes(raw)
        manifest["inputs"][path] = g.digest(raw)
        with self.assertRaisesRegex(ValueError, "historical Git source differs"):
            self.bind(root, manifest, source_only=True)

    def test_noncommit_object_never_falls_back(self):
        root = self.fixture(repository=True)
        manifest = copy.deepcopy(MANIFEST)
        manifest["analyzed_source_revision"] = self.command(root, "rev-parse", "HEAD:" + g.INPUTS[0])
        with self.assertRaisesRegex(ValueError, "not a commit"):
            self.bind(root, manifest, source_only=True)

    def test_invalid_git_never_falls_back(self):
        root = self.fixture()
        (root / ".git").write_text("gitdir: /definitely-absent-smooth-fixture\n")
        with self.assertRaisesRegex(ValueError, "repository error"):
            self.bind(root, source_only=True)

    def test_git_query_error_never_falls_back(self):
        root = self.fixture(repository=True)
        real = g.git

        def query(*args):
            if args[1][0] == "cat-file":
                return subprocess.CompletedProcess([], 128, b"", b"fixture query failure")
            return real(*args)

        with patch.object(g, "git", query), self.assertRaisesRegex(ValueError, "query failed"):
            self.bind(root, source_only=True)

    def test_altered_input(self):
        root = self.fixture()
        (root / "lean-toolchain").write_text("wrong\n")
        with self.assertRaisesRegex(ValueError, "source/pin content differs"):
            self.bind(root, source_only=True)

    def test_extra_module(self):
        root = self.fixture()
        (root / "Extra.lean").write_text("-- not in manifest\n")
        with self.assertRaisesRegex(ValueError, "module inventory"):
            self.bind(root, source_only=True)

    def test_symlink_input(self):
        root = self.fixture()
        path = root / "lean-toolchain"
        path.unlink()
        path.symlink_to(ROOT / "lean-toolchain")
        with self.assertRaisesRegex(ValueError, "symlink input"):
            self.bind(root, source_only=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-data", type=Path, required=True)
    args = parser.parse_args()
    NATIVE_DATA = args.native_data
    RECORDS = g.decode_records(args.native_data, MANIFEST)
    result = unittest.main(argv=[__file__], exit=False)
    raise SystemExit(0 if result.result.wasSuccessful() else 1)
