#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Render this library's bounded native doc-gen4 inventory as Markdown.

Adapted for Smooth by Lattice from the accepted finite-etale renderer at
source d0d6b47943a8dd8e7a42a76ebdc5adb53ce21409. The earlier markup adapter
is adapted from Anchor's original Formal Frontier ideal-completion recipe.
This is not a Lean parser or proof certifier.
See docs/README.md for native generation, trust and parentless-tree limits.
"""
import argparse
import hashlib
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import re
import subprocess
from urllib.parse import urlsplit

TOOL = "97d4ecdfc8e09e7f511724c25e303d448de6a3db"
MODULES = (
    "SmoothRegularity.Conormal",
    "SmoothRegularity.AlgClosed",
    "SmoothRegularity.CenteredPresentation",
    "SmoothRegularity.CotangentRelations",
    "SmoothRegularity.CotangentDimension",
    "SmoothRegularity.CotangentRelationTransport",
    "SmoothRegularity.LocalizedCotangentComplex",
    "SmoothRegularity.RelationJacobian",
    "SmoothRegularity.QuotientRelationJacobian",
    "SmoothRegularity.KrullDimension",
    "SmoothRegularity.StandardSmooth",
    "SmoothRegularity.SmoothAt",
    "SmoothRegularity.SmoothLocus",
    "SmoothRegularity.Dedekind",
    "SmoothRegularity.AffineDedekind",
    "SmoothRegularity",
    "SmoothRegularityTest.PublicAPI",
)
INPUTS = tuple(m.replace(".", "/") + ".lean" for m in MODULES) + (
    "lean-toolchain", "lakefile.toml", "lake-manifest.json")
MANIFEST = "docs/native-input.json"
# No missing-doc exception is assumed before inspecting Smooth's native output.
UNDOCUMENTED = set()
KINDS = {"def": {"def", "noncomputable def", "abbrev"},
         "theorem": {"theorem"}, "structure": {"structure"}, "ctor": {"constructor"}}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode()


def read_file(root, relative):
    path = Path(relative)
    require(not path.is_absolute() and ".." not in path.parts, "unsafe input path")
    current = root
    require(not current.is_symlink(), "symlink input root")
    for part in path.parts:
        current = current / part
        require(not current.is_symlink(), "symlink input: " + relative)
    require(current.is_file(), "missing regular input: " + relative)
    return current.read_bytes()


def git(root, args, data=None):
    env = dict(os.environ, LC_ALL="C", GIT_NO_LAZY_FETCH="1")
    # Do not let a caller silently select another repository/index.
    for key in list(env):
        if key.startswith("GIT_") and key not in {"GIT_NO_LAZY_FETCH"}:
            env.pop(key)
    return subprocess.run(["git", "--no-replace-objects", "-C", str(root), *args], input=data,
                          capture_output=True, env=env, timeout=30)


def bind_sources(root, manifest, manifest_raw, source_only=False):
    revision = manifest["analyzed_source_revision"]
    require(re.fullmatch(r"[0-9a-f]{40}", revision) is not None, "full source revision required")
    require(manifest["docgen_revision"] == TOOL and manifest["modules"] == list(MODULES),
            "tool/module inventory differs")
    require(set(manifest["inputs"]) == set(INPUTS), "source/pin inventory differs")
    sources = {p: read_file(root, p) for p in INPUTS}
    require({p: digest(raw) for p, raw in sources.items()} == manifest["inputs"],
            "source/pin content differs")
    # No unaccounted-for Lean module may hide outside the selected seventeen.
    actual = set()
    for directory, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = [d for d in dirs if d not in {".git", ".lake"}]
        require(not any((Path(directory) / d).is_symlink() for d in dirs),
                "symlink directory in source tree")
        actual.update(str((Path(directory) / f).relative_to(root))
                      for f in files if f.endswith(".lean"))
    require(actual == {p for p in INPUTS if p.endswith(".lean")}, "Lean module inventory differs")
    probe = git(root, ["rev-parse", "--show-toplevel"])
    if probe.returncode:
        require(source_only and not os.path.lexists(root / ".git") and
                probe.returncode == 128 and b"not a git repository" in probe.stderr,
                "repository error (not explicit source-only tree)")
        return sources, "explicit-source-only-content-continuity"
    require(Path(probe.stdout.decode().strip()).resolve() == root.resolve(),
            "different enclosing Git repository")
    kind = git(root, ["cat-file", "--batch-check"], (revision + "\n").encode())
    require(kind.returncode == 0, "Git object query failed")
    line = kind.stdout.decode().strip().split()
    if line == [revision, "missing"]:
        committed = git(root, ["show", "HEAD:" + MANIFEST])
        require(committed.returncode == 0 and committed.stdout == manifest_raw,
                "missing history requires exact committed manifest")
        return sources, "missing-historical-object-content-continuity"
    require(len(line) == 3 and line[0] == revision and line[1] == "commit",
            "historical object is not a commit")
    tree = git(root, ["rev-parse", revision + "^{tree}"])
    require(tree.returncode == 0 and tree.stdout.decode().strip() == manifest["analyzed_source_tree"],
            "historical Git tree differs")
    for path, raw in sources.items():
        old = git(root, ["show", revision + ":" + path])
        require(old.returncode == 0 and old.stdout == raw,
                "historical Git source differs: " + path)
    return sources, "historical-git-bytes-matched"


class Header(HTMLParser):
    """Discard native markup, retaining all text including hidden implicit binders."""

    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack, self.text, self.kinds, self.names = [], [], [], []
        self.feed(value)
        self.close()
        require(not self.stack, "unclosed native header")

    def handle_starttag(self, tag, attrs):
        require(tag in {"div", "span", "a"}, "unexpected native header tag")
        require(not any(k.startswith("on") for k, _ in attrs), "active header attribute")
        attrs = dict(attrs)
        classes = set(attrs.get("class", "").split())
        if tag == "div" and "decl_type" in classes:
            self.text.append(" ")
        self.stack.append((tag, classes))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag, "unbalanced native header")
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), "text outside native header")
        self.text.append(value)
        if any("decl_kind" in classes for _, classes in self.stack):
            self.kinds.append(value)
        if any("decl_name" in classes for _, classes in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError("unexpected header comment")

    def handle_decl(self, _):
        raise ValueError("unexpected header declaration")

    def handle_pi(self, _):
        raise ValueError("unexpected header processing instruction")

    def rendered(self):
        return " ".join("".join(self.text).split())


def decode_records(native, manifest):
    require(set(manifest["native_records"]) == set(MODULES), "native inventory differs")
    require(native.is_dir() and not native.is_symlink(), "native directory is not regular")
    expected = {"declaration-data-" + m + ".bmp" for m in MODULES}
    actual = {p.name for p in native.iterdir() if p.name.startswith("declaration-data-")}
    require(actual == expected, "native declaration-file inventory differs")
    records = {}
    for module in MODULES:
        raw = read_file(native, "declaration-data-" + module + ".bmp")
        require(digest(raw) == manifest["native_records"][module]["sha256"],
                "native bytes differ: " + module)
        records[module] = json.loads(raw)
    return records


def render(records, manifest, sources):
    require(set(records) == set(MODULES), "native module set differs")
    revision = manifest["analyzed_source_revision"]
    lines = ["# Generated API reference", "",
             "Native doc-gen4 display entries from all seventeen shipped Lean modules.",
             "Import `SmoothRegularity` for the library API; `SmoothRegularityTest.PublicAPI`",
             "contains checked private clients. Private helpers and some generated",
             "declarations are not displayed by doc-gen4; this is not a full proof census.", "",
             "Signatures retain all implicit binders, but are native display signatures,",
             "not complete source declarations with bodies. Short names and universe",
             "variables have the source module's namespace/import context. Source links",
             "refer to the same checkout. See [generation and scope](README.md) and",
             "[content manifest](api-manifest.json).", ""]
    seen, rows = set(), []
    for module in MODULES:
        value = records[module]
        require(value["name"] == module, "native module name differs")
        expected = manifest["native_records"][module]["entries"]
        found = {}
        module_rows = []
        path = module.replace(".", "/") + ".lean"
        for row in value["declarations"]:
            info = row["info"]
            name, kind = info["name"], info["kind"]
            require(name not in seen and expected.get(name) == kind, "unexpected/duplicate name or kind")
            require(re.fullmatch(r"[A-Za-z0-9_'.]+", name) is not None, "unsupported declaration name")
            link = urlsplit(info["sourceLink"])
            require(link.scheme == "https" and link.netloc == "github.com" and not link.query and
                    link.path == "/FormalFrontier/smooth-regularity/blob/" + revision + "/" + path,
                    "native source URL differs")
            fragment = re.fullmatch(r"L([0-9]+)-L([0-9]+)", link.fragment)
            require(fragment is not None and type(info["line"]) is int, "invalid source lines")
            start, end = map(int, fragment.groups())
            require(start == info["line"] and 0 < start <= end <= len(sources[path].splitlines()),
                    "out-of-range source lines")
            require(info["docLink"] == "./" + module.replace(".", "/") + ".html#" + name,
                    "native self link differs")
            header = Header(row["header"])
            require("".join(header.names) == name and "".join(header.kinds) in KINDS[kind],
                    "native header identity differs")
            text, doc = header.rendered(), info["doc"].strip()
            require("```" not in text and "```" not in doc, "unsupported Markdown fence")
            require(bool(doc) or (name in UNDOCUMENTED and kind == "ctor"), "missing docstring")
            if not doc:
                doc = "Generated structure constructor; see the parent structure and its fields."
            seen.add(name)
            found[name] = kind
            module_rows.append(dict(name=name, kind=kind, header=text, doc=doc,
                                    path=path, start=start, end=end))
        require(found == expected, "missing native entry")
        module_rows.sort(key=lambda row: (row["start"], row["name"]))
        lines += ["## " + module, ""]
        if not module_rows:
            lines += ["No native display entries (aggregate import or private examples).", ""]
        for row in module_rows:
            lines += ["### " + row["name"], "", "```lean", row["header"], "```", "",
                      row["doc"], "", f"[Source](../{path}#L{row['start']}-L{row['end']}).", ""]
        rows.extend(module_rows)
    api = "\n".join(lines).encode()
    output = dict(format=1, analyzed_source_revision=revision, docgen_revision=TOOL,
                  native_input_sha256=digest(encoded(manifest)),
                  inputs=manifest["inputs"], modules=list(MODULES),
                  display_entries=[{k: r[k] for k in ("name", "kind", "path", "start", "end")}
                                   for r in rows],
                  api_sha256=digest(api), proof_certification=False, release_acceptance=False)
    return api, encoded(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-data", type=Path, required=True,
                        help="native fromDb doc-data directory for the bound run")
    parser.add_argument("--check", action="store_true", help="compare outputs without writing")
    parser.add_argument("--source-only", action="store_true",
                        help="explicitly allow a source archive with no Git repository")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    raw = read_file(root, MANIFEST)
    manifest = json.loads(raw)
    require(raw == encoded(manifest), "noncanonical input manifest")
    sources, binding = bind_sources(root, manifest, raw, args.source_only)
    records = decode_records(args.native_data, manifest)
    api, output = render(records, manifest, sources)
    for name, data in (("docs/API.md", api), ("docs/api-manifest.json", output)):
        if args.check:
            require(read_file(root, name) == data, "generated output differs: " + name)
        else:
            target = root / name
            require(not target.is_symlink(), "symlink output")
            target.write_bytes(data)
    print(json.dumps(dict(status="matched" if args.check else "generated", binding=binding,
                          entries=sum(len(v["declarations"]) for v in records.values()),
                          api_sha256=digest(api), release_acceptance=False)))


if __name__ == "__main__":
    main()
