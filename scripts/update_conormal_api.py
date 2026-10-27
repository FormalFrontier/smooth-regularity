#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Refresh Conormal source signatures without relabelling historical native data.

This deliberately bounded source-text extractor is not a Lean parser. It preserves
namespace, universe and shared-variable context and refuses an unexpected inventory.
It neither loads compiled code nor certifies proofs. Other modules' doc-gen4 entries
retain their original input provenance in the output manifest.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

PATH = "SmoothRegularity/Conormal.lean"
EXPECTED = {
    "Algebra.Extension": {
        "cotangentComplex_injective_of_infinitesimalSection",
        "cotangentEquivCotangentSpaceOfFormallyEtale",
        "cotangentComplex_bijective_of_formallyEtale",
        "cotangentEquivCotangentSpaceOfFormallyEtale_toLinearMap",
        "cotangentEquivCotangentSpaceOfFormallyEtale_apply_mk",
    },
    "IsLocalRing": {
        "cotangentSpaceEquivTensorKaehlerOfSection",
        "cotangentSpaceEquivTensorKaehlerOfSection_apply_toCotangent",
        "cotangentSpaceEquivTensorKaehlerOfResidueEquiv",
        "cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent",
        "cotangentSpaceEquivTensorKaehlerOfFormallyEtale",
        "cotangentSpaceEquivTensorKaehlerOfFormallyEtale_restrictScalars",
        "cotangentSpaceEquivTensorKaehlerOfFormallyEtale_apply_toCotangent",
        "cotangentSpaceEquivTensorKaehlerOfFormallyEtale_eq_ofSection",
        "cotangentSpaceEquivTensorKaehlerOfFormallyEtale_eq_ofResidueEquiv",
    },
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read(root, relative):
    path = root
    require(not path.is_symlink(), "symlink root")
    for part in Path(relative).parts:
        path = path / part
        require(not path.is_symlink(), "symlink input")
    return path.read_bytes()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def extract(source):
    """Select only documented public declarations with the supported header form."""
    rows = []
    for namespace, expected in EXPECTED.items():
        start = source.index("namespace " + namespace + "\n")
        end = source.index("end " + namespace, start)
        body = source[start:end]
        universes = re.search(r"(?m)^universe ([^\n]+)$", body).group(1)
        variables = re.search(r"(?m)^variable ([^\n]+(?:\n  [^\n]+)*)", body).group(1)
        found = set()
        for doc in re.finditer(r"/--(.*?)-/", body, re.S):
            decl = re.match(
                r"\s*((?:@\[[^\n]*\]\s*)*)(noncomputable def|def|theorem) "
                r"([A-Za-z0-9_]+)(.*?) := by(?:\n|$)", body[doc.end():], re.S)
            if decl is None:
                continue
            attrs, kind, name, tail = decl.groups()
            require(name in expected and name not in found, "unexpected public declaration: " + name)
            require("```" not in doc.group(1) + tail, "unsupported Markdown fence")
            signature = (attrs + kind + " " + name + tail).strip()
            line = source.count("\n", 0, start + doc.start()) + 1
            rows.append(dict(name=namespace + "." + name, kind="def" if "def" in kind else kind,
                             namespace=namespace, universes=universes, variables=variables,
                             signature=signature, doc=doc.group(1).strip(), path=PATH, start=line))
            found.add(name)
        require(found == expected, "missing public declarations in " + namespace)
    return rows


def render(source, previous_api, previous_manifest):
    rows = extract(source.decode())
    historical = previous_manifest.get("historical_native", previous_manifest)
    historical = {k: v for k, v in historical.items() if k != "api_sha256"}
    historical["display_entries"] = [r for r in historical["display_entries"] if r["path"] != PATH]
    tail = previous_api.decode().split("## SmoothRegularity.AlgClosed\n", 1)[1]
    lines = ["# Generated API reference", "",
             "Conormal entries below are generated from the current source declaration headers",
             "and docstrings, retaining namespace, universe and shared-variable context.",
             "The remaining 22 entries are historical native doc-gen4 display signatures,",
             "not a census of the current library. See [generation and scope](README.md)",
             "and the [content manifest](api-manifest.json) for their distinct input bindings.",
             "Neither source-text extraction nor documentation generation is a proof audit.", "",
             "Import `SmoothRegularity` for the library API. Private helpers, model proofs",
             "and generated declarations are outside this display reference.", "",
             "## SmoothRegularity.Conormal", ""]
    for row in rows:
        ns = row["namespace"]
        lines += ["### " + row["name"], "", "```lean", "namespace " + ns,
                  "universe " + row["universes"], "variable " + row["variables"],
                  row["signature"], "end " + ns, "```", "", row["doc"], "",
                  "[Source](../" + PATH + "#L" + str(row["start"]) + ").", ""]
    api = ("\n".join(lines) + "## SmoothRegularity.AlgClosed\n" + tail).encode()
    manifest = dict(format=2, api_sha256=sha(api), historical_native=historical,
                    source_signatures=dict(path=PATH, sha256=sha(source), entries=rows,
                                           generator="scripts/update_conormal_api.py"),
                    proof_certification=False, release_acceptance=False)
    return api, (json.dumps(manifest, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare without writing")
    args = parser.parse_args()
    root = Path(__file__).absolute().parent.parent
    old_api = read(root, "docs/API.md")
    old_manifest = read(root, "docs/api-manifest.json")
    api, manifest = render(read(root, PATH), old_api, json.loads(old_manifest))
    for path, data in (("docs/API.md", api), ("docs/api-manifest.json", manifest)):
        if args.check:
            require(read(root, path) == data, "generated output differs: " + path)
        else:
            require(not (root / path).is_symlink(), "symlink output")
            (root / path).write_bytes(data)
    print(json.dumps(dict(status="matched" if args.check else "generated",
                          conormal_entries=sum(map(len, EXPECTED.values())), api_sha256=sha(api))))


if __name__ == "__main__":
    main()
