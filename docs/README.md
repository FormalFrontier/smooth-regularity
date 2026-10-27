# API documentation

[API.md](API.md) is a generated, searchable Markdown reference with two explicit
signature sources. Its fourteen Conormal entries are extracted from the current
source headers and docstrings, including shared hypotheses, universes and
namespace context. They cover the ten first-order/formally-étale declarations
and the four split-residue declarations over commutative base rings. The other
22 entries retain native doc-gen4 display signatures from the older
[published source snapshot](#bound-inputs-and-reproduction).

This is not a census of the current library. The historical native input has
148 raw declarations and no display entries for `SmoothRegularityTest.PublicAPI`.
The concrete theorem `MvPolynomial.isRegularRing_fin_two_rat` in that test module
is outside that native snapshot, as are the polynomial and dual-number
nonvanishing clients.

The [Artinian signature and boundary guide](Artinian.md) documents the two
Artinian equivalences separately. Neither the Artinian library module nor its
clients are included in this generated reference.

The root [README](../README.md) covers headline results, installation, build and
lint checks, ordinary-import examples and the conormal evaluation API migration.

| Module | Displayed entries |
| --- | ---: |
| `SmoothRegularity.Conormal` | 14 (source headers) |
| `SmoothRegularity.AlgClosed` | 3 |
| `SmoothRegularity.CenteredPresentation` | 3 |
| `SmoothRegularity.CotangentRelations` | 1 |
| `SmoothRegularity.CotangentDimension` | 1 |
| `SmoothRegularity.CotangentRelationTransport` | 1 |
| `SmoothRegularity.LocalizedCotangentComplex` | 3 |
| `SmoothRegularity.RelationJacobian` | 1 |
| `SmoothRegularity.QuotientRelationJacobian` | 1 |
| `SmoothRegularity.KrullDimension` | 1 |
| `SmoothRegularity.StandardSmooth` | 1 |
| `SmoothRegularity.SmoothAt` | 1 |
| `SmoothRegularity.SmoothLocus` | 1 |
| `SmoothRegularity.Dedekind` | 3 |
| `SmoothRegularity.AffineDedekind` | 1 |
| `SmoothRegularity` | 0 |
| `SmoothRegularityTest.PublicAPI` | 0 |

In the historical snapshot, all 26 original display entries have native source
docstrings; there is no missing-docstring exception. The underlying 148-entry raw declaration inventory
comprises 26 displayed entries, 19 authored private helpers, 6 persistent private clients,
95 generated private declarations and 2 generated public declarations.
The two undisplayed public entries are
`Ideal.residueFieldAlgEquivOfIsAlgClosed.congr_simp` and
`LinearMap.extendScalarsOfSurjective.congr_simp`. They are generated simp support,
not missing authored API documentation. The root aggregate and test module have
no native display entries in this snapshot. These docs are not a complete
public/private/generated proof census, and generation is not a proof audit.

The historical renderer retains implicit binders, including typeclass hypotheses,
while stripping native HTML markup. Native pretty-printing may elide proof terms
as `⋯`. The Conormal extractor instead preserves the source declaration header,
namespace, universes and shared variables verbatim. Both kinds are signatures,
not independently compilable declarations with bodies or a proof audit. Every
entry links to its source; historical entries retain their older line locators.

## Bound inputs and reproduction

[native-input.json](native-input.json) retains the original analyzed-source
revision and binds its seventeen Lean files, toolchain and both Lake
pin/configuration files. The bound snapshot's source and pin bytes match the
[published release snapshot](https://github.com/FormalFrontier/smooth-regularity/tree/9766c97ed58e7782bd209414242a476034d6355d).
The manifest records each raw native-record SHA256,
the exact display name/kind inventory, executable and generation-receipt hashes,
and doc-gen4 revision `97d4ecdfc8e09e7f511724c25e303d448de6a3db`.
[api-manifest.json](api-manifest.json) binds the rendered Markdown. Its
`historical_native` field retains the original native input bindings for the
22 unchanged display entries. Its separate `source_signatures` field binds the
current Conormal source hash, complete fourteen-entry name/signature/docstring
inventory, contexts and line locators. This source-text update is not a new
native doc-gen4 run. The manifests' `release_acceptance: false` and
`proof_certification: false` distinguish documentation from mathematical proof
and publication evidence.

To check or refresh the Conormal signatures from this checkout:

```sh
python3 scripts/update_conormal_api.py --check
python3 scripts/update_conormal_api.py
```

The bounded extractor refuses an unexpected declaration inventory or symbolic
input path. It needs only Python 3.10+ and does not execute Lean, Git, a loader
or any declaration body. It leaves the remaining historical entries unchanged.

To reconstruct the original 26-entry native reference, use the published source
snapshot above in a separate directory with the matching retained native `fromDb`
data. In that historical checkout, run:

```sh
python3 scripts/generate_api.py --native-data /path/to/doc-data --check
python3 scripts/test_generate_api.py --native-data /path/to/doc-data
```

The historical renderer binds all original source and pin bytes, so it is not
a generator for the changed current project. Its 27 tests also run with
`python3 -O` and `python3 -OO`; its refusal checks do not rely on assertions.

To regenerate native data for the original 26-entry reference, use the same
published historical snapshot in its separate checkout. The following recipe
is scoped entirely to that seventeen-module project, whose source and pin
bytes are required by the historical renderer; it does not generate the
current source-signature overlay. Use `update_conormal_api.py` above for that
overlay.

In the historical checkout, first successfully fetch `lake exe cache get`,
then run `lake --wfail build`. Build doc-gen4 at the exact revision above in a
separate checkout using its own unchanged manifest/toolchain. Its pinned Lean
`v4.34.0-rc2` matches the historical project. The tool is not a library
dependency; no project pin change is needed. Use its executable in the
historical project's `lake env`, with new empty output directories. Run
`single` sequentially for all seventeen modules in the manifest's order:

```sh
mkdir native-api rendered-api
native_revision=$(python3 -c 'import json; print(json.load(open("docs/native-input.json"))["analyzed_source_revision"])')
lake env /path/to/doc-gen4 single --build native-api \
  SmoothRegularity.Conormal api.db \
  "https://github.com/FormalFrontier/smooth-regularity/blob/${native_revision}/SmoothRegularity/Conormal.lean"
# Repeat single for each remaining manifest module with its matching .lean path.
lake env /path/to/doc-gen4 bibPrepass --build rendered-api --none
lake env /path/to/doc-gen4 fromDb --build rendered-api \
  --manifest rendered-api/manifest.json native-api/api.db
python3 scripts/generate_api.py --native-data rendered-api/doc-data --check
```

The URL passed to `single` is the historical native source **label** required
by the manifest and renderer, not a promise that its revision is obtainable on
GitHub. Use the published snapshot linked above or the rendered API's relative
links to browse the same source bytes. Replacing the label with the public
release revision changes native records and fails the existing hash/source-label
checks, even when Lean bytes agree. This example is **not** a new generation
receipt. Fresh output
can differ with the native environment; investigate any byte mismatch and review
a new binding, never replace hashes merely to suppress it. Changed mathematical
source or pins require affected verification and, for claims of new native
display output, new native generation. Source-header extraction is recorded
separately and never relabels the original native records.
The native loader executes initializers and uses `debug.skipKernelTC`; it is
documentation machinery, not an independent kernel proof checker. Imported compiled
dependencies remain a trust boundary even when project source and outputs are bound.

## Parentless release snapshots and source archives

If the analyzed commit is present, the renderer checks its exact source/pin bytes.
A present-object mismatch, a noncommit object or any Git command/repository error
is fatal. Only an explicit `cat-file` missing-object response permits content
continuity through the exact committed `native-input.json` and matching bytes.
This supports parentless snapshots without importing development history. For
the published snapshot, matched content does not change the original
analyzed-source field in either machine-readable manifest.

For an explicit source archive with no Git repository, add `--source-only`.
It checks the same manifest and bytes, but cannot authenticate that manifest's
commit. Invalid `.git` metadata or a different enclosing repository is not an
archive. Both fallbacks establish content continuity only, not historical object
existence or independent native-run provenance. A new candidate still needs
appropriate independent evidence; a file cannot contain its own final commit ID
without circularity.

## Provenance and licensing

Lattice adapted the Python renderer and tests from the Formal Frontier
finite-étale-algebras renderer, which extends Anchor's original ideal-completion
markup recipe. The original work and later Smooth adaptation retain distinct
credit under Apache-2.0.

Documentation text comes from this library's original docstrings, with display
signatures produced by doc-gen4. The external tool and its contributors retain
their own credit and terms. No tool implementation, fonts, CSS, JavaScript,
external dependency documentation, source book, cache, native website or compiled
binary is bundled in this documentation. These explanations and native display
signatures do not substitute for checked Lean proofs or a transitive axiom audit.
