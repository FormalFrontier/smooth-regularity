# API documentation

[API.md](API.md) is a generated, searchable Markdown reference for the native
doc-gen4 display entries in all seventeen shipped Lean modules. See the root
[mathematical overview and ordinary-import examples](../README.md) for scope,
build-cost guidance and the conormal evaluation API migration.

| Module | Native display entries |
| --- | ---: |
| `SmoothRegularity.Conormal` | 4 |
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

All 26 display entries have native source docstrings; there is no missing-docstring
exception. They join the separate accepted 148-entry raw declaration inventory:
26 displayed entries, 19 authored private helpers, 6 persistent private clients,
95 generated private declarations and 2 generated public declarations.
The two undisplayed public entries are
`Ideal.residueFieldAlgEquivOfIsAlgClosed.congr_simp` and
`LinearMap.extendScalarsOfSurjective.congr_simp`. They are generated simp support,
not missing authored API documentation. The root aggregate and private-client
module have no native display entries. These docs are not a complete
public/private/generated proof census, and generation is not a proof audit.

The renderer retains implicit binders, including typeclass hypotheses, while
stripping native HTML markup. Signatures use the source module's namespace,
notation and import context. Native pretty-printing may elide proof terms as
`⋯`; these are display signatures, not independently compilable declarations
with bodies. Every entry links to its source lines in the same checkout.

## Exact inputs and reproduction

[native-input.json](native-input.json) binds analyzed source revision
`0c22cc0c557137465bc0927e301a4ee1fd7a34e0`, its seventeen Lean files, toolchain and
both Lake pin/configuration files. It records each raw native-record SHA256,
the exact display name/kind inventory, executable and generation-receipt hashes,
and doc-gen4 revision `97d4ecdfc8e09e7f511724c25e303d448de6a3db`.
[api-manifest.json](api-manifest.json) binds the rendered Markdown and input
manifest. These are content bindings, not signatures or attestations that a
native command ran. Exact final artifact review and release acceptance remain
separate from these generated records.

To reproduce the Markdown from the retained native `fromDb` data directory:

```sh
python3 scripts/generate_api.py --native-data /path/to/doc-data --check
python3 scripts/test_generate_api.py --native-data /path/to/doc-data
```

Omit `--check` to regenerate the two output files. Python 3.10+ and Git are
required; no third-party Python packages or Lean build are needed for rendering.
The 27 tests also run with `python3 -O` and `python3 -OO`; production refusal
checks do not rely on Python assertions.

For fresh native generation, build this project in its pinned environment,
first successfully fetching `lake exe cache get`, then `lake --wfail build`.
Build doc-gen4 at the exact revision above in a separate checkout using its own
unchanged manifest/toolchain. Its pinned Lean `v4.34.0-rc2` matches this project's.
The tool is not a library dependency; no project pin change is needed. Use its
executable in this project's `lake env`, with new empty output directories.
Run `single` sequentially for all seventeen modules in the manifest's order:

```sh
mkdir native-api rendered-api
lake env /path/to/doc-gen4 single --build native-api \
  SmoothRegularity.Conormal api.db \
  https://github.com/FormalFrontier/smooth-regularity/blob/0c22cc0c557137465bc0927e301a4ee1fd7a34e0/SmoothRegularity/Conormal.lean
# Repeat single for each remaining manifest module with its matching .lean path.
lake env /path/to/doc-gen4 bibPrepass --build rendered-api --none
lake env /path/to/doc-gen4 fromDb --build rendered-api \
  --manifest rendered-api/manifest.json native-api/api.db
python3 scripts/generate_api.py --native-data rendered-api/doc-data --check
```

These native source URLs are generation labels, not an assertion that the
development commit exists on GitHub. Only relative source links are rendered.
Fresh output can differ with the native environment; investigate any byte mismatch
and review a new binding, never replace hashes merely to suppress it. Changed
mathematical source or pins require new native generation and affected verification.
The native loader executes initializers and uses `debug.skipKernelTC`; it is
documentation machinery, not an independent kernel proof checker. Imported compiled
dependencies remain a trust boundary even when project source and outputs are bound.

## Parentless release snapshots and source archives

If the analyzed commit is present, the renderer checks its exact source/pin bytes.
A present-object mismatch, a noncommit object or any Git command/repository error
is fatal. Only an explicit `cat-file` missing-object response permits content
continuity through the exact committed `native-input.json` and matching bytes.
This supports parentless snapshots without importing development history.

For an explicit source archive with no Git repository, add `--source-only`.
It checks the same manifest and bytes, but cannot authenticate that manifest's
commit. Invalid `.git` metadata or a different enclosing repository is not an
archive. Both fallbacks establish content continuity only, not historical object
existence or independent native-run provenance. Final review must bind the actual
candidate and authenticate generation evidence separately; this file cannot
contain its own final commit ID without circularity.

## Provenance and licensing

Lattice adapted the Python renderer and tests from accepted finite-etale-algebras
revision `d0d6b47943a8dd8e7a42a76ebdc5adb53ce21409`, which extends Anchor's original
Formal Frontier ideal-completion markup recipe. The original project work and
later Smooth adaptation retain their distinct credit under Apache-2.0.

Documentation text comes from this library's original docstrings, with display
signatures produced by doc-gen4. The external tool and its contributors retain
their own credit and terms. No tool implementation, fonts, CSS, JavaScript,
external dependency documentation, source book, cache, native website or compiled
binary is bundled in this production documentation. This provenance statement
does not substitute for final independent rights review or release acceptance.
