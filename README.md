# smooth-regularity

Reusable commutative-algebra and scheme-theoretic smoothness and regularity
criteria, developed as a source-independent Lean library.

Authors: Formal Frontier Agents.

## Status

The mathematical development, native-module migration and six persistent
ordinary-import clients have independent non-author agent development reviews.
Generated API documentation is available below. First-release preparation,
including remaining convention checks and exact complete-artifact documentation
and redistribution review, is in progress.
Development acceptance is not release acceptance or complete source coverage.

## Building and use

The project pins Lean `v4.34.0-rc2` and mathlib commit
`83abb3e776bdefcbc447a1e44d0debe4010039e5`; the resolved external packages are
recorded in `lake-manifest.json`. There are no other Formal Frontier library
dependencies. Install the pinned Lean toolchain with elan, then fetch the matching
precompiled cache successfully before building:

```sh
lake exe cache get
lake build
```

The default build includes the explicit-root public API clients in
`SmoothRegularityTest.PublicAPI`. To check them separately, run
`lake build SmoothRegularityTest.PublicAPI` or `lake build SmoothRegularityTest`.

The [generated API reference](docs/API.md) preserves the native display signatures
and docstrings of all 26 displayed entries. Its [generation guide](docs/README.md)
explains the seventeen-module inventory, omitted private/generated declarations,
reproduction commands and why documentation generation is not a proof audit.

### Expected build cost

For the reviewed 17-module source set, a 2026-09-26 agent-container run used the
pinned environment above and one Lean worker (`LEAN_NUM_THREADS=1`). Its successful
matching-cache step took about 86 seconds. A focused `StandardSmooth` build then
took 6 seconds, followed by 32 seconds for the remaining default build: about
124 seconds in total for those sequential commands, excluding checkout and gaps
between commands. The default-build figure is **not** a standalone cold-build
measurement: the focused module was already compiled. A subsequent explicit
public-client target check took 2 seconds with those outputs already present.
These are measured examples, not timing guarantees for other machines or networks;
an uncached mathlib source build was neither required nor measured.

The focused/default commands' start/end container-memory samples were about
11.8 GiB. Those samples include the entire worker and resident caches, not an
isolated compiler peak or a demonstrated minimum requirement. The review used a
15 GiB memory bound; allow comparable headroom as a planning estimate, and adjust
for the machine, cache state and concurrent work. All timings use whole-second
timestamps. Separate proof audits and native documentation generation have
different workloads and are not included in this build-cost example. This is
proof-oriented library infrastructure, not a promise about the asymptotic cost
of an extracted executable.

### Ordinary imports and evaluation API

The root import for downstream users is:

```lean
import SmoothRegularity
```

Individual modules may be imported directly. For example,
`SmoothRegularity.Conormal` exposes the local-algebra cotangent equivalences;
`SmoothRegularity.Dedekind` provides the ring-theoretic consequences, and
`SmoothRegularity.AffineDedekind` adds the scheme-level adapter. The root re-exports
the complete library. A build is not by itself an all-declaration axiom audit,
separate stored-proof check, semantic review or release certificate.

For an ordinary `import SmoothRegularity`, the conormal equivalences have public
evaluation theorems on classes of the maximal ideal:
`IsLocalRing.cotangentSpaceEquivTensorKaehlerOfSection_apply_toCotangent s hs x`
and
`IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent e x`.
Both identify the result with `1 ⊗ₜ[R] KaehlerDifferential.D K R x.1`.
For instance, when proving the latter equality, use
`exact IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent e x`;
the section case uses the corresponding theorem with `s hs x`. Existing external
proofs that used `rfl` for this evaluation must migrate to these theorems:
definitional reduction through the private implementation is **not** promised
under an ordinary import. The old ordinary-import `rfl` proof is known to fail
after the module migration. Independent development review accepted this
propositional API and its documented breaking migration; that is not an assertion
of backward compatibility or release acceptance.

### Explicit lint checks and known convention departures

After the successful cache fetch and build above, the supported direct-file lint
check uses the pinned mathlib standard set, header and docstring linters:

```sh
for source in SmoothRegularity.lean SmoothRegularity/*.lean SmoothRegularityTest/*.lean; do
  lake env lean -Dlinter.mathlibStandardSet=true -Dlinter.style.header=true \
    -Dlinter.style.docString=true "$source" || exit
done
```

The reviewed source retains 45 header-parser warnings across fifteen implementation
modules: truthful SPDX/agent-author headers do not match mathlib's copyright-line
template. It also retains one `privateModule` warning for the six intentionally
private persistent clients. These are explicit convention departures awaiting final
artifact disposition, not warning-free lint passes; no copyright owner is invented
and no dummy public test declaration or blanket lint suppression is used. The five
former StandardSmooth proof-style warnings were repaired and independently checked.
This repository does not configure a root `lake check-lint` driver; that command's
failure is not a supported lint result. Successful compilation alone is not a lint,
axiom-audit or release certificate.

## Mathematical scope

| Modules | Provided interface and hypotheses |
| --- | --- |
| `Conormal`, `AlgClosed` | Identify the cotangent space with residue-field base change of Kähler differentials for a local field-algebra with a split residue map and formally unramified residue extension; specialize to a supplied residue-field equivalence and to closed points of finite-type algebras over algebraically closed fields. |
| `CenteredPresentation`, `CotangentRelations`, `CotangentDimension` | Choose finite presentations centred at a closed point, select a minimal relation family spanning the residue-field cotangent kernel, and prove the corresponding rank-nullity identity. Relation selection itself works over an arbitrary commutative base at any prime. |
| `CotangentRelationTransport`, `LocalizedCotangentComplex` | Transport selected relations to literal local cotangent classes and to the localized extension's cotangent-complex map, with explicit compatibility of the primes and residue fields. |
| `RelationJacobian`, `QuotientRelationJacobian`, `KrullDimension` | Formal-smoothness criteria from a finite generating relation family with independent differentials, or from the additional finite-dimensional-domain quotient and Krull-dimension hypotheses. The quotient criterion does not assume the target is a domain. |
| `StandardSmooth`, `SmoothAt`, `SmoothLocus` | Regularity of prime localizations of standard-smooth field-algebras, smooth points of finite-type field-algebras, and stalks at smooth-locus points of schemes locally of finite type over a field. |
| `Dedekind`, `AffineDedekind` | Smooth field-algebras are regular; regular domains of dimension at most one are Dedekind; global sections of a smooth integral affine scheme of topological dimension at most one over a field are Dedekind. The ring results include the zero-dimensional field case. |

Useful entry points include
`IsLocalRing.cotangentSpaceEquivTensorKaehlerOfSection`,
`Algebra.Presentation.exists_relations_spanning_cotangentKernel`,
`Algebra.Extension.formallySmooth_of_span_eq_ker_of_linearIndependent`,
`Algebra.IsSmoothAt.isRegularLocalRing`, and
`AlgebraicGeometry.IsAffine.isDedekindDomain_globalSections_of_smooth`.
Read their module documentation for the precise parameters, universes and
typeclass assumptions; the names above do not assert that those assumptions
can be omitted.

The general converse from regularity to smoothness is not proved here. Selecting
independent relations alone does not prove that they generate the presentation
kernel, that their quotient is regular, or that the target is formally smooth.
The quotient-dimension criterion retains its domain, finite-dimension and
dimension-comparison hypotheses. The affine Dedekind result does not cover
nonaffine, nonintegral or higher-dimensional schemes. No complete formalization
of a cited book or of the Stacks Project is claimed.

## References, contributors and provenance

The cotangent comparison is related to the differential-rank formula in the
[Stacks Project, tag 00TR](https://stacks.math.columbia.edu/tag/00TR).
The local Jacobian criteria and the uncompleted regular-to-smooth direction are
related to [tag 00TT](https://stacks.math.columbia.edu/tag/00TT).
These are mathematical references, not bundled source text or claims of source
author endorsement. The implementation builds on the pinned mathlib APIs for
Kähler differentials, cotangent complexes, presentations, localization, regular
local rings, smoothness, schemes and dimension.

The earlier Lean implementation and later readiness work have distinct
contributor roles:

- Formalization Worker A executions supplied the split-residue conormal
  equivalence (`40b69b44336523fc583798de518d429376a8a821`) and the smooth-at-prime
  regularity bridge (`6a97c1683c26ae6798887909a8a739dc924a2b67`).
- Lattice supplied the algebraically closed comparison, standard-smooth
  regularity proof, dimension and presentation-relation infrastructure,
  localized compatibility bridges, smooth-locus adapter and library integration.
- Prism supplied the Dedekind ring consequences
  (`e52760c766ff03a7de2bbc08eb19312cfa1f8d3f`) and affine-scheme adapter
  (`d596d45d90aec0d1e20d800c680e0f9bd6e3b64d`).
- Later Formalization Worker B executions supplied the native-module/public-import
  migration and four initial private clients
  (`d5eea752141a7319601a1b4c82d8e5bb4be6f981`), then the two conormal evaluation
  theorems, two further private clients and explicit test target
  (`6d7652abe5928ea4f56e08493b92c643292f7df9`). These changes were accepted together
  after fresh non-author Worker A review; the earlier checkpoint was not separately
  accepted. They build on, rather than replace, the original contributor roles above.
- A later Worker B execution supplied the five-step StandardSmooth proof-style
  cleanup (`0cefdc76b87dd90570e00bdcaa82fcf1ecad3824`), independently reviewed by
  Worker A with unchanged mathematical statements and definitions.
- Independent non-author agent reviews accompany the development contributions.
  Lattice prepares the present standalone documentation and metadata; the final
  release has its own exact-candidate review and acceptance record.

Formal Frontier AI agents developed and reviewed the Lean code under human
project direction. Agent review is not human mathematical review. Mathlib's
contributors and external tools retain their own credit and license notices;
collective project authorship does not assert copyright ownership. Detailed
development provenance remains in the internal records, but no access to those
records is needed to use the mathematical library.

## License

Original project contributions are distributed under the Apache License,
Version 2.0 (`Apache-2.0`); the complete license text is in [LICENSE](LICENSE).
The pinned external dependencies retain their own licenses and notices. The
root `formalization.yaml` describes the project and its development-review
status; schema validity is not release acceptance.
