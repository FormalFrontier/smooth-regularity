# Smooth Regularity

Reusable Lean results on cotangent spaces, local Jacobian criteria, smoothness,
regularity and Dedekind domains for commutative algebras and schemes. The
library builds on mathlib and does not require a source-research repository.

Authors: Formal Frontier Agents.

## Headline results

- **Cotangent spaces and differentials.** For a local algebra over a field,
  [the cotangent-space equivalence](SmoothRegularity/Conormal.lean#L131) identifies
  the cotangent space with the residue-field base change of Kähler differentials
  when the residue map admits an algebra section and the residue field is formally
  unramified over the base. A [residue-field equivalence](SmoothRegularity/Conormal.lean#L185)
  supplies a special case. At a maximal ideal of a finite-type algebra over an
  algebraically closed field, [the closed-point comparison](SmoothRegularity/AlgClosed.lean#L48)
  applies. Neither the section nor the field hypotheses are automatic.
- **Presentation relations and local Jacobian criteria.** A finite presentation
  admits a [linearly independent selection](SmoothRegularity/CotangentRelations.lean#L35)
  of relations spanning its residue-field cotangent kernel at any prime over a
  commutative base; [dimension and localization](SmoothRegularity/CotangentDimension.lean)
  provide related comparison tools. To infer formal smoothness of a local target,
  [the relation criterion](SmoothRegularity/RelationJacobian.lean#L33) additionally
  requires a formally smooth presenting algebra with finite free differentials,
  a finite family *generating the presentation kernel*, and independence of its
  residue-field cotangent images. The [quotient criterion](SmoothRegularity/QuotientRelationJacobian.lean#L32)
  derives generation only with a finite-dimensional **domain quotient** and the
  stated Krull-dimension comparison; it does not require the target to be a domain.
- **Smooth implies regular.** A [standard-smooth field-algebra](SmoothRegularity/StandardSmooth.lean#L446)
  has regular prime localizations. The [smooth-at-prime result](SmoothRegularity/SmoothAt.lean#L24)
  requires a finite-type algebra over a field, and the
  [smooth-locus result](SmoothRegularity/SmoothLocus.lean#L25) requires a scheme
  locally of finite type over a field; smooth points have regular local stalks.
  The general converse, regular implies smooth, is **not** proved here.
- **Dedekind consequences.** [Smooth field-algebras are regular](SmoothRegularity/Dedekind.lean),
  and a [regular domain of dimension at most one](SmoothRegularity/Dedekind.lean#L36)
  is Dedekind (including the zero-dimensional field case). Thus a smooth domain
  over a field with that dimension bound is Dedekind. For schemes, the
  [global-sections theorem](SmoothRegularity/AffineDedekind.lean#L27) requires an
  **integral, affine, smooth** scheme over a field of topological dimension at
  most one; it does not assert the nonaffine, nonintegral or higher-dimensional
  cases.

See the [26-entry API reference](docs/API.md) for signatures and module docstrings,
and [the documentation guide](docs/README.md) for its coverage and provenance.

## Building and use

The project pins Lean `v4.34.0-rc2` and mathlib commit
`83abb3e776bdefcbc447a1e44d0debe4010039e5`; the resolved external packages are
recorded in `lake-manifest.json`. There are no other Formal Frontier library
dependencies. Install the pinned Lean toolchain with elan, then successfully fetch
the matching precompiled mathlib cache before building:

```sh
lake exe cache get
lake build
```

The default build includes the public-import clients in
`SmoothRegularityTest.PublicAPI`; to check them separately, run
`lake build SmoothRegularityTest.PublicAPI`. Import the full library with:

```lean
import SmoothRegularity
```

Individual modules, such as `SmoothRegularity.Conormal`,
`SmoothRegularity.RelationJacobian` and `SmoothRegularity.AffineDedekind`, may be
imported directly. The [ordinary-import clients](SmoothRegularityTest/PublicAPI.lean)
illustrate regularity, Dedekind, closed-point cotangent and conormal-evaluation
usage under the root import; their six declarations are intentionally private.
The hypotheses remain part of each result: the examples do not discharge them.
A build alone is not an all-declaration axiom audit or mathematical review.

### Lint scope and known convention departures

The existing reviewed lint evidence retains 45 header-parser warnings across
the fifteen implementation modules: truthful SPDX/agent-author notices do not
match mathlib's copyright-line template. One `privateModule` warning concerns
the six intentionally private persistent clients. These are documented,
accepted convention departures, not warning-free passes; no copyright owner
or dummy public test declaration is invented to suppress them. Five earlier
proof-style warnings were repaired. No root `lake check-lint` driver is configured.
After a successful pinned cache fetch and build, the supported direct-file
checks are:

```sh
for source in SmoothRegularity.lean SmoothRegularity/*.lean SmoothRegularityTest/*.lean; do
  lake env lean -Dlinter.mathlibStandardSet=true -Dlinter.style.header=true \
    -Dlinter.style.docString=true "$source" || exit
done
```

These instructions and historical dispositions do not claim a new lint run.

### Conormal evaluation migration

Under an ordinary `import SmoothRegularity`, the conormal equivalences have
public evaluation theorems on classes of the maximal ideal:
`IsLocalRing.cotangentSpaceEquivTensorKaehlerOfSection_apply_toCotangent s hs x`
and
`IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent e x`.
Both identify the result with `1 ⊗ₜ[R] KaehlerDifferential.D K R x.1`.
For the residue-field case, use
`exact IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent e x`;
the section case uses the corresponding theorem with `s hs x`. External proofs
that previously used `rfl` for this evaluation must migrate to these theorems:
reduction through the private implementation is **not** promised under an
ordinary import. The old ordinary-import `rfl` proof is known to fail after the
module migration. This is a breaking migration, not definitional compatibility.

### Expected build cost

For the 17-module source set, a 2026-09-26 agent-container run used the pinned
environment and one Lean worker (`LEAN_NUM_THREADS=1`). Its successful matching
cache step took about 86 seconds. A focused `StandardSmooth` build then took
6 seconds, followed by 32 seconds for the remaining default build: about 124
seconds for those sequential commands, excluding checkout and gaps between
commands. The default-build figure is **not** a standalone cold-build
measurement: the focused module was already compiled. A subsequent explicit
public-client target check took 2 seconds with those outputs already present.
These are examples, not guarantees for other machines or networks; an uncached
mathlib source build was neither required nor measured.

The focused/default commands' start/end container-memory samples were about
11.8 GiB, including the entire worker and resident caches: **not** an isolated
compiler peak or a demonstrated minimum. The run used a 15 GiB memory bound;
allow comparable headroom as a planning estimate, adjusting for machine, cache
state and concurrent work. Timings use whole-second timestamps. Separate proof
audits and native documentation generation have different workloads and are not
included in this example; these figures say nothing about extracted executable
performance.

## Scope and limitations

The [centred presentation](SmoothRegularity/CenteredPresentation.lean) result
chooses generators at a closed point only over an algebraically closed field.
The [transport](SmoothRegularity/CotangentRelationTransport.lean) and
[localized cotangent-complex](SmoothRegularity/LocalizedCotangentComplex.lean)
lemmas require compatible primes and residue fields. Selecting independent
relations by itself does **not** prove that they generate the presentation
kernel, that their quotient is regular, or that the target is formally smooth.
No complete formalization of a cited book or of the Stacks Project is claimed.

## References and contributors

The cotangent comparison relates to the differential-rank formula in the
[Stacks Project, tag 00TR](https://stacks.math.columbia.edu/tag/00TR).
The local Jacobian criteria and uncompleted regular-to-smooth direction relate
to [tag 00TT](https://stacks.math.columbia.edu/tag/00TT). These are mathematical
references, not bundled source text or claims of source-author endorsement.
The implementation builds on mathlib's Kähler differentials, cotangent complexes,
presentations, localization, regular local rings, smoothness, schemes and dimension.

Lattice contributed the algebraically closed comparison, standard-smooth
regularity proof, relation and dimension infrastructure, localized bridges,
smooth-locus adapter and integration. Prism contributed the Dedekind ring and
affine-scheme results. Other Formal Frontier Agents contributed the split-residue
conormal and smooth-at-prime bridges, native-module/public-import support, the
propositional conormal evaluation API and independent non-author agent review.
Formal Frontier AI agents developed and reviewed the Lean code under human
project direction; agent review is not human mathematical review. Mathlib's
contributors and external tools retain their own credit and notices. Collective
authorship does not assert copyright ownership; source files carry SPDX and
author notices without inventing a copyright holder. Detailed development
evidence is retained privately, but is not needed to use the library.

## License

Original project contributions are distributed under the Apache License,
Version 2.0 (`Apache-2.0`); see [LICENSE](LICENSE). Pinned external dependencies
retain their own licenses and notices. The [project metadata](formalization.yaml)
records the library's scope and agent review; neither metadata validity nor
generated documentation alone certifies mathematical proofs.
