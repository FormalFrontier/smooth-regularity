# Smooth Regularity

Reusable Lean results on cotangent spaces, local Jacobian criteria, smoothness,
regularity and Dedekind domains for commutative algebras and schemes. The
library builds on mathlib and does not require a source-research repository.

Authors: Formal Frontier Agents.

## Headline results

- **First-order conormal maps.** For an arbitrary extension `P → S` of
  commutative algebras over a commutative ring `K`, a `K`-algebra section of
  `P/I² → S` makes [the canonical conormal map](SmoothRegularity/Conormal.lean)
  `I/I² → S ⊗[P] Ω[P⁄K]` injective. If `S` is formally étale over `K`, this
  map is an equivalence. Neither result assumes smoothness of `P` or a section
  into `P`. The equivalence's forward map is Mathlib's `cotangentComplex`,
  with an evaluation law on every kernel class.
- **Cotangent spaces and differentials.** For a local algebra over a
  commutative ring, [the residue-field equivalence](SmoothRegularity/Conormal.lean)
  identifies its cotangent space with the residue-field base change of Kähler
  differentials when the residue field is formally étale over the base; no
  residue section is needed. It agrees with the split-residue construction
  when a section is supplied. The latter requires only formal unramifiedness
  of the residue field, and also applies to a supplied residue-field algebra
  equivalence with the base. At a maximal ideal of a finite-type algebra over
  an algebraically closed field, [the closed-point comparison](SmoothRegularity/AlgClosed.lean#L48)
  applies. Formal étaleness of the residue extension is not automatic.
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

The [Artinian criteria](SmoothRegularity/Artinian.lean) state that a commutative
Artinian local ring is regular if and only if it is a field, and that a
commutative Artinian ring is regular if and only if it is reduced, including
the zero ring. The proofs use the dimension-zero and localization criteria
from Mathlib. See the [signature and boundary guide](docs/Artinian.md).

See the [generated API reference](docs/API.md) for all fourteen Conormal
signatures with their commutative-ring hypotheses, independent universes and
canonical-map laws, alongside 22 older native display entries for other modules.
The [documentation guide](docs/README.md) distinguishes the source-header and
native input bindings. The Artinian signatures are documented separately.

## Using the library

Add the library to your `lakefile.toml`:

```toml
[[require]]
name = "smooth-regularity"
git = "https://github.com/FormalFrontier/smooth-regularity.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves the dependency when you
first add it or explicitly update it; your `lake-manifest.json` keeps that
resolution until another update. For a fixed reproducible version, replace
`main` with the full commit of a published release. Dependencies from another
Formal Frontier library or the incubator use the GitHub URL and full published
release commit, not moving `main`, development commits or PR heads.

Import the full library with:

```lean
import SmoothRegularity
```

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
imported directly. The [ordinary-import examples](SmoothRegularityTest/PublicAPI.lean)
include private hypothesis-parametric clients illustrating regularity, Dedekind,
closed-point cotangent and conormal-evaluation usage under the root import.
The polynomial and dual-number augmentations over any nontrivial commutative
ring also give named proofs of the conormal image formulas `1 ⊗ dX` and
`1 ⊗ dε` and of their nonvanishing. These use coefficient one and the
square-zero coordinate, respectively, to detect nonzero classes modulo the
kernel square. The dual-number example does not assume a smooth extension ring.

The same test module contains the public theorem
`MvPolynomial.isRegularRing_fin_two_rat`, proving
`IsRegularRing (MvPolynomial (Fin 2) ℚ)` by smoothness over `ℚ` using only the
root library import. The declaration belongs to `SmoothRegularityTest.PublicAPI`:
import that test module to use it; `import SmoothRegularity` does not re-export it.

The [Artinian clients](SmoothRegularityTest/Artinian.lean), also included in the
default test target, establish Artinianity and reducedness or nonreducedness
for fields, finite products of fields, `ZMod 4` and the zero ring using Mathlib.
Their regularity conclusions use the two Artinian equivalences. The public
zero-ring theorem `PUnit.isRegularRing_and_not_isField` belongs to
`SmoothRegularityTest.Artinian`; the root library import does not re-export it.

A build alone is not an all-declaration axiom audit or mathematical review.

### Linting

The Lake configuration enables Mathlib's standard syntax linters, disables
implicit auto-binding, and uses the Batteries environment-linter driver.
The header-template linter is disabled because the source files use SPDX and
agent-author notices rather than an invented copyright holder. After building,
run the environment linters with:

```sh
lake lint
```

The CI lint step is required. The private mathematical clients belong to the
separate test library; the non-test library has the ordinary environment-lint
scope.

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
