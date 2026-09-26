# Generated API reference

Native doc-gen4 display entries from all seventeen shipped Lean modules.
Import `SmoothRegularity` for the library API; `SmoothRegularityTest.PublicAPI`
contains checked private clients. Private helpers and some generated
declarations are not displayed by doc-gen4; this is not a full proof census.

Signatures retain all implicit binders, but are native display signatures,
not complete source declarations with bodies. Short names and universe
variables have the source module's namespace/import context. Source links
refer to the same checkout. See [generation and scope](README.md) and
[content manifest](api-manifest.json).

## SmoothRegularity.Conormal

### IsLocalRing.cotangentSpaceEquivTensorKaehlerOfSection

```lean
noncomputable def IsLocalRing.cotangentSpaceEquivTensorKaehlerOfSection {K : Type u} {R : Type v} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R] [Algebra.FormallyUnramified K (ResidueField R)] (s : ResidueField R →ₐ[K] R) (hs : Function.LeftInverse ⇑(algebraMap R (ResidueField R)) ⇑s) : CotangentSpace R ≃ₗ[ResidueField R] TensorProduct R (ResidueField R) Ω[R⁄K]
```

If the residue map of a local `K`-algebra has a `K`-algebra section and the
residue field is formally unramified over `K`, its cotangent space is the base
change of its module of Kähler differentials to the residue field.

[Source](../SmoothRegularity/Conormal.lean#L131-L159).

### IsLocalRing.cotangentSpaceEquivTensorKaehlerOfSection_apply_toCotangent

```lean
theorem IsLocalRing.cotangentSpaceEquivTensorKaehlerOfSection_apply_toCotangent {K : Type u} {R : Type v} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R] [Algebra.FormallyUnramified K (ResidueField R)] (s : ResidueField R →ₐ[K] R) (hs : Function.LeftInverse ⇑(algebraMap R (ResidueField R)) ⇑s) (x : ↥(maximalIdeal R)) : (cotangentSpaceEquivTensorKaehlerOfSection s hs) ((maximalIdeal R).toCotangent x) = 1 ⊗ₜ[R] (KaehlerDifferential.D K R) ↑x
```

The split-residue cotangent equivalence sends a class in the maximal ideal to
the corresponding differential in the residue-field base change.

[Source](../SmoothRegularity/Conormal.lean#L161-L171).

### IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv

```lean
noncomputable def IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv {K : Type u} {R : Type v} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R] (e : ResidueField R ≃ₐ[K] K) : CotangentSpace R ≃ₗ[ResidueField R] TensorProduct R (ResidueField R) Ω[R⁄K]
```

If a local `K`-algebra has residue field isomorphic to `K` as a `K`-algebra,
its cotangent space is the base change of its module of Kähler differentials to
the residue field.

[Source](../SmoothRegularity/Conormal.lean#L185-L197).

### IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent

```lean
theorem IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent {K : Type u} {R : Type v} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R] (e : ResidueField R ≃ₐ[K] K) (x : ↥(maximalIdeal R)) : (cotangentSpaceEquivTensorKaehlerOfResidueEquiv e) ((maximalIdeal R).toCotangent x) = 1 ⊗ₜ[R] (KaehlerDifferential.D K R) ↑x
```

The cotangent equivalence induced by a residue-field equivalence sends a
class in the maximal ideal to its differential in the base change.

[Source](../SmoothRegularity/Conormal.lean#L199-L206).

## SmoothRegularity.AlgClosed

### Ideal.residueFieldAlgEquivOfIsAlgClosed

```lean
noncomputable def Ideal.residueFieldAlgEquivOfIsAlgClosed {K : Type u} [Field K] [IsAlgClosed K] {S : Type v} [CommRing S] [Algebra K S] [Algebra.FiniteType K S] (m : Ideal S) [m.IsMaximal] : m.ResidueField ≃ₐ[K] K
```

The residue field of a maximal ideal of a finite-type algebra over an
algebraically closed field is isomorphic to the base field.

[Source](../SmoothRegularity/AlgClosed.lean#L37-L46).

### Ideal.cotangentSpaceEquivTensorKaehlerOfIsAlgClosed

```lean
noncomputable def Ideal.cotangentSpaceEquivTensorKaehlerOfIsAlgClosed {K : Type u} [Field K] [IsAlgClosed K] {S : Type v} [CommRing S] [Algebra K S] [Algebra.FiniteType K S] (m : Ideal S) [m.IsMaximal] : IsLocalRing.CotangentSpace (Localization.AtPrime m) ≃ₗ[m.ResidueField] TensorProduct S m.ResidueField Ω[S⁄K]
```

At a closed point of a finite-type algebra over an algebraically closed
field, the local cotangent space is the fibre of the module of Kähler
differentials of the original algebra.

[Source](../SmoothRegularity/AlgClosed.lean#L48-L62).

### Ideal.finrank_cotangentSpace_eq_finrank_tensorKaehlerOfIsAlgClosed

```lean
theorem Ideal.finrank_cotangentSpace_eq_finrank_tensorKaehlerOfIsAlgClosed {K : Type u} [Field K] [IsAlgClosed K] {S : Type v} [CommRing S] [Algebra K S] [Algebra.FiniteType K S] (m : Ideal S) [m.IsMaximal] : Module.finrank m.ResidueField (IsLocalRing.CotangentSpace (Localization.AtPrime m)) = Module.finrank m.ResidueField (TensorProduct S m.ResidueField Ω[S⁄K])
```

The algebraically closed case of the differential-rank formula at a
closed point (Stacks Project tag 00TR).

[Source](../SmoothRegularity/AlgClosed.lean#L64-L71).

## SmoothRegularity.CenteredPresentation

### Ideal.exists_generators_mem_of_isAlgClosed

```lean
theorem Ideal.exists_generators_mem_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K] {S : Type v} [CommRing S] [Algebra K S] [Algebra.FiniteType K S] (m : Ideal S) [m.IsMaximal] : ∃ (n : ℕ) (P : Algebra.Generators K S (Fin n)), ∀ (i : Fin n), P.val i ∈ m
```

A finite-type algebra over an algebraically closed field has a finite
family of algebra generators contained in any chosen maximal ideal.

[Source](../SmoothRegularity/CenteredPresentation.lean#L35-L64).

### Ideal.comap_aeval_eq_idealOfVars_of_generators_mem

```lean
theorem Ideal.comap_aeval_eq_idealOfVars_of_generators_mem {K : Type u} [Field K] [IsAlgClosed K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ} (m : Ideal S) [m.IsMaximal] (P : Algebra.Generators K S (Fin n)) (hP : ∀ (i : Fin n), P.val i ∈ m) : comap (MvPolynomial.aeval P.val) m = MvPolynomial.idealOfVars (Fin n) K
```

Over an algebraically closed field, if every distinguished generator maps
into a maximal ideal, its preimage in the polynomial ring is the ideal generated
by all variables. The finite-type instance is supplied by the generators.

[Source](../SmoothRegularity/CenteredPresentation.lean#L67-L109).

### Ideal.exists_presentation_mem_of_isAlgClosed

```lean
theorem Ideal.exists_presentation_mem_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K] {S : Type v} [CommRing S] [Algebra K S] [Algebra.FiniteType K S] (m : Ideal S) [m.IsMaximal] : ∃ (n : ℕ) (r : ℕ) (P : Algebra.Presentation K S (Fin n) (Fin r)), ∀ (i : Fin n), P.val i ∈ m
```

A finite-type algebra over an algebraically closed field has a finite
presentation whose distinguished generators belong to any chosen maximal
ideal.

[Source](../SmoothRegularity/CenteredPresentation.lean#L111-L130).

## SmoothRegularity.CotangentRelations

### Algebra.Presentation.exists_relations_spanning_cotangentKernel

```lean
theorem Algebra.Presentation.exists_relations_spanning_cotangentKernel {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] {n r : ℕ} (P : Presentation R S (Fin n) (Fin r)) (m : Ideal S) [m.IsPrime] : ∃ (f : Fin (Module.finrank m.ResidueField ↥(LinearMap.baseChange m.ResidueField P.toExtension.toKaehler).ker) → Fin r), Submodule.span m.ResidueField (Set.range fun (i : Fin (Module.finrank m.ResidueField ↥(LinearMap.baseChange m.ResidueField P.toExtension.toKaehler).ker)) => (LinearMap.baseChange m.ResidueField P.toExtension.cotangentComplex) (1 ⊗ₜ[S] Extension.Cotangent.mk ⟨P.relation (f i), ⋯⟩)) = (LinearMap.baseChange m.ResidueField P.toExtension.toKaehler).ker ∧ LinearIndependent m.ResidueField fun (i : Fin (Module.finrank m.ResidueField ↥(LinearMap.baseChange m.ResidueField P.toExtension.toKaehler).ker)) => (LinearMap.baseChange m.ResidueField P.toExtension.cotangentComplex) (1 ⊗ₜ[S] Extension.Cotangent.mk ⟨P.relation (f i), ⋯⟩)
```

Over an arbitrary commutative base and at any prime of the target, select
from the relations of a finite presentation exactly the residue-field dimension
of the kernel of the base-changed cotangent map. Their images are linearly
independent and span that kernel.

[Source](../SmoothRegularity/CotangentRelations.lean#L35-L119).

## SmoothRegularity.CotangentDimension

### Algebra.Presentation.finrank_cotangentKernel_add_finrank_cotangentSpace

```lean
theorem Algebra.Presentation.finrank_cotangentKernel_add_finrank_cotangentSpace {K : Type u} [Field K] [IsAlgClosed K] {S : Type v} [CommRing S] [Algebra K S] [FiniteType K S] {n r : ℕ} (P : Presentation K S (Fin n) (Fin r)) (m : Ideal S) [m.IsMaximal] : Module.finrank m.ResidueField ↥(LinearMap.baseChange m.ResidueField P.toExtension.toKaehler).ker + Module.finrank m.ResidueField (IsLocalRing.CotangentSpace (Localization.AtPrime m)) = n
```

For a finite polynomial presentation at a closed point over an
algebraically closed field, the dimension of the base-changed cotangent-map
kernel plus the local cotangent-space dimension is the number of polynomial
variables.

[Source](../SmoothRegularity/CotangentDimension.lean#L35-L67).

## SmoothRegularity.CotangentRelationTransport

### Algebra.Presentation.exists_relations_linearIndependent_localCotangent

```lean
theorem Algebra.Presentation.exists_relations_linearIndependent_localCotangent {K : Type u} [Field K] [IsAlgClosed K] {S : Type v} [CommRing S] [Algebra K S] [FiniteType K S] {n r : ℕ} (P : Presentation K S (Fin n) (Fin r)) (m : Ideal S) [m.IsMaximal] (q : Ideal P.toExtension.Ring) [q.IsMaximal] (hq : q = Ideal.comap (algebraMap P.toExtension.Ring S) m) : ∃ (f : Fin (Module.finrank m.ResidueField ↥(LinearMap.baseChange m.ResidueField P.toExtension.toKaehler).ker) → Fin r) (hrel : ∀ (i : Fin (Module.finrank m.ResidueField ↥(LinearMap.baseChange m.ResidueField P.toExtension.toKaehler).ker)), P.relation (f i) ∈ q), LinearIndependent q.ResidueField fun (i : Fin (Module.finrank m.ResidueField ↥(LinearMap.baseChange m.ResidueField P.toExtension.toKaehler).ker)) => (IsLocalRing.maximalIdeal (Localization.AtPrime q)).toCotangent ⟨(algebraMap P.toExtension.Ring (Localization.AtPrime q)) (P.relation (f i)), ⋯⟩
```

At a maximal prime over a closed point, select a minimal family of
presentation relations whose literal classes in the localized cotangent space
are linearly independent. The result also returns the membership proof needed
to form each cotangent class.

[Source](../SmoothRegularity/CotangentRelationTransport.lean#L44-L194).

## SmoothRegularity.LocalizedCotangentComplex

### Algebra.Presentation.localizedRelation

```lean
noncomputable def Algebra.Presentation.localizedRelation {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n r : ℕ} (P : Presentation K S (Fin n) (Fin r)) (m : Ideal S) [m.IsPrime] (j : Fin r) : ↥(Extension.localization m.primeCompl P.toExtension).ker
```

A presentation relation viewed in the kernel of the extension obtained by
localizing at a prime of the target.

[Source](../SmoothRegularity/LocalizedCotangentComplex.lean#L34-L71).

### Algebra.Presentation.linearIndependent_localizedCotangentComplex_of_localCotangent

```lean
theorem Algebra.Presentation.linearIndependent_localizedCotangentComplex_of_localCotangent {K : Type u} [Field K] [IsAlgClosed K] {S : Type v} [CommRing S] [Algebra K S] [FiniteType K S] {n r d : ℕ} (P : Presentation K S (Fin n) (Fin r)) (m : Ideal S) [m.IsMaximal] (q : Ideal P.toExtension.Ring) [q.IsMaximal] (hq : q = Ideal.comap (algebraMap P.toExtension.Ring S) m) (f : Fin d → Fin r) (hrel : ∀ (i : Fin d), P.relation (f i) ∈ q) (hli : LinearIndependent q.ResidueField fun (i : Fin d) => (IsLocalRing.maximalIdeal (Localization.AtPrime q)).toCotangent ⟨(algebraMap P.toExtension.Ring (Localization.AtPrime q)) (P.relation (f i)), ⋯⟩) : let E := Extension.localization m.primeCompl P.toExtension; LinearIndependent (IsLocalRing.ResidueField (Localization.AtPrime m)) fun (i : Fin d) => (LinearMap.baseChange (IsLocalRing.ResidueField (Localization.AtPrime m)) E.cotangentComplex) (1 ⊗ₜ[Localization.AtPrime m] Extension.Cotangent.mk (P.localizedRelation m (f i)))
```

A fixed family of presentation relations whose literal classes are linearly
independent in the cotangent space of the localized presentation ring remains
linearly independent after mapping into the residue-field base change of the
localized extension's cotangent complex.

[Source](../SmoothRegularity/LocalizedCotangentComplex.lean#L90-L328).

### Algebra.Presentation.exists_relations_linearIndependent_localizedCotangentComplex

```lean
theorem Algebra.Presentation.exists_relations_linearIndependent_localizedCotangentComplex {K : Type u} [Field K] [IsAlgClosed K] {S : Type v} [CommRing S] [Algebra K S] [FiniteType K S] {n r : ℕ} (P : Presentation K S (Fin n) (Fin r)) (m : Ideal S) [m.IsMaximal] (q : Ideal P.toExtension.Ring) [q.IsMaximal] (hq : q = Ideal.comap (algebraMap P.toExtension.Ring S) m) : let E := Extension.localization m.primeCompl P.toExtension; ∃ (f : Fin (Module.finrank m.ResidueField ↥(LinearMap.baseChange m.ResidueField P.toExtension.toKaehler).ker) → Fin r), (∀ (i : Fin (Module.finrank m.ResidueField ↥(LinearMap.baseChange m.ResidueField P.toExtension.toKaehler).ker)), P.relation (f i) ∈ q) ∧ LinearIndependent (IsLocalRing.ResidueField (Localization.AtPrime m)) fun (i : Fin (Module.finrank m.ResidueField ↥(LinearMap.baseChange m.ResidueField P.toExtension.toKaehler).ker)) => (LinearMap.baseChange (IsLocalRing.ResidueField (Localization.AtPrime m)) E.cotangentComplex) (1 ⊗ₜ[Localization.AtPrime m] Extension.Cotangent.mk (P.localizedRelation m (f i)))
```

At a closed point of an algebraically closed finite-type algebra, select a
minimal family of presentation relations whose localized representatives have
linearly independent images under the residue-field base change of the
localized extension's cotangent-complex map.

[Source](../SmoothRegularity/LocalizedCotangentComplex.lean#L330-L355).

## SmoothRegularity.RelationJacobian

### Algebra.Extension.formallySmooth_of_span_eq_ker_of_linearIndependent

```lean
theorem Algebra.Extension.formallySmooth_of_span_eq_ker_of_linearIndependent {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S] (P : Extension R S) [FormallySmooth R P.Ring] [Module.Free P.Ring Ω[P.Ring⁄R]] [Module.Finite P.Ring Ω[P.Ring⁄R]] {ι : Type t} [Finite ι] (x : ι → ↥P.ker) (hspan : Ideal.span (Set.range fun (i : ι) => ↑(x i)) = P.ker) (hli : LinearIndependent (IsLocalRing.ResidueField S) fun (i : ι) => (LinearMap.baseChange (IsLocalRing.ResidueField S) P.cotangentComplex) (1 ⊗ₜ[S] Cotangent.mk (x i))) : FormallySmooth R S
```

Let `P` be a formally smooth presentation of a local algebra `S`, with
finite free Kähler differentials. If a finite family of relations spans the
kernel of the presentation and its image under the residue-field base change
of the cotangent-complex map is linearly independent, then `S` is formally
smooth over the base.

This is the relation-basis form of the local Jacobian criterion.

[Source](../SmoothRegularity/RelationJacobian.lean#L30-L70).

## SmoothRegularity.QuotientRelationJacobian

### Algebra.Extension.formallySmooth_of_quotient_span_dimension_of_linearIndependent

```lean
theorem Algebra.Extension.formallySmooth_of_quotient_span_dimension_of_linearIndependent {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S] (P : Extension R S) [FormallySmooth R P.Ring] [Module.Free P.Ring Ω[P.Ring⁄R]] [Module.Finite P.Ring Ω[P.Ring⁄R]] {ι : Type t} [Finite ι] (x : ι → ↥P.ker) [IsDomain (P.Ring ⧸ Ideal.span (Set.range fun (i : ι) => ↑(x i)))] [FiniteRingKrullDim (P.Ring ⧸ Ideal.span (Set.range fun (i : ι) => ↑(x i)))] (hdim : ringKrullDim (P.Ring ⧸ Ideal.span (Set.range fun (i : ι) => ↑(x i))) ≤ ringKrullDim S) (hli : LinearIndependent (IsLocalRing.ResidueField S) fun (i : ι) => (LinearMap.baseChange (IsLocalRing.ResidueField S) P.cotangentComplex) (1 ⊗ₜ[S] Cotangent.mk (x i))) : FormallySmooth R S
```

Let `P` be a formally smooth presentation of a local algebra `S`, with
finite free Kähler differentials.  Suppose a finite family of relations has
linearly independent images under the residue-field base change of the
cotangent-complex map.  If the quotient by the ideal spanned by those
relations is a finite-dimensional domain whose Krull dimension is at most
that of `S`, then `S` is formally smooth over the base.

[Source](../SmoothRegularity/QuotientRelationJacobian.lean#L32-L75).

## SmoothRegularity.KrullDimension

### RingHom.bijective_of_surjective_of_ringKrullDim_le

```lean
theorem RingHom.bijective_of_surjective_of_ringKrullDim_le {R : Type u_1} {S : Type u_2} [CommRing R] [CommRing S] [IsDomain R] [FiniteRingKrullDim R] (f : R →+* S) (hf : Function.Surjective ⇑f) (hdim : ringKrullDim R ≤ ringKrullDim S) : Function.Bijective ⇑f
```

A surjective homomorphism from a finite-dimensional domain is bijective if
the target has Krull dimension at least that of the source.

[Source](../SmoothRegularity/KrullDimension.lean#L23-L51).

## SmoothRegularity.StandardSmooth

### Algebra.IsStandardSmooth.isRegularLocalRing_atPrime

```lean
theorem Algebra.IsStandardSmooth.isRegularLocalRing_atPrime {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S] [IsStandardSmooth K S] (q : Ideal S) [q.IsPrime] : IsRegularLocalRing (Localization.AtPrime q)
```

Every prime localization of a standard-smooth algebra over a field is a
regular local ring.

[Source](../SmoothRegularity/StandardSmooth.lean#L444-L451).

## SmoothRegularity.SmoothAt

### Algebra.IsSmoothAt.isRegularLocalRing

```lean
theorem Algebra.IsSmoothAt.isRegularLocalRing {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S] [FiniteType K S] (q : Ideal S) [q.IsPrime] (hq : IsSmoothAt K q) : IsRegularLocalRing (Localization.AtPrime q)
```

If a finite-type algebra over a field is smooth at a prime, then its
localization at that prime is a regular local ring.

[Source](../SmoothRegularity/SmoothAt.lean#L24-L54).

## SmoothRegularity.SmoothLocus

### AlgebraicGeometry.Scheme.Hom.isRegularLocalRing_of_mem_smoothLocus

```lean
theorem AlgebraicGeometry.Scheme.Hom.isRegularLocalRing_of_mem_smoothLocus {K : Type u} [Field K] {X : Scheme} (f : X ⟶ Spec ↧K) [LocallyOfFiniteType f] {x : ↥X} (hx : x ∈ smoothLocus f) : IsRegularLocalRing ↑(X.presheaf.stalk x)
```

A point in the smooth locus of a scheme locally of finite type over a field
has a regular local stalk.

[Source](../SmoothRegularity/SmoothLocus.lean#L26-L51).

## SmoothRegularity.Dedekind

### Algebra.Smooth.isRegularRing

```lean
theorem Algebra.Smooth.isRegularRing {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S] [Smooth K S] : IsRegularRing S
```

A smooth algebra over a field is a regular ring.

[Source](../SmoothRegularity/Dedekind.lean#L25-L33).

### IsRegularRing.isDedekindDomain_of_dimensionLEOne

```lean
theorem IsRegularRing.isDedekindDomain_of_dimensionLEOne {R : Type u} [CommRing R] [IsDomain R] [Ring.DimensionLEOne R] [IsRegularRing R] : IsDedekindDomain R
```

A regular domain of Krull dimension at most one is a Dedekind domain.

[Source](../SmoothRegularity/Dedekind.lean#L39-L68).

### Algebra.Smooth.isDedekindDomain_of_dimensionLEOne

```lean
theorem Algebra.Smooth.isDedekindDomain_of_dimensionLEOne {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S] [IsDomain S] [Ring.DimensionLEOne S] [Smooth K S] : IsDedekindDomain S
```

A smooth domain of Krull dimension at most one over a field is a Dedekind
domain.

[Source](../SmoothRegularity/Dedekind.lean#L74-L81).

## SmoothRegularity.AffineDedekind

### AlgebraicGeometry.IsAffine.isDedekindDomain_globalSections_of_smooth

```lean
theorem AlgebraicGeometry.IsAffine.isDedekindDomain_globalSections_of_smooth {K : Type u} [Field K] (X : Scheme) [IsAffine X] [IsIntegral X] (f : X ⟶ Spec ↧K) [Smooth f] (hdim : topologicalKrullDim ↥X ≤ 1) : IsDedekindDomain ↑(X.presheaf.obj (Opposite.op ⊤))
```

The global sections of a smooth integral affine scheme of topological
dimension at most one over a field form a Dedekind domain.

[Source](../SmoothRegularity/AffineDedekind.lean#L27-L52).

## SmoothRegularity

No native display entries (aggregate import or private examples).

## SmoothRegularityTest.PublicAPI

No native display entries (aggregate import or private examples).
