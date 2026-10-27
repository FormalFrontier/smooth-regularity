# Generated API reference

Conormal entries below are generated from the current source declaration headers
and docstrings, retaining namespace, universe and shared-variable context.
The remaining 22 entries are historical native doc-gen4 display signatures,
not a census of the current library. See [generation and scope](README.md)
and the [content manifest](api-manifest.json) for their distinct input bindings.
Neither source-text extraction nor documentation generation is a proof audit.

Import `SmoothRegularity` for the library API. Private helpers, model proofs
and generated declarations are outside this display reference.

## SmoothRegularity.Conormal

### Algebra.Extension.cotangentComplex_injective_of_infinitesimalSection

```lean
namespace Algebra.Extension
universe u v w
variable {K : Type u} {S : Type v} [CommRing K] [CommRing S] [Algebra K S]
theorem cotangentComplex_injective_of_infinitesimalSection (P : Extension.{w} K S)
    (s : S →ₐ[K] P.infinitesimal.Ring)
    (hs : Function.LeftInverse (algebraMap P.infinitesimal.Ring S) s) :
    Function.Injective P.cotangentComplex
end Algebra.Extension
```

A section of the first-order quotient `P/I² → S` makes the canonical
conormal map injective. No section into `P` is required.

[Source](../SmoothRegularity/Conormal.lean#L92).

### Algebra.Extension.cotangentEquivCotangentSpaceOfFormallyEtale

```lean
namespace Algebra.Extension
universe u v w
variable {K : Type u} {S : Type v} [CommRing K] [CommRing S] [Algebra K S]
@[expose] noncomputable def cotangentEquivCotangentSpaceOfFormallyEtale
    (P : Extension.{w} K S) [Algebra.FormallyEtale K S] :
    P.Cotangent ≃ₗ[S] P.CotangentSpace
end Algebra.Extension
```

The canonical conormal equivalence of an extension with formally étale
target over the base. Its forward map is `P.cotangentComplex`.

[Source](../SmoothRegularity/Conormal.lean#L100).

### Algebra.Extension.cotangentComplex_bijective_of_formallyEtale

```lean
namespace Algebra.Extension
universe u v w
variable {K : Type u} {S : Type v} [CommRing K] [CommRing S] [Algebra K S]
theorem cotangentComplex_bijective_of_formallyEtale (P : Extension.{w} K S)
    [Algebra.FormallyEtale K S] : Function.Bijective P.cotangentComplex
end Algebra.Extension
```

If the target of an extension is formally étale over the base, its
canonical conormal map is bijective. The extension ring need not be smooth.

[Source](../SmoothRegularity/Conormal.lean#L123).

### Algebra.Extension.cotangentEquivCotangentSpaceOfFormallyEtale_toLinearMap

```lean
namespace Algebra.Extension
universe u v w
variable {K : Type u} {S : Type v} [CommRing K] [CommRing S] [Algebra K S]
theorem cotangentEquivCotangentSpaceOfFormallyEtale_toLinearMap
    (P : Extension.{w} K S) [Algebra.FormallyEtale K S] :
    (cotangentEquivCotangentSpaceOfFormallyEtale P).toLinearMap =
      P.cotangentComplex
end Algebra.Extension
```

The conormal equivalence has the existing cotangent-complex map as its
underlying linear map.

[Source](../SmoothRegularity/Conormal.lean#L129).

### Algebra.Extension.cotangentEquivCotangentSpaceOfFormallyEtale_apply_mk

```lean
namespace Algebra.Extension
universe u v w
variable {K : Type u} {S : Type v} [CommRing K] [CommRing S] [Algebra K S]
@[simp] theorem cotangentEquivCotangentSpaceOfFormallyEtale_apply_mk
    (P : Extension.{w} K S) [Algebra.FormallyEtale K S] (x : P.ker) :
    cotangentEquivCotangentSpaceOfFormallyEtale P (Cotangent.mk x) =
      1 ⊗ₜ[P.Ring] KaehlerDifferential.D K P.Ring x.1
end Algebra.Extension
```

A kernel class is sent to its differential in the target base change.

[Source](../SmoothRegularity/Conormal.lean#L137).

### IsLocalRing.cotangentSpaceEquivTensorKaehlerOfSection

```lean
namespace IsLocalRing
universe u v
variable {K : Type u} {R : Type v} [CommRing K] [CommRing R] [IsLocalRing R]
  [Algebra K R]
noncomputable def cotangentSpaceEquivTensorKaehlerOfSection
    [Algebra.FormallyUnramified K (ResidueField R)]
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s) :
    LinearEquiv (RingHom.id (ResidueField R)) (CotangentSpace R)
      (ResidueField R ⊗[R] Ω[R⁄K])
end IsLocalRing
```

If the residue map of a local `K`-algebra has a `K`-algebra section and the
residue field is formally unramified over `K`, its cotangent space is the base
change of its module of Kähler differentials to the residue field.

[Source](../SmoothRegularity/Conormal.lean#L255).

### IsLocalRing.cotangentSpaceEquivTensorKaehlerOfSection_apply_toCotangent

```lean
namespace IsLocalRing
universe u v
variable {K : Type u} {R : Type v} [CommRing K] [CommRing R] [IsLocalRing R]
  [Algebra K R]
theorem cotangentSpaceEquivTensorKaehlerOfSection_apply_toCotangent
    [Algebra.FormallyUnramified K (ResidueField R)]
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s)
    (x : maximalIdeal R) :
    cotangentSpaceEquivTensorKaehlerOfSection s hs
        ((maximalIdeal R).toCotangent x) =
      1 ⊗ₜ[R] KaehlerDifferential.D K R x.1
end IsLocalRing
```

The split-residue cotangent equivalence sends a class in the maximal ideal to
the corresponding differential in the residue-field base change.

[Source](../SmoothRegularity/Conormal.lean#L285).

### IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv

```lean
namespace IsLocalRing
universe u v
variable {K : Type u} {R : Type v} [CommRing K] [CommRing R] [IsLocalRing R]
  [Algebra K R]
noncomputable def cotangentSpaceEquivTensorKaehlerOfResidueEquiv
    (e : ResidueField R ≃ₐ[K] K) :
    LinearEquiv (RingHom.id (ResidueField R)) (CotangentSpace R)
      (ResidueField R ⊗[R] Ω[R⁄K])
end IsLocalRing
```

If a local `K`-algebra has residue field isomorphic to `K` as a `K`-algebra,
its cotangent space is the base change of its module of Kähler differentials to
the residue field.

[Source](../SmoothRegularity/Conormal.lean#L309).

### IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent

```lean
namespace IsLocalRing
universe u v
variable {K : Type u} {R : Type v} [CommRing K] [CommRing R] [IsLocalRing R]
  [Algebra K R]
theorem cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent
    (e : ResidueField R ≃ₐ[K] K) (x : maximalIdeal R) :
    cotangentSpaceEquivTensorKaehlerOfResidueEquiv e
        ((maximalIdeal R).toCotangent x) =
      1 ⊗ₜ[R] KaehlerDifferential.D K R x.1
end IsLocalRing
```

The cotangent equivalence induced by a residue-field equivalence sends a
class in the maximal ideal to its differential in the base change.

[Source](../SmoothRegularity/Conormal.lean#L323).

### IsLocalRing.cotangentSpaceEquivTensorKaehlerOfFormallyEtale

```lean
namespace IsLocalRing
universe u v
variable {K : Type u} {R : Type v} [CommRing K] [CommRing R] [IsLocalRing R]
  [Algebra K R]
@[expose] noncomputable def cotangentSpaceEquivTensorKaehlerOfFormallyEtale
    [Algebra.FormallyEtale K (ResidueField R)] :
    CotangentSpace R ≃ₗ[ResidueField R] (ResidueField R ⊗[R] Ω[R⁄K])
end IsLocalRing
```

If the residue field of a local algebra is formally étale over the
commutative base, the canonical conormal map is a residue-field linear
equivalence. A residue section into the local ring is not required.

[Source](../SmoothRegularity/Conormal.lean#L332).

### IsLocalRing.cotangentSpaceEquivTensorKaehlerOfFormallyEtale_restrictScalars

```lean
namespace IsLocalRing
universe u v
variable {K : Type u} {R : Type v} [CommRing K] [CommRing R] [IsLocalRing R]
  [Algebra K R]
theorem cotangentSpaceEquivTensorKaehlerOfFormallyEtale_restrictScalars
    [Algebra.FormallyEtale K (ResidueField R)] :
    (cotangentSpaceEquivTensorKaehlerOfFormallyEtale
      (K := K) (R := R)).toLinearMap.restrictScalars R =
      KaehlerDifferential.kerCotangentToTensor K R (ResidueField R) ∘ₗ
        (Ideal.Cotangent.equivOfEq
          (RingHom.ker (algebraMap R (ResidueField R))) (maximalIdeal R)
          (by rw [ResidueField.algebraMap_eq, ker_residue])).symm.toLinearMap
end IsLocalRing
```

After identifying the kernel of the residue map with the maximal ideal,
the forward map is Mathlib's canonical conormal map.

[Source](../SmoothRegularity/Conormal.lean#L349).

### IsLocalRing.cotangentSpaceEquivTensorKaehlerOfFormallyEtale_apply_toCotangent

```lean
namespace IsLocalRing
universe u v
variable {K : Type u} {R : Type v} [CommRing K] [CommRing R] [IsLocalRing R]
  [Algebra K R]
@[simp] theorem cotangentSpaceEquivTensorKaehlerOfFormallyEtale_apply_toCotangent
    [Algebra.FormallyEtale K (ResidueField R)] (x : maximalIdeal R) :
    cotangentSpaceEquivTensorKaehlerOfFormallyEtale (K := K)
        ((maximalIdeal R).toCotangent x) =
      1 ⊗ₜ[R] KaehlerDifferential.D K R x.1
end IsLocalRing
```

The residue-field equivalence sends a maximal-ideal class to its
differential in the residue-field base change.

[Source](../SmoothRegularity/Conormal.lean#L361).

### IsLocalRing.cotangentSpaceEquivTensorKaehlerOfFormallyEtale_eq_ofSection

```lean
namespace IsLocalRing
universe u v
variable {K : Type u} {R : Type v} [CommRing K] [CommRing R] [IsLocalRing R]
  [Algebra K R]
theorem cotangentSpaceEquivTensorKaehlerOfFormallyEtale_eq_ofSection
    [Algebra.FormallyEtale K (ResidueField R)]
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s) :
    cotangentSpaceEquivTensorKaehlerOfFormallyEtale (K := K) (R := R) =
      cotangentSpaceEquivTensorKaehlerOfSection s hs
end IsLocalRing
```

When a residue section into the local ring is also supplied, the
formally étale and split-residue equivalences agree.

[Source](../SmoothRegularity/Conormal.lean#L370).

### IsLocalRing.cotangentSpaceEquivTensorKaehlerOfFormallyEtale_eq_ofResidueEquiv

```lean
namespace IsLocalRing
universe u v
variable {K : Type u} {R : Type v} [CommRing K] [CommRing R] [IsLocalRing R]
  [Algebra K R]
theorem cotangentSpaceEquivTensorKaehlerOfFormallyEtale_eq_ofResidueEquiv
    [Algebra.FormallyEtale K (ResidueField R)] (e : ResidueField R ≃ₐ[K] K) :
    cotangentSpaceEquivTensorKaehlerOfFormallyEtale (K := K) (R := R) =
      cotangentSpaceEquivTensorKaehlerOfResidueEquiv e
end IsLocalRing
```

Under the shared formally étale hypothesis, the canonical residue-field
equivalence agrees with the one induced by a residue-field equivalence.

[Source](../SmoothRegularity/Conormal.lean#L383).
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
